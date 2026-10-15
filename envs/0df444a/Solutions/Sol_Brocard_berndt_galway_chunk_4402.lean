-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4402
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:30:00.608987+00:00
-- url     : https://prove2.me/submissions/0910d2af-c780-4d48-b7b9-7553573e2cdc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 791546762 ≤ n < 791726618 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 791548012 1250 791546762 791546831
    0x110d120b3106060801140102011803030c1d0d06050c040933050a170a1b050108181c0c050102030a05041a0108030301120218150102121309 61
    0x3004920011a00c12060801c0d0703040c01500c0d00080000102c0e02d690080b5000107421000500500300c10a501c4103585806100000300c1140400c01c12030244c0000404400003915180311074a155070001c0040e03884407013803980f4a041707040880064a2509102d0000380501d840d0000600040030003800d950040c0341e81d00041c8101c10b26900d80d400c0407149088001e50303180c94a9140b100d542e4245261320142c490242c00c446e29141008030007459200c810300761038124801d103c0301f0307000a100b0300b160100c1042030300c046c8400a0708000000d021000d00610810a01080034900f102d01c5e0800655030140045034244000959100581102c0c0b84011400103811580000b0500c07900c410268822031140f40254910254071102c00b03c000002c0d0000e200c1e25005910910050013504118030740c0c2e114051006003900d24500c50105150186401201c403401c44e007000c01048039065030140150340011201010f03403454240030041c3e00000386590f000c0c8555a503600c2c500404450981c049501c40d043c250700c100c04 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 791549262 1250 791548012 791548039
    0x31609030c030c0810050405030d1806060927080712140a120e0a0309050915090f0411060a091406040308121902043210020a03020c01110d120b 63
    0xf210705a541c0b007465004e2180b03645d1290729040b1482803500880d40030029524000950420740c011300904407100044c012070b10f40d4100010124803800000381070206011450740b80c000005c441621385c02030541c0c444003202c00b020f00002e0080e005c07550055840b0031100018943c05070300311100c02c210644510045d01c0000c501105607003001c01207840681c508400c0c080c2c107000c289141d854a035034280060110f00320280c00d10032840d0081541c0e61101040030348504058540c00021801c0b901611640c221580480512041c0440310b00c5400188206568007172034140310000003400d41480744242e207200c1700d081001402c81d075108400c0380d009540240541d074880608980b090006481910802000c90040070b01220003071a50003642c044444041c40101e551504c480c2410384800e000d81003c080014032160a14035030b40b480860049200e49030300500c07082c00d1b24078020340b44c040c28801e0941070002100e03588030038074000140c09012603180e00d0b00c800b2400200c0001005030201c6c2c102c0d903510908558156 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 791550512 1250 791549262 791549273
    0x20a030c02190e131b03020112240e040209010501170a0504150501092a05090114070203160e0f0c040303030b0a090c020a0203070b0301080a200603070509040e12031609030c03 77
    0x1004040c005c0c56440000300d045074500903194280d12009020551441626250842c0f96001e031400680540000e4141d11000c00240c0001825800405250b00c114052106500b012030000c3e0141c0401c1c2091611940010a0f1240850300140716407040d5440c4c3c3c000404104024507141c0e140b00041c03106002d00d5858285140181c0302c1e541015103640700c0c42d0307190326003008065242024101d05803a11840d040e82c603001101d031210100044511a1020001000142c80c1080004400b48241010281e01802c20041050419015005141a800460a0140c281070b6002210f003101c1e40360030001540100074000c100341e81c919621546403d80703006000201d003a00410b291032024070807800da5084948444c07040c0e40030700003030042c0c0000380c2c000d43d00080040d1100c1e0064848030404c10400004815540c00582581e0040b01c8510002d080480c0415103418540241c10308101c141c4083c201000d551443c4240a00000f80022480c0d6000a0a90340d124040e03000c80025540208a40c0411510b030f0421 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 791551762 1250 791550512 791550541
    0x12050c04020a2705180f0f0411010c05030f0301080f0d031505130f0609062c0403110a0507141804050d30020c060906070503072a0f050706020a030c02190e 68
    0xb50306c4d81c2c0c004030002074001c4594254203103d02c4d0303c4a6000c00003051480119205001c007402102d4503c410003103811220121009107000740105401498241c007103400b2a82040d01001d4040c05040c05d001c0d054440034030034000001511000d460b4021642c440902800261504c0c40c01d84180c189000d0740441e49002ca13800c200c054400540e8148100020344501544506110703002182411800011400003403040ba0740e001c00d20050b004854511f1915112541440d242c0e902a2005d44106001c1c02490b0a10852203210030660420900b01e0380b40a403241078071400c9004035641080311400407840c3e8051140713070343c81510300280c0c0e0b13114002c409142c3c1d01000f5402066841840c2c490b540010360351841c0001c03014444d0600b030f0745803801c60b21400b005480c0012070804040030000d5414071202d03051140c41c0c00000440c0038044901860000381051420301009400010440d0001c0288201280e008020900d00a0f03042d1403001d5442c07201c0e00591b054061540141c808900c400040c0328030031481010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 791553012 1250 791551762 791551771
    0x2040c09061808100e01090209010f1d040803070c061107110a1a07080c0312190e07062a08031003110d0b06010e01110712050c04020a270518 62
    0x103500c0325201421a0350101d03641c0c42d2181c00000c1c0d108403e0282c09002035000b100040d2403050004c07c013152680d00080071300ca0b090b0011001100400010004500d00c91903405014400001e40c0c80141001e849140300f6100041c103040510024010b00f404000d0980e2201340c1645120f4050382d160003844c40c1a400703616510149a203d80340040780451085180301010000075141011180707003040507030340d440e001d40082c6000d032100c1c0070134030903240f00000e01180c0602c2055441d1141400040b1030b0003a01c200d4a40300040302c07041c2e21599060003840c1d004513030420421080c8024108261a0884880c0d01c4212108020010840802400842d101c3c0440719401d0ba48621245007481801074184038080171400c4014242c0507040c400f090140d40903022a00c68540189080007030034912040c802c1ca0302020742e0246404100c84420f00052210900c13208402504c11101540341055961008048003032440c90310310760906840340445840c0c41905500000e003809020b41c01c0e940e084c40c40b9120a41012503 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 791554262 1250 791553012 791553017
    0x504021b0c18010509070c02030106030303051602060f010501210e0a0210030207020607110d051c20030702120f01060b070c06020105060d061508030c0a121e050f0702040c0906 77
    0x6074603403520b8201034064001c2541401c20445a2074582045001c00b0050005818044011840780158900380100e0000d10300030344000c20070341029060203813804081d111903800c40d0444824458014514003800381103a00920b055482e101407600004030010600000c083c0d140c1c9804805d6041581c045214400700d80212014014100c1c84a000c2d8140e12810400a5100b0800c00c10705001503004102c124524a010302461419003060350340524159030b10110300340509030132041900395540400719100a400740507106c81212140c000342c03941d900485400911685103610b68002d00a01000b060007070581c00c000070300c48203548101c0704850350701805041d1440c0c1201540811030500502540f8041c02016000c1202041c040d1102002400c01800181c40a800c9801c001080381040004d84000d41d41d05004e00710410192501c280044640031116041c071103d60f000c42c0d40c103807801001c000500c00c281800c03540c171940d10340444001c0c414048000d5000d850310b0300c0d0201841e4484001800e59180b074 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 791555512 1250 791554262 791554273
    0x10e0706080f0f0c0a0504090f0b040506030d090302060d0207021c0203240a0e0f15010806010f0602060c130e09010515040e0a03030207060f06180f021305010807090504021b 76
    0x100801808001c048940740201a0b443c40841c202609040040000c0091440d0682c1000d48030401d5405654084482092140c2c03599012152031600303200c0c0c241c00080440060541254080340504052000c1c031010307100e80d9010483c2d241c031040e940c0441c1c049982c01810b440e08181c203004054a0b41300d22400c1640a44214140c01c07070b03505100380b1100c070000307170003005075505559515069019220003002c1c0d0159000c1c41c0c17078141e0b6843c002c00c4000105625000e0f880306079070604120f589803030030580c0265803010714080b0400c00c1039008102650014800320a0507a602d0f0300c810b40b003180d1181d650050500000c00420824a0035040d030020b405002e0052200d034100130403000700300c16105455403550280d008011401c0009001e41d00525000b44600c90208449500d04011000c40b0313841c0d40041c0c031401460f046950702941a01ca0100b2420135608218200820300e28941040c40660003010b06000680000c58041801001b440c002480010030665a62090038550132070400c140c1070006143c404d0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 791556762 1250 791555512 791555521
    0x40b1306081f030b0a110301090f0e06070512090c0a091a01020a0201140d110a090e01151718010905010b12030c2e020a0c0215130302040c050c010e070608 68
    0x1e500c1010b1110301480480c040310741507442e0300b5071103a40602607000e130325900c5002e180900440c101660003402400800981c00b103441c81203030f040c0c898000c8a02c5403a08180e040203207a0760440300b52075001c100b4500194141d501c090419151201c5210017540c031002d0310400286000c00c0e6085840c4547c00c0e49030381501110080016652001c42d21002400f1400c10380804402858201c00341405480d05580031450925004d008903227940a040e00d180052002c1905000c42e540f694512401015035180408400c1c11402000340800c510301d1400c092021030b40c011070500a0489038880b08032880800030010350100f45032442c000e042100e6238074080c5194102c541c104041c04400d4502084045001d81076800600140d80c0d40460309113180503d02500b1042444440d80310b101a024429050f110044000480c2c01007003845940a00b03d4344208008020f24040c0a8a800060084a0341500c010628004036031042c1d55501400c804456190700e4510414010040081d04030206d0b80e03e0b07280c040c41e035240c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 791558012 1250 791556762 791556781
    0x305010506270708060a1d1f06020c0f0a0e0a06140a05090a181707061413030f1b060b0a091119090308030c120a061d0408040b130608 59
    0x800000c0d842c00030012100140000c1d00840055601c4040108111b010300d0315451184d10450b8a0280409060740c2c05e01000a07403400780100039104000e0b080b500c84042e1420800942d511103610a0902408403010002e58544814150501902c100b41d030103080b078541902803000804c10352007480100c0040c048248101d01340031b41305205440303014201103130315034a41c001c1e034001d86021964403448041032020000469800e00b142c5500c680e004071417599404250600c0f80685001080385002c500400d0705002c10851202441d540590f4903052484032079000a4044c1c03448894a00e2036448036822400c00c03410094190310100e0300110450b50a030549e626403481008aa1421440030001081044070061520300c41501c08002d20103031410022039601e03690742071283d8006842d07588840d50007280200e01092032480e400c2c2c0c4980d107110200b00341460041ea00d8800b10f10440607100c1c02c211308000c60203100d02d40e805c0368054120902015990043c3c040100480c01040c494907000401040100d0394210 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 791559262 1250 791558012 791558059
    0x1d030307090b031b220e041203050705040e0403020c03010608070810092301020415050306011d0603011e03080f04030219080303150f040e0105060a09140a0902060408070305010506 79
    0x880c0e07803d0a20709107031640c1e452141c0d01821103c00319041001c49001342d00ca405d846540500320071800c038203203410300b8030f40310381c0040e800480c403010306003402e007049841c55114040d00c04440c0c0c170800300e20170758a580c2004d0741412412244150594240840403900000000b10541180c141104454402d40900309240032071300c038a00300402040040811401780c00e8075608913055a84d140d0001450301d541c80c800c2e03141c0c420030703854407502044000c41002455030304020000141a40f045541c0c034203002c1d010000d007a42c40140901100c00308a440c02e003008024110341b41d00036641c0604903da40d00c1058007021003c1e0030922089101d10403e45503080d6280c0716040300c03400c890300c820081d4203588841c00d1440200344088800c40d04607440550008040e0341d01e0069070f03140301204000085608020301840005d00e10f68100005445c00c0c000f04c520490140424207610289001001441c0b020901c00240b091089512004a51180d103902009015065224a00401c2c040303c00d11105c4480b030303540780b9804 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 791560512 1250 791559262 791559271
    0x1306260105031e0304270e061302091e0901091704080a0305030c122401030c0504140a031a0108010501060e0f010e150703080f0601020a020a0b0702041d030307090b03 73
    0x10381001003188201c0c3d04261008110b1040a0180ca083c16100c0700c015001c01036210f4484240750044a0f04035200900f0b20076400351110302d81c00b5011a290404030411600d5981c03000038066600580010001140000205e070104840c501e100708604022503c40c1c040c015070f120540d84903541159041c03131004d0003022281101c1c80e03074025140320112510180c2d0b090300010090302e04150b003004030f900030700d030b01014081c41060022942244200001c1c100740e420030038941498149403410051b000940e070010240c50464864020182e00030f50210b022039800c0c0384542c40246205841c11403c0d80ca4090b80c007105058600c60740c000c209030381e40d0300c1c021a01120754040694208503901d81d0340002c0c0d4844d003078580140c00046c104109000c9918a40c811a0b0310a07001540020040018011028125003003035410034400d20040c406003c041d000258103501d680700d802c0c0d171780354000b4080045440b1904840642540c079215103606241550046071070f640100c44510000d2016000031078400c107120f044c0c9015 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 791561762 1250 791560512 791560519
    0x50f07140a09060501020a14120417160f12050f0d02060717010515130302190302010912051513020306070809240610090302040906020418060e04080702061306260105 73
    0x1456543d02c40040c04040b501d880c2342d25001c2d40701d030f880c0400d2103030340244000d14140c2030348a9440c0b03ca9a40c5410585c248561800400308032000300b0888801c0712040c01070710580000005c102e0110725080d842c0078481c5010300d0880c05000000c07224203401040c2244074510a4940840e440f0403142c03003203a81182401600d600c01201101590940d640502138540c58031192480c00100d9200d400090301e110101041301021840054288115680100120010f106150000c1481c900c0303030784c0b007036240d1881841e0000061300680c0010042d0110103020083d16401805540300e9080c0302400402c0d0030012100d003059841181200014050030300613050300c2880d0300e8104441c3c1d403500d40401c400f15600c041d81c6410004013840100140c0d44511612400500c42c5034016919850701000350303034a11040e05224211854410100030042180010503440350b80103e000350344001a20001d40c441c0074800c8461441300030b403034003c2801508520b13000b48910b00760b00b006080700c42c03509514107101000d00031240c1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 791563012 1250 791561762 791561773
    0xf0f071b06020703020f07030602040f0f03020d03211404030305221101180e011a0a02030901180b030405060103051606021c2127030503060904050f07140a0906050102 73
    0x460807030381c09030800d01e01c68816035149032951040b40345800000d400a94607141d0000d0100064030014441e03100400d20681e40e0540140b031900061184124a07002605102010441051050504000300c0b03014103000b40400c400e0f805081503101c220003c0364102d0110780380102003034803040e00c05403203a1004030b002946500841e160387da0440403125510901c0c148001104400340d2101554004005452030b000005a00d42c50088580040c0c0399818010380740140401610825a43c080126455400f0a0905034010312039200c401c0b00010442c0c1c80307103c00c250b0206c05d0104220780481c50314100d074064000c85034140c20041501d54240300e548a101c4c05a440b010003140100603074010845030341450705002001c0c004801c05c400c184000c040c5d04101d01da03a07032038124000851540e45501e0b920039290322811b810000703036406130440c131014004511445009001400b009420400e9503030300b24134041620380d45a96950741c050413094101c035a5201c0e10a50801007a41d800030b1250500310381d0168010003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 791564262 1250 791563012 791563067
    0x3140f1503010621120e0915010504032003010c050903030406120b1c050709020406050409021b2d0d020c10030905070609170d0f260f0f07 61
    0x800c03039018001505552074000026402d240d640280c81001040701058002e9041458209800266015140203008002c08100050349444c1c079608d038000106682c028170301c008200180d806003d150f00c0240300704000c2c070392842c40e0340d00d0000101d428802a0024047e40c180e0030f500341d416009821503a5010b5000380010046184503d40e0001c0c0d80814030307030005500c4800004220407040002c14456040e0021201c141008401c0258000900b0314200071400d103402c10000a01900c110703c6a42c108a8020440c1c801070b0407142803500d501100705c0c1c1150103c01c4881d2008007840c00e66140031914000d09401c2080f845030110b02111050304a50140100350240d00c200861580500a10360401d0b030703100c0d07181c00012030030081c600103044030ba1903c072081ca24240b00084611520b01d10070301e030703501302101000d0300a1b0020221283c1c120b00b4240344050300402c0a0500030340481c4c064022242c0341400500090b0b000d603400190148803601d203041b8465591880c1940e40c403401e07a89401c0c0104c804400c41 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 791565512 1250 791564262 791564281
    0x11508150f13020d0908092103040302010809031309061e03020a150c05011107060e0a03021f02120c070c08150c0d060506030f15040608030d0515030712020103140f 72
    0x80d501070b000801410325030b00482842c00c41780c2800c01200c1e240c000041200091500541f05d0b404e02d0032043c115180305020703606142d12805a440000e050041c0031002c40d000302000c0c82561291511651f010f82c4550755003050001400d00c920480c01c160028021940c50750352521303068010361b034014000004580c80d2412010603410718a01c0441004449416940010001e010b010315241c002d0b4000b540b5030071241009001c0340c070030010b020b82c03542c85642c5030000290041350803d041052003410900c040b001104080103441000e0202046e4460a000c22005030b4800c00034003c80c40c041d241168415031208403481e034400d42045102542203289000401180c1010010004c840c40044013042c426501c0011607015001a40c2c003504072042042040ba5983c00b028106058440444081c04032920301604203403a8858961071402c00c03030700c0d00006130424a00c1c03221100b5255018080b03800312943c2e9207681c2112410080100c1c00213090003c3e03499000c03801903400703001d15070841020b0a16210f0b5800c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 791566762 1250 791565512 791565529
    0xa140903010b030706020105162d05130801050906090115180f020711190f051e12062508151f05071704060c03111203011508150f 57
    0x515a15640354400c0c4856034030f040c4020030041c00190004036290070710012804019030042e00315000c001000340c0401d040e40b41d05030100e0340322040f03401201000e00300070002c40b1b0301e104030180742c11075034410540007030a00b205500507481303000c50308150303502521005840340c26034040c40603d495844655200740203600709007505030715140207284009204688600c1380000d0ba080b140e01664400801440b5611605101040d110f10044080703083c440703517041880f009920002d83c00b94501030051402c481c280c10380b02501900360488020400b5087c0c5900480c0c1d0790380c0340e60485a404042c072640c03040300d00546100b02c42d600d0300d100c1502c4220f00e17559501030b8001c0c0b81e140ac100841c2d0204c51140a43c4d1400300c03d008002018116548180c1d4420540c10010140031055100e414854420001044240d90000740042c841c0d40c0b51404828040c803885041e0b107065044190b0300c4001c0b0001000152120803801c1c9034006000d10703151001c060340d500280702d44054815500a80003810040e1600c1c079854100003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 791568012 1250 791566762 791566777
    0xf0303061c0c150f110d0c030309140106060f0c05150c1209030c0c01080c0405040b060706060602010f0b19030314131403010506090709030803040c12031d060a14 71
    0x1841d02a01c055501c0300c029a5010390302c43d80708514080301c4481400e5000400c04404051410b00480c52900d01000d86c0d40d41038150703240800c01041d03140200406200703800001184e50080501c022160302d407420980208460701c00c43c0c000c40e16080d04020154060118148002d8001d80540007415110780c03407441c6000020103009010008000c04150f105101000902030304e2800f000395140c19643d03995610300102a0b00d0300d0306001c1c038030b802c000100c10b52008076820b131035058902107944040507010600da0700910200412260600601003040c0b41d05601a0003143c0c20b054050029840340801c4c482c0484181d11070802d104050581407003c00c0c02000300da095629400d206528100f00c0341c0c058004000c098001c2d920560021440d801345190034000c454002e6400c07168008607041509000d0304a002511005200b40004000034042c40562001c050042092004800c055405460001c1000c0f200c00f1955003200710042804400b070610b24140c484464103500e400300c051a2807850040d0f03d411405 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 791569262 1250 791568012 791568049
    0x513020f0705010e06100f120501020927010e0f06040b300d090e040f020102070902120f090303130602030615040626041208070320040807080f030306 66
    0x111510400c0345002004898001e9000040e0340c0c00c9010f4850070000c0c01380038207440c5221035006100c00c28460004030111401c2500d018141011840c0150182c040d038140c1c0d035803100c8030500240d80244042c010302c1214103401c51400c0f26a8855241c15001d070000d4907419000c1051500080032400c042d03101c4d10590100070101c12030340015202d0641ca110b882408001800700254030b02d5802c40c410070440e00703e0303070f85800e000300801d0801030480b81442004001910f05150340515000b564001d01107040a4410f0101c150b5843d05000c01828081d1010b445610a00031000c00140d42401301000303883c0181505800c126450380d003030311414065000a01620340c04002001d041183d43d604000a0000b00902c0c1c54001c1528503c000c441d15000d80f0500408550120108110018018081000b000b0b0018280003619480d40481100140b04c0186400741d04a0590101071501e01d900b40600100c4203840101c030945603c03044207030307101c0d54490702d07002c0c40b5030052000c100c05241c4030880c10047c00c1d803030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 791570512 1250 791569262 791569267
    0x816020a0b0703200f0c1e0d0c030306260d020c011b050f010504050a020a091e1e091b0504060308030f092109100c0203150c090a0308040501200601051302 68
    0x5240c07444c0b880c0d000b0350000418070070000703c0000303030301050200d800240030390f0343c0e1401102818050b1a07101d81040c00c000080003418004103080500070b0340600301030010255a00c0400060504000e50654020b84c070f51441d100352540c11003070600c0001c0403042401d06030341d51241e050182000004a441d0b0390003c90780f0303009003004999105401d1065601c524011750040080a81600503c015085c0581009288034180b000303500d94498103880c800b00294403072000240385030315100b940c0e0703102d1100000761158504140a15090180750b9480709000c2c5047d50240001aa40c0c0782044200d40d02440020310441d0700780001070328032440c8040150311440901c1503544a030818034000c80d20044010108010390408143c5068a0030241d42c0b0003403110103030615420280058001076516144090408070003880c40c1c0028500c0c4e8121019911008005021b501c3c180b13480303240c140743c03980150103040d0008952480c2c0303000b0f800c0300800914242c0421406401d083c2d090006028010042030304030f0002036002c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 791571762 1250 791570512 791570561
    0x110115060f0215040c0524070209040320060f1513090501060503151e041a092401210c06180e090d0e09090d0e0307050603070816020a0b0703 62
    0x54840300e04c030794810000c81d40b07074a0503e4100300000c400031040c101c0311400d81c088400424144001c031124190101d030700300801c1e610b503c3c0c1100c2100d003458008000c4107204058510840c400030b840c1c1e000c2c40203040c4030010380c0c0d00e000c200030031818403031500c682c45422105a80c41e2850183d000391581801000040758803501d92012034901604413000d401010b003070310b04012039885600d030f98014040d807081c0380b004141065202d082400900c1c11482c40d49949240224198040800c05e0f003070041045480c40c0c48202d1b00f012449031b504801d20030703129503103e00400c406100300c01306c500d6a0515484000001d8681c00d090781164052412623034540a010354000c00f080142c40c24070124816040075000b41045841000000d28510b91030403006d000707403c044140a140200811402203c01c014540f070b401145540340003c0c9003112a901031500f200000050105213640401110b12138010700605000d61035450b08200d960700c80c0c980018000b0b1604201141d251482504a2200c0300e0508846400b40c812 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 791573012 1250 791571762 791571793
    0x60f0203090601030501180f1104141302010801090c0f050705030d05010f031505060a18180309170d02150601020a061b032d02210106030b01110115060f02 68
    0x8281c881c10040d034000c02c010410002d00b4041c00700a2a060100d108100d00c4664512030291004c150041c1201d039000207000e22a229640721080149a414500300c160030071104404042540c2001a80054400c2001180140d1a0300842015000ba031740c400c4188034544808842d10340058a08a40e00e0100700306031103a01c10076000d81070180c04400341540340c081c40c52070842141e1000e0858404601e040ca002c00c0a5555103881c0032048407a40d07000c0e248060300e050414001400081094190810500455030a040d40400404107a41d204d105140a2540749061240e07200040c1d052500168000e00600303075140300501c19540c000e00103004036240303540d05603a100b0544040c280d01250f40c00f4280300c0c4480302c59150041d03448072403060b01404c013010b807010105140402d00c03501c100c003400d400180c100d08400100c4840001c0026100c03e98905507100c00c00203002c1c0081941d101e0020754044885001c03418107100f08031150b400c4200a0001500d0503006681040e21805850150301660030030b1031755500d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 791574262 1250 791573012 791573017
    0x6040f020a03051f050109140601030e07030203120d0c141c110a02011401050f0d0807112d15030a0506061606050109051006080c0313020a030302060702060702010e0705060304060f02 80
    0x2035561800c1d0a0640d0312051300350850700140c2c445800c060428080524880404201c0c0d0b40040080ca004100002c101010030f1070b00180d50b000941500c20140110700c08000e8030007401c001c0800b01c20074441c01071882c004031481c45000100b200720600030801c06844604400c42d1600311401c0c400003241481d28901c681000e504020044e0004d82d4480d010b248420725001030850242100300d03044c80c5d5841c2140d000c28a918100d8500a1030000c0010301c407003d1240300d031600601a540200400300074103407007d840c03421502c001e140d200315032416035001c826450f1111900c903149003c0000c4905540d2000d02c990058500904429044881000030703c2803246800c42079200301c0c0c01100c2c081000d5141240d108103d6000609040c490500c06400344007040d8070481c01504001d4000704152281c88500d011031003406040340c000c5d40f00120702ca00108244e00400c0c0c203440381e0720a4080c2c510651b41d140041e0700341c030010269540c0c10b422a00c001e2006281c403801441e00075008000014107001e04113078410807030303 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 791575512 1250 791574262 791574283
    0x209041b0503040201090509010b1c0204080a0507060207051008060f0a030501021617030106050307140f0418050612100903030b03010906090b0c0c15041412040603060b040806040f020a0305 83
    0x41d500104100a65030041c0f04840100342c19500021250f241641304940703400f4010a52035501100721990804401903016100940100d0301034403054002494947c0e44c3c2c03812031140d40c0160207011720004861514000261300c0030007a490f02c6007681e40d01c2041103101d140109540358000d4603000084045982440135104080c22082c1c0e42c1c45900313150812a03041b0746d45e81e803000c503c044200300521006606c882540e421130300c541001a80c0a180c80800800d50040e00c515484c00d040c017050010f80400e00070314509804001e16404c1040e038031200240484100d007900e484500d907102100340004c0045a51181085030b002c4c0c900020380910400001703080d44c4520300180c0e101d82d01c521021041c8072070000901c0e00107054202c05031520700c54000c4c0540700c454441901329040000300005060066400d17134514850b501c0416034116900f04441141c080e00940510000203141600201d8420f10700400c5500742d506400003880681c5e10342e0b07210314801548400484e00715002900000004030308100101e0305 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 791576762 1250 791575512 791575517
    0x1b0424060e150408120903070b0c16060201200906040b03010f03121b0b1b03041a100b0702060a05120403020d120209011d241309050105130209041b 65
    0x10405020100100280300c5408106000010402000f2080d13001a02003500d0280c0c2100c65203d10007400082c1c104a0581c0c411600380c02d001030101c503244d0300810071602040e11650310076207070740e20380c1c41c01c07407c88a840c3c2d40782244040b03848000689004800240070502e41c014456440e194540f950f0754690380080e070081c0b00e0040310070821310400186030400c01301c010b200d141003d6031040b81c25904100360a00b0782c0c06000c5000840210350b0382240a00c0e420700442c0a00302017680c80c10a0324000011340c0522404c21146400c0c0d2022800209c01d0390554000c46e2144840c0b981810181d4007017100c207070300c04260041400380c02c00280400b00340c41c400341c5104501a4001d400296103886010b02841102000ba1510302c0c810418081c0c81c1c0e801054041030746001d00c070103189075500b8402280500c440c21f130340c5c482c900d141d4007076102d17010448800801e41030106c4214843d0180d81d8146403c1681d07400e00400c0c2d0b001600600d1842c40759115030182c0240c1400510128000c000503290b0b854088401080900 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 791578012 1250 791576762 791576777
    0x3025a01140714070618020d0308040308010605031b030a0f060f290706091a09010911091e09030712050306090f2401020c030706050a111b042406 64
    0x74000414841d031211007418018030a02840f4280d020074480c0010090410fa51503110b200c00401a070791100380642e01810700c0c00101200d04001e42406c83c01c41e0200c0000304000c001080152081d4282c1c0d0040c540a2040100025820311082c85604024829900c040d0f4910300c040304440c0d10b01950b8001e02c10a0b91700d014080c2400007030038070044083c0404a9010604401586507180e050881c0d5050f03800540002d8007550038500701c15290b011411624a240340b0105003e00d441042d0301c080d04a503c21880c08180c1065402070000c20380d000c9410140000440c480c07203040248148042d544001d8140c142c0c0d00d4251156075000524000b614020001200401008800c0c1450014540c101502960b00b030390385d00d0400d014a141d4100d509226101d400d40c0c071003914040e4020270105200440050075140c409845200080040e0821183c00c1c000401d401c01c0101401c4c00802c0d100081c942c0c0400b592110f5640c0c00a20000d00a10705045c006014500031410005401d00c00d000060b0086507906d00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 791579262 1250 791578012 791578031
    0x80c07050c062805180d08120a1b020609060109090807060507080106110c28050a080105040605070503091908120f0405010e070509040209091504050a03025a01 70
    0x41c2d83d511a80300610034010204405203040450300ca40d00d281080840385003c29009070300c2d00b01624000c040010724110001418040b020b95250040001d4500b62014208441544030003241c0c1c8110559096015030003010040c04441c1e925003088050500428200c2e00d4103015903254811103a044806200190062006112003984820544003d046090003481c00c4054100020b9400c00c071520443c003800c10412000c1c001020460ac0b14004103c010304154030039603110b460354080c00301114111a076074039050000c2c400070b001c1e0064a028480a400a210030006410350f030708407855540301507461003400d1142500940381d4400251041440d418001000d0805240172803c1d1a4108510589508030090501140d201c0d04401c0e64000c0e01183c0c0d801544e22101300203410021680d104000f8950740c20200300902000140300c081c200c0c440c2c1c2c200c40c1504002d0400880a400c0000f40041000c010038001d00081180745203c0c80030700004810350b50008100f0400d0103040c00781c2d03000d110141d44401001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 791580512 1250 791579262 791579317
    0xa05031005010507030f27032001080405060103060e0109061b090803040b090105030c120c1305040c12020d1b0c060617070b07031215090f0b01080c07050c06 69
    0x400809083c200b0750704180c00382c0da025280700d082c00c0000f410088441d13910340c1e0001d03e41e500c0d1605020041d0044000d03580f2418504401d0080101000c00044c510031001c0706544a09003151249400002900d0340380d00715600c1e03c01414031540351150700d41d00e4005440110312544100d20304680101040161715500031b2002c0c2c440002c0d42e100304040c2c2c0041c007007004502010b02c00c55915501c00d2820654030f60351100c091090b8000e90000030b1140300103808110458401c24000e0100d407182c43c1c10380080559410800040d5032002d1100c0340021040900b03058420314a4000e0b04000040340c00214491244e450900700c44a00b40ca0841c0014651085035000e210292248030064000303455896a00c1c20440d1480d5981c0445104480108000041c0282410321a032440a000e0f80792107020302c8590304c036910860151b0101c0c0280c0204503c2c00440c948094510704c1402d0030345e041030f1280c00455481015260b030507040300340306942d10700401049100030b40c2c429004008035002c0109090720481c082214 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 791581762 1250 791580512 791580541
    0x140f0601110c01030b0a03060c030c08090f0a030f0e0d0b16020303040c05010804050a051f0e0c10030203090114011701060e010614030415020d09022815140a0503 71
    0x115414081c4484401ca480140441c0b06140e50000303080c00f26060108501041100703103607a10147c0034600e8100b05030f8a0540c180c01c511960340195680100645518402036140d1110169100d103540c0500c5150340028001c0ea0130130440ca0250074500a40521034000c00c8042d1107800c1c04803074100d0a50104240001c07401c81c014070101b1207100543c29464145d440d00d00680369802518180450240001c08010007045480d0740f140d4000103440356000425001d401001200c040e558105040c10102d2b4107800e00010301440c90f0500400301c80d04180e10710b034254000c4d880a403281180d9500d81d000600c00c500590a1280203010301e03901120480140c42d41c0a086850b13607040382c3c00e0300310031000402203e940947e84071610006500b10a65980b1179107804d4003044807084000c2c140303900115400c0c100b00003d500c41d042407402501d0b15850564122040c50044032000c2540382c52505041080c8071020380c0f030301044c01c0608030341000070701003100b00d200405540120000b0070002d40004100302d650321980c0300 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 791583012 1250 791581762 791581771
    0x30801050a06180326120405070927030311070803060a0801020901092705010305031903020a020d230301031511040b0d2f0d05010f050a0312050409140f 67
    0x400f50403c5040900d050b20103026440050060064a8201c90420071445184180240303240c81c91551403603002e1030010030100840707003503440c0d014100300010070a8031402207030501204c400c0c4105140c940b0713500060141010364000c0e400c256561030b001543c1051480142041806001081d0b128a1300d80d0812884000b80d07000441c0f2a40140302880360780e604044200e0946981c012401442602c4410100c0300b000c022a94104030707802c200c0000240140807009001d074280141c00c1c010708103400707001a400da115000210005034407003041030340e070f051098a0340c14080301c0d29060a969a00c20841e9030079a90820b0f0400d595410004030001462082e61041000e020022407589007440d28006001c1140d00420040c02c00c0c03079803100d2054444600c800c0d07010483c0005006101001117018010301150340000ca28111501c2c40c03c000400c50319100000481100c000a1141c1d100505581d0784a20741d0010020403014400c2c1070002140110707940c01154107004440c2e044803101e181c12050f490791f0a10161 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 791584262 1250 791583012 791583017
    0xa120b060901050703080c13120501050603071a07020307030b0a021c060e0c03270115050a0506030c0a05120403050a0f1b02040b060405060c0105160906080f06011b030801050a06 78
    0x700103022640c004003074a08840d0981000000c550b6259031411440c840d0608220941d0f0034080042a110b40c00340010b44428007820003041159a510305140c2c1d41c0000d400795002032820000d4103246040c81c0785c018055688080c0550314401c1d544d654045400100380c642010180d00400d42c030030254281048101e18120103174061206528001c1402c0000c00003030022500341d400040050703031a0124101d0307034071000e038214650056081d08004c028002d01c903a410243c900010140002254a002810001600d00040c0018616100d01000882c43c0d4842c6070000d0502000303014a01c4040803401c906403040740a611056550899000010185462002800c0a100721101d41b102c040c5a100c10390001e40c0e9055500007501509031000822901a9a0ac083c1d480b0b0400500c1425000042d0066401344080c400b40282e8034880c06d406551440c010300903080012198800140d21002e08405540c00c448181000444100010060034150b40c200c101500130400ba03900401031801c1440142004040700c1c03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 791585512 1250 791584262 791584267
    0x160501020316170c250218100b1806210907060207092d061806030b16020d0503151005030708010801060f03030c110a030b0a0b0f10030c140a120b06 65
    0x604015030140161071515040b29640c0a100080c1100080c40602d5a60018004440c0e00c03815181f00c02c918800300e4440001085580001604a00138000c2e83c091b54012810143e44a4003001844940e03008074541d1141141204420b08207050b040d180326014030642c1000d0111135080c05406450038149500000d0fa103458100d9006035401400740703c03040c107450700150040c010425203100018001c0303501300c00e4a620500501402e001b240780d100b881184d1184400403800da07a0205010507410032041180b01581240c0d02d4020b10920030401941d0001040c1c9507020040e042030042490a4400d5503c140880d000106200302d450700a81c18038010001c0714020300846d03003041d071100c030b02036000e10000782800a4110103500300038041000001c0c0c0000078240000c4c241e968200300a84642c16030b00790086a00e4200e03000e4250910300070100b880003000d030003c6900601100200c00500481200c075003084480d0800b0f00400c65100020481d10804d42d5601c1e00d41510740b101207088440305500c103032248004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 791586762 1250 791585512 791585521
    0x10806060904170a0909061503110304050c0d0c120807020909070303020c13020c1b010f0504030c05120a05010c0e011d09150118030501051501081005040216050102031617 75
    0x4050792480c0ca024880e040e1902c60700020010759502e601a0004c40501c0d04088001c03c494452040c20400c0c00803503980ad020b407000b41580404688016a406070183d002561031002604103140d50440681c032620400074019590107040c00c0d000d400c0300b0105c0d80e1541c0080c2d180b01b0340c47c06200c1260052044c6000c0c108441c61030f07402940d04d2101c2c10aa90190800c84c4000c80001d4469040d10000303880181a80c03100b65090444200c4000e0240c4c80c1d60101d4550240319070418460015a000d40f54803480b251016070600b420442a003208402521081c0f00b01d181500000d2400e009005a410321600c4407002d02c0d00c80070000d490f0b00070f80c60041e110080b04031245200c41d03a031400001e41000300e8042d080120380c4558012281d20140041d00b4840d11141c5e180082040030560001d403140f601221231595a0b242d42004607400001903585241e0b03006001d4040c840703842e1036400ad0041078400c411250310500c5680d03841c4d003a42c104580c049035104c01040305200700768101510342c160307140d10a4111040d140 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 791588012 1250 791586762 791586773
    0xf071d09060105091801050c0309160e2406070f060c031a0907091d01060206070801121401060f0305030c010501060c03020a061116060c11010b100c0c050a0e010806060904 75
    0x40500c18148501ea00c4c801189182013068160f41c80070740064001e001c81d281a86058401f9441590540200d00c41ca41121440402d5001d05809981d003480c403c02e100e071070b03c00c420032407149d0402143c1c0c4010f14003000c10380181d0f180002407190512030303080242c524840d0304060084480c00c184400a041c1884103000340304002c004110900c000c1264102c50710344414100b02d4844082c0d400000c444402800b08100b100c1004143d641241e05940c2194000e42d20014210f5400da800c0c0302d1100c03001c0021003c980000c10300150203076081070301400002d50703599036551a41002d0069000703441d56080062003c1c4c0550080c0581030141809080c01c5848981941d002541ca210310180a0310055451021413946c101d000101c4048103c3d00031241c2c0600c1050420318000e104401d00000814040301800c0080c40060065200c0100000c00210160b0541c84007640d02c0c040c640e4003201e50010380c0034045001e81e50342c52542e020303102d038081784002581402106843c210014040e07a200e1003503102000300040 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 791589262 1250 791588012 791588023
    0x1214190608010b01050409150302060f220f06110f0105070504080708070b0f03070302070204150e1b03160c050d030b151603050a020109060c082a09150c0f071d09 71
    0x1c1c41c610001511300c008074508c500d1000d0640000307501400c0002e6401801d085600031b840291503801d01101051001c04110303d0f008443d10413400b185010759001c0014502a00001203d454010261541c1c1e0f0542240c940c02c480048a403800402c80105e42800350040c10452003026003c0720008055440c1424100112400340b100c40c14014100040001c2000c0d210b44c065402007680500107105034411404001d0400c84036021f14220300c0c4100740085c1c0140c44040780340102c1a0344035510707031440d00d42c166150340f4045255051010b000d502e5030102c00080702003141010031000381d0b0300021a00240401c019114042d00d00c0303070701c02c40814800329200d60440c1a001005d540e043c1051580c0d501c15a50a902610911801074901c2d864402e40c0f000e115084036045205da8200046100c90002c1d071107038190001c0030f200140b01d01d0201071104c101e050a0135019100c40741b000070101814122101d580600d8081c3c00c1c110450f01d5000701c0c41c200034000703000e110701441c4100d6001481303441c07030804c41155854 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 791590512 1250 791589262 791589269
    0x80c0301091805070b030f0a02190809070803070501050f131a040309030605160e01020a080405090615030c040527060405040c09060f0e071b031214190608010b010504 73
    0x540e5140c41c060b20408810004103070070f50100c29039095079035072450618560012a000d001344000300700010b030300c0b51803031003110901c0d00c801101000556102404460211000741180c9180c4a206004505100100b0140c02414480d00002c9454a00304c426000c0c5190050079980000b04ca82841d20005000083c046075406c54451000100e40c1e6542800c035084002640003528191522041c03010b07211025040040440058603940f90f812094801243d5400c1903800c0034021200501044c003007403400150154002030300400e4041030058540e240d4219900a0722100030f00000024100708034180184900c3c414804a02c6000000b403a03c58074540703c07580286058480c580e01c100107803c1140101808010f032018042c01c01405807180a60043c0c909140640f00706c0340300210010300150311601d4204e140e00d0100c0760f50420b216090350309403102c2d4480c1e01c500b280507880c3d6241c01000c100b040c5005114400c18880172134201540c201d4481103d00d25009942c2c2641400784902e05a6000001c69088 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 791591762 1250 791590512 791590529
    0x1e0f1509010c08070c0803071713020a2106110c0607050307030b03150103140715030e1e0d05071a040c031b0305060c0f0702060307090501080901021303030f26090d080c0301 76
    0x4988d5007007030807195059452580d07000c1545401c140180400340381400744203240300780c46401c080740c4c40d01d40d0450b00e50b080d190004050a1040d03003440018459030040580381c0000c15045007082c00c406400750810804917240c2c40001d4010040014440d850701404000d024142d0217003081c5540409401b1f8203040500000e0820204001a1074417541c0402c0031400031320b40401d44c01d218140503000100070307100d440994540c3d403050707200c5850040041c422448400e00540004c210b8103aa12901b0340f107036080b100007912101c24006415004446141180b8400d0b849000840002c1f401c601d000c4410046415401d00d170028541805c1c00025070010b0710344e0300312081c1880c0d2512003ea00050314958841c1441c000e41144001c41400800c81e00140c2010544101340c8601840f03a47d580d0700d0b50f00301e010b812410344504007100c8003000868001e007484c03e8030380d000c1d28041030101c5852450781002903006500c10202c803444810009101c01c00d1141c4c203110140d502d0f03c1034082c140029006214081805603001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 791593012 1250 791591762 791591767
    0x20603040209090c03070e01140925090b0c01021e0c1b0d140c030708031c110403120c030f02010606140a051c0920031e0f1509010c08070c08 62
    0x2c914404000c4e2070510b000050885000c2900c860355240901d0080c800d07402180d5001c11007021034074205000d1803140d034200c03954004c040701c00103688481c0e4001049201c1406440040401c080c1100300003001303c0300060001590300c40e078a0f00180c1e44c1883d40111407080201c28801c1e41c583c1100030468400e400c4c0d482c55115520305144002401d110540711005100700e0801c131124085440c045100d04803181e0460540711110350341d0110a03201c0c0300712180c030035a62170007001071a841105070b44036a001d106002c010344c1c1001e0302c079612199000c5024a0001c003140340c030117060007055440120400b1000f0244028004640b8101001e86940c580c2019040001e401090b441061849401a5444002c1c040003803100403030381100e580010424503105a4032603001e1000b42408990002075001d03528400750091119a5241c401940070450340762001c602c5018100c014020036004101d01d01501d007295102001c14142030301c030319086510110540d01072000d102c0800240d507402904640e0000c0d04600490f5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 791594262 1250 791593012 791593021
    0x20c06030c1b16140d1b0810060e060a0605040b0c030405151903020414010c1106131503062714150111010b09010e0703020d060f0603200a0f0311031e07050304020603040209 76
    0x201c503592540c0107185503101d14022070208c2403071034106c003045400b04694450349031074003824000700120038081d003004503038100400c100d01854400100420840034055070304007519040010501411458400401c400106202c070500691608039000410b0b5400c0c01c502d010318100c40501c000d002c2d071900c1e0b81070104040e540424003003407113030403141040c0040c005540ca44502c003d170802c0e00c5040c00b651243c2c184001c40d100b4160b009200d0f0f6402e07204000c0c03140c0303420705c0c5848600125042e4641c40102454860700700d00d448010607006140640000c10b1031000e0900d18200042290205040c07426441e81407001d20350180e00e401c2c080380c0c10b4448089558400755580380c403d9010b88900d6500080b0369180c044002005401060884203888450754180300f180c0b0b6503027005a0304800c840401c1c800e408100710820b00c89000301440e4024030258140450401002e546400c5a07030002c59200701419245915802185c01810000e94801400d04010b801c504250b004580240402840280100c8103400441e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 791595512 1250 791594262 791594303
    0x100b0d06050408030103051b0609040e0c0a03030e040e0a32070b040302040b0f011e02160f05010323010b0702121b100f020c06030c1b16140d 62
    0x12a2269002203041c8a00e0600b0f00c0c101015510920050f2000c3c024a416aa0b800a5103d101c4000900080c0301d43d040052075404c000007080e00c03002004c0c40d4810360007402520b89271100f4400085009441d0103801842c440c00f0300c420340380c0650980120b6040400c1040000d91230300c000804018074604950320b108143d085020215021484060580c4038101c40040e07894030240062061324170944040c010011010148100300c4400d0311803d0100b940c1c140712040e1340c140b082c40080701c00e1f0503104440c00c078a80381c40d02803411401034100c94069140751905116550b054022190307204040881d032204441e0076030454100e003006029010024000041ea802507581d10b550b1222402000d5059440d40744103030014400c08400c0c0c0002e00d000b95071002e90080c805001e29440d0058203640e802034003080b09440304000f801c0c5d00040c903003100d082060010040d00c00050700c1c9400c500c62008010601c4151841d641c2d405021154006070010145240d140105d8442c20078101c6034551205104800041d0289030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 791596762 1250 791595512 791595529
    0x2090f07090b0c0705030d03090503091003021312170c070b0901020a0b130605060a081e0a0614090f06062803051b0a141813050604030c060b010c0302100b 68
    0x5400c00720008509101d1500f404038450040b00d1040b42158465144208290f040e1a084000030384546c1060240c001c4d10b040c41c4010b841d402600c3e18006241000c50800c0070041c8040c2e800061a48020150006c100030040c00d014100142c0c11600605109044040300d98490060084010059002c200c050300c40c1d00230026180030540c40080001c40e880c0003190f0440031603080310240c820a0400010038907c0c02d0400503101910600c1c40a414804601c40c9001d0386c0200044080d43d40744501c02005c408503603a482030320301480c0105110321a0342000480540307005159010884240c114605202107a034460b4004d80248440c0d100c4546c00e516006001c0d54082036a07170001d03085008035258040c00d6a0320960340880381a04403030b01c04d01140c8038042070040c5800d42d803405070018074403400842004880150541d1185104200b0741d100300a80c0e03a5030707081040680702200071560080c10a403c1148500500c2c403103103002c3c070f801d100c41d051644000355501c4500242d007c9141d40c0e0900e0109903150701c00c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 791598012 1250 791596762 791596769
    0x60f0a0c1a07030e0c0a0b030c09010504090204060f020f010605010944150115030b0607122006040209160905030a15050108121206040207062a090302090f0709 70
    0x403480964a050345014010701880204c16120780640000e034026443d01c8244403082d01d105401c0b8a05688c1da0640c803001590188000d103061110621000400c1c0c0c0b02800104040c000540e0707100300491070b2a46c00381c60504640f12403401a41000800e1005ea60f11020000889120f401b00401401e44007892030200da013411741c0f46800b0a03540c00328031403608160562a800c12190012103203042c0e028815496001400c2c00b440c620f10011075260810b0620075000701300f00000042110b440d240055aa203400034a00d1401d80f0003040e00c00d202c1d99150700c0042170341041b92131004090b0425281981c00514104c070001c080b00900403000709465401d5120b078030407202400020f0100e942007d03540c280003500740311503c040c80d089820000003103000e40d40071812454000700160304500b41107280b40050070b940c0c3c008240c0798000b5801d019080200d0118007460702041444560708942035402e41c40015500c81d07000031a814005145010001a102c0030421540003008800e004025103130642c044844030805e91 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 791599262 1250 791598012 791598053
    0xc07080c0a061a0d0309090504141c08010e011511070801060305030904050115080109022203080304150507050702010e0a030c0e01080706020106140105030721020405010806060f0a0c 80
    0x18110100b04060340b116400c0c0e40740074106800d080e941030811074882c500c50001400201c80060810110f901500300d243c0141c0b00b12004041c0d071001140803850b14210086244c0304490720240180c074250007100130760241c02d4540300e9040660404003551000702a05000710f040022140501009042c03e00c5135034094015400280101a5a405d269640381c00910b8440d10503882c007400010070b6940d00c2c40c503001d10807d80e12404403d80c6890103d074000d4001002c0c104141c801015288a07034100c0c541c0c0c05001d9882460615100d06160810b51003081080d061050b00915040c00d2100040d041800d544c12035a0910701410700141ca0404034142142c04c0c0c0c0b006201c80482c0c0c40c04112150a0040c0174140e8803640c00f202d144981d141001c07402d0342c042c0d120303120300511051030342007030744d40300310011540100305040840c10f11503000c00987c00301d0102d09401011942c0070409011300c0d03030700c24891500040c085038003900b8221001d9040c0064460304080d14188600c3c2106032041060b400d035580c0030651400b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 791600512 1250 791599262 791599273
    0x612080d0615020307050c09060a05010f02071e08010b0d0b0a020906130803071b05130f1e0606020d0e1807020a08030c130608040b07030f180f02180f0c07080c 70
    0xd0b0207562900084011a424000c69940824a0810f11120781c070590008000701c501c24600001035521655a801c06011806819804038000c01d01e40d0a1401c440d104190120205140c40340403421145000c03600e0788200c4100000c0300200d1030760741c6141d0b000300c0c400d40010781c2d0780b00e400c00240d09803180180400101c0380e01c4000007280c0c003012000d0600e40703006040034012000d205803181014441030140603030000190f00801804041a40b000c00d0729045480e0000e5210900c1325415070003180c001080c840b443e00e070b41c018030038650b043c4000b40710824035040c94442510014002420380440359458070000484000040150380708010751003006401c14000d03940c1e4200085507101035802007881403c03503860105d0000344644603190183c803d64002698100c19115035108801a0000e0b0500304081c90311521030011088070072170880d40c03141c070032440d0124140251042c4000d5286d108030000305c50340c03038004000f8400203401100341d102c21031041041c1c0d20851407604a4007800303035446854091080 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 791601762 1250 791600512 791600549
    0x191119050309120d05070b0406090b13210509040e120301031b1202010206060909010b1201020319020408071517090102030708180a0212070504090b16030612080d06 72
    0x200040040c440d00703643c2044001030001c1d045954000c0c0040200008204110290200d044400f2541d0401c2c418a40816490a1510307920314100060708c200c0040002c4400480811103904d2201c03082582d03900298028050000c0302401d14000e168502e800380e512002c018204101c04d05c1481180c9011211094403542c4074184a140c4411740040001070b64203640003c00c00c84100e0ac03c50b408590705074001c4c4907542e0b0742020b0002c0114090000c0c801903486205400e0107035030306078414142d8105000010b03200e2504149040482a0314100b0303000e007500c10842031020075004546401a1380c040e110441003030700748410403990048200c62003880007001e5400e000144406400660040420f81d43d0f07902c442c0c0b20407455a070500d100b0400d4000c190b201a4898005081a003c0c51046139044802c0d514015510004a400d42d18020011241340c10054200900210350030304121041c0818901040510f0801d1940b0718881424400901846004520001c2c1c403581030700588054102d46841ca80328944 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 791603012 1250 791601762 791601773
    0xf030723032b020c04050f0c072d05060115140c030c01020d1d120d110d05070e0109080304030c090e0309030a060f0f09021806031c0206060a060302191119 68
    0x4000308004011301420068850501d8540900b50003040050404181e80d00c9072032800c1c0159001d51422a1b2001c0103845403802c0c0c91410342c0301c080e131010450701462903c41c6131600c2414000c0c140c0040304c82401381e02c3c0034443c0303035401003c0f1040902c070500042c1d039403000f090f041407a5000d240d2102c41158000112010501c401c0c1c0c002c00954000d105040c2c518904030303640f03140c45c0c0302100e03031340d011403002806a4907602c00700790855284003d007403401620701406030b03030420b0648004544500c0400c1500b00c82940030f50303001c00000001c0c4040d0016505260940d41d0b01100c880c090f00c260707103103140c6814240820100500c1140c9030319200074200e0f09410011300d4414090b00c41c104042111901c0c0c650a0414020b80b80900301d01d003075005110b01d44091803424000b11300750300903120310b80502c122511141500082e1051100d0fa011300e40060130700d032500b203003000f900385140c0c3c11410801d170040c0318803178185e41e661005461141e500d0400c0654101d65481442c90042303c050000040e0b081d8440000c18003c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 791604262 1250 791603012 791603083
    0x3022701061e05090d0222110711090403020303310c03050106082b090b0c010b101e0e1f080a11040308030112020a1706060f03072303 59
    0x1280c15911502c00c114082e00395500d015160341142c020481140c48001890200810b0404400c07041e0703c0c1c104204a42c0c100e50498403202e03c02205503a0000d140d2051000c00c142803844e07a00100c07041c4105240c10b03035000b522408041c20200c011354500f020000c502440b0240301181e000386038040d484540c41c070b0500d06c4416103507100544955103410000300781110041925000d286d250403004100390358080e9030800030400148208100102140d020030310701c2c0d041000381010840c0d4000881c15001345820801d801e4020f1031042d0901000c040c070f11380c81e41e1407046600f140703421a050803810a0103040100f06403140e1040e540d0401210b80060103005600043d42c3c42c022403d0890800c0041608001e01c03806204134003015000f072500703000400c0017180d0520a41c004501c040c15aa5001d03075a600200c44a1060310400e8500d134104804100301421b0000380070b4100d020440c0185040391810240d2280300f000c00c1d6041526030b5410062008a440422448403520513110791204054004282118200b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 791605512 1250 791604262 791604287
    0x7050a0e0a2c0106030510170c1c0b07030513020613170f01150803030c0a1103190e090f0703020f070b0702070510030204060206130609061505150408070302270106 72
    0x1070000304000f040c01c0f486442541d11070390107600b1f9455818100b0462a1080f515556494818402c1c1e81c05010981c036846c400c52440c809030981c4564406130341c40e114104c92001401c100425140038100210304904045070031090b41c042e5030450b039951130300c0714011800700640c2107000700c3c9410108502c0c3c8008001203000c009032001001b00314101e483c89061100f00c2c1c0601c20b90525900600120360764505480c01048805100d050041d020441004a6425900907045220241c4a4071109402c001c0d00014000385888041360580c1e001d14006040e45c9080344080c01c2c1104060380480c00d8205c1d0031840c2c00b22440d00d03030042104c0c3c03441c2c80c00e01070003955103d903801494014070b03051540c000b40b58083d009503000c1c1e50140e000307440c040c0d5a04640000350003280e00c0980ea13a6072110f240c04003240c442d2150045071415800044001340c03c0a007408000e5445503124014240c04100030082e80138003051040550740c0c129007285e0f80c800300b0800170f000d5016030360184c2ca20402050001501039008103208484 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 791606762 1250 791605512 791605589
    0x207150816020307170d0e010b370b070b18070b090a030c0906090606021b040c05070602070b09010506060403170706020c06010e0a05242e0206040c0b0307050a0e0a 72
    0x1f42490f00c1e400b420380302c052903880d811030b940407020300050144d90f410080d1600403a82d6800011aa003440c0005004070740e0183d04841000070b852820300101030030301644070121b240408001840c0803900c60b43c41807688141440403038041420700b620780c0d41003450700045030006055900d003900e503010000180440d220700f010103403400600088450000c20a03141042c108203072202860a410144000b50500041d03690801c8001c11030f2000040f0184040c3c2121409001d4420481c030780980c0321401c554000e030100e0320442c800e10042000820f90508509420303088080a51502400c0c41e10801134002c40c42c8a0803140034150001c10180c00141c001880f6600d510010300158403880c400f8010317903058650850340741000d100d403860705040a03444a4101c4a1032101e06400801e00c0e402c9d030410100a07d00c060058200030240024442072004150290209080f40d03840d6042803000501948900300120341400540951803d00c0e80d40c0c010300000074400f5a80d401195803200d2548036410564103400b032030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 791608012 1250 791606762 791606771
    0x40b040801060f0e0c1207030621052806020d060503010207050d030b010e0a05210f0705090a06060221070206040b04050103050a0e060a18170a0207150816020307170d 73
    0x10810f04d800f280034042d40707003044914608180ca800440001c40010078500074135813280c9000441d0103040c91350500804500c3c0c541160900c0340d26100d8105013031500084d20a0301124040070700d4000890113075030f00d2030b8001d200680d160a0031140c04040c201c0c0d0b500042d4103510108140c0240b080110302c2c43e100026580c1c04101c0c0d03100d608019502107002c1039141e034000c1d00386142172019080000c140d102118420ba11203c1c002d0803070b0401864903401d031007215059080b103c0100030908000c0710341508400f0181e4140b02640c141100250f03503140303007030618840c10b2268140000c50350b03924040b01c080c40c0d000342045035150345401c0b90b0483c07980b2921410340000e1a00d0001090900d80c1e11500b000c01c0b1640020784899112564000041d002e5528541242c401c40b280c48000078140d90000001d40c0301d5000c15580322210301102a050407025132010248104501e160810726521031200e80e8030003e030052800c0315a110010032031442c0114080200208061108a81e489081d10045c110b445c203107201c20300c03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 791609262 1250 791608012 791608019
    0x206040c0b0301121203021e09030106210201081305070b0406200a02010e1903061b2d0507050f1c0315030b0c0f030f0412080405100c0203040b040801060f 68
    0x101d5500c000d102d010700d21143c6203a114002850040341005005207031401600b04041005001580c140303040e640c400f00b20707000038460390300d050a011760402801c07111882c0311441101e071000d182c1110700c05d82c02410001b102000035101c0441d0029154242d8104040b500d0080e1500070f114000d52107801080041082170400118500444e010700c602c07404160090f01d030840d200d0340151211031b020f2242c164880e03404403d510f01e03003034000d0341d030001140624000b01d100c4000800c1450381016000e0100100024070007100080c0740020458000f04000d60189100d28640c80b0302240c05003c0c4c00c0c0c004000d4001c07200345a5880e140000c0c000c441002e00789110048a014401c00c1c3c08a03069012118a4002507010410125a0328103400e80c0c8584103000140c5070200c82070603516a50701c104d40e46800b0b280f10700240000d11625040102c2c42034042e00f01507070b060800d601c44603628090307240c0313800800d5181e10b44407043e94800d2082e40d0040c82c6031649a07485903125005c160280c010f074001c4401000c204180007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 791610512 1250 791609262 791609279
    0x31507030609050f06013c030912111b0f0a08011505030f12091206010305101107020901031407092f090d0807111903060b120c040902010309050d0206040c 68
    0x94040c1c01e050711802074001c41c05c8043c0b5085c560010445d1091501c0c4490b00c10310340341d03908440c6c47c030449560b00060708a28524040c1042c1d070003103040d0000c01003c14050621400009030416120f9070656401c0c100d2000280003032440d40741c02403007540101f482c180c0022802815004400505507965074101d07100c1d152000c0c10b47da0050030000d1006136000181011104200d00e004102d40c0102802c070001e400e0405044074600a02a030040380d41d98052038064001c0c00c0180306540540009000980ca0300e100d90f00043c80c0d80c04103010242405139140c01405440c101040382c00010410581c00703000103518540b02d03482098042070055418581c01141d165028210b8003100d81c080001003a0107402815a15030b2045038224180485190342d4401111280342c1e01c021442e100825540300c101e420302d046250020541c0e0520840c503002c2e00a008a034008000f010a461041800c269070001e501792480c00100c0c003030f119a48010b0003d019041040c03a4403070740403480c01d10550040a40814565030f41c0d040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 791611762 1250 791610512 791610541
    0x90c0f0604060e030f01050f0708150303030103031218081908010812030c0c01022d03060a050909070308041403070512060a05100b03090a0b010803160f0203150703060905 75
    0x55011400300024002c05000b08080408030002a04a41240d001656420701b11042520071030a43d0055004000c0c1040e80940c006500403503042000005c4034034100825981d002c103000050500c01c9a251000c2c1c4c0e0a100d5201501c00c410340000c090a403a001d0520441036404104070b2000444a4481400f66030300801c0c0090403148007800400c5000d01b41c4d070980144d50000303010309851120800072510348180900151030030b110303c6080c84c42d000c12140780c84164075102c4000d1a4100d1001d10401c5100c1c5d84004054040340c50603146ca00495855150b414102105a000105a4440400d0219000a0f48102e440d0141d42c02d5046480042d00c420410072140440300d00c090280d03003c4800694000c0060300119000b45400b9421011580c80e20613080281e04110b94105d410b070310015101090160702c0301e0890041c8503a00145107010030f0785c140c90164403500840641400360840b03400e003c541b4100110105090510102401810070340c1004002d1700703503841a803c15034140700103c0ea49040d00d105 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 791613012 1250 791611762 791611789
    0x19020a050105090a0911074d0d060f06180501120b0c0c030d0c020f1203070c1403162303090108071101060312050403140601030309030335090c 63
    0x50758480707a00e1701c6210300180c00c00e07118503c4011011722804002810207500c5031500c540341502d48840c50308014158442d01c04040001c83c5083c40c40001d401200d01e0382280303400c800c00644043c40f078251541000c0001e003c180080780c0c1040c1c038014001400240d1180e0000d0f4040b42d1550501890741c0c2d0300c14070b03a0030f40350566005c0d204c0500d1a011540041c00e4100811082142c1404c5d203082494820013101102c03002d500d0440980c00c09001e44040310814400d00c181c1c211550740690450410500081c08901100c500804243c400316400200c54030400030f45208214850000d000c00d0128035000004840c0c1c1e1200703034602c480e90210700d010040007005a07000004180c1d101089503a8101084550001a24001019541c0c1d6400400030402400c0d40c00d4801c41ca980b0b40c43c2c0c1d240e103036203480c8444081602800c5002c0e0018001400020b601a500c40304403034040c40e12940b41c45c2c1c585140c00012080d00007206250f1042182c0240b00c507403001d40b00740300301d43d00025210300242c51340a010316a80c1d03d08 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 791614262 1250 791613012 791613019
    0x150a0f05040509012d0908130e10061b02300d03020403120c060e06010902130e0c0d150b030a1b02011418030903060c03010e01081c03050705090319020a05010509 71
    0x1041000170555000080b0601410010440030000e445090365580004800310a91017411000d100350f0161400180e0010380304070304024071600e003580043c00062103c2d020900a02c0302d400e50030640d5a0130f01805000040319507a8550301328414040340d040442d01c45c80e00181e002e09411004101c1c000d20076a000c480d0003079030310402c41481c03907421214410301200c100c2d42c0030380d1480c590b41c1900003040841e02030b1200400046c0c0c0c40d1202104803c44a4031540306c0c0256044400c10070450110020540703000641511020840e0504507d43c090382035901e401c1030303207855008001c100300300a40d03412994104101d03146a036030b900902c0e00124240c6210307110362a5440c641c0d601046124040d200342e899109011800d881c2000b0f11400000e01700781013a143c0104855004c4014440c900c0c00035810303401030414000404058071034019900e00414081c1c180c400741a521310001e0b240e6030040003140e06144004090302c20055210548103280c0300c034881c05070302401d0206400f14417940a0405ca400508008 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 791615512 1250 791614262 791614301
    0xa020315041a060604031a100b0c03090d030221030604060e090a150e01020f030a0b0402070f2d030503180106061b080d02130e090a020f0108150a0f0504050901 70
    0x6001c081000b4000303402e55400810401c00000811140d100c08640440f00d800e83c09140d0401c0149201e1081003500504030711501009010129a030000c100c4610072401d840e002c0091407a810143c3c18034050490544400782c80101c0f208805204000035803241c0011501084040d17102e07000f6018404007160140d0311070f40442d01e03001c007144400107404400d81180601140788800c01c0006400d98000480003032024102006128008105008484d402c02040d18214144110364440c44480001030300c01418103000a083d007100310a43c00c0589070450401070020865402074a0000c10f1035000315000c2d0b49660040051029184040c0500700480340e940d079441e580c0d0501a1004e500b603003030650b812914031004000004502c00603001804107020115030007210b103441c100030320101c05130041c14401c071500030302c0c89400140c0c0e9949603088514004e281440741586c4520b00d410341c090385048080d031301540c4100001005c1c0d4162600b542590401e4400740203d0301d6588a260aa90b003c550b03446450100c03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 791616762 1250 791615512 791615543
    0x10504120c0620040501140c0703030516050a11090609070509101803060c110313121e06020c01110c1203060310090809040b1e04050910020c0a02031504 67
    0x5049044034482c001d101c005840030060320035001e1092a007081c041003100c0881d080102d5038000c400301800f558182e41d40d03450422a1b80c0c00580702c68250000030280503000c2401850b1002100c5c4101a00e03511500b191040c0301d00b400d0440003402440350203071055112500040490400300c030260b02464039621040d0518100c1c40401ca07603075400041403000c201031403501e181e000440c1e0221400075401140300244040360070000500404100c802060b5507403081008030045042d200d4407108175151003e81403c48501481c2a916902d00e144003114441c944401e1801400119402400310720800002082904442c40c00c01e0075034090600c1d00c4415400900c41540c6001900740119400344000741030300c0800700d18181e40c4080b1403c035101910044400300d60448641058030640705007080032120007c0f203181241e000b800079400003100301d0185460f503022444288040000c1c483c1040ca060007903441e40288903c1590b02c2c0c400b660203921902c502d0b00080400d100c0040514003481e0022503a4420140 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 791618012 1250 791616762 791616767
    0xe09010c17150a03121403070c1e020301051e0a0c020c040917070c030506060906060d0b040209131b050f040e070207030b0a0507090b090a050d060b090f041401050412 73
    0x280078500300c40d01440541c8956483c2e910801c0510700c141450300789100000001001c0c181241004103280b50108140a100e540241c030f0100c005a01c008000300e40400c07800d0076075401d0641c200003509503007018240045c90000a89407201c0240828240307117240c3c1c07070b1a00c11040d01e05040510015030800b249070340f40f904050308015500c5002d00c100f4250a000300010888941c400441502c4d102c1284034140304001c824411240c00c0703d41180d40441a007094070010754107101e29003140814564554680740180c545030191a15540000c05000458403540a840f01800f40200c424140c0c800394019500d5540c0201c06680b8540c0a400082d400c0c1030a050f05170a107403402a24010642c401c0140c000001022072400d144034810940c40810641000207000c1c1c00b992098104891501003400a0081510785c1030241d401c8920071500b940c404c00302824068014030101d200582c110150303404100000c1890410140201d2240554075100c2e81c001490320300300d40d41681c00400702444103c02c01001c03032 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 791619262 1250 791618012 791618057
    0x7030f110d180c06110624040c020f01050a020c010506060406080f100902070809090f01080303270304060201090b0f0609150f0406150906090e06041503060908040e09010c 75
    0x141c0d502c0c01d06024a040c1c990b41c8019600c0e601c0540041c031110981918140140700d0203401a440302042c000f0461151410200c0d071400b0041c503800707030303554210800520744200010b400741a15072000b00310506102269001030350110382a0080741d030a040200707000c0d05080e0225022250566552600b51b1901d401c40c03113161502602c68224120140400710700c10a0343c0c80107054071032040c103c032a035400706013052103c000d000420311503a01d4501c40040081c0c100200032030b6808010381c1c01d106400746000400004a4001388038170020751001080200303c06070154030038469075001740b400d00030991746c404007213501c01c5044407aa604203400318049007004400d90307203500507500f0080c18000c43c110050049001c07910a03034044050902003000c00100c50741c000661001601c02443c203611074500b80f1102c0c1000e000094035150180759503a62030704020290180000c00341d0390000d42800318078030500b0b08503005c0d08640658070703d01422102050240744148109621012030352642c0c13904000003940103002d81c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 791620512 1250 791619262 791619281
    0x703050a091a18011d04050a150f032a0501080604092405091614060c0f010b0a06110c1905030d08040b06060903060c0702150406050307030f110d 64
    0x124519401041004070003900c1c820728a80709090a483e00c029a48460050040c694264107002c070301c0c401164a0180205143c3d2212400c1e200460241c441d0b410010003000b01e10001d81c07840b062254081034850181c852403007124060148a0240308e0404039010f40c818428507440c40c51015007204008030350041c0e042e03940c0107100500000340c0d5400c680b20120641c440d10045010100d031301d016121601c042d4070407103400c0b0074481c0090500b260307065084d0502842038092130400c0b142d45000d9490664902c0200e230401203213101992449003580d80240d000c0c200c0c0703855507441491001c3c0003044043c403651203600003e5000b001001080904804d001c040e5800d1408841e0b020146074000c9895201003241c0c168014150340c403c202490030b4113040e442800003505e014440d410420030141d8580d40018510b400c41c000040c81ca80c1c94040d48002071254441d04240d01c1e042c1004640040c04a030000701031842442c2c6910248045042030600d0b10444004402030080e0440c14004c0003018038443d840719605 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 791621762 1250 791620512 791620517
    0xf0901060f230703050a0f2102030c0f07051b090c25140304030611070b041415070c0210080103050303070c021206130c090b061213020d0b010501020f120703050a 71
    0x1410034480b00070326074000c075402d81c0400d00000b0360f07031401c69011005490b200340c00c3c07418007040302150b90b80301280301140d0030a1559503004000b0540901e1840d040b2000a00702c07000503541c0d01c1d542d00e403c58440500350f00402440f0303030302e00095a0604180301e6080c030039018042403510b030480c0c3c40080d4845100e2624800c44488004a2041c0080c607035007c000890f4000c04d00960719030f0318501d01401550079050038089012010310a020009901501250704a43d1003802c1000c80c40c841c01140d4501506500300503086400c8005000180342c000700c181c8510f40c002d540220b10036220510584100c942031000500301d5004100186405100c1c051114100f0702c001c000c1d00c074289078140e10501d8030506481a5114175041c1c1031020401541c00c20400c000d00a80304140170605510001803102d000f0500c040340c40042c810001290345601400d28003d243e03000b0924010201d503404d1031498034400340683c5004d84140d503c40090341900060002004040e1400c0514217481e50390300311031a41200b2491410b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 791623012 1250 791621762 791621807
    0x4080d03020c0109020a030b01090624050901021005010b28020615120a0c140d03020703080a0e040c090503010c02191209030c12020406051012380f0901060f 69
    0x5944031b040b544001c50090302c040e25a9410148424200c8400340d103c5044250703880e07001c510048502c0c0003005903642d241403a580380c030b0700c60780185e0408a00d02c0b80600014030f040000b00e6864400005003525040564400c12515684207413012400d003180c5060303002d0b03030000300005c010b902c80c20750191098a0241a010441d13041c0c503000c0d4902203860b041116038100d40361b01031103090000c681d4011058002c903443e602080450b11b0207500d66207240409401c0c3c81d800103071170b00d10a01804480d0040b11000d881003203c4100864010101c41143c0a998030075400c001c007a50302c05200040e055a240c2011a088070480c81c60340e03881c40d000b2070031b002010030301100381c0001002c6480c0c122031000a00010b01d20354418201807040000301e5030fa90f00014402e10a80d10200d2080f03a0062171100024506400011454601040729690100c106e00c1d116040306003144400c00c02106404d20030503440f00b0750303500f9200940c030340c20080200703002d008420014071114100710304d223480784580310941e2002114030003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 791624262 1250 791623012 791623031
    0x1051209011b0305013b060a1a12011e1215060821190e01120f0204051c020d120c0f08041d0106050904020a0216030308061504080d03020c01 62
    0x204070320b000d072144401103942e6100402407404507030b5661200b4110308010f001d803440f90f14090405001844c1040114040341000190a5156641d0100140c407a01c000c120b1450281c0f0300c00c25460303105090a00c4600b00c03003c00058900803068540c00d59030901c400c0655180c2c100050b211240c0805007058400c0b01c010301c4424251540e5104110103403110324041c00c4000c1602803240e4040c0b0416000101513a070411988e400100d41010003458900d00d450310304513401108004840d100101c50071409028600038010066020319401002210070540c0e10071004010ba00c1d0086040c00c0f00040603400c1198041c0c0d42d40060000e2302105203114081c03e0012150070300b070b150b41030301d16880314080715507100005040c060303504003103115015420012001740a940c10440002c20300d0007140d00090107a81c0100c3e016240900900c403150400611080c000d010707541d00e0034000c1c10403000791003e6019403201c501000303120070146e044034207030307148800104a44161040100c3c025445a182e10b0403c0d503980d40e100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 791625512 1250 791624262 791624291
    0x1031e150609150b09010e010c031806200328050f030a0b01030f1824023129041d220c03080c160801061508060105120901 54
    0x50040c08440c000000c1035000208103181c00c0a150301302035410700c0103210301c04150f81d00400c41c521080342071800707005038002854140c6900040d10035280a922100348003050180e4030401c180d284c0360014015454003038680d40c0075902c903c1445015142c0260601000c1e01c0c0812445cac020105200070300c1d049103451040003400640b6042910305001c060303142c00c0720503119070b45409020301c04006075404018500281d510b0100848440b10001d16800d900000c82c552000c0d07105091141e2110401c003903580d074154910400c0f031000c07600e0300070001541400809042da03d0900704142aa09417109424040d4490741924901810540b401030080d0000c0001050484140c0784001926490f41410415400c11500351000c24002440b80422810349800d460b01080054047c10100ca070050711142d03442d0844080e543c100704c0c1d002d40b82c4110104c6518006941601540000101c8055903003001014071a0340c0c2c210780085085d14070500003401401001c001c19404000a600725100c48000030707040041e4403c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 791626762 1250 791625512 791625521
    0xf040f0308030103030e0406050306060409210908120a080f06061309050601080919110406081f0507030c050405010e0f04060611070f0b0324090a0507110601031e15 72
    0xc40d003076003010004008050300500b904074412001c50307007400414205000300780e075031200404681c40b503501c400700030080c070401264140980c80114105890320300c1c19000504400401d100c0d03e034883c401e5581104030b40c1d601c1825a0350f1310041c3d980d000090b0712805c600320322150025000340d5002a04000c1a01e200188030b076820000c0019480218007403030040005810048014220086a000174001e080006180e0b101d110002e94012009181c0501325030100740100320036000402d01d40b141d64090380160307110083c40c03a501e40905000740080e0b0743d4604100e085c0d925080701000070400602017400302d50f00510f5507020702d4030090704040c114082d4000040a4070764982c088000320301421005012104103101013000b4043d1039801d4600c0500c2e01020b0754141c4401803a0b00940c4241200c290302c0d4480450310041001c00042c01c007035850a1200c078070801040d06030303107080106000a283d040003920104070a0304880d001038018250381c007150550b00d000c07100490121001e980d0407400760103040071440b4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 791628012 1250 791626762 791626769
    0x142703160b0915070306082b050f0c030705060415141815250302070f0f0512040e061017061201020d02130501030e160b09040603051c14040b07080f040f 67
    0x2008501b10b440e183e441401c00102c0c0c4003280840c80c0a45039004101c8100d02040840ba0341c1d864031a641c1c084031240c1da009406148400380040c040001c8500a0100005e00760b40118060108100c1c00741c08031490200b160341001e403805075800928001540903400d04205005600f031041507d104071555003034000c1d1807404440c50106c402040c400b0105070b4100c955039a9004ea140c2c1400c5250143c592108250005c54080003020300a481c120321041180900103140c090000321400c0c2c1e244c1e0748410301031404401c11510280203080300b90600340701c0b5114100303855480505461400c0c01d51905010302c0143c54000113461084e64003000200e010400c80e20082040c51404088400c1c40f80c1004001015a4000e0b4526581030b440001c0100100410400010403544803181103591010302d07c000ca03020313001c2d9a1001d0070b03600130b900d00080250303840c2c10070854194542e0b84031160191200c0880301d40c1c3c050ba00656002c80410b02502c40090780d040c1c02400310f00c501d40315103070926130b4a4100d104e01102c0b640 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 791629262 1250 791628012 791628017
    0xf02031c09120c1a04050904030309060f050f0a2a020609060a140a090302010915020d05010807061b020f0a060c060c02010203150112142703160b091507 67
    0x10861560303211020341c0181c020601d4100d4000d160307858840301c2004601540301242c140800b109410a00d110860700200b00203031090241d4036050401500401e1403000a80e00740f810b0012900c1d00803114410f181c03249551640d03402050321107010b4480100010080c0b9403400924540c0949a400c168444040001c810b0340108600c0c908940740c103080660141410380d80500300000f03011220703000b030215a44800c4031800000d03d0109400c04031301602c200c800c00741c07049070640300c0d8110701101a002080d400c2c00781481441181d036181d241d95542c2c6560f22456000440d055100491000e00c0101c0c4140640000c0c1941c441001e0a400921510040c1d8002c0f1b02049895100504101c00b5024184818070f540c002141036240c0001ca403e181c1121030f80090402c1402d40c20101c4801b102e03880240703610036035002200c480c94008130b222400707900e05e00c8007500940020400e890b001c10000c211104803548803021882c0303041039a40c032440c940c005400e600c10b6020300300010213109451841c040c401d0030240d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 791630512 1250 791629262 791629303
    0xb03010608071d090604030503100306050f01240203031311040e0c12010c050910120e0d0207091806050c0d02030705070209010b030f040b09030912031e03040b010608040f0203 77
    0x440400001403081d2689103c10a000410100010100b1410750264050502955994820802c1c00c604681c54000911032482c120034000c507a4424403481c0e050701c940a00c00704800094102c68003000840800f2400164020000281c801c000156034040c141e08c1428000c0d50100100c1c00a010345545c1c0a42005503440344403044c0c8180740850101c0d0f0500340e107000802c00718085c400000d08610800110074003d0b1034400360380c60741d9440741003130301500701040b4810803401c0e908440d20350700c2d00c04d0122141d0040c45494000300301e8151912070b889009240306e006440c02007095882001416000f41400e907506001d1044403441c80090000318441d0520755105903490301588100043c2d0389040c1c200ca01d5070b1105204209001c00304d03000c040e401541110f07000805540750366410f4a180314500c011a000580711482070344a804c00006010316101c841a4a04c2c83c0403051400b000340d000494020705158840c60042045038000c10b6940d41003400343c80003d40740c803940d4022920300088041480d00c2404007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 791631762 1250 791630512 791630519
    0xc05070f0e0f090601090b030c0d0f0c0f1202190e09071a09130b010302160309180209010c41010605010e0112090503130e0403093203191202070503011e0f0b0301060807 74
    0x45040003009810300d10310403001c03503082600710ec5010100c030714000d012f070307002003074845204664101c2c05009008201030050700d49031415186442d51101d00c169030841e103480c0f610615012000083e1202454040c0c43d022007544107030600e0018200c8500320a050550030000360004101c501c81d03603c1480c2c040c0d141d9170822440d02c46070120400119080744600303441880354410582e407250a002d000d94101c426060306980449000ac8400740b0003081240e00c030700b14003001d15031034042044ca0313030304840c150000c0001b6036544006482101c0030082c8140001d50f030702d0b4040303c0e400c1d030f1340d0201e11118028011641040c0d240744103962031560301e42200e40d08584001c00c01c000c00d540980c10b00c0c05032014242d0390104c5a010040600c9000f811541886811032204e20310015032800c02400740f080d1100e154500c103121103410480e00c403a10041e070301c00041c002c3c040041450305050290100c0c00498000415a003a80d114084005000703602c1200650343c5c854400d10480c4d0317424000c0ca03025011007405000d14928 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 791633012 1250 791631762 791631773
    0x3051308060c0c121908091204080c090105180624030c07060e1b0d0326010f081912020a1a0105040b0d020a030201030902010c05070f0e0f090601090b030c0d0f 70
    0x301c2c034071440c2c140c4900f0425001c182078117842c91302002446050455107030301d6513140d0a00784001c409400980350404078001402c1c000003d0260780e45c2c04150344082072641c03650140702c15911201d0341104021a8040843c01500704004c482c0c0007007005000020131104403c01150f8182d205951060041a000c66518284070310383c404c14100c454502c004000c0c05442109071914410300c3ca032441c2c0f0540c412480c89017494000c6c1345c0c4952105054490094030500b084203c40040710038018030112040d19400810a00710001740c01e002031480a42c3c0b64a0f000043e0381c2c2c940718005504040c011802601544000142400c008018502c06001b10310383c151b04200c1800b080701ca008206034030681ca071410450258079400190415650280b0700400c1404a83c0016910038075051030007040c510a5650020300320b446800c040041d2003c0303034001c090700c0e104c40620112412040c2ca2024a90b04a90700400101882d0340c040f103a4444068152004a0401000109800030080c8240d41a01c3c82d038812004103c3e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 791634262 1250 791633012 791633023
    0x703060e030901090b1e0d1a060408032502090403020109030f090f0504091e050a0210170721020c01060e010918060f0207080409020d0b040501050d03051308060c0c 72
    0x20100c0c0c025414020720000091803c1043c1c13049a28200700000e080c0304c1c02c20100700150440d000c2c4c45000fa43c2e085004104c40041c41903211003c01c400031150404400c4c80c14078100c0e001c4480c114000c609050301110003409a00400d044594002c0940c41d82c00d0040c1c40d41d503100d5100318004c2d00000340c5040c0500307000d0183c2054201d480c0800036050000d11619645d003882d030003038450503540000d14180a1400d0b200903420340003c0d1090000c094072860810100080c0e1b826218800c2e20050440b03800300070240c5800301d440140100103403800c0c0001300210711440c0d00820620303400c105038000750790b5982003104a902a1444891513511644c0c103114a1a01d801c0d40c074018100b6031810010308045100a100d50507064400611654540f1044448554150140d80d03c1c50f41207032500340d44580d26040c0200070750040e49480c4285041c006840c1d9986400d00c600c41c102c80000d085400314110039a401c58140d4402c120501d10081322900c046603180e400c101e0701d4458490101c0d800d9071003055040c014a0706 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 791635512 1250 791634262 791634281
    0x3062c0a0515131b0e04120e0105131403012c070b030106090b0a030b18070f110613050f070306060f24030c0e0d03020102030a0e03070c06050f070b0405070306 70
    0x450303202d414010840b03c0c07000d003a81169000300000381c0d00b5121480d0341c01c03544400e0b400300c90440110018001030107401400610148004d89407400d00c504128019a524040d02d8800201d140da0744c0000c00001c002c25000d0302a20000800000e00c02071a407041d520b2000038a03805a0422103149040c0c900b1203401c01c80e0001030800d65010904540c9005801031000f2294010080704000c080f0750000070300d0107030b044080ea80000505d000e600a4807100510100c090444101d400035194100950055004008120507021010082c0005545503a0700300c00c41c003c614401c45442c0300d00410494503000a04c142c40c007542c4100d4022807180d141400c8040c086015801c8008028140c402500000c2e0300400150080a0542008100030044010039958890103084694102c496a07104808055041d40114420407084004000c003002810082d59030b0b01910500403c14040002e0a00045008001400001400600c0c1ca85011382c160b0707600d00d42e41001d460440e000d5001242c00d008101883c00362202c1c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 791636762 1250 791635512 791635543
    0x18090d030e030307050c0a0c0303030f380a17010b040c0212090919090c08120703050913020408071203030c08090d080601090f0f050a0602070501080103062c0a05 71
    0x80c030394007680c403480041d2a2100340a030019010240140621141500a4000d00c00081080d1390781000f40280055030030302c044841c0ba0001c5026030580f85811203011040c2001013116880c0c1c0310044a642020080100d035114540c0c0307000040d942c08820b018510b402601c0008281c0a5a50090000396020740903644290b4202c1030700b031940038240005444d840d04049131030320041c1d107480b400494035007910641c0210150905000405014180000c101150000800c42d084900c1c0405800a03d0003100350050006004004042840c500710741265502da14140005240030703a03038440b1a113030a016611124036907420380000c0040c0741d018418024500100c2c02c01270801d1a020344816150740c001c140200030320118a0201d08c090340314202c4000030b010f95107404c14496440c0c81012907000c0c05071107400d104046450011820502c007146400031143d06842314074481e425940d6441c0545460240c1c4002c035407510300a02d4a007000b002c28010704200201c0506880c1d0500d00300903051003000304c9181e07007 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 791638012 1250 791636762 791636771
    0xf010e0c03071809030320122811040f080f0c01090b040b180901270c201203010303030504060e010605010e10020a0c0e06090f1504020702060918090d03 67
    0x10081d4400c50300b00c00340d0b180000555131081d20301903004024413040501103038500d240400d0850100c800030911010707003080050160703941a02d1911000c4040b2540c0500c42224000d9516820054000603441da40e030500d55420151281d41c1905419035a80c00850720784d10801e08010421001d110f00082d400e030038a004440c480c10244d03860790380d2180740304030400088001a25540c5005011100d800c00400629000300c070b5079207543c1c5c01301c05581d40d0b0030000c5072024000151719a000920500d402e10210303480e550038490284200c9001c00e40745112180103802640420f0201c4000c82e0021406584079031070028082c209030900c04102c51001d04015080c4e8904035042c4000d80c0c00c40d14000304240c0854140c0041d81080c5400c90503c0e6080400612182040001041c99440104254400c03c0d0a5958610035991881d0766a1b50240540d06030302e101203c14400a07490509400601502c0c2c00a001241742c0600c0001143c1c012260602d5842c00342c0385102440f41411051200d10f084903030300e240500 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 791639262 1250 791638012 791638019
    0x50d061d16140403020f0d151a0d0507091508010207080319020c0a20090a060504050c160f14100e071406040504020d1415040510270b030f010e0c0307 66
    0x800c1c078400c03800302a01c11015910441a20b5440080d183c51888e4044c010a9000040000c500c025000b010a010694400d002041030381303040c50b800d041d400c00d03040402000720526004408000f0040341d503502907407080b451386c081401da009000500c02c04d44200759580c0c0c0e914051101c0702c02c05035510003822038075004202c0b4611407500010040341c0340380c0115840c9240c209180c1a83d12503040504065040105482006a4440154006011038000751b8040c0b02540d04c1c40401a43c3d0301c00c0c1d04200360118851081c98000c1803001d6196000184100050760307800d084640c481d442c0c040342e01046c00309651103c0d40500c1c110003d204520042c00c4692209800c01c0520703001420078001ca004144c0a00e6010440c11100f02c01a000b041016400340c100500905000c05162171094024000600841c1040c0c049000b00380b5032190201107401d400c013290005030890503e540852030420310311201e1502c40745c804510f41c0c0d00340a220710001c10b034000016040441c001e50382c1051100045144039800002c2e040 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 791640512 1250 791639262 791639297
    0x12030e1c0503031504020903151b0405030a0618142b090e131205030a110a050d090309050a1707080c030d05130b1201031e0210050d061d16 61
    0xc81c0c04c40000d940c0720105290610100c1c0080c0500c00c940c590503c5040300c09028500701d0901d060051000f840701c4000ea03403860703094903024801d61089580582c415054803021454071760002e01e0780300035001206901ca966807100c1c804410f103080e46042a800c6400640502440c0d41d81c80d41d2800d40e19121005d40c00c00402e4090b02c000c0440c030644c045181900d0014401c21030b8802c2000300c5a030702042d0a2400c05030320304002c003950021200c81d00c5480c50124641071182228007a50350214055a5151501c91712008040c064050040110184001c01402203419910100205c02808a0403e8101d40c641d01552081ca0040594005c03590707600448400075250700c010a0084119040d81021682c2d070b40005050b1140406c03580c000d189c8a1400302c4c80810000e0365000f0305d41200d014203034001100002d4028601e404c441144d0081d071100b208211581483d018002400c95a000340c1d80000307101d99540d10b0f41045d50088030032540c4c41d0020030208524612150202c0c2100c50b468a4982c004d801a0180c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 791641762 1250 791640512 791640517
    0x90b01080906040320070f080606090c0403050a08090d0b04052a0f0d0813090617010c090302090c2104030215040f02152209050703090b06090603030412030e1c0503 72
    0x100c1a20b170303020035298280340d003042540020b02c49000345c0e030080750b615203219846d10401c1d110103108011710b80200d26150010420b075015070ba04003015010044280d40e41401c65804402d8080e0440d10548118001c61043c2e640383d441203000e07901034413001c5810b005540441d51844090000d0020914003c500e9841e41c142d110b0f032207181910201015000c41c00c0004260061002d41c0405030304600c000701e510780c601d030000130440302e80d07202c00c4507030034400003100c1c0c01c4e00e0f90030a10400045403100708201601e0820b0301d0030340040710401620700d4181d000c1e480e801102c602c051403030400301040040c40708040d4104402c00c0d154082803440c15650600e03139517030200c1074a5514041d12502e440b00100d4600c0041c0d9045070030096122002001e6520301445d81d25030000d0740c2c810103c81915203030020741c1c0640240501c0303840702e60082440c0400e070358140400105241c081c080d1b84d098401804086118503e5512901c901802500d612000107180000c0101c1c540c2000803400088195a0341d600003d40d0020a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 791643012 1250 791641762 791641787
    0x60302070f1205120a06031208240f0a090501180c020d140405100c0b010b0c03041820120a0c08040b091f0606080a0e030901080405011401090b010809060403 69
    0x8826810201c1503400701e642c0e0040c05048400607803c081482001035045e80500c3c200c0e4130a40c0011202123209a040c0d507500421252080c2389458910324008079030f42c0c850303164442180205184072214136080806c500055541000380b50565541c0148412a18040303e186000d0b105a024004110410300094403070321001701560134850910a070300790010b042c0c02620054000500141001003002d10001e14a00d030021003501c008c4520310001c19000a42411680454040e0004600e040d01d000c920488428070800741618169807100f80650300c0d00740c40c2164500442800090340c81d89800f006c007540741c03030014051264062504100624403074000d5072030343e40590441c000300d810760744500029042c050130303007c1144292900040c006d000c04144d8000c1c0203070b81066840d46400d0b41c07078400784011a00b02e600014016442400070405661144042503400383c4114000b00b6844a4002000d140c3c0b142038100d44030081c0c0f5640801c0309541e11142080e8800500f030010f241d04c0c286500c0261000f1b00781030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 791644262 1250 791643012 791643023
    0x9010207081e070b0709030b06090609070f020a080a021c050c100f02090d030807030c090e1611030a02030d0b19030206130b031302030c0d15180609051501060302070f 73
    0x2400c8202400074070241c85145404c0196000c90380707030038140100907001314041110719080f1107001c148079041641d2000d120305400b03048104151181441900d0000070288500118802c0c00700100004440b10302612503105250018420200300c0d440c2d407030a2111903041e03001084014030456034034a00014200c5681a00c2c038400082440390301007450040c0c80391541d480c2d080482120444205079110b2491442440596805c100e40171610604a0780291140312350700c410780034040801c80000140281c07899076809428020740e20410000c0150541d08251082e40c0035030000b043c0c0403a0860503011b200a0182d046a2400da031460746085400c00600c03e001c081d02411000c0350b46218409220303419401b80c03405180b542e840e4540b01d81074290320080c2c00400c078020700480d100c02c0498103002c81c06014107603000c85284030306031190036044010155100d2191401c00c3c9541000c000c1b4015102d03071403000313015401400ca0008240c402040550060344400101481004501c01042c0e188072070306603050348039 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 791645512 1250 791644262 791644297
    0x170307050601180e030316030605030705030309120102092710062f070e010f090b100e0f060d0912080c0904050606040f0f03050c041404112d04050901020708 69
    0x2202100c006100013401041c0718440082407202c81034030f03480220600021594144850b944800c00e050726000c0717520606400d58800e0000e900d0524151a240303006aa04030001070074180080e0005a1000c01e09201c12000740344140b0500000803010340c926413100c50040090025458100028014402d4843c0c117614010036440c01c2210703003400c00170300f03209055080448411544480c2441540e800a00c504283d0344003400d400600000300340144283c02b0381c0240585891401000c041e2400301210540d03aa2107500c41c800a41c2c540d0701c450140020328000b81000880c41e41502d8001c0c1002c030000d5140e402d010700582044015041d042c200e510b03600c0240c8d4003044913200e80011440e14055034100c0010301100b41d1000c100041304580b00002c49024104990055403210b083c0710885244d9040b160590b0032820000d008604a0360070a4a1418090001108050b0040e0341210328005840c642034401052150704c0454074044c080c0310f401101c0d400003140f03030244a6881c2d08040c840c0038050203030b20446 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 791646762 1250 791645512 791645549
    0xd2001151707090c0203040503010b0a0311010c080c031c050a2a090b0328090c090b010c02030a0507090606170a182040110d06170307050601 62
    0x42c03120500034824442e0501c00005280b5029480340c0082c00307070030701070741c60301404c00e000b031801d18500d400b202e40100e5800803260840004442c0300842240903946908104180c00d03402d0010002004102817900401c00940308088110782074404c080d005280103404d00c001005c1d0a154011089800014451100020088580b0070b60301009503501c4080500004010009521440c4400c0c50014100088411044800e40407200440c1c45a010103484003001030814000c0c40080e43c07020980c102c05041c000b5606540350300280c98a002034000b00d0302e582286904110540d038030700598004d05083c0c180180c800d0f50103100901a448020b00111080e922400c900748001030130810491142d800c40c00c028902508503803441110707803099221038010b88012842c04090507500600c0c0c00680c0c84c03115020b80d04140424100c141030f00990280d01e510f81d45455030b0460358403c50003064030402444010505610302491440403000100e61007890341c10802103040007071004107049064030007404120802c000e8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 791648012 1250 791646762 791646809
    0x6220b132d0f050c0a0f02031315030207050d181512021e070c15050720190305070f1a1603020c37050a03080d0e0d200115 54
    0xa060100c241c19910f4482030050b0390a144000384860b5000e81c45003100c0c050300c200100c0c6c0d2481072404992012141c0070f000d01c01d94054000100105031203250140c20250580c58807030400c610038041c6008a680101e6542c0c0025440e6408401441e1340c1020030310304c4c0c81b5410050140d000c02c850306041c1a80c0095801d03855500c0300b9a04d8400c050345240143ca88003245002c0000021038084c2c0e8801c440d24007c0d00f00054814401c0381c2d40305501c83c500000ba40454090f24122200b81e4107034540c810710a1980c00c3c0030f900d0315541007004502403802800c88034681107000248405036080001380700e812481c05480f0416003c103c4252a82400c0000e0145c482c50904034205284001801c0d8000350748408400031500d41c0c01082400488041c40f034644000c2ca88051004030020300c43c407904491804001c00102d80d1500180207154a452000314a030703004964000e003041d030040000c02c007103114140754200501c5c1d070b000c1000001c0082c0c402004042d01d040304440030b141e154800d0101710804402d00c20180b00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 791649262 1250 791648012 791648021
    0x1b0715020a062c0a060b04150b07051c050d180f021003020409021818070206070e011b03030c080c030c180402090d050c030c04050c09010806220b132d 66
    0x4204003074103c0c045026042c01c4e03165800f5100c15503046007405903070300040c81c203881640c4243d0306031074200003142c0c44c0000281d0780790001c00e01540c0b80c1c0076605101188040e003000844169006c1d81d54540d480c0c880400000131240c201a2095201000c500004c00050309076149002c401c0e012240842d40440402084010384242c0d04040f00c517034004a4500c0d640305401840400122084880c245400c03c0750042e21600c40088484a0040e0701040115190601560301d01d0084507043c582480f0201c0c100d18000d250b10761240341180000d80e2814a480c810754002c0c2600d8020995000c0d141c9503080c0900850000c0c003c102d25080ca0140c200784103289a516a81140c0c03010781e02501c204207491403810840e840360181c441840c0a40900d850740803140c5024454030b0b02c0b500003000700904055a500045581c0300c4010102d40d003040c00c01100c80e0b0008a00341c081005004100f4000c11482440f4043c0f0041400c5081c2410b0311030308111000c076130300e2036540285541012609100008160031f182007800303030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 791650512 1250 791649262 791649311
    0xa0602090a0f060507060f0207030f050a03060b030115180b070204020901050715050a0f1e0e03090a0b0a090501030b0913020f0d03031a010507020a1809081b0715020a06 74
    0x40c402128000303580b40d0000d01401d090303806006c08100129004a4900503032040c078900a0006008150841a141c0500301500480d811071800240742901e58908001079031080c3c2000e98082565040ca5180c1680404002203c007558142d0703a00c403604d8071081150600400d80300910494000c00c030801983d1141054a0200e60400c12a102c04d107161f2686600a00043d03036902052403d06410b6038000d88180989100c07500303d01b40c0342403107600c5081c4440050082440e1000c26020070002130100780e45400b480c401070580307000c0c800c0d512610402c024207184203550005040c5070a0444148840d526001a00c1e072100d4440305101001403188001803906403032003d12a030042c1c2d2202514141641648620301202c0c41007a04000d00c6440c030300641d00c078011104001d40c0518000c0080c414495034001004240c01d00703c0c008103100500350364244103a0002003481401700c0181040d0314100d00200a00001405810002a248140c0c050000c0d03c0d4102a400a0b05a50f00c4250020304554001c0300350211 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 791651762 1250 791650512 791650529
    0xf03160809041118010e060d02070f0b0708100f05010504030b060406080d050909060a0803070807080705030a081f260a0b07180801060b04031e0b0106020f0106080606030a0602090a 79
    0x2483c9000106003494019201103007480e80031110510365540903900c268a40c031001446035041209408051010350700c018070403074429071003840d598005042903003054006e40f010b40b00d800c01440d11207084800704000b5030101c45104140001000140d8014003141e003542e40008c00ca10301c6545540200f000391a05501c4a402d078403401c1c20a07000c02d54004c2c06050000c900310b0710000d080d2150342c20403400301c8241c0900f40040c1c2040208200040c200001004c41c0c500c1b03242c7c040d0a01c1d80f1500c6039421341d00110118408107040a04210b00f03003003c0a9410508481c2e0500784505e5810043c42d41002c118908007880c0c40b1030650b561210302201008036010040c3e020440001514002d80c004000740c540855215800004490118000e507060040360141c404607903146003014610303103442480c100f00b00c65800c40d0480400041d80461003c0717007181e0103003031190000d18862428250782821a5040e0340300c0d4010741c00c40c0c401c3c00b0f0281d40110b07100c45095040030700981c03a0b0114200060042c94240d000850307 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 791653012 1250 791651762 791651771
    0x6090f0702010e0703061509060b0f0705070e0a0609050a14150114070c170d020a1514100e1303021b011103030f0a0b06040e07030e012d0b030f0316080904 68
    0x8200054210780401f162903034001076165a1a0350300800d41d100d5004801e107291050101310003040900004d04000e901039001c4943d11b550ba055404103840007501d91580381920b0302c400b80f100507010300400d80c122464040810800742d00d2210501c815001400080f020407030801c41c0d0140703a105c0e100520000200300e40080e0f0310340f5640b600305a254030030b200b0800a102191071052882001040c0b94102c0c2c001074001e03080740c01c89503a6034200c200070308202080fa40d40d034800001e000c048000c0c0f400d104101d01905d0b41816420705509040f04800101100b04d00f4508100722400a6808074041107448402c1c9811034043d12031030300603101d02d44290b400011a12000c803c06c0001102910058043c80018104104004d4000144155440340d40501c442c224961004140d4027482684034030340c4068403000024000c03852003032410007071003c3c840f080700090491162189800d10740c407405460901c11070041c560b080c0d040034031503105d028140c00080c006a90003128414071080740210740004000600402 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 791654262 1250 791653012 791653019
    0x1d0610030b030f0a0203060906060102102c0a031805030705150918041a07080c07021203030a02040302180112080705070504060f03050d2c010201110a03061d06090f0702010e07 77
    0x1541e811450906138070910460020541d0350360041009ca000e01c40680c0540444404800d4103806001c00807040225541410740351841c81310034800e0392980f42c030140007400b4118040d08009084c0b07080c002082210500c580000c10244d98005003150481d84103131030014107455404040c040302e0107041c14a980100b940d804030311404110a034903522841c8501808800b0f241c0741c6a4007020324404481100100781c8004c08108000c40940140c10761620003040c010b10b5100341c411090542d001a030740004200c0d0042400e00444c905540c0c16002c44517480e100304200c0d8035003003082501c074428190242070384100081c2c0200303001042c0030800140c0700c0500700740300045d40c64030900ca0f006868401682c02d0b000301d04c8a050418803c60315440500510245005650b2035800006041d00750310000030705540d41d442c0c62802e0307a200364005d081440c011703440c0002c005280900204e0f20b800540b808070040c10000303081201541d54442125040030461070003550b2682d615005a00424244483e00d409100303d09000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 791655512 1250 791654262 791654293
    0x709230c0a030e0c040207080a02240105010804021c0803011a1201030803100b0c0d0f0203120103020f010302071e110a0e0403031508030d0504230c101b030e010206011d0610030b03 79
    0x701b8011300c62b43d0840342031240c2c5e09262620300702d8020300ca600d8162000b00410480d84035801d50303900540000d082e0b2003100030190050700d10341c0520f20101e544801c0800104481c1c40f084405d101a0199828030510f00304583d4607560080c1d02c14040144600300c0030020031841ca010b100c900d0044c020300b000c03065540700c07003c1102d40c2d1044007070119000507400e07030020340b59244040705131102205444a056000d07421a800c1005841899880c0c604045e402d010345000309103d134080c800141482c3d61160201d44643c10014260740090701c450740a2001108100400c0310504440c81c2d01035011f20b00010600703d501101c2c00c000329503038441551440041a050314a140035441a40514407552b03050300000031150000321401d2003c0c50b0404560001c81d05d9100340d050616075002c0100f950700d804050a620164020b00b00c1280034010790000d075069074180d4443d40c04010301e6014006400c0d10031520390803c02e19441c44500104224020303a0074070401421240070303400c03030f100080780282628200841e4040b40b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 791656762 1250 791655512 791655517
    0xc030702040b04142e03061e0c140702031203010602011d210c0a1a010303140f09040209040608100f0b18180f0709230c0a030e0c04020708 61
    0x6070321807442c002102d80700745018880e110041408122072042c0f980d507101a20703100300340d0710b4001403821003281120750031404508102018600c0b8000000f280340c05000c803d040400e024a440c01810702d0300c100a0441500846003100040c5800e91950ba901410b10100341401c1d8000c00d44070f1911030100012a420f0b4064000700f50070580c00a10492082801610941e582c0140440f110b00e600318070a90b85080e081d01c030050441d6a814000c80e507081d582550b600481070104141070018410000044c400c0540c000e44009160344410020b030300340301d808552824030340310312407500d44110b90004110360b150300c440d0072010084c00c070f0100740e84183d644c10000758007400c15641130050003031405960844a1030202d90703071600500c669518240c1641c4000486200b40c00c0914008520320440c200d440f040d42040000320003500008001056141400300000401044800c101c500c841d002c20030011500900816a083c2d883d091501103018840800c01505009404601c56000b80c00001e085c014018030000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 791658012 1250 791656762 791656777
    0x51915060f080d09210c0f0923041109070c0b010806091603080a0323010b0901030e2419020c0106050108060d0314070309080d0801060905181b0f0c03 66
    0x10f442980001600413101c403c0d4600416820840981030890240c0300c1c90301080ea1030740305515040b2042e80b07039100c15101002079806110095100c4080707140507103c84d01c0d901c0340c01e0352580e81c02060f400c06070344110300880d040030410f001e0710b0745000040d210f500c502680c003919034011002e0150340d6190f40ca915211a07044a02c400a0f1090410303542d00c500d840856582129000034003035050a407403e9046004d0014444410100a040f808900282007091519802005011440759983d0101e00015041d60f02000f041d07140ca42209022141c4004401000d40c00707a035610b6070154807035540c1040200005a0000500c00d214400715560407400700540c0400203840003600c8010303041d9540c00411a6104200c50300a00099030030802c0041c40c0b20240140c0316062290911010481c0c484900714900007158425500084a907001044415002083d440c00f9203010713500c207000300c1400c4414520380c56010346100260100b582c8400546c0788180242e5005800c1c0c40b109954038003040014544e00d800a98 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 791659262 1250 791658012 791658029
    0x16020c100e040c0519021005160f080711010c08011a04050a030609020a030f200f01021e150c0c25030201030c270918051915060f 57
    0x4a6600149040c0d40340000d00e500558518220115580501003d084000640b905104c020b0114114218851074913062078402c41c0e004205951412811409445000d00402c001c00b8545044002d4642c0c060b0714194003144904000c2c516840e1400221509610b45107103400a52130941442c412a0303001c01c000d8100c1e91710f402641c0d12400388030306403e440d220b18800c00e81e00c0f4203155010000507880340c203e89a16400284186071a0355280c88102c0001e801102c00c446c81c242c88100d41d8210110082c0a0500c23980580f61180030407100c00010b903403000212240c02d40180d0134214080c0d410810420f101031010400303400140e41c2000003607104180c001407840c025a0141c96020101d00000303400307860000f42c001501c1d1100c245540c00560041c0184510344080010700000c1d0a49980d03031010b26040b1040800858203540c4c40c10112034121100c01c01d82c62080030413880501c002ca4000100c0e05103c02d119550004403244910b440c0490000c04802119418100800056005040b00c0c52004683d401c2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 791660512 1250 791659262 791659273
    0xe04020d0e0f0318012001020f03090d030504150209030c030d260f0c0a0516150b01080402060403020f010c05100f0c020309010c03050c0f1f14040b070f0c0b1602 71
    0x144082c540fa4000c1100702142e01c003002440c1c1041e50f114804c00300300042c601a91000045201c00c4860030b907441488000aa07a8002041c015100400c000000d004090b42c50b0411403400e056407107807419141d141403a1a00d03034000c50b108202d5582808000141040101262003406402c100070300210a1908107034901c00d548095600c0d00d580000c2070034850400740e010b0f00140e40c2ea8102c00c0d9480d03042102e000301000310900c81500114a0f0008a010280c01142013080c0e000e541002401a5881220381904000503c0c0500006858940c01d0701c0650354100c41100307003440d0340700048440c00b110a8000e48144107465500c54558050744c444000b25241c008280450b42c6600030036aa01d07c40c1020407400180000c1909011a11410181000b2040241500d64840142c2c241e9868080764841c10301c2600c1c0c07036603081c081c0b01049203e2902c508141c51301c442510b1905440b04014200d00030100020310184d2174413084600d03c513a40302440c1c103900030023031101070420b100d4070321845c25032000700d1002d40704a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 791661762 1250 791660512 791660533
    0xc131514040b090705090103020d1b0e150909062b08090a1208120615040b1c06060f05030703060f14040f0e0a060b03030f0f1201050a061b030e04020d0e 67
    0x154080c813400d199142d05240041d4400110000c6d80700341c0c80000c800e9500d02c420f4030003904280d50310845446650f102c0c4078034070980042081070032055000b0110b5000c20899852903469025519601550484026480042440380f1000070b290303040c0d02030514510301100d03070b00304074200001e0303c5855000d50f900c1101d680c91760321a030b000303040341c9001802c00350052003001001031034003072600e030711000181c441c00001c820007200400039005600f10030070740c0c040410101c0d00010280400351086040c06400e1124915103203026212703100b03105000c0c1c10050000002850326000303030400001000384220080d02199500e8107820351606620b00d0364800c44c2000d0120810984a0040c40402d07540311024116003800c640d079a000400502c540c00340c05020a203c0720800b1200c90002c0d0000c0602c0000e10343d40d50121101e5400803900c1600b045100d031001480034444a43d0190035030500c14100030704040001504d08094525105440c00a58070500010343c540940103281c02c07011200340c080c000c641c9120790 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 791663012 1250 791661762 791661769
    0x30907080d090b07061517060a0b09010630021c1509090507050d0303020408061605070305180a0308040f0626060d0606030b06090610020c131514040b 66
    0x190154030708009801d07494140074002c841801080301e00c0c03140200007040d4120a520700d03207410f8507078407070700500300d003410206100507090100c95441055000e04100b0421605c0005101e40b0040c018a03003001003500300301c1c1028049031340c0d04a121417030350b41102c081411400c07150040e501148a846031280301c3d9851301011525401781810381001c05021803005070500c02e21030000e08294205403014400c40c100040d9170307100c0c0324a82500c00d02964001d6034441c2854910791070308401620009540c0041c812020803503620100780c0f041e20b540f42c82c1c0581e80c1e04004e10254128081e00c0b420307030351201c250000003017002000c5006100b1124407044014580741d8400f800d403003080a1265444140403800c0c05183c8100440c148076511034801040040110707140d4490404036503040e001166076030110001d10007145881c40d00c080d0306c03000444130300c029903082850081d2511a0442075030300645e080c00c0300030194000c3d900401040d503d0700c580e00c402ca550725420003a240041c070007840e000301d1820364030740c08906 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 791664262 1250 791663012 791663023
    0x20060402130c020c0f0105091c050606030304030b04030c0609141e190f081b0307030e040c2712061b0f020a03180902070308190509070b1b030f03090708 67
    0x16000307040d10110413020b2042200041e45071302e0400c0310812400a141c1e8070410620b14441e2032140c0c99000354030a18100d454140b015000c14400d40c810300c010000640d1184900768000d6061a0011641e2400d142160241c145080d00821002c031a03c0000040e031400207070402480147c00c021025203401200c2c282e21500a090030364801c01c8002d6003003001c640c0402c5001a000e200fa0510392038071517600d8155403511140f14a2550940000030700c0000d00da800005d030380642108840c1080440000d038000707817258400d01010080d0109440c9003010b04e4001c44181c00040030300305455123160015250078401070074202d040100c18410b04d127800641900c038040c0740d00c0c140c01c55001041100c40a071819100840d59095100c110310240340081001d540354009844918403075180c0080609100d40e10000e002807044040e5605483c250410500b0340000800c181100d80907003181b652210501d40750010010105c1d64040184400034112255030000c0d00258031901184055540c42c0d511444090b407100d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 791665512 1250 791664262 791664281
    0x6080702070302010507050c0913150605090f06010c0204020315010305010e04050706080901060f0617061212090105071a0105120703080307051606150906050d0503192006040213 78
    0x580c8081020b10040d40100010030340c040c042d4080f142103000920010b8401b160454019207101802c501170003c11542850400003200b00c40400d0104a05140110340220030060400840030380c0700000ca4800d9000f0849120b0440e0050425541e0f0303c0e01c10104401080c0200c035480c00a860540009202c40800c10083c0c00b807031303104000d400410301d000c03811107840340c000c2c0466507075560700c000000300842c03041d0310800204860f031508840c14000d02c00280740c90000418560003101414855a40d20b1004952808199404140d607512112407000480701c40c014208000c2c090840f000c90002c1c40d8408210160481c0c208a03801041a0504400d0742e407030700320328803008210f08000d10100c1e0340e01c1c4c09200688000703001210121103442594884c48240c501c2c2500409110741001c0080c0000c14480c064007002d008143d07041d0004000359036a02d43e603031080300111081c480c1140c03200341e4003e1040310001d02d1103480004804290800010f00c548801055901720321600b00c509405080c0300300b80c001e46115 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 791666762 1250 791665512 791665517
    0x60e1203040818120f0a0308061f140d1503140a0f02010f050906070605010602190b0a0213050d0b0609070c050d08042d060b03161a040e040318060807 66
    0x800400529a805000200e41141d44c0f15041481c0e0152240e4100440d000c141d0400c001071a160481c3d0501800e0002c000d803945004124603084070039500712007407824500704c0c40c078a001554107404002000040c0550b520b4007190030f051500888280d0241e012503400d40340120510956071185210040d540d0f009074900805400a003c020005980a07140c18008841c550411b54a00f80a010000700343d80c2c0480401c840c00740d0389000600096504200009004400b0728a4922651f491b4880d640e04050052007940c465400140154064802d0040c0300300514020b0029003000950f0718260703071866001c6031814051284600001c0c06540f1402110030030341c4e08800549886401850211442c5a0040055984651205528004031005000c5c880e1507110304490f411041c020b4504030082d20100040301d84264080040341e40c00400ca60215011105981c0c100300344942845204001401b603940300700c0030844800c0800c400c0c5900501410019201d59460317440d4036485450a9840f060140c070180700 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 791668012 1250 791666762 791666767
    0xf120f1603050d0c03120902030c060d0c03050c09011445060301150c020111160501080f010b121e010b07151e020904020c1b01090e1302040c030207020904060e12030408 74
    0x3d001b0032940501d1010703001405031a220000c8402054407070b4080710310301750328030b5030790716491042d0b030381440360a400c00084440300b8074082113103000030045182d0894000c0100400241d1505040001690744101d01d0740307040100000c4120680d00e118004d0040c28140764500040c058110351401200700c0303040e28200003130703240c379058252000c440c0c3d040070320320480c18007400d5217482c2085c0b5420031800074007000b00c0d043e0701442c0c0c0c18a8001458000058290031501d401e407001032051400d03550588101e00c4209440c044195100d111609008400d0350601c3e04541010002050000c0711100800d034103406100a0700503810181004421944089c41020020b034110003080780c100f2a80e00107084611000b000503007407047d001600d41c10007000c44280d40001c0507841c01c01c461540c02100440042a8900b0481da0301e150046955804089104000748690b50b034811030b00590740642d044e80c0314240c0117030001d0642d2a2a2034403800400368002c81c101c0707910440d202172511011680c200c034031403030f0300804850 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 791669262 1250 791668012 791668037
    0x60d09020d081306020703120e0310090605070909050c041e0e072f06010b0a0e04060801021b0601080d180b0307020f070906060c0b100305060a020d0b0a03020f120f1603050d0c03 78
    0x8030056101c034279040c0c0c0750040d240040c28198503800f400d003655001301030000740c508001c1c2c0c1c042c00b143d116600c013031500e03410003082100150444041da021120203044500380c000400b4a021a03c845d06c1d00003110610707950701880f000650248800c20440c40f0642200a8207641c1420719018900c1440c5508290784014010300101792000047c1842110728100301206401c0000000c0685015030054481740c1e6000c19078200403940e0000c0c1030f801940e1a07001c2c0c0340300d50500103c151a81e5071114043e09001c0050480561188110600d80040ca090a002500d03810011002519240b2122041d2a207210311000460001c03410320030b54049804a444650750501240d49082c05400010b01100c55100710750400030208005000d07152290181800041e6680038804401c02103c444003405800340409110900050701c600b0000668400201e03040310100710000b0002d803030040b10070010480341c0100400c880040f0040e04543d0b041c3c0e44a10160744801100707042c21915403505044c0a4001030181a101 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 791670512 1250 791669262 791669267
    0x2615090606070303150b070f0213110706050c0d020c010c021606170a02160b01032603060405041b18050109050f0112050c0301061202030c040902030309060d09020d08130602070312 79
    0x40b000c940221703080c0c50031381d980c1c2d805c0088140c02c011030507100211003020910451920004800503108040010880c4415920b10215180142c0c84000d004541d03030401324100080c10400d84e40040030542c415036032030b495089524082c01b00f00d04c001025200b401480400c4440000c00042990025540c1d4401d090580f29140a00314010b054801c1180c1e08200d413545a042e02070b40407109900031010380c041075140d49840000140c1680b00c0315801c0048000095103000d20404481d0050001c07074000c10591100c1c10001d00403031010064000a69103c6800107405040030004c84034003019810801041e80d82d00b00c50000e54000311030320b94101604c080144100c1c80c4240d120300c05140500c080320700d4100c10901003421140303150400104000f03000b40103411490100020a6401d1041c2c409120303401d071036408250b40b402030380d030001d200b040040740150040840381c1c4602041d80e001411003110b008030381040310b4140d10603c4140700c0c4c50700c4403a001c01c03002e0000602e034084a034041003502080e071005208 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 791671762 1250 791670512 791670521
    0x5060a09031b050610060518040f0f141501030b030c0d0f1e060b010e01020a0215070f060c0807020613030c1e11010e0f060d0c2615090606070303 64
    0x21018003070590750502980002c0548150803074407941c000c0a15007001442210825596440841000703c2048001d405030100c003c4241080f034199400308010140c07404503400b50034405980c4c0c00c403501e000884081c1c0c3c080b02c25200d01035404007100004424601c0011019900382029164050380002400e1071141040001f05c49014016031030034502d55103907a981a20042c0e0100c00f015541401070069051217054452041400001d080c0300010341d0940c0c0010752907861000d4082d2007a008420181010f4820504070342d6515404503120f00700613820724002005040d900888000aa68400040e000b1400000e4007800b0b05280f004c08040300001e546c040310005d1340c03a1009c81d040040c00407d0380210348000c1280001c24400c0020405c04404500010f01600080d403a42e132040c044104403425a450701401c40303503003204805000c60405d07050349060f140100048928044070412100082e00c2e0055003461a0207549080e8a103071125404000300300e81003200b62200707640310310100700d2030f00020b000340d20 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 791673012 1250 791671762 791671781
    0x50c040e0c0d1805010b100504080d18183c0c0203070209010e0906070302160311030408070e09070b0403110906040e07060c030e040e1207060f060b0c1905060a 70
    0x4011499480608040d00c0d403d410500403102691140c0814001d40790070f060540c0c609289260940c00c1c03c0c0380032401951881248000c106004d0080d80e2034031506030084001c1d000d46154401542041c040071030250050024020b440140c10a500440b00301214020640c0e4030800602c0e45003d20840030018000188420b05043c0c007544802c005090058a800c03410074000c1c0882048142c662504210301410007074014180030401d441081a42114011401c841c10722542500e040c008458810407c00c2c550300c0b0f0740d08070718030500c1001800600508410071107482000f00c1c2007920031907580d40d8040301050149000040c40c0041c06240b01030326080ca440c1c50b86d0b00c000004e102103a07400b0303680d031400d04000c89174112400040e105406841403540cc078000980c90b0b03000703035410400d034014180120b440b00c82c42c80411032003800010b000e8080c02960340092114a0b540350003001200c1d500d005035071169128140701034060140304101c110080400310a94035941e044400303001c0070780d01da180365030090142c0740 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 791674262 1250 791673012 791673037
    0xc131a1306080103051b100c0c090234020f042d02090406080a020a0509180d050717030f27030c010e010608030705030d05070e100909050c040e0c 64
    0x1409803904440503014001c0c010364881080303a50440c2007040c200240c450030380b000c050301c14401c66610744a0785242008404685005490341310f06240c0083d941c44160b118020300c600105a0203020344e62041608442c91a291306000b5101d6880502104000c600c000030b980b11045180020050905400815141c0040d801c01400002402d2403200549400c480e028603040c2c0c08290390805090a100d0000a41070100c0240031008040d030010f100303100360f809040d00540c0f02d00003055025500300c8410340941d000c203040e5040c901c2042002401c03600000810b890300c1c44d405240c1c40a8041d441c1c00c8a0040742000e843e44240d5032480468440c45440341002142c113078448070300c080038403818005003064810440c0040b420314280060300d42076504a8000d012140c104110030070001e40000201d40f205000c204010071280c0c1c40400560303040710a105960b40204161054140141c0d11003454025034040d0b0704100080c2d00c3d0004006550b01450040003107064840c1c010408618aa03000b800e000210385 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 791675512 1250 791674262 791674267
    0x709090f12090501030b041103010512071d0604060b0c1905120f03060a0902040608071b0c0902030403020d02070501270b0714070504090f020423090d03050c131a 71
    0x540e0380821485900c1c06200019441eaa02400395682c180140c000b9944219014405070401002c540c10a100610841d44104401d080801c0407000603c803400007892040c10242c60002904403540c0b000350b048903c50312851030920003043c02c111010681d0704c8415510020041c246180c1184440201802400e4540b0310071403c8891901d0514030060640c6100403c40c0703900c07405d000c404c0c440f0240503500300601c0280140f000f485456444a07600341d015074189800c03008460032501c6250700352a09000035010422030180810800301c590019401984203508480d4805243c8008036140c120740d014150001d04084151840c4004580c020b60b0150000e030246042035030369a80348000c40d80840011500c54100100400d0842000d120045c010f1a080d241401180321980d584000d0b01c50701132000b031045540307043d2100c50303001c1040e81039584810503c0a04150511036042a41c2da24403014601c0064101800901812039000961b4011341c01c0381c15121515080034980c048500c2c04000001601005 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 791676762 1250 791675512 791675543
    0x203011a0a0903140d17071b060207120806010e011409100315030c030c0e060a1719030210180b0c03071206060302210402150c0a0605010311011808070909 68
    0x640c0081c885a03086000346448010b50748040c0c1000c1c00201c18940360b072000e0003008a00e0b60000b08000310388c2003440d0f1031421540249807074802800342c3c0802400100c0b000041c403a206130800c0050707026030070988a030902c86090400446e290381600d2092103d18800b80000c0d10b0604100010505052150801140700c0c1c0d140d8000c8074055001e6401542d9490b40007008000344940d46004002034100365003983c03154504840460001441442007400c1d6010544811503c180103103d603490045240d0140c19a40f01541002540e81c5203000d0280502403400d5204425244e00744d48200a81c1e034404940416580d40344501c081607007009107000203016048151007440070b00c83c85428046e1242d5100143c4649170713512b034441004a1800c0000001600b6000d22000d60f6900e060951000580d05440d6070340d203600e0f8000c2d400c101448000030081c40c00d00b400401044402651a038403d002a40c4d04002d00082501d549903001c05442a848560480401481919807640095104034040c0d080003299421 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 791678012 1250 791676762 791676773
    0xa200a0c060e15011e0b09040e0d030b0a23060702030109120306030b060406180905010f020714010507020307020d0b091f1401050f010f0309061d030304150203011a0a0903 75
    0x40d00248104503000303004002c07070030840025044e000d005228000f00400c03034103071881c5d00041114080c1ca0a03115020030b44032210750b0b640d009080303003200281c150344450394080d0006e4090403804100741e20600480201081c0d081a0034034054640c20b2507013510f220451401c00340900d640c004e00090340c05548650001010490030040960140120fa070001101071440c203058034510f00c0540b08602c22802c0c04010000035004131940c00c411001550005070341d22041c0350040c010b108524100d410940089003200030b1101c140030100c8240b400c8d0000b80b00c1765032042802c90b187d10914a009601140092000000c292290007250348030b0004000c030785161408030343c07541032100215000c1d822680c44280741b12140c01e020081500412043c0e03803296806010030000390042c14040242e100701a581c84c038400521540341c00c0000c25890100081c030003110082203c1c6c1d05c0707520848082d07803484080700741c00d1507035041031086038100c400b030505500c00480c044070315001300e80c07003d10003000700001c00c0d0010000c01c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 791679262 1250 791678012 791678021
    0x130305010e030a020f01090839010204140f0a12050f0604080403050f061b0901260105190e132102011a040e060f0c071b0306050a200a0c06 61
    0x1071608004548480103840c009244c00422502e9842a9040030b080030002440f030b10032749622010350f8840da10460210040d450814402c07820302a8114030240c0500390022043d0b008000340c0b40301110710380880e44035001f40b2655044260080f03402c501404000c1200201d003070740007100b641c0316100f5204007501040c0240c0c0b030708005840681e40d1800003c0c0070410800208100003055046c007000e0841071910b504070764183c03c0380c140c001d8244440042d120f40706a202e0f40c540d00300005110080728407100741c0000c540e03074510240600d87c0600c050317000304010104803080882c111090b030034840360720780d4800c14010f40d414641c1c0000c44e01184a10700d542c00c0d4082c2280050400c10b00d0354000101c1c13070285043d0700c9418820b110014001e03231910580a8400001041c007070b07403215520390380d200729894042032031f14984920403018050044002c059040c21510a0141080300c0c0170315000d110303503113503500d0769411900d40c681c51251380080084181345450038000940852411800d00c80c01d0303d4813a44400f400e54 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 791680512 1250 791679262 791679281
    0x190b07030810061706010806030a0b0c0c0606030a05031c0b0409110f01030903020304031106040e07021c090509060d030912030806180106020a151b0809070b0a09060513030501 77
    0x910700000b009a00807003a082c1c00000d2820345803007440001281c11280c010140506030758100300d507a6000545130b407010402c0741c401c15070001c44003415140c038095442468000807441c40c3c80d4090000401c07014030b00042d0341f00ba1945c200c40078510f011b0a041030050386c01d00307030308020408580b203080401403683d50703200c2c101d0424000d081c00c00c00800c81c0010403202140c0c20481c41e05162610b407240c4042680001907038140c0340d1103031041c6100010840012064000c03507010004000b000c004014420381e001c00c00b03110f8480d14a242c0c0c803001c108000140c90441c2c0d1800f0780d035001050140004c00c00e02e84500700e842100d00909000702556104e2420720f21034000141c040c1c0208180c0360a002060500011034100e0200d20000c4414550415200a4030385030700c103d01a1001b811101111b864400075844880300d07030200d03110b140042126480181a9510480d80480380340101c010001c0c0c1201c0c0c0d001111381602c40e81c2c1d00c5800190a111080d21603400c05028445200c0c030303030840800055001d12440402 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 791681762 1250 791680512 791680517
    0x60608160e12030703030528090c03020409030c030f0e090c03060a031e0317040c17030d0606090e0a0e190501060803030921070c1206150b090406090b0d02190b0703 72
    0x1a076042c3e08024064420180c952312186401e1a80d114118002c4440020032000d00702001c201d000140c100307000c1c07103132903034101a42c41890700c9200820140c01c010000601d5209864140750071001c2441980c0c4910180c03203642d08140c3d2840045c1840902e00010b652001004040f80800c688035181d462003021081c215601c2a0030003c555000d05801046550102caa0a412890f030351030710745c0d640c103260f008034407640d5030010010748448420304050081d29040c0e0b0b21100c007040702650700d200040500d1454851000c075400300a0209840580c61f00444c508402c03040014001c00034070341965800344c10501019500381d50794440100703086405000650090000350014424180780c1c51621002001a4080000c00c1c04100040400a803902d40b8180840b01c0c00c11340c0300404101070411a001e40202e50703240c2000fa04802c00400c0703104125002d8070755058140d07001c002d01d42c1c540c4140c1d0704903480f01e140d03c0c2d03100c018444034800514040781c0402001d44040d074009016030b41c408908203a600041001c801 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 791683012 1250 791681762 791681767
    0x60f011e0807030f0e120a120504120e010e03152205010203151807050a1209050703120e15090a030b010b0403290a0e0f10150603060608160e1203 64
    0x400394075000d8030150004c42e2030108403002c1c248031440ea80356210b51003401d24100100380f54060310700a141e05020032480e500248210f24240c07800800181c807404442b004120030f600c0e101c10551060520490900c00940206100d5851f803500345540c0c1e60007444000588459440d0000c0a02d55020360080a80329200258032410040a004e0000c0c1000d0764042c00713074080c0d0440300d5903440a0300c100f54201c0c51504205a4481080c14119944070540e00c00036030309814004810100f11000034518110b80c0070b1401082420607010003103500c092086096544901c100340020040d429182c000c080c6408000c1c40726824a40c3c950f0b84d0714086100342e018266206d0046020414090764500501c40309140310302e03191f40d0102c42002c20301d841714040e2900d19080da480d6001c0071211170801ca107a80301101401241c914151a100c54405403100707800e16411044d12060014145010380290401d2300e5031138030b038580b43da512050400100300112406908101d004c90707100d0900c1e01e629003c900d51211300c0002c0d6030b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 791684262 1250 791683012 791683021
    0x30d0c090e060d02011409010201180b090c060310030308060607060e1b010504062111040803040f050f03031209012a020d090b030a020a02030705070e01030b011706060f011e08 77
    0x1003181c80c0081031503000321803101c100700040c2e038040d00c64100782c41a40c01b11034580c9000c100403801000c0302c070449180b41034a00c101806204909005034800d2811004848020101d0420301110740800d41e00c0d01d0806c00081d00030300c002400b441220f5401100a41418107142003501c1300419a5007420fa2004290041c1c01c50500300e50701150046905d100c04e08001d45000d1500000030005800d94a903a91614031030528a20303078000030b80280000e1a00c48041d5500c0e0b42c0c644001946a5000d4400e030403410540e08400504c600f401132442d60314100040155081c1400343d0440c45195400420051495507111038401012208500d5003800c0b100d0341020424220001c2406460300306400111804d020120404204080d01841203e9000c06400030140e2900320401c02039282d400740c003c004009000d0051701190132500e4609490403240039a440b01107230f0340c0c0c401c2d54040c48803524666a200e0340050001500e90b0808400d020111241031512000403001001c1074146c000f400d10080c40051540350610 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 791685512 1250 791684262 791684279
    0xb1c09030f141c1e020705060a1107023f030702011b14150606091f050c030301080c0a1d0402040504141507030f060506121b0a030e120327030d0c09 65
    0x100b62800351101140380c1b40058803601c2c2da8010040c101c408140d12421000c100703c1b40340c030585503415400750448005100146c0041c103103040c0f540305500c004407041840c0d0402500700b100c0011071000e110113180381900c5034004450408060003480d080d89918600000001c10825891007407920490252840317403c0d0024a10448070060140e03071007010240000c1449540c0c002040420450300c0b2807130000f00318852001d56031802041c0d2003280e0740c0400720001446000204003408a40c208542d49010252103440c030001180c0300203607802010751a54005070050800340d02c07041d0050f020b00c542c100c00700766500d52140b0704400021105c61148421040c00009a0140515044031507010018001e03a420907001c80c9060246944152001e0003040c08114109048044000a5040d0700c07816681d40c2224600035000e4407030441046114480e02c40314194441e030742c900341c84c000c40c40d8680f0495105504e005500421003a031480642c9400208940c1d090300a9502c20100411032640701d601282c1d2a02100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 791686762 1250 791685512 791685551
    0xb01090612053007061e06030b010b0d060f081e01020a022d070e01031a0f0123220b040902090c03040c050a0b1c09030f141c 55
    0x40400d44841081c1c00c000410124440f82a000c150311040c2c0d60810703031401c241c030300410300d0181c0390210b0340010705005015644c2c202c0022450744e200002100f04000040c3c50071281244405020403c00c90018860030a0500c0208121b800c003010110702c1640741d14181c002d0700541e40c024801c560295081d100d01001c900e1024030f0810002c030007141002034130342020751281c104100c4891044c141c510001c42c510103030a81e0801c81407442e01150000343e120491214040c1c420701040c0d41d020090b031817006d046403420741c45520800301200d0f01a420392904560700d284440d200307240d0600d10181414207610b40c44985a00035002500d82c1c0c1c0402075541c0b0b42d4913508645c00c14440744c1c000c5092042000151321100c52882e00108503560070b43d5256203900308034540e01046c1e0042c50380804801000240c5108440c041c04581c2110b006503061060000007000403140360800042c0820301500d11b82d01414050340389072501407041c0b040329241141c4205003080c8103c10345c0324540d1407940c0368682050401074200 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 791688012 1250 791686762 791686769
    0x306010e0a051023060d020705061f0f0e07030f0e07090e0303100b071a04060b18040201020a17040b0f0d0b0a0b190c051501060f023f04030b010906 65
    0x12820300f56414512002a0302807030b130328001c3d8082010400c2100c00e40794042240e45180461004548401c00362030300a4a0390020307100c03144c640d8242e8080c0040321b00d00200c450101d501e10b0060950700c514000101d40e200c24002c3c04081410390310700090106188500034800d2107070400014280c9241000e1003401100d10758210401564006d0003000406c12140c43c4c54000d40d411000030649803030651402c2c450900c038258154445140c81000d20080003e2a00a00d035012001c40c0c0807480303450b521202c1900d90400329000781c0140d01500d10100402e0b20043c140c0b55003441d0340c244614040d1581c3d405d00199101005203080914001002c0b58228614414000c661030100c3d541c0550030301e003440c1110315024840002c1212032001c801c410442c0c0c09600d030f06422607400410340d01c490051503010000310740248225004104455120705105201283c03420034041e11650829108502e600518100046032241c0782c1c18407110b4040b4001001941c004c4c2c001075205920303003e6558144401c10342540d00f20791 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 791689262 1250 791688012 791688031
    0x2030a0206011214030f1c020705030a121d030301080607020705090a0b0a051e031b060a030f0902120f011118091b0f070506010e0c0a18050306010e0a05 67
    0x44101940d0302144850441e407821001c100b410410341003400900302c50790f0b41c0c00309078440029070508901081d00030b0030301071007030b0f600c5035010f40303102c524134400e9101d901001070180c1c0040007180916801000c00401307110800e40c001865012010044e100e14010500e0000994800300040104d03032002c120266001c0890700c06801c0c42490040403e43d500d00207494402c0a40d201c441541454070303855942402400b00034a4100102c80118010082c008400d40302d0303000e4041d04440340800e00800b181441d003007101521071440e08400a80c08c800410002c0c980803a20307500c0c0c0e00c2c50030260b500d0400210b04940040d01a0010481d110141c03421605030250a03081000140702000c0d4001d49000c0301c0c498841c09641300c24040d40c0312014007103030210980015120000220721210508404405003207428412030894802c1c1e40c07a00d189070055002102c150503408000c114003911988201c0d0881e080000c500f9080c000f00d034035040000d0070150f090f0801e440b14030581c0700b007014501c241d005190300000440d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 791690512 1250 791689262 791689267
    0x80f03071814120d090302060715020d050603010f09030824040501060305061008070c1514011e12080306040903110f01020d0b220e2a01141602010309111309020a060203 74
    0x41c00050301701d40b201d02c0040c2c4161004210b500c2403000300041c1160005002000319035034091440c501c0000c1c4429a9034501079072a00741007400240b4a07110b201c030416003644419640356514200f4500c00c80028000300d01004207085d0130a01a29540a01ca019002e182c03804a014600041402600d120b00b000300001c02c0516002e022006400c000010140b980003190002504010b58411002d08085000c0d26004a503030303000001e0000d054401c007400e541810300450f02c4280c1d1000035403054222620060500e5004101040d281d240070b52101031414403906210300c2140b2041090b80c11f1081da00740600640e5000100c03410b0f0080503103e50510100201d034036400412001244810100003a540300403119500ca81c0224449030400608500906e850300480c0003040c4619a401120700c016811800310b80c0585101513100d908005880050610a41e90b40002c1c0d1280c0044010744030014003520b0504d02c02d81609070507120030f40c130345158a0140b41c000c01d220700e80c1e01c1403084082c0d00358030640864106 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 791691762 1250 791690512 791690533
    0xb03072c100501030203060a0e040c1a040f1809050d080103021f1706190308041401030603031b08090d080a08060103151e0f170613080f0307181412 65
    0x3421540564500303103001603c0c3e5847d8004170340301c04015040a81d0410742601007108111000400704103a071504100e1030704048450080d03549038042c5000713404036480c1031501072156420002c02001c0542203401c0110f030301c6030161281d0b810000751020700800a800040180f040d8104030313543e007684808150008001c10a074040041c04d4050505900305d001c9050008500d544e030340d903a050500e0800722400a2101c1d562071400101c40c2e401480784840e1a038241d05812110741c028447c2c402140e4150f240c2006031406208a0700c0e0401c0601000c82e5503070303400d00c038401240e190001c100228900c1520100d0380c1d0810810040d103600c3c0000d0444d0704150078280d40e00103071140c42c09980c046519440c00740c40451212000954802082e410542e2120080000068074081b0602040703025501601038520700d444e02e550701807042c210800d001d00408010442c60040c24100f500456001760940b520700f40c198a050070072740c81043c0c9584202446c129540c9040030b0351400a06461080f1200401030001116 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 791693012 1250 791691762 791691781
    0x50d1a090646060305070b070201180e34050a030b0d02010509040b03031b01091202070e01150509030a0302010e100203060d060b03030f040303080f070206091c030b03072c 75
    0x1440b09403140120303410180328140403001d80184014507440415a0035064403140c1c00b004e1504034042c140d0014408442c803110818072064550203a80300072201004998a81c08a40001904d04d0401c09440b100e0f401000c99112a031030150f101100179a541c0c90b0303202c04440d4020140d41da00100076210b02c41c00c008020040c0e030001704032207540400361000720720703000e03000006821400f6200c030340007442104143c5000b403000198040600d041c4a0303400408104a903000890381c0f80040d0040c9403c4c400c1d40e800500c03800043c2c403004e0b0403940042c81d0084c41c0c1101c100c0400c1c1004190f90085000d0b1f9103c1e5200b4105620038032441c1c0d080041d040c4114254901040012844840480c0c0500415903480706e8110a0301c042c0b048511051814144980d42c1d69a450000e010300000c441d01e00f09d01c00102c010580c041d20114185004661800080034070620380040c010141c420708141c907040c19903544030385520352070500145009002d150b0401440220030030088a0f040990103080c0d91410680041061044 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 791694262 1250 791693012 791693101
    0x150106050c0c1003060b0d06050901150f0309060603053a020304121a0103080306031209010e1905042309120301090b0a03060e0c030f03030907050d1a0906 68
    0x1002c030b03443c48800f5aa00e4050f03000f085107421110840b0400a00300684040c0d071340141d011a0b5061f10300c01c0b40c6a90306c001e40c120301c80000c2c40c80310020302202d40b000c2030180b090300101d03038081c001c18002030003580d42e948017450440c1007545e528080304441c450800c01c200d0b00e040400184110020041032060f44980291030b44103600074500c111a0351800c1c8410b0200984a0303004c1c00c1d40c0011034007901d58480c01c00c01d500d42c104607000b0b8820311440700012070741d00550090300c44900d0180c480710070b0003800c01c0c10001482803100c0b81900c0085032080004050f82c0c0c5015010b08034800c8000c142076032240203c401443ca40003043c1e104103038001c2c03d03450010740c041006c9034110f1302112070006000c1850340001d884a4090741c800f0f0107050801100c010700030001f060f00701c2c41a000f10201c031003001d280c100082d142c1c00115950507050704010010065030800b130707000c0045144540404244204481148507003030a040c0c07401c2c0810ba011401b0001c030b0b6000e9000100503030b49200088141120712020000201 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 791695512 1250 791694262 791694283
    0x21c020c060705010b04090c0e0a02070f080703110319030506030d1e0c1205040513060f15030b04090320060108060106030207050c09010801050601030f0e0304030318090905150106050c 81
    0x740c10014201041c04005e500107149100010401c0c400300c00241403419004409014101509600901213140081d4034400c0380c0e060f590105d082c102001513510341901d20303000200250140040c110040640800610044c004206111001c00030000082401001c907180204110b000350710003000064900e4001c0c0c1d00414a0703480b030038010241d80d2100300849441c807d4540081c8400e0055234841c0f44190810003038020748030180c81148034502c400d11904292641840381c80450b00f07000070700f0722000c00c0342000e1241d65009410003142021145012804030703034144005800082c8401042081190202070303003001200494020301ca20b50401c51101e4640006104400605031700080b04020450288203052050344001c141001039a51800401d0113002c040707600e180000d00c1c008560840030010700c62004611004001541041d065a80170b8800509140f0115034152451900003804665800361461305841040503000c1405684411a810181a0000c0b000d0150610041c503d50000140c00400c2 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 791696762 1250 791695512 791695519
    0xa080d060b071a092b03141603020c070f09090201080c030403050306010c020d0501021c0e1209100c052a0a0806040f170409020c07060f0c06020f0f07060c021c020c 72
    0x119104d00416a240c040740c10310401002000204600314102c1d50156112100d81c151014880000a01070f02e0b04c05030011142904410380d2100c400001500c6503014003010403402d0b00300c5490f1a110756071050310960701d60020072240e8030340781c0030000c559200b981b10360001618015103045003825940503040e0300000740f10b68100712207516924155038030000c402043e030303800c04001c40d540c80030312080e440c4145050300002041c0e8100081289250000920001d4501d68041c1b243e042c92010401c1000a070900c40308601007000009000c00070800520280d10450031102c0c000590f0a08a241c01030202d16a0000702e11034060f41d1400c21030044080f488960003544000c4500141d101032606444040384450514220720f03001c074002c51b15408580c01492061211421641d07800c0d0f48240460740c03030700d0086603400000d41000190001852980107404401219503516041c240d0a00d400e414a40001005449068917002601a26a01031151061031102d01c0c001d000c03c809607070b4010f9604c00750035015500 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 791698012 1250 791696762 791696813
    0x17012d0e070b162a06030209060408010e1b0d080a030f0f05100f240c050304080d051209070501052a060112140c0d1709030a080d060b07 60
    0x80c1440a0000310058a607511029854507165025003000c42d10700181100e030084542c0a8a4404e4a03004c200d6803400d21485000c0c00f220b08080044020390803001c401c5400050620011550000c00e003d070094a40700007004080e050000000c2000b000c0000c41c240740519080b6074150086181c000c00c65910220ba4140070552402482c03000009003d44000d40e56100d18010502030301c040c1006c00f500c00c40300350503000300344d40c1d4480b0b4000c190070044031200104c007140280c60302c5503a07001d4007183c1082805401624105681e90b03101b10300304800c0800840000c1c0e8002004452820380104142c0c200c00500018241d95080000282140c4295681c0c82d45054075a540c0d0380d100e0711118020031100b000c507000e46400396503460310100c00740719100084031a03201e00c1c074110000f010000394041c00c915000b0002d900c1d1500c41c0d1903007540c0e806004010600400c0800c01f00c07a190300c1c02c0040141d8188200c03000da64510b00e00300c045c0100e42d11074020701e01c150350821002000c40d0346600c3d52031529200ea21a6038 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 791699262 1250 791698012 791698031
    0x1c0b0a0b0307051225030209031b01090801020a030506010306080a020d060515030a0c030209090d0807140705011d010e0102090112020c03090a08030a1205070507170c0717012d 77
    0x1c0f0b00707000382802c1c40011a4070900300b101e800c06164485030b10003025501400a119a0070003179003603000d00a1070a4041d4404121303036401c00c040e4030201c0344088060408108807500d6090403802c2e40d0000f111b44c00840e844205016041d60f051042d0b4006002032000782000302c0c19a03002441c59403200d42d002e441c05440708045010360400148481136540010211114040302d0b2904030080032044c4000d03071186c035504001800c0002c02240039200490680d135080b100e50f8460301c00b5600c400d01c203140205001821302841c000650b0034412807504020202110a110320744900c450700399a10868203070102d90040c0000c42c801d907040031440b0081070015101584410b0240c1186240d8003a50010590010f00007000040b81900031006000303003451035940518411300548401c0640d001a640b000000350100f0150010604041e1070020b0000d51002da1841e154400d106580b50400c61380007042c1480d0341c40405100020244948c002080e1038030007510450b4442da04d00b000d40d20b40c4e04c1e03860050310b031600c1c0f020 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 791700512 1250 791699262 791699267
    0x312100510030506041508062a04080c030c031b040b0f0a0e0403110102090105091002010e011b110d0e150c03070609050f010e1209010912081c0b0a0b0307 68
    0x114050200034141985140ca500801000b601c000d584460042c2d1501b00d00d00714841e41203100a003a1012034004000d2500c404071103c51f500b1091541c0410715806854110f40f0900c0d00004100070180c40e0000c000300341c00c410806040081e04a00307580729074801144102d14443d21b201d59a000c1c98115400a5064031000124159118112070700e0780c40b90b542080424070301c1c640e10155002c1c80c001c0d070b01c03500040b0b00001911708038454881c00d50b02141d400d01441825240c031b00074003681c401c290710020a0550002800509503101100d05210024000e8104d440d1309921040c0191034002c040c004001004c2e80e100081c0101d203043c22303c2801180107036440d05400c004a02120703140d504900440350386003640d08141005000023a4100d0382e900031440c007445001014011402101401c84c050403d010500ea5041c14a0f440800080d040c00710141c0d0000b0317425110800c29500900071f594556031403032841401340404d814002c4020303c1714030341000e007070050b1030311417513a010740d01c0442a96a032900c2d003a205 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 791701762 1250 791700512 791700541
    0xd1a031615110607020d11120315060d090b1b090f06280306030311010905070e0a1e02032d040201051b0a0c1505040b07020f04060503061303020601050d02030312 71
    0x82c0c40c440c04081c03001c41c40d400140c1d0b50090046030344903203410a4101c0c0307458940000b211110542c0c1f00c1030000c00c2010a407081011014000104030380d142852001030001a11542401500c1c0c9241100821480c1040c1c1c3c51030181d094650301c1c0c940c0c9482c2002c0d00081d450284042c03554014900402c0c400f092210820040c10b0f003881c01e038204440741d400c1d40d4008002d015140400c40c00100c01541c202c2c41203034140255005a80c0c44009410400c0c00d00341d1040000d500188031041c195100d1403103038108403642034803080311600304d500560f50b450421003103880f060f030620005508a00780e903141c0c5c0c0014240303c130003034001c0c1e82468456554100d81c4410080c2c05220821000c09006403d03052080260705c0511008035030614490583c1c1091b403017000d5403035020700d214103042c00b202085040014a0b10301c0c0510400030006000007482c0c2c1c0c80740042460000b0444200d5041010b8040c50401c4c1a0100490783c0140700c03c071048281c0310303000e501082d00c0e4051000500d458901000118440d0220b4118 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 791703012 1250 791701762 791701787
    0x204120b150a080f0d050301060f0c050c0d0b0f010515030708090a1a040c080705010507060b15130e0f060d0303020d09080a03090b0f1501080702070306020d1a031615 73
    0x2c01822103480d01500d0b0303100e960003140707000244103030f81958006600810569048450365140c140764a440c581c402e4401c1c02d80c20740111a203001e840190642c580d6144185001c40b4042d0071040d043d4a0015580b40ea10141030300700768810103004e14036503500350200d0112544060036140440d038680320b81049a2810780f017583d000f000c89000d03040e440c807000340da4040240708500816400700e00641d501503244d01c8580c11300074207001510812242020401c2900308080f150400b800c401c2101200c42103071052038110305040c816038a54101c007080400d521042503a00f1900c40c0ca100a000c0c10700c1800190300c0066910001d05140d00410940402d6126034003041000e50805025595061084801001054180021104290100040f49101c03110051170761203560b0000034405020301d000015101801c00820810031485141070200000320300340040e01a6040844012915030900d51465440b115000300c8640668403462140c4980c003040400a0b0031038007850a5445a90a090741c2100d4400c075001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 791704262 1250 791703012 791703019
    0x506070f0912060e01050a0b030c060901410f03240405010303050d1a0f04110d0e01020904061508190917180603010e01090b04020c010c020a150204120b15 68
    0x36100c1003806142d801524000800713a008100c542e494000740c2c8200e500c05c0d034a994050380a90308405450405500074000d44405050205041d49580c10141d000c8c1280d0203e014510428804010700385030940b80038424101d00c51509050020384801c88880f404028180c2d48408030050100040c0100740344115410380300603200f03000035a10fa050140040d444495022641e920300f030001d05905010607000380103a540285081100c101500410001d440c105006540d007440400680380264441e1103028080b800300070015850362045805c0200f1154240d010850700060401a569800d5019900d180c0c03202440d00c40446081d0b6040140d001802c000074000d29040d4520308284100600e4009000707142c80e06210100481d480b5414884540000e114510421289000520000405402050f841d410184c401402d15091040d41400e40d800543d20b040940c00500c0a2800d0000002c0c4000084443e46415403a02e07252035001200151280c0f00a0407900c00701010038071150f00d43c11041e205a2005 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 791705512 1250 791704262 791704289
    0x901091401230405270105011a0c0304030f0c080a0309060311400b04090b0109080d030e01140a090c050102010b0a0605070203030f1c050a1e05040c050402030c0c190506070f09 77
    0x5e00d6428002c0400307014030328008811061201c81d41151070200c1c4c21111940e4095030805140d80e4440281340310f01c0c1030458238014500004240e060007004407a0105d8002c0e56407a060500c3d0410140490341d80c00455183c21100700324120403180643c00100d12810070480300c4107207000c4030398000509041d000c0c100d0051113450714006070f034a101c403015005882224904005040e0000c0c01034400034882d1155815a801070300b115850280a544a810808116000403c403490410300e8400300e000304540c61001c266884410070184519682c440010b040280000c020100c11900010503885152103101e00700400054550119241031064540e100c4111104c0390f2680100050058000c540d19400729400d03280000190034800daa0203844013083c1c0b81200d02d00d450030080d0102001d084018001d50380c0134000c240010f8562258070055200e0010f602c0001e031640d6506265509050701d250b00c1d02552055420444041a07003c60f00e06e420138800c1c14075010103d1030030810f550400c190341c0b0004042e50030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 791706762 1250 791705512 791705581
    0x1c0501060b0a0c1506030506011a07060903120b12060a0f02130603060302030f0d050d0b2e231206190306020a08070c1a090c0901091401230405 63
    0x100c0304400c0700500c44c0c041e90100d100204444000c540043c03001070555071040c401003045038110150701f00801130206c8030a14282107505c1d0f00c0c00340c900e031000072000107141002280100070301c1c2c403a104030008122a00710460a040e500d40c1e41d43c03080a003c908015030340700c4122100d9151541260344401c8600c01c2003085030307070f1072001500401031032000340c0c000d000c0c003800c2055844010030841004000c80c1c56040c00d25840d25000c40003400d078011003903009210b020ac0e8041d501c0808912008032150541c5820b0340980e4035500034205000c01c003404000003032020b0500c0c00c100700801964500b40b100e1000190b40c0e035030b01c0002205c00500e0000d05404d80107030000481401006d800401c49040a9116a021a22050b070110348941060700d01400034141c9c88a000104c3d44c0071002141c129014004176050700c80c05030002440303e80f003a400800c400e65525500c886a00c1501c103154010300050014080481090401043d050000046944529902c07400180c1d20700a066030a82007610410401c000c2182 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 791708012 1250 791706762 791706767
    0x1805120f0d050907170f030f0702011b061d070303050d050a0612060504050120190e12060901050f0f150a030b0115080619050f06090415091a1c0501060b0a 68
    0x450046048a80d0508496481550001b522482046c2a1401140340c4090300114a0321390300301c0e40f022410400404114801c2d681164240c203161401440c000541c2440208a8003400421101f110000c0d0844501000800c0e04081034030b00043c03012401182c241c0c0c1e190000e000900ca207800000340b15a1441c100b0040c800341e0b42c04a4407552080c0001c1002031900c0e080e02010340d00e244080c1e40307030900800c84500c19001191500d100c1c40940c1c204030703078040082000162941c00a2a0700f10903a401a030402018843c2405030726006401c0e0340380f1403d84d0030140040d20400707400130005080402c211510341000e481d1950201c0045400400c11074203941c40300e45a20b80c0303034580c00d80180083c10b082c01041e90303442e05041c1461150031803103030007203030070f1802c1c052001698180040c580e000380140b11604149c1c4950149030315662400c1c90382c50b985410403201004441101c10203088003528101c910303c5940300d80e80400c2c244401030038048038010300c46c40d215000d40055044000c8030318000c146050581e8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 791709262 1250 791708012 791708023
    0x9080703020f060402090402011116080c040f06061b110d03050a0314330402180108011712030a1d070f060c0c06050a0c050304030c091805120f0d0509 66
    0x520907800d031207520000c40c602e80e543c1d00b03041e100a503008105c0400f041c01580102803000903806418107503003800310510910318400d161503111001c40d412802181c60356240c02d11800c0d1180060110030403800e030426000508031030400030b200380c10441102c070310fa00780441c000f21914000380040111a40c0d030460320307008009410004a201c0401d040100401c03030010f1105c4180c1c07240440c9101003d52031205a51810b088400000400820550145504103071300c2703900080082c20502c0041e0300358400d0440004021050507481145005c10312600e00102c090042a406585146950314a0300c0343c8520411000404035280c440030300e4100c10280760290703000402c1c0b050403502c95404004010360303101c00544a121406d01700401c000103900d41070100d1801100580102000c0e4640710b244a100c964603240707075502c00d41040d40d140e5155a81001060818007452410140c0441e80500d070f29010750780e02d03075240e150992138421040042001110b040381c4000f601c00440c20720344184000d0510400068650 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 791710512 1250 791709262 791709277
    0x102070b0301060302040f08340e18070b1c0b0105040e160807030221150a03140601060c0305122a030a0e030a1d04060b03070e030705031914100908 65
    0x1f50310391400082c240320108400075a100410041000490707600c403401d00264100e01d05001c115000d8102290440802c500705201e46141c211122b20302e840d41181c82e00e000b01650120710600030400c1b14102020992643e8017803170034201000f040364080400142c07600d0040350000d0f001141c00c4010455100140c2c180390f0a0703400d10343c030b510747e0b981c0301c1110031801c1c0d119540d86044080c101403161242d00c03021800481d8080c0030804140ba0584111000070040842d0b0b90060b01c1e80c04043d915905880c00c20300c1711f1801008541085e40030220a540d024003540980001c3c11104116000003420300340207498101446500c24000140c5c0b500c0040100c0351940041e504038200ca40303401d0840b900e41c0f500100300d038030100158503207081401082100c00202c5d01c0c00340d0600d03049500c454000420f90039a10245000e1212a02c0b09000c01c1315140606181c0440e07980618841c1d804050010011000001501c410580001d000c00c080182c000d060b03803503c064000d00703240d01d07898030010344140580f00000d13100c00c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 791711762 1250 791710512 791710529
    0x30504051017070f0e0f03010905061006020706050313080a030905010234320307200315060402161b0e0109200c0c04050411130203010807090b0102070b030106030204 73
    0xa62640e0000311005510f13061320f007020a00c880020400b0f4600301e02c124500300e200400215010390580d03540d60400304195100104401031200a016481d010301c100390203440a840d055003145405081c100102c0c105610107404500b0024140e80110311a401a110641d0408004c0d595880040c1c00c0043c0c01c2003901210440c421410480303045072005460244196800140850082c0140004100e200b56402607654048030041d0307020859900a001500605010303512800780c3c40b942e240402d292240f9500418400c0e0058014900035103c2c80d8255600420305450040c3c54140e5651161005208000042c01501051803040c103c0c408405425042e10400c80d00540241d9035204070001b0f503541270f0b05080702c9443e1211103000c07074108070010780309441d1076804403100d80b420100814101c3d401a5416612031029015402c0b0b1814141d055007000069000d045182d985004906515007409020320803004e03860303201e4a00b047c0c1c0f0801c854805008040342c0c1d242d4030750b076410001c0d00035802446603001c03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 791713012 1250 791711762 791711807
    0xd0902120d02030a09060c050a020909190510060b070f0b060d17040503070501111c0e1c0302063102150c2503020607060b12011a0f04050c040e040305040510 69
    0x5803241f085c0d001078540742e030110003403500501990801181013001002c943d010b109262001100640003091004214010000f60410a0600d203820040d80da991304418020101040300314000381070105042d007402e803c80c00c000700ea9110580003e9401070703a130304d020300052100414899800d00840082044440480440e101503965000540c0c4a80c142002a40160050b0f9507000090058511018030b041c05407030400190140790000079403505407014001c00840003035118004041d01007000d243c0141c2120f0720304181c04401407140c5200c2c1400042c0791035240144140720119200d120404000d0b9000d405a19280c411800920350350704140300f01020802c824403843c03499444081a1030041c2c0390040d06441c50403125880304400761101580550b0071100d4070f01c541449480c2840b804158406880b43c680c11040103c04000f10003040b0100709108500e04414060841003e80444084503541d8441a40c1355681d800c0580d001d002d190311094100c03003480c0820081c150712032115114509018074901 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 791714262 1250 791713012 791713019
    0x60906030604121b0c060c05010c031107110f040222121205090117070e01170f0f0a0e06040c17010e03040b0c0a08070804080607030504080d0902120d02030a09 70
    0x50340c0340000d072070140098200b080600d0f41148103000c194805209454880d9000300385a03108488541c036580a00001100c01e0201000c0000070300030f07200500c03010b1800f440340c03841901200c1168490b03818010040da03103480c20504651582c060244640700300400840d12501038140c0f14003802c607541d000404038000c0078000301d001440032540342d07846500b100c401001c04404174030907100360340003800640c10303c600d155600e4801500400058400e90a03682e03035070700b07469640780003420307610100c100080c2c01642c4c9001c1219000d160301515600c20b106000240440e20f404140c40020034000010101500801c02040301744541c46203414202d85624580010409103d20300600701d0b80360040703c1c4413a03081000200b0441c0b1140010305800d20190042c3c942c20741040d5110b6100b9802400c0840302e81c1e00124040002c0741c2c0038481264000280d040a00c4580361aa8841400d4454490b00b034425035a115507007002e40d01c62080b540c100204050465080105162000e540c80c0c01041107400010000e11020 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 791715512 1250 791714262 791714269
    0x4151503050c36072303060d02030c10021c090e070311040308041d0a05040b06061e12060a05310902060a0c0507080a0503040902071403070c03050c06040e1803090315060906 76
    0x5100904c80e0040601b1a140d400800080001c0507070143d034107109040409074160340e941d40d80713031298030160000c08a00c428440030f0f0203081d24100002041c800510001c0142d0003580089580c400050701e0001902641c0039507106c9513004a4002074600e540c017140116025900300019291404086c169040582e245014030041d280211001000c1040c540046050740c1441d001600610041c100100d51140002c030240e807094004154003d5207000a0081c000ba40c1070002030000505070030759581c15001d0010700761080c3c0c0340c0e055000d40007241705000c1000c0d040030700d40d101a400d164014901590f0381c0f0720240051807104114000e40d0b07640a45100000c113500000303041400c59074420048c40c14a0b02e044800d00007500720395019100a030b2080041c00c82a80103000170702e1810300c2a07000500c09825401c01c0392400c400e40e0140d5000d00020002440500d6151140c0c1d68494125200003024a41d521141811405080389090301849514007080d11030b02010310540c400c81d01500c10101960741d082c1003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 791716762 1250 791715512 791715557
    0x70f0509060d080a03050711010e1605010c030206070c0302010f05070206040c09020310050d0f020a060903050d081902090a0503010507120b0a0501050a051303020904151503050c3607 80
    0x1043d00c40100500d600240c003030340100794003d0300e40c20b2100d404801103507041d007590340c07030705446203541c02c4450072020203172584079400041c01c1d00386050301e01c03080d0b43d6030040c0d52458050f10740c105001241c462042014800d4100d05402941d2020a2220b800c041c500a9520b0500795002c542c460100c01c0c0214200c82140f09503031103240b001303403e4040ba030301c0d040c1844040000047c050714010100c3c5691009038840500f4100200311565501200910f54201113052044841e10700c010400c800c014088070195281100a241720b60107001652181ca060010307130244810740c0455003550030103082094842c1c009040a01d22940c96105000c2400e0703042c100030285429000d002e011640c107204050b81540300d10701400c250b11010304040101d5031a81c000a00010b022202190400ca80144081ca4901039014100d0740641080f0007206250842c0e0702d0340d880b15000c0e140140106060507225800d2255890750b0a41c0706d0504103c0d50158080c0d5490000046044a250340400c86000a00c01c10240c02d200c0c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 791718012 1250 791716762 791716789
    0x2041406040c03090b06100c08040b12070903020a051002150a0509010f1e090510021206010f1b0b0c0405060304050c180106050d0506150307030614030c032805070f050906 75
    0x4105411b079940200308495803035003010500030000c92030014000942140002e00c0607200544e1401c5d2034400041039101c140400806101c10012681010401621020404015142e0854070300e12921000d1004a107420450440c8000700c40c02d0000f400b902030510380c0000d008012400c001d0000c108001c1d0b10509a0382a00c48111207070000340040700311590991b20260301907210310261103440c20250030045c00d0343c202e1a0079003503020700c20341070007425a00506403a000325442e04004480f01c003440c1f9111b1245c82d8129001e082c0d11040d4000520300003440040343d0152500400d03442e100d08150800b00d5841600c40481d03070045580b4441c0646d9000f000c1a1a412540c0705c1d0b680d00e2400074a00c07800f901820340913100d40d412448030005551a125124003851103660250b400180d11854070400548000800500d0350185d00100e400607100c0e1408100c8640c40305900e91209041403840500c00660b00310448040c0141c0a0a5000305a0b800349600301012034038211800c0d031726a120a420440101c40800 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 791719262 1250 791718012 791718023
    0x1090b0c0715020a170a1d0303340b060a0b030108073003050d0c030501051503090f070e1f0f030f061d030903100209030c01080c0702041406040c0309 66
    0x81d041080701070701800314070701400b5441541c14120070766840e0340b140e074952a00321011503400301e00035040c90761203082c55000010082120940c060400c000c0f0341c070b03803007001041545503820782c1e00a081c40c1035800c8010001c008116400003040598104031103107040595246100ba40c10300c2002034000c40690940c0c7c10707120410050212640b030089640b00380051640b20130351162b001c503010b050780a4508040c20780d0341d0107611159a12025030f80740d14100c459080f02801818a4840140810740b42d01002c0e020704001251141e64139140d5103641840d20801215800c0107105981e4081410150b0b91001801294501d200d0300a21000c44c0702040500c240d400b544000b0900340808102054141084051240c000c80000850326001410020380c4030b2542a00c0d0700380e074000100c1020a04041101088881c0c1d000011401d11150500107610b46c08058011410030110002161380d4070314040482d00300960041c4108000840d103000703058140d6041b142c2a20403481d241800034064028011403400c02c1e4401c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 791720512 1250 791719262 791719273
    0xb070e0915031e070308030a020702041d070b07020301060b030702030712020613020126240927030d0e010603230d051303060908180a2111040203041101090b0c 70
    0x4040c040f506003505800d2000c0c07440f810318000041010440114002e0880d1030025940d022640144016644d425a0b00400ea00303100007010b420b058007042c4402503c9800c00000c3d0380c3d0b591400081d014140d190003c6c5801c074800418030541a400100031700301a07105045058480e00403030016611000116068403100c120007440070015031141c00035040c1008100240e0105400e150000b02540700c0448030483c02410004280004100300e00388c121000504842204152500040d0703040c01d41800031076204814079001e410300d000c140c140b040c0c55180e20001c8003000b0000c07180c00c0c0d55010f41401e00c02aa407800c5664029583c2541c260b0290300c0600103c0000d100e404481c9008584541c8120318503114245006000700009044c0c0c01003614032030250b00003a071103001502c00300b05401c0c0308600042c03040b41c0203082004259078000038480090010064480c0c141030354280440164103c1031010f52040c40001004100101403420000c0d0032000c0c3c3e41c8401080d01c03014440d40750f210307038902c0040300d6029 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 791721762 1250 791720512 791720533
    0xf1803071d1305010e15010f05010507020f0a1a030f06010921060e0f030c070902090a1206110c0a060e061e10050a150206061c0303180b070e091503 65
    0x1071451881e005410040a11403007403203034a51508440807004041c510703030844803014003c100c55501b020b02502c0103d090f0810140f0b0040081c1c04d034031400c0c40081c002c10f00c40f820303111140d8078104001c0040c03a11180300a88095500c00c40280c56100302c1e12100070b5801a40440c14a500c6010198291042e03981070304045042c440c0700c0d41c60844d4a80301160803549481c02e603400f001091010580007003502c1c00440c0ca071140b203501e1500b40405070300708c03105480c4103000084840d0388a4032040121020a04004649a558101440030f41200e04103104180000200390604000002c2c0f240140d41c000c1c0002c101c200f11100c8165241c0d0419110a02a1091111030b014a003410040680e00300b240300004004096440300440c80b40822070740036090b0124480080c480c130a07010300685501100407146204008200d400e03440c03081002420240405913218004080400d581210351075494009240481c2c52800d108000d1483c000782c4c0c10280584105008185009031205504070307020300040107821041c14 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 791723012 1250 791721762 791721809
    0x90303120507140d06090c021f140609101526040305040b0a021c020102030906280b01020c1801080d110703381605181011030f180307 59
    0x1241400820591726000000c0000d500d1003207070010304040d000341020901190210080d01d1500c50141422030908011150a202310581203031b0010b002c464501094489440341e1124034442c0c2c000704100b0400d4107a480b20316420480c1d0441074161500100303c0745d0366030496000c800ba015907005021a80500c010f00202405401414014586104846800c24001c5000c200415101c0075600175035400001d01811070024031a80c0c2c0d1100301c410340d0501d8076031f291060850381980280320f40007455a032943e90545038400c1c4046410a480100705884100e01441d20411400080c0314400c8103215590b0f1501c4928000c603922408403500304c02a00ba118615207585000c0c01c0d01030b94601c0b07080d03245110072504421800f010320041b00d000c9650311007071400c400c403540d20103100042c44082c4401440070560f400c40e580041c15055106803140405442006419504044660000c080301d00012401e80c1c4500880e101070150350300c0344401000015414024591500c480303000b4183d035191884000c485054 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 791724262 1250 791723012 791723017
    0x51c062601200c1501090506090105030d020d0e0f032b0f140304030201021c0c030605060c0606040b0f130203091036120e030610150c2109030312050714 67
    0x400e030f200340c48440140c11803800348a4000d801203d0861b5403035040c0202400d001d1030050144c541903000780341000d5882006582c603421090410100540046800e0068075100100343d2b60603c0a022204030a0040c03030540840c4004510803800d10b01c01c0c0d9124140b0340c1c450404204524119220100e2100812460030003691004005600350740d001c0103000d820202131981100701c2c0d049188000f90410f009413008040c0d47d95540007a20900d020700c0804c04110002c5592034012104a9001841d070032164045001000c07101206584803086a50340281904503800440c8104805d81c25039491041035a0f424007221401030a590030b280010f2900240511141c11801445041107c1c1d0b20060545a690700f0348013950508010003d140c115002c002400e00b00034060b0001c407c00c08500e016030808a002e10f01c694040c40d10001c10901c1c4c0307411418400c3d64003014200200c8407180d000d110006441c007401c1c12640d84011400185004188042c821462046d40d00680950742c41c8050b0810344a015586034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 791725512 1250 791724262 791724277
    0x11410030605180f0319030c0e0603190e0309180112031d0418030f1416110a09060617010312030f450b0403051c06260120 54
    0x1007400003100c88540300d0400000e6200c160707040007540c0d640151b0795000c10261542c00c04000745800d000c0464113060f0094202c18400300c0c107031506505d99880e4104c400d244054005020481480c29100041c1100040002c0c681081e040d01c103c0d0480401d11040118590700348200c0c1c0d01590071081c84000a0300c0303003696040d10216440401c0341000751400080845900100c1608011484e900d444201a005421000040f8540c24140c12401c20901d64040ba07105a062100c00f1581481144040000d0080226034114018208090590729100c406009001e00d01411001c100086070400580024090050590754481c4110720000201c0350141d016181c2c2c8450b201e02c00c0d80701c103040310080041d000c81c8c40112071340f44070942d00e5500c2c504c002ca081039090b16490480c51000c0f40385001281d002203250b41c11952619107a96161080d600d100114a100701401e10014200000003502c207440c0c518a8544501020a20041d418009501822540c06c41d20000c2004035002682213040500300250860 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 791726618 1106 791725512 791725531
    0x1d07020604030c0305030903130b0702090c07111908010c0e0f0114090904030c0b18100606020a030f11011d010606020c012c04050906060102011410030605 68
    0x10883e40f21001d81071200000200e1000c400403c2141c101781d200084101c0c0d8191665070107500c590000d03409074403e20340100419035800d4000b003140e00c002d070301040803a00040303100c00f4001da1140403007031640928015640000c0c40d01003030064003d01d450035600c00604111002c1004000540c199009042002d800c1a4550142540341141d00212003100c45401d1541d80e442e0865151041840041800c059133043c089607014840a0740d4084d01440107a5040c04c041440640c1290424410140168060820200030030302654126900511500d0000319841c40d6400090a68525542d118030001d0301481c0010440c0c000e10582d0041c20483c400b80150b1440f1000080c4104400031714000c50241d114038500c04500850203002040e00041e1040c012450602c20168407090119201405542400400459554110381c0240b2840d4042000012181107803640b4008140007466a00c4 = true := by decide +kernel

theorem cover : BRFrame.Cov 791546762 791726618 := by
  have h0 := BRFrame.cov_init 791546762
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 791546762 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 791546762 ≤ n) (h2 : n < 791726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
