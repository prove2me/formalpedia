-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3754
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:35:07.800361+00:00
-- url     : https://prove2.me/submissions/12e2dbda-4edb-48ad-b4a7-58c3fa0a3436

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 675000000 ≤ n < 675179856 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 675001250 1250 675000000 675000037
    0xc07030803090f031c050a091a13020901140a0806010305250905040c1d07210213080c10080105060904020901020a0c0b0d06061403040807030908030d0504060e03 71
    0x114040034081c0d074100c5429001d840e42c10b070000b20383c0e500d10b034041c44001801000345580c00788a01300f10301c40c1aa2220801d6001c0c0220300082e650014050404004080700d42840320200e016412540139001354180c0c0648000040d5854072074036281a18480030040c400d20041c003000c01c200c4004150f0b981281e6000c002010381460440c07444048041c6491180c1c0d0b5000c0004001800e00f07558041d503070040d4024035205401c682007003070301405050701c0340709031800342140014441e11550040b1040c0345149428039030740d91130305140b011341c0c064410044030b00c440a980308800300c1d00c02e1703005c98000c404590494111600401440051340c003030809118059003d10701384006055030504d50003c003400001481903804810703caa45200124a05411503a0042c0c004201c21900340343c544181006040d05e4100000344029400c00070f0b00c4d500c402000205481c1000c07581404160103580500c000e0503220f01075907100c2d9603807221300000b4282101c041e50003d05008005442c2c0101108a034501c0c4036510501d8138 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 675002500 1250 675001250 675001253
    0x80d180f020d0212030414120d09050f0a051f17010f03030e0604171b03030405060412020d1205181509100516240510030b07030b090403020616050c0703 67
    0x40d4105485810703030300715980300c0c003503110f84d4401d100900242c5403540c020940340c914141071000c500102c0c84400025400101c914024039008810740c01124411614003116142d01000324614404d81e07807000c1d4000a03490121654014404105201d2202e1503950119210b601c661040355160b0a105400d15503000301001d0001c1385c0310301c01c0b0030000e50f800391420f0300d0250b072284040c3c0b0145d0815030b805080d42100c15607210b000c2e041000d0400a4504030300640c241810007000030342c6485140b207804052030014201c070045440320b44d900e002c080d4124102195040384000302500c0c0761302454004000500051404001d403810201c00c507440b41c082c4021a0401803400288a9148045240641840001d12000b2490320380c030209614032510031500c52080e40d03001f211004294200a4040207050300344000c00401c81ea904c11a02c08481d0450017507416a154004c0c250000c0100c1c220480e00202854108420b054000410300e010340c0c0e0140181811504564085810f80075244080e04150880d410400 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 675003750 1250 675002500 675002509
    0x627030c0813061701050411220b07050d030506030319050a0207050423010e221403070c08060f04081c11070308041505070509060703050d0504080d180f02 68
    0x95406100d018040d1a1207070002d42c04201c0d003800c0c0d00c00030004404142050b4418980c1c00c141340100010341d0103200850040007813407154015075002c1d0b1070504501d400036003280e004021010041007402101590341500c0c2c10510f886510601d000e00c0440c2c1820082011130500100b16070003214220500d0b01651035209080700c0750b600c01e6454204610840c040032171150b4542c8107030000b20488003151040420170100311042000140d2180701d00803604c204009410a10030418003007051400300710b540b405800e140c146000c0303041d030b0740c0000c59100100310341c02003002400482c006e8a03200700888030281e9825000d41011402260000c0048005000a60303400c1c4001d05500c800e5500e84031701162034486401c4800b2260000103061703000440140c2031105002039004010003080c400c081c1884540b422a03405032407031060910f00ca00800000603040149071140c0282c5190001d864028001401c0504220046401019801c14141c1c540120350203050ad0b42c2464210559100f102e400540c4859009c00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 675005000 1250 675003750 675003767
    0x190f0c0609030e090901330b090a17210702010c0b10050d11100206010b191101050907080d02070e0a0c03060b0a091d010806150307090f09062703 64
    0x11400c1c480d00102c01d05407070741c5109000d4824890040002076440d1300004860035200e0300080f44411f1040702c0050301c0c10b0039610710380c6429140e101c0c4015a4403a0001d001c00e810004551210a42e94040003d503105081c002c070311a100340c10a240c56120318041c070380840c0c12500c039000c002070100d204251004000344501481d01d40c03040540d00302802c900c0d61140820003480c91440121210706030400d010200c1e2404a6456204220510040180f98100507103c500343c0b0494030b141189541c3c100c01545c003680300e88109040e00c0c4406000348158145040810ba03101200c0c0a094002c0c00b441078a0304000b031000420a08030f5801203216010b83d115901d50380001c006105802c410161204004110140c61000500081140e640d0700c44006181c40c040350321035018140320170b00a0070a03038010040d4200002c0d086d9000141526003052108100c0002480c012080c6e0003d61100d00300861040a08050342c0b2240d10503000e101d05000c043c0319201407015481914650744484800c030303001c0c600842e1159851 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 675006250 1250 675005000 675005003
    0x21120c0d0c0213090501150b091008090109020424091b03020c070816030501050c040b070b06030a050709021216171513020c0c030a080306121c05190f0c0609 69
    0x1011690920030000001352521510280c5e01c03a911200c0a0040030103202c1d0800051110b00c015508120078031001407100c07280001c518080002d164042010501c5c20b502802d0b0a5a00400800041c840f402002c043c00048000301814003442c02c40c0002d0401ca14043c11590200100560032031000486040e4025000401c000065200740c810118009404004000c0000340102446021500d10b01d8104e007925001068110081410700040024603503600950b08500d521072065007040d82c0720350219241c04000d01c4081c16510800f0720015445035264010844035031a03a5240d000d6a680d410300c80e45440d54858a01e001440300042c038025444800c80aa030440c5c0c031041942c8a4001c1000090340c0040b080e480308089950000740059480010440403c003200305601516804603540c0fa840d80600006101c94000d641e5010b0380c402e00c0c0020b000c1240d80c00d10040911107010601e0f51b0003000341d004903541141c1140e04003054500180070b01c19900000140c0c0d59003d112901c140e481c80041d2004100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 675007500 1250 675006250 675006259
    0x21190312050405280c08070f0b09010c060b032b0f08160f050c0a03020d030b0f090406110c060c18060310060f0302070206190f2102030402060921120c0d0c02 69
    0x126200014807402c145d50051032907000422005083c00c440c4c3ea02e0080b59800034019201c01c01c001c021a0b600014445c60003500020002007644805010a003840104904a041c5510b43c0203900c1901e004042d00400029540c0c2d41c4d14149030080609a030300c040140c5883c0281c0d2440c140385440c1c14440c0302000340d101218a480c42c1030029020401e8078003045940c0842c096000b1030a203040c815418860a4131406c400c4443c01da802c0107603404250110000f41010301034684561503180b0074494001180d601355064021900300d483d20a04400c003d4000a10741140502c00119049003494840280ca01803400c41c0301d8100c3c06841c0c410300380e507081040a10982410307024070504000d17a0310381000d00306800e90207242e07500c10100810018030741184091a942400031324203107a00c820016621100700307644003040060f62510389000054150107000f003080c1d440840c1014040d0003065441c6800581c0004204541141060300080400c40c055860101c440361b2081840d1010544200720395100e8070300150 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 675008750 1250 675007500 675007573
    0x131503060605030d020304140316060215070905220e0d0806030c2407020109050a031505091212090109080304050a1203020906300c130506070302030921190312050405 73
    0x71168525038810f50300c02f4000d41c00081100310801500301c60300c1da0246d55450450805800e18000424003c0124107800c0a0282c0a007021080412984180048850001220855a11780d14001d044803802c4941ca0b000e401131001c03620460510041d50f040904040910103100c0f014180349a000c0d4014040580c100012a1000101a101c0000e501d025500500ea0307079500c800564855407d07208068035423001d80c0e011260142c144991f0200b964094451190074003115200c0c40786090140c24400d601404014001003880b0802100244201440b440341c141800356510980e0150304038001d5400854004104125400b2000c00300c46030200c9541c4900403034410b07103640455511500381c00311080c80d040c3d038000a00318020b031500c05040c1c004040481c0c0e424170340303102654003e40768064005000d028072030981107006e0014022614070440454281100e210000c285c3d036408180d0140c00f41036011420092071300200c400340d401a0b034030440d040f400a0100913448444640401072842200314490301c00c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 675010000 1250 675008750 675008773
    0xc110622060b10200f070b132c07020d0c0b0403120f021b070b040e0919050d0305131703090c13060e060109081902131503060605030d0203041403 64
    0x2241c1d0814420f0320fa03a24648030075500807103500400c20181c9000c0b12540403901505402100003842802e03103205c40e1600b03444400300d09004034040002d402540600c0300208282d528000d000001c48042c3d85000c0c0d5284443d140c022060740caa01c0700b620a04006841c03185d0480215103e0b82c4040e0300144a03141c402010036090040100300c2741c0002c801c4030036540019051480c4041c0802c070032902c00c01d41000d0403c092400c000716100744914480e0080c1c42d011040000d12614003030142c00d1041c00b11030f2800082c02c1c1985032494072200695000004240b03441c02048070346454003032110582c5d50010131110503402c42c204030750040e003008010301b402e841010044086500e980c0c600002c1003030282404140f0301d081005003161418003d003000c1c1004000d15081049040028203100f85069641c604050310f255800803c042d154000c0c1c02c2600107090141483c07008083c41c00880440b40107038810080540c491f4201511a4988080240103901c240810710030024190901044298020110344021514 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 675011250 1250 675010000 675010009
    0xd0203040c0503010515010c110d051f0615050a030b0402090402040e04060605030609100b060918100f0b0f0904020412080a030b040605091909150c110622060b 70
    0x480302240c110811403801c1005050900a1607045511540b0112550448400080041c4144117014180000d008032030016612003144000e00300b600007040c0c802e400c068604440600000c1c4104494032803800d000000c1019001c0c80c40d2240328140e60340c0900d0590008400c4000c2c2c20905042d0390300590801c43d091a607a203e00c01840201300b4011505054500350401c60221600c41e032016000f07400ca9810003092041c0841d01900c4c1c5040072000052074404440820200c0c010444996040600180c0c00b4882400c0d4100e01c0c0e128890010070b0051a90315420f600408001d1841401d0b0800c030306010321b0744544105c1d0301034114800041c0005040c40d07517a65010441148072281a5042c0c1c50020710102085d515004a2015000554084c0441c40c80c2402281003624002c02c40380c0302c07512900000c0030000c0311383c0000c0d450343e800c00110b000d0044525040c3c0000d060103019007001c281c1c50094158841004a01d440c071174411400903d0121012000040e60914201400c941a42d13560321240c0c010343d030b03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 675012500 1250 675011250 675011257
    0x10c0804050111120313060e0a111011010c03020301080c011110020a0201090c0603050610080f0103022209050706090f08030306190b0301030b0f06030f1f0207140303061809061b0d02 80
    0x40120300316040480c1800c1803030441e0b0700300e15840790707070f800c01e0b8021404990300c07028512b42d80c0c800781c40c8810440e00501e421075500800142c540003035400c020801d008903a060300510b060f150040d098802c40000c2d1001500d07081c04611381c01190750047c050785229910241d002d0901200640000726500c6800e903035004000d10650040c0003ca50380b002403001504100e480c00000032100d0425030030500b0030b14a40c1d6107141051100910a0b002000309070410b081c80018003070301001040040c0440701c1e540c50041d841e604030340100000291800d81c0091034100809001d011654650040c1d071035a00ea600a01c80c03e400340b011041004580711800150400240c40158021405a00400c20500b844c1e0740c6a409104003400c1e95210b035020003103a103040f9001140700a4140304001403040c043c1c0300200703004060301131002c000d800d41e4010303402608c21440100085100c0c0c60700301c034a0794520b0400051444910020340d070030405a8403100000e8004200c00c1d04e80d40990281e40b441508014000e4034907030981c0e1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 675013750 1250 675012500 675012511
    0x1608090f1c03080711152d010603050c0a170c0412051b0d0209190f0f06050405090d170601050403080c1b030607171312050c0c010c08040501111203 65
    0x5418070128145036006100a42082c158580302c030716155000c406583d150382c60040c1041040440000c10784410100c0014410080f40340000d05060480240d2100516070920520001c00d017800c000440d5403110104a03002142d00d92502040040c510301d000681c02402808103200c0c030001c00010401c204088450b00e2600c0c4620020040c40780b446c8102540207981c4a010703402200074140e1040180d03100000075520414513403d21480ca001c4134010f030302504060710300c40b9050b854603054800c04d80a0b904103078140c0d1000c6e1014409030310740d9450380750313900300aa200f04d00149803200650300008443d400c1907080441403414a0606450b6150080d482c0d1102c800c02d4406d40c840308050920b200c41d20020b00e0a020220090091403412110180400b008000c0c59404411080b0001d001d154194034141c1c0001d81064540000b01002080504a0392040804010503c2070340000c0259605c40c0fa03c2490580d840241d06003060300c0c140040d580703ca1034a0024505020700d80e240784066610314059440782 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 675015000 1250 675013750 675013789
    0x409020f0301030c0e07050d0218040c0203070302010524090a02070c0e011d0403020c0f03120309010203040311010902010f0e03011b081803040506031617040c030c0501051608090f 79
    0xd51442c581070b01e50912075800081001002006c02030b81a8003d400e45007498991000560381740502500e03030812000351071141d6481351406680140496000020b400034501c2038000300102c1e20780c0d10091003041c0e403440310034111202c414004c00c43c0d0308081008a41098641c0b8000d424203c860703403000d904a0007500030200510400d0010444012844040032680180c2c4041c402c03d03051585000351200c01c504030260240002009040303407503c04002076804c20170f40451490712414a8003032180030358020b89007500002c0c078041f060140c1c0c510620410b509154141c441b410000b1200d0415201c502d081c4003415450f5581e22100300121085105e0111142c0f0240d0307444180e4a0101c0707900445885001c00d40e0307050b620a10041c000381d1200320490b0740006103188012151466203100f10f42c0b03510503800f0700141010100070310003000b0441d0203803030640303101d81080300e600343e02c42d801103c4c107004104040b204008058001400b080c0550020022044040c1c1000c4890f11903502181c4022030700761105000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 675016250 1250 675015000 675015007
    0x50a0303091a1e07050a020a030e060d0515040c110a0620130509130201090e06041b120f09020d060e0705030109050f192f0a03030f1d01230409020f 65
    0x300008034503d0707944600b080c1082e9080140d0014008e644e0b411030f0100805001c0d000060101d0703681c5080136610000000c83e0b082c0b105240c2814664403040c940360b00340b0300a40c200540e4080302800b03080f800c0e402040d08001822031a0b0261107840c060250140c06404074041c08030650344000242000705030000c0c18040707203d011fa00e014180240700f10004d100105003e145140b0f10010303a44028007004407501c41081c806a43c03a0400020700625100b4003e0040c0c825981000014942001000c0503c02c2c420604105001c8800360321003c0c0e0b01d28010007540102c8514001001a50b55405511092030310401c0703428582e143e0001c80d0849040c8da20989281d4810340210425180400200040142141151074111465954000c144082e0103602034505180985041c4d8042c50b000dc0b400c02e040000c02c02460542d80b810040d040b41c00302090400080c0c51031000b107214030885426501c0c6c2d41011f079180c2e09107100c143c0340d0000700c3c6039031482038200210801002070303150ac290024205010850301c80360394 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 675017500 1250 675016250 675016291
    0xa05070b0601080108030a110c06030702070f05062503110714040b040e0a02010c1b0b0c0114161211071a0a0b011e2006090c0a03050a0303091a 63
    0xd512001801c10b03040241c4000144807030340021050300c001c58120b040c0111803110b00780006040a01441242e60003003404810441c90341d03400105501203400752123080e800f2039101c005012261240c0139440d4809401c0c0d0061219450580340c2000150307000340780c01d01d511404e8590050800300c07554000b810321580101003c5d0540313000d11611040010864081104615551b45142c840c2c0c105038002c1e06000c454801e0606001c904140c1c1c4000391400c526003180e094680302c681009030803000000c0d02961030b060400001e040d4041c1d20a0154001c003045010140290b10308540c40c1074800400b194290303c0c0c641076080c9180c1a00a002110312803240762910b0b140203030740c0d601c44140050041100d50300300b00142c00582d801040000c44000c0b041c0300000c410b90320a9043d03034820351107809182000e800c441264416400401c400340100c0781901a55142c400d104204000c002c440d002c080c1054008c0e0031408000fa000c2d030701404e5440d204540301d4510118840c178180c0416011285804a04000c191451 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 675018750 1250 675017500 675017513
    0x50702071409060402031b13090c0221130806010f1406040e19020405030a060506240306040905010e07060f0219080304260a051207020604080a230a0507 67
    0x502428816614141c02011035000034420440500035901443e400000325820385001d5110168031511805100d64400e112200750f1a440f0682c0301c0c56011528103402d928081384007182285d0610380880c009080c00c0c85054280b459940008442e00c02d04400d0140058251010300401340248110b840710400030385031114940c030500103604110b11603881040203000080550f4642904a02103281c4c2c1140505001c0030000240b080c3d0300072507418842e00c0e003843c0030000d0030380081c0d101b41c0e0142d460413505d12540c000303500d80b43d5501c80254400071040c400581c95003000d90007100d2a0b80210004a50142c103040d00c1414094550405800100003041c103811a540402521204024104107c0c0d89a0341980b1156201d000180c0010401040b501040c401c64a00140b0101c9180c0700030300481c0c1e03034038524002500315804040f41d203039038451500000b4078190002c41c140c3d10a0307802c00c00c0b03030703260401d50f0390103c1d5441000743c5450101c0c0d42c2d104481c008601a00007800d84000c882c0c603820b179034034018200030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 675020000 1250 675018750 675018763
    0x603050105101103030c07030c0f05030a031d071206140f091b0f10091503021206030d0c020105030702011e02030103060b040902011b240b150304080307111906050702 73
    0x901803048412019000503c00001c480d444851410100d44034501c41c60300320340200b02500060100a00004943d0900002200804100b1415107042014407094081624100034a0303501074060f81200700c040025406000d0400811480b400c000a14504407a4200407027500986644e00c0c00722401c0304010412208012800c0121031482100d000030280b41d0004c4e0300c04051006160041408401c02c0d0b00990040c608640501503407904400c020740b0041c4010020b41000110000f07041380c94000c141942004200000c1140ca41c0d910411014032030f4005440701d5101420010456680308141112a80bc0040c10f03900c480c11084d01527543e5142d814510140c1e805034820a20840c940803055005030780140f0b45c4440d800e019001100b1f00425420300b4819401c45400084040340d030000303605051422131b80068820602114040071032070880e21001c010303000440d0000c00c41401040402c0c1101e02402c1000d0900617108121850b0501c161074929205030001da08440190f100c0e03043c014583c0c0c05002c01d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 675021250 1250 675020000 675020029
    0x72d0903020114070f0f020d05100f0f0e0d08061807020109020909010509071505090a09020409060e01120b061c0c061b020d110f0607050706080c0316120b0a0603050105 74
    0x80c2404d04007540c6849640d40750001004000b0480540e28800710b403503030244a19000d400c54240c40280d0069904c84000d4440218144101490049201c10038000c038800c1c0754061100800034030034107548000c29075041002500d400e9001c1c4400035070091440c05078040500c600c0d56a8004680c8200d24814024001c0c0c010300300c0f02075a4141410458040350005500c0210fa0000610701038a46a02c1d505440c03a00c101040d00307821002e0780001013075880058006004507901000d040100c2a41c0d245c010b031300084280610100d1010b859000004a4502100c8030740045004002080b400410503030140000d0384940b003100c85055213002084030f0b680045555100c103003410f103040d80211041e0700246407a411018028510040003500760440c2c0c54015000c2d0710004090140f03a0788181c02e04059070303290110310554000500c3c03000081c403210203040c207490065401c240600340a88803044280c91640003c55070740800c5a4a42d0310b0061555112880c00040c41c0d0f0b0b0301d000451354181001c0c44004a40c030407a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 675022500 1250 675021250 675021287
    0xd02011e05130308180729131406130e04050d020c13020c0a08040b040e06030c0609090415021908180703031b1703011715072d09030201 60
    0xc01081e088805070384000c2d03d501d40b500c091542d40f10707a485680d6109210502e0224810300b071020591090f8103004c1185444035564803204001c0034180341c4128411400f050750b001000000802a501180302c50740340c0325900404180c282030105000c903a0810281d40038102c0e402c1004140000d01c5024040002049031920140907052038020100707620300c0f100d07800b95500e20303400140500103000078010740b80d07800d50142e407a940d81c03aa030380078024940d04940540580b50700300b80d000c2812494002950307011703181e0107802d003810909401c0c1007080d0094001c0c0700f51030700314074680c907106d808415100404440c0e880349072201c00d20a030004010f00b4084020a46810000c0c1c2414107080d200c000140340086a61610f80865401080c04000206100b00d11004051001400c02103070441020408ac5060306e42402524a419503140307007095450f0050030394601c445800f2400700303c08501c0740e008026104007012600b02c1981040001403008050f41c0030a07400100010f10500856a200c030f070500c00c1207018003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 675023750 1250 675022500 675022511
    0x2041514011209080f0702100305090a140f010608010c1202071a04021c030509150703090605130f03290f0c07020f03060f010e130c0b03060604080d02011e 68
    0x40650081040c4000c0d03903410301090750030180b0502003680240021030360041100d5101d03445038010b200290490f4608034400d014030f2618003481c610901c12070348900714510082c941c1e54403a490310101c05c140403404210a000b0714940304042074007401100010030300040009400050840c008001d401c44035000c40d005401080b83d03001040000c2440b080c0180c04464800564441e0710015134002d00317001660344041c0c803441c0c0c00c3c0e051540000c00740420101c256094089100715485010305880380700c0005012600c3c150b028020148690080d14171400c0b22500b00d813215407500d2401c80840f400d43c1c0101c41c2c0740d18410900b2180e03400c4035250707110b114200008003d00e0404a00511034041c00800e482010540804d403d070555560820404600001806441640c2001d41c0c1c8034081c00d000b4001e0304142c40018010071188030712400b844241a801c1031111000a0501c1070950195202034603480c1d003c00140400700e0050010301291a105030641c0000135994030039014051103010f00010742c105a440d10 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 675025000 1250 675023750 675023759
    0xc05010e0d0e0f0d120e13110a0f02010b120102070c0602030408030a0305070905130b030d08060a0905090304150f02011b0f05071406070203070311070609060818060a09020415 77
    0x40500c00d0182c8044880100741484140072032243e401c00f010250081485029181078943c0000078080d4414044e51900b200c401c0070008101500c80781a85203104050030000b081c0b101c0c3c40354170514001c00c01440041086040c050019000251152075400325950006e40c450802c511004075000504207400510b040515081c5080d40364081c00da98002415120710000341c810b840761858101400008010038400444100d2039401001c0c00240a40644103e00d01d1050742400390158903c2003030001c103580c2e903c03418a845240609005812071186d41300c240300c0030481c0303800001c01800c1000c1a6031000220009800000d003980c01c0704400c0200c110302000446045640b2000c04031080401d8200f0aa0794046484c00c01180303040071440408a0041c58140482c441d4003100401101d8003c0d6102001c48020301c0e40075443c3c0b1421302c43d4001169a0510805c103182c040c040541d070042445406010840c64000300d1030500d08200c030aa00c080b951034040b80b085203070a00c200707842c411110ba440b25105042 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 675026250 1250 675025000 675025007
    0xb030601320906060a050d05010902190e06160c030b040308100b071703060627011d09070318080c0a1e0b0604020c030405030f01020310052b0311010c0c05010e0d 71
    0x2603c0381e4020b80e0002101c0c182c0304d0050080390790041e400e8a04000c3e640e5640c41060081d0005100c1201019501200018440c8181001d858502005040c285400346800c0e045040c8460598111a84641e400001000c2008460518851400707a103c080140c900a040a4141c0000d80c00c2644048010700002001c40d103005e00220344100c1c04204255a5158100080c0c10b030f01611108500644030800080c1c0d10055004541200310070a8070b50410246100c80d050020310441030030584c1000c4030000060181d84640c100c4620920410340078101180da82d11461515400109503040580c44005d201080084200d100c00440f587c03a07240000d40041c0d0744d240107081001518262103681c001c02d10b9428031006200300c400074000202154207200034806000d020f1740048032580342d048040100000c0c1c070300742002d1003000426031004807031108413600b00070a080b201c49142502040022000003c04032000d10498241070302c140c0380c0c1c6c0c8007c102c41c42c3c000e082d20b001d030340d012001d074100740001c4659a40 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 675027500 1250 675026250 675026269
    0x21309052a090d050a120e3a1a06031509100903110f071e0501090909080d06080a050609010b0a0302060f0c0d0c1b050a03020402030405010b03060132 66
    0x7158550b600d0030660002500d14440c050007600d00d00407449984200008183e0540e20b028458903199207e221a40c10080a11a0294440c256171121601d118190524803000696801416844201e40c40d850312901c03070042ea1200c0c1051000b0140c4240001032500708600305070315440300c7d000c00c2149081202c6980702d104001d103910b8101d407100802c200b014000e102c03c441842044084407103a2800c080300c00c2d0307105a0303803164520010458590020760b004411001c3c0a0700d4041c0c542074603007413400840030014030300c0840546038206c085c03009000d914464040d2030000c10741c5100a2881d980c603410014140308010301803880d0f0760704d0421a80034507207803104010200c903011900d079600c5034075200100030244505100140c150080700003560313189400407000104a805030283c00a442450321207240700e92260301400380e01c9071340104100010b19090700203507482882200041103030040c4101003072030460207800007452640c0844510000e040d003049104141e00958016006045101002c5064461b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 675028750 1250 675027500 675027571
    0x1103010303090320091003110d0c0303080903090d06090506060103090203060601050702011e0f081f120516081b030c0901030b25050910360902130905 66
    0x241c04c15000c0c850610100030110090007612071501881c11044641401c01d041c001141e040c11124541903050400550100e411640503400200403070a5803400e40b241031000344588a42e120820211045407038202039441d0040c0b08060104800f94030f0303d4014100500104014101880c04e090180940c1c1e000624070f03005002800c1c02c6a6421440c00100c810380c0c081c0c000e07101340c0050b031019040a65481031000c1001000303030f610100c40303858103c1004102098545c030840b4115941005103c0340c07050402034450640704904075402020b40036102040710311103902c141021f8110b014440c0070704d005261200035843c4102c019109003100100001c08000e0180400382c1000c0c50b200000b20441454000d000012280c000b101455882e00d40c001002a4404121103004180030300c00d50100c640100300d0740c6c0d20b04151010483d440144403c1c0344c050b00824540701c0d20880f6083d00c000030401c09620091080c00e1440207040c4140341030000d25000d03a440907000c1900c0610b000b50000e10701798110740c0d0f981d0f4030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 675030000 1250 675028750 675028763
    0xc070f2301180b09030a06060803040e01150203090108060607060e010b010f0507020d120e03030d020d0f050906130819030501080727050c25260a0c05030d15060311030103030903 78
    0x6540b03200111b450324081c24001000c075490302002041064000024104607260a110820580e0300c80d85820a60084c1c05100005a48280440d0101c0d40c0540c0d0291b0f4040c90140205003010840d858090560b565400300b280c00381d40d10404a02507590102c64212480c0d094145a8a001b2296000c07915100c40f0300e2020380145044055081c00718071480d44903d5040d001030880340c482d841010002c0c02544189441c092a038a0300941480040c07080c05860b01c52541e0901070100c0780e580f49941104402c003848101c82883c400c00603c442c85245550310401300c0d039039503000281581000282482d00c0c5039504280a8103080400549000001c01070851801c814503d01103441d86605122403110f01903400c040d601045020085000030404005003000740b8041c1000284419182da24070042c0b00404202a44000c4100700c440400c5000307130058401d07140320341c080fa8907000540c03041e84100c0e0004410800b000203003904c2080541e80c1809003614490704864950f00d19455560003800270a0203102c000e001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 675031250 1250 675030000 675030007
    0x20303090d140d06030b15090609070c020d050105090106081510181e020d140705031f120c05210a150f0906020913020705060703020c070f2301180b 65
    0x81da0032803054800c0040081e4041c8070b04d03a12450091240442180c00b0440001f550502490500c0c00404a034001d4201a0031001c0d40d4894a9089031503020181003070b89c21245100801000850074071446118040700030000601074100b62686040121004140d05940b03042001d2003441d00004200d08200c4204280e0000789041920000700030b0310b200b0b0b0208409aa01144e00781d010605d41e0001e15180300100010080c05001103525403403054203581da040006c1c002d00000314070104004024260700c1d40440403c400310341d1070400100c00c805001c1c00f00e4482c140504104041e0400207071101c03c2c0000c1d602507581c000e1015410310303555191144003a1110219520394961440c0355408003001c20b0030000144804410340c04e0a00113580508010f0b4010320000c84000380c600701e9440ac0c1c845160340304026024586138920700f1030103034000900d001400e01a484c0c0000f10b12118800d400010442d0302842e43d00d4142c12020094446982a0f20a044c0014035003103e00e6030340e21003100d1041e2501c0b1005982c5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 675032500 1250 675031250 675031277
    0x90b301503030f1b0708030712031b08011e03050303010b04031110020c010c0c08030c0c0a081b0d060b0d031e03060e04151b110d0e011706041b0509030607020303090d 73
    0x303800e84c95440046c00307000028a1105104021850408884680e1820300c600401d813890340005100d400752120025080728014014440d48100742d000301108034428141858898840e03e0840c3c1c03003a07000449103040003030100200500c1e00c010b40ca12040480d40c0455034510040041e4850280910550400005880082c1081140c80c0b5400c00381000004985e115510b42d41240d42d07070300004101c144505000712002544c40c4000501400480c0c402188554444c00c3c40c06000d03004072040303400c0b261207403a20005442c0d03894102c60501198043d94444541100e034827840040c5185031003990040500b004c00074050380500c0c801103a01b2640c020042c90b02550520703110001800811b000851040c200c240050126901400c106400c9460f031080c1c828011402c4815514108400c0d40680440c120180070200d41c0b004240d02544014054404a0098100d41030f50165210b503400d00b40201d413000c1041000342c04c003007005d654400803030700040d45541045480302c0c4e0f5480119200c0300410600e24000c11 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 675033750 1250 675032500 675032503
    0x309150b03031b0c01020717030d09020d0803070503040c0b04030305070f03021501150201060f0e0c0d06080d030912030c120b010903080301090606021c090b301503030f1b 75
    0x141d00c0d000c683c00c040781018035030890540702c01da000d02640c01071154041c003280c1c0c0401c249204c545220701400940c031b4800501c40c00000f400c8040410b0fa03118040c810050b0214460714011031050241e0766070181c4e01d01d0305280080c401030968007c2010508140300520000b504441180c0710290000c0b00862000520300e01240b410490001c0743c030030b02a800c0000107240301d42000c41d101c800003580003403000c01d0b195a210034502240740b1981759800c0d2000003160b14251038200800e08400011008292692500f4100e443d059040a84000080c3d171440c43d1400c0c014140c0402c00f040e4140c0c50140034403040403d0042100139004031044109a0320360803601d15030701034806030004603071041d045602c80d0b03903c41608000b000c25200d940e0250240201031408040100d42c00b80008580380c42d60405142881c14010303c171307041305084801044140591040600700079241903c1400c164031242c05e54640244140b905010000780703140282d0041c441300100c060960103480c58002c040300400d000380705400800c0e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 675035000 1250 675033750 675033757
    0x1f050a0302032806060e04050610050a1202180a0e040f03050318061824010e10050409140706170a0e150f160c03051c022511010309150b0303 62
    0xf0100040c010414001007400381c00c00011030b0220385900c103d2004901c2407005807081158542d44c41a6000034072000c0034040d201030140d0800707a2500509100c140b5407000100d0340429030140ca518440100141c15142007107494000d8145c0d0080013640b030a00e46d58884262404020003000e0084c00300c0000c00401c489148640d141d09840c049410504103a41c00100e0402d011003451054081c8440745202c030449040034000c1120551000c988581c64900620000480070b030503004408414480007515598a00515014074010ba206a0801e821015080d20b0704209034070001c144030004404d006000e0301c0c50701c0160701140380c0102140344000d03000311504000702d810010085c0d810034001c0c09008201d00c0d60291003030072403544200281c5840001a103a00005200080c00110100000011040c001401a00660204d9000b60600131507241c0507105d0302c211f00f030001c00c030410074500c0000e00030f0103074003012008401c1c24104a610016103540c80c8600b1144a41c01e0070721b0b15003c5106071920200300300e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 675036250 1250 675035000 675035041
    0x60a02100e0115030c030b0f091507121406130c0219141f060501030515131d030a08010512030403080c0a150b041b080112031106151f050a030203 64
    0x1c0d03c1041d9140c0ca490442c901c207601059501089407000030b0110842110928002c0c00d541004100034031464942c03200451004000d0380410030806000411982140580701c0c4050540c1e60012140c07800c0ea0030700040030000082034038cc0a05000c1e90b18134458004c1905040003400318280c1c4012841c0c3e0804060302a82042114036074400d5407020501d141c1850004281424040703424011242c0c1c5000440540e4005d42e5030141d8105ca4140140041c6131826844001440f0400c000c9901c110b01101803420400304030009040e84c100180380862039511842c0d803805407508807000a000d4030100645680d9020740c2c00b00400060001443c40c5a0070810040d42540ca0b0713110150748010908132036008042d048070000c1600441c1070080400d1001d01c01040382074240c2d0f05a5618544d46e182c1855080350071030f00d000980501c19502c030281c031007020502041d84130f06c052444d08420210072609100c1c0c5861003080a241d45025440c0c601c42c83c1e41d00c4011244085194035016817251910b20700142e4076026410b0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 675037500 1250 675036250 675036281
    0x1050109020d0c030938151302043c0303020c010f03051005240d021201090b220204120b01061106090a03050a140c10150f0506030a0e0703050a020f060a02100e01 71
    0x1041307014000c2e0080302c7c81401d42a03450004000d040c03413800b0306038010385c0070b5071035041c030030301d40340c1510313404d074045103107911061403103c6005484101701000d5140c0a5001600123804c200d40000203541c0240c05806d600c2c0007890204024500480f40d004c0d41c04090003007078132845805400c50700400e404500c0103003030507903045040e90710071303c42e0030f464025030111b002c022801090900000f041200c0e480f43c440e4082000d0015280000c6030342c600c43c5809080c4074510003855081c40702141c0108001011110320744600e240c0e041550600c1c0010b010303410756011881450f40080d0402c4128030004c0f49401c0c8140d41818815100c00400381c090f0395600c6841643d030101000800c0202040c1000902c040d10356134001420041d0031044c082d600580e21040c0607410034082511010071007420448003c552146034603a0004454003810036090034010141e00039181c40d88442e484800750714081300c01c400c20200840c6c1e8140341400c1407001070349940a0321200256585e40d800c040c01031000039000302c0c1c042c100104 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 675038750 1250 675037500 675037613
    0x901020304051002161401020604020f06160b0604050f04051218060d02030a0501140a14060904050c1819091517030c060105151e0c01050109020d0c0309 67
    0x440250f561036107508a6421760810240041d1400101d1050309000e20306a020741100d54540c0c00b401800d52009102a0b0040d00800680300400f00e6081d0f50610544648111041d5060690401c01611800f6000b000030800c01b00074003000950001e03042d03401319001c500d1f21b0303243e502603580a01c9607009410440e800c80300004400304032a2440d801548100c005100400840c1d884003002c02d402c2d082a8107190700240210740a0000d0191104004030f0300e44014015490071580e00080780580700180c0c0d0710703203603020085004000400001080d2445413000e5407901074038034095080d001190140e10420724402d5030740704680440c0380040109006020340484000744165900d500755a290701044250b40c0d01c2c041d101c00031525142080120784802c1c0c031144d0f801d0a100051701d001155500c03840314200d581c103041040e0101c0e1002806171a001f40901c6500588074000203460380207403030034580d900e000c02d881c01001340700080302901300d455040e6070b0b100c6451a0b1050072100c001c000300e03001c400195a81122 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 675040000 1250 675038750 675038779
    0x120c0b070609121823120705030706030c0507020607050a05151e091b1906021005010e090a120201090501020304060504050c060f0409022a010906051e010b090102030405 74
    0x1d4000c289030b01d01c40e2803034500c52032440b0011074810740d91032001e0303580408400302084144440f600980b0644d007500003080084258100280312100c0900e100d10306900322070002c11152034240921340040c085410113202c8000c1001004100780300d400002803003a0408186841400340030000c03d221250b00c281250308289078043e001d01030000032034a9029103480d4000c4a484402c183c000103000b0840880280b180340d00d611b007800c8120401240251700300c803a05c1d015a0b10010f15410361402003100d6006800d200300f22481180940381e0503003281049038800000e0103204400000c40400ca55044401d500844c401804d08a000d005d050101810341e60000c000c1c401840302a82c8000d004500c600202c1d0180c0c1150418002c0c2d0780180c800686030b40105010801c0b0f01125a00201a07241c0040350b10741e40c40c81207414907102c0032403aa07000c000981d074490104d42000302500c1882c4c0c002c900c03400c41c1400490110190402c50505014042c60f89002040101c80d40c0d008100b9a00a003800808481040c00b00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 675041250 1250 675040000 675040013
    0xd030e16030206160210091703070503030a02070512030a0f0506010309020d0213020d14010f06030c020604032105090c030105011e0b0d110a11011a0d02011b0506010605071b0501020601120c0b07 85
    0x85006154149903101e40341c0139208c00c0003045410545c3d102020b54150307030700e10b40890003d4002c02c0c0c0550300c038000c0c9150000d03030701b0001008601c06da50741c10002a0855541d00344104541c0c00521a80c185490809203102507902c48424141c80c0340d049070885a03221941000e00040c1c050b00742110300c903601304020850300c4450940300d28143d450480a041d84542c0e40c0404906542415005202680240c0c01180200e4030030340750b152841c0040b144103025840a0440036040ba1821180f4502c940c00011050038207280072301a150040c11070441600301c0c0f411140c1c0b0342c0c1e83d9440d03521450744850350000e1941c222b402e440d004206040c901c1000181c5030990407d015140c910207542c10012941f174a44940394901554034000ca0507800545518240e000c0b1f540155005c52190203120b803022415205040083d004100c45406000d41d543c90030380ba022540b03859040c43c0d80040e020141e056201e1002e000d544d0340004d00a0441e41d401c48031448000d4907042200c3c040a5541000e00c4040300040c80c5001e002c03d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 675042500 1250 675041250 675041267
    0xc0612071806050c120a080412022503050615060d15080706112109041a030d030605190305061519120b0105041a04050702010b0d050d030e16030206160210 68
    0x404000e07030300b29185c114881c4003d840381049020201c0e50f20004a00407408151964400c00e14a0040303880c0c01c0c07200d41da0030030403440300140f444480402d40b00600030000709001c00d80d040028100007100284c08100069041e004e0000c1904076940e8035550103000d481c08901c0b604c01041213900ba500c500741c64a030010582c0c40700a4000d038141c03040740308140e01ea0030311000046500c1c1c00444c0c11410120355608100181c0202e00148208880b8100545440d070f0b8244007002c0d070301c950385d1400160640b9182c103208c4a11000071402400c0300d201c800400c08140c011078001c0c1c0c00b100c200461103061022a00082c03003006900c00441024002950109803400345406180717119002d100740712802e0ba61001008103a0f40307102a20780803444c40d100c0243e45410140c00a5130801d00500000c03c90342e54000125188407100041620590300c121500060b05405100c0e501e100c0d40900090088202407411492201c481880b00034011400050818419441c2c001182d0071154000c2940c2c1d58255682001480c070403 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 675043750 1250 675042500 675042517
    0x150612060c0207060801060c1e06020313110102010b060313030203070c0f08010b0a05010c03080601140720013f02030f07120203060f0d0602040b03090318030c061207180605 76
    0x8604400413424034028486581221207558482201282e107a0324040c04000303000703031380c0007078820a2284000100340d80095031058803c0940d203100e10b41e0030700303041c14116010950103041d03900d0115402416203800048a912181c5000f4000021200e0f180481c910b11502501920700141080b010038500500300d4054200c071002c0e80240320240380c0008104000c1441d10806010400c4104020002401f6030551540034005041015140301211140e0459520240301190840711a1204400714070340e0030141001c0100c28030305046200c06202c0e8041c0302160b00d440044043c00c0640440703208003482c40b081244401807410564407804e043c1403070680750405860020105203580c0c2c107000441c05c14425a407052000410700140c0240b030006121030403c2c07440068620310740822011031480356900085028142c148011581c5140c54042400f10590700c102c52882600300807000c90032513842505880e951100e1140c11800c98603000429546904091b0550414461441c00002d005810101800b40c80 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 675045000 1250 675043750 675043753
    0x108060105011e0f0c120504031b0b0f0705030708040f0510020a0c140319050703021806030c0f130e0f120408071a0f12010f1d04150612060c02 63
    0x50362560015500c0e9900da10f4500c28039420b070070070440114450241d00e01500c0c01c0d420445000e07403441e150281c01421100c2c840003c104d000600300f04100e041d600d0004094005420b08c407100c2e04240b41c0c11111701c24078805840c001c0001c1603180070f00001f4400c6860403079101104030368959540d0002c144032800ba200312072041c0c00c2020445101800070070715800c0b03142e00401040d850390a00701c03120074001c24800075a0b050311900c03d00c01c0282560740300c023009207400394009210a601e14410840348402d400c2c0b1036000340701002d061110715200010702541851084031009820300030311009c40c0700e0f2882c103810001c00a0402200c50000400412007042c87c0e1001002e540112002c1070080c981446188109911075225400401c0741170703800f65a203048441d254a1041c945151040d09001135040000345803814400340d00100301c5121100103a000600e203078241c0c01c01c5141d05c084003d070501e400400107000900340d405d004003551426071050002d88440b02c1000e0202c0784070304001006001510030304015 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 675046250 1250 675045000 675045013
    0xd1b0905011d01080c0c0703060e0c030319080a0212040c0512010902031e070b0d06080c101d030319030f0e1f0f0b090103050a0611040b04030803041103010e060108 72
    0x6544591250281854862000020395202c1c1004484114000b4102d84280340f044c040c00483c0f210600c0884000c6000300c4000c55200c007580502410007440b1400c1c90700c02d620400039080340c10045000c48440c42402c2c01c2040d595580c100000020344980703140c03500c00c801c1d2042000f040002940980c01a540152031040c0103004e80c200700760894017003040195140d40100400305808840740e480040141c0b120081d241100c1d95021741014035009003c40048103a211141484001000c2049482ca11401c80c0ca0211100101c10007512010701015480750031181100d1200f62600e0406c101c4500c2009454600b00a03e8144801002003400c0000514503508261600980b03031000604610445588103900740316101125101c0c0080245a48a406594988025039001d90314214418001c50290001d4900350b125460f0160072680390b1204100b07000340c140402d0044890880c2030341d09403580300c03030796643d81c0c0c4640c1450710300503005a00f695450743c240b51298014580100c2d4183c100c0e03001c40102d907034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 675047500 1250 675046250 675046259
    0x207140610090506030703110f040204030b181f050406090c06030b1306030812040f02040504080c0f1b01050d0e0102030a0603120806030303040807021f091805010315050c0d1b09 78
    0xb42c58056800607810f50160071b0500104004040b40041c03440c009000c0e4401064282c00f1900340d801603031041d00d1204003201008183d00060001d4011102c003d40a005054075081c0030815600ca0001034000041c2d4442c0005c04104c159803090400681011160803d00d5031544001e0180030582e0344c150185140802c50004640d16016600540358170041d0700d41401c810344801070034403100800554100c0c2607030707960002507100c9100c0c403402140110840c540e0303010402140b038601000a034508a881d406008003d01586c0c2c101c0c01f000b5451403d103007241e9140fa08034031807400703041c500006544d10f500c00004d000c141d0040d503015001301da00c222141046400340510503210050200d68880d01134004100190008503111700514504e0320082c44180c9190410000c03003030001c140304001d0040740c6d0046040c8604100082d1001030714181003401d12056066075034402080400107124610140c548001c5600e0352101420f940c400d1003150001c104040d1040e1100d00d503000c0000035500070801000d030108 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 675048750 1250 675047500 675047519
    0x1090f090b07080606040f030606090c08040f0201050318010f0507020c0603012304020d0e060a0510030507030605090106210218070c120e06070501090b0c0304031707030207140610 79
    0x400c58000c00000000e0342d5269040d01c40c0b44000b0f14003644148108804903455900400c0300014501884000030744904100780b0104544007a8001007c0c0308009040000150001c071103900740720390a103051fa07100e0f02d62000c011241e514600c0d82d162103500b08000da1100d5504c40e4080c3d44507040a82c2102c03040d19200c1c062125612003800f8420303401c01d00c88094860030b5404038606414003401b0704014906101c0440341c400303c44800100700c2890300300c1000c1c401c4141d074038003039581c100200380c10031000d41b46542d842565480c502d10004020700c0d22080058480035080d4002d000a003070b0586602501169200c42d00c100039201c0700201c0c4078610200b42802c402182491183c40b4100076101c101144000c0d0b00c4660400c0b0030b8240540403c040301e843d0111135140c90010340b45030b41c40342c000404ca031985803902200004d40181aa1302040c1e06204000100303501299003800c200350052102082e450320401100030b07104000d8013411010380d90b050064030f2a80020494030074150191080c00454441c0241c6 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 675050000 1250 675048750 675048761
    0x2060f0f0f07030e0a0819140f070213021b030d0609110a0c02030a050316020414060108060112090b1008150421090911030f010e07020a060902030c0405040b01090f 72
    0x118081a1a8070028401da80681e100441101e5060304950314070405640b80600c55001804080314000c5030303004170b504250401e0000040c0315011701b0480c1070180e00e035041c10440c000c80b58081d02c1004c000c1d190322152900f40d0704881c000c07081c0e521000000c507101100640c0d241d2209140e00240c901e0708000092401407480303622121901150380a00d01180000c0446485070803202c140c0c0e25005d0600988002074081005055010170b0440c00640c012850042004952103518803a2902450b4420403506a13030121496903c05400d0921541980039522940300900000400030703c003000341d41c18860106010043d03102240d190604840942500d00c900d140d01020603100181003801c0d440392084000000400174058401500d401b401182c1c0c0c070200c80065800005c3c801004d120700100b401005071030541050b025141d4490310004608200c0d40095840c800741c10040c10303040d601c5605e0000c40d40d0078480d600300c010008100388154142400d058200201c2031140c41603240c903140764100c0d00300a50241 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 675051250 1250 675050000 675050011
    0x160c1e0f050d060f060f061b020312070c030f060506040e0f0c150c030d0c0906020a03050d1a091005031902011d03010e070b04030b0c040509070e130c02060f0f 70
    0x803940098503040512881800d40d980868000f81c9440204402d5100ca116a034024400902d420320401d241c004090000c00c2d00c00401c00e01060041440400343c0c6001586030603800108a2565440c04942045443c1d03603040d4000801d014054030360a0148851381e040180a844100e50800c41c00f8849104156a090101c1c040c0304250020030400d04e00745402464030130301c1020740721410715001a882e6060b08550214140303010b6242d8950704e16190591060300704d8098251400140041070b4107440140480c01030b404402e03240760302c507421502c0040300f500c00b25000345005030000c0e03450304102c1d050484070500380c080c945c007900c61080780f818540c031025280040c458040e150704100d060035801203001050100d102540564840d00035151f01c000070000d040c010300d00300b119117450754214501501c00040141c00c042c8041418403007441030f0f1350303216429a00402a4200202911303440b8000c1041e0244003445e03c01c80c3d92900c00c0c0669166008280305e4401c07a09641051400e0355046001610040c050b02c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 675052500 1250 675051250 675051269
    0x30e0915030d20070e011e0b0712030603080d0203041101091203111e0304090e0d09060309020f1f03050c0c1e0316030f020c0a0515070206160c1e 64
    0x10740400d00e9016030f0224000710080919030304040c00c5101c0c054508190b9900c00500703090098010000c0800424591844550504d500d400c054946500ca1007240280746010300310000b03808920348514061351181c0c00441e481000d070b60710742490f5400740009400480d4240c821407102d060351341c00e544c4510200001e45008a4484c49408004d031800c4400403c5003114640c0c2e441521500160010342c9a0390381e07510401e41c401565150701f4000440705481e03543c15108115889400c194108980001581041e60710350f2400003080d600b2030000460411171040e00b1a044060001398076090308016030700140380351440d1418441c54903603401600340e030b115200826030341c1c2d000b55070952070304851124460394215005044909040c5500000c0c01070720f08401088000c00c00900043e5011501070241c0b44610307408403120b40c0c1c907503c0c10340820389072038020f00100c03131a00001030740c8021552110280d410490003a108280c00744003516042c1c881000360300806860348641402e44a072261040049001d98841c01d1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 675053750 1250 675052500 675052513
    0x120610060309060f0509011b080402030a0f0312050703240b0d0507170703141e0c0d020c150105040b0904111c0b10030b010603090302031603030b0d030e091503 70
    0x100072070003004040701c116080c0362038141800c82400e1a005550040140000019540707128400e40c111600000c141039050201102c02c000c00360342c002c42e41c1c161064105400407604615403074100d480c88000f0f01c2c3c00240d40d01d0402030080300c5906901959102c4070480c0c00c400c1180350545003110714482440f80341d40602c01042740031014410390b0070103600034100b81060f64081303440750100d0200107001c94018002a54850b1000788283c100c403400c07500b248005c0f00050311100e285611104141005250401c03034a400109941c0300340e41d56048440402c1110b00b17441885146007030312341c4001e000384100c5201c0c5041001d40d07100340c0750803048140501d601400307000c15940b0400074020f086600101320240138901c003408501042002c00c000c0d00c501c0e500d16605403218114640b035140071006820050416180c0420b10700040c0d0000304944440c01d078060030801d9036405181c00c03801307800d81403203690b044200080385c40101500100d1064140380202c0b56984035a40380c001c108103c00e564002c01e80d0581c802c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 675055000 1250 675053750 675053759
    0x30e06040c0305060a14131e0305090a0504020702011b020f1002010204150807020a1104090c1409071805040b0a0504090803090705190b071b0b09030105061c12110714120610 76
    0x7000c203081c43c4912230718140f4514040119034109200314040e400314000240c02c50f041d1a140c3c124101510003160118205481500020f1200300460741945101d07480d01c0e540408d640c1e90b42c1c0a40150f18006103410780c03040040310000d020790094801c00d8440c01141c080c10743c4650181001c50304c10310081d4014404541c981e101d000c80a800c403e4400c0c0c000307603903000000100c1c030004800c4014010340c030b110b200c4039045e0300280705240c80000c16a0082001000301c115040c02d80540310b030b0849200302c17400301350300d004c000002c1d02054041c0d000d0340c2d00c1860020010700f0409260041d510548080094403007140c1da0300180600030780c44100076418075600800910509103801c0140170818001c0c45038201d14044408080da141101da008403e0b80000814103130550f140c01d01076950300000549000d052400c0109540c0450140b0010090242c4134001500c10b45a00c208141005e03004901d08a40c1034a0790388080c1c120307614440404c50701659078007241070390382a000941940503800038807000d5860703842d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 675056250 1250 675055000 675055021
    0x90216140127080904050c0703080609060109050d02060f0d06030317010510050a0c060f0506030705010302040803070f030210140612010c081515270a0f090c030e06040c0305060a14 79
    0x200a080f201e42005018100460b105c52085603ca411070700d00090f0350758528180544201c0000780124840c0b03035250b082009990380300e226030b0103d450984044e0b080c4845880048d1842c0101e18096000002c003203400c1a0764501c90704507004481c082d440f0307805020200f81c0c00b007810a5003405204d81000510503400c003880d1044009005150721444c00a90a00150b0744500c1500e15107000312030704544940510401d881d00b400b0040060800f403d045103840e1402c22140d4503409004000b03001404034030403d009050003170212248243c1c02e00801c101da2059200641640b14041d0394540c011300f050030380c021401105101d00f04800d801e944640d00035656620480700700c00582804580c2001c07641c18a06c0e13030403115030080c004d8440d41c00c41440300d1041403003a2001101504100c07602c50b4460446c1084070500414250040c4c44a060020820142c00c2800340c02500c0b8041020006104039410042400301d13045604081da0710580c03d413581919070056481c240c8a0f040ba20509010f80701000c00c03071050f130 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 675057500 1250 675056250 675056321
    0x15110a020c0d230109030305060406120816080f070605010909111002070b0c060604150b0d020304020402041503020703030509010c1b1703090f0c0103150314070902161401 75
    0x41031481000c0901c0c4125081007840c103403807400405070344034171100741056014000c40d64000380c00d607000c200c0d25180030402400e83d1030101e005000140001078803850620a400720005581c0c00001042d80d8410250b0001c0d81944000d50640e01e2925190010951243c00d00449122036001130790050031028210810020021b03440d1000d055209502000a000088801420045080c1c801502051a14200344001c5c0c1d0341411405581c0351002406011620403041900d041501c62500142ca90b0f03941c0c40803d00921942d00a00e441c4000b460704218009d60580050070b2440c8a079600340155120389403410f0030f035081145400c02281d403450502030100240d51000603684d0040071004821030700080a2400380c0e200f1384140070135401902a01070101007c100c2d048560300b0030700c2c0030000d4603001d001c6210b542c121404010b200c400740b41c901d040842c0c01000380001824041604541d640103d03038490b40c43c8980700d8030440b0b4442624041800418043c440c0718407900d040a1040c0302d104204a42c562080d4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 675058750 1250 675057500 675057503
    0x2070c080f0c0901052709070e06151909050a121505010e01090f140124050403030e120a0213021b01050c03150109030f0c170c0f120a050a15110a020c0d 67
    0x4810b010344d400c0803004003014054034499024150342410401499010000104502d0050032f07410a82c0042420101c125820691101503007001c010a03a80100e8085210f6803000d540300319411004a01c003406444140d059901c900036443e1401004200074054078024410314403803041c0c00004020084090300183c0c0110380b001000140d108902d00300320303080d070003e8000d00c07800403000c0e480201e041d03843e91078440c100845003442c608003499a40c2c01064101244012805420040800c43d0120020002034503000ea0041c0200b9020b01070b01075a000a401011010403605010040b0040528040c4551800340841c507009614664a05000c555041c02854207981000301013600080441c60742c20f00d0f4141203100b580c0f0000c00c0c0b0718088031109440322000951446403c038003007001300b035621205088891134043e42c00c00c0d43c01e014200e0040c00d022013100d000d8558042c1142c5030041011560031040d6014268004000c10007004031100c0460080001c050f000d80c0c096050f044aa19001c0130801105 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 675060000 1250 675058750 675058789
    0x70611240a181103011d0703060b010915030c140c060406022d030f0c1611151b011812180302040f050a0b01210e1002070c080f0c090105 60
    0x1508052070b04024403482e00550700900f14850306992481c086c043e002011141c12500d00d02c603e00c02450f192241e2036171100070319541e603c016940850f40036807001401840388169414550360b1540010f0003401c074030100980080c4462603038082400144003903c0c51032113624001c0c1460b40e120340d83c54000f0741c050020446500050858140549000603040a01901c01200e4544904140f81310995200014000c400c80752000d00c140140007020110525225801c40750860280a0660104070f2802755000301a02da0100000c0c070440b1247e1200121400e502c0d0f00008001d004203070321141c110141364060007030100886e01c2910358018414850001024101c40030b0b40da080380c2e00e42c0010101d51441a034907003196141c0080040062252080302c01c0d262080c28130340c1d103441c054020800101d50b104408140350b07603180c441c154800420825015441d0711021304654607038541c01d20842101943c41031001c4c44c0b0802d9101540c0540205400b01220406064607a9a9007007408000c500030003140f0343c2025 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 675061250 1250 675060000 675060011
    0x41a0c07050a0308130605040b0a0e1203130e0108060412050c0304090609230124031409060f0c0c07050609010314240303190e030717070611240a 64
    0x2d41d0364299810045201d555030b207a980c01070030748a100d0340b003c5030711943c02d0207000e01c0b04110804403e8100d807803416491400404044e129400160b000741e2810780703203296200115400407060342082020065600403c91903407181c2ea5a0b24140c1d4038482250002c0c820b10f150300d00f0410700c60103000034001d02541d440a903820301e5200e41c03c01d0122030440d40000c2c00300c1c4c1c0380e103551842e944182c0141c140340580a01c00124075810f2060098010182c1e02d41e0f81c2c4009500d8a081013aa4444e9124811114030035801c01c440e420006c6803107603070700380941d82c0700c00700c030401804106100059001c89071030809c440060440f6500d042d003004229040b85c00035078145500c500d044240c07030829115044c840e0481c10301d01c01c519001c1100031011807083c190014000d0707000308504072102800410280102c6c0c914030300141e002e917401020904105c415030241d01079003003c0c4004500c201001c180042a20401c0e526140e0b1400039041642d60b4500c10103000c884100800c001011200210b8081944a081004046038 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 675062500 1250 675061250 675061259
    0xc0807060509100f020a020c01081b160209070c03090608131202062a0d020c12030411180c1b1c03021b01020304031715151e041a0c07 59
    0x90314000c84010055030482c032070440b018070107840b81c44c8080d00001c6085040021850000e5039a19000300410306014042c0d00003420307042440507080440030082900c41e20ba90b0721007a041e405882d1440220300c5614002c00103002d080c4249224010590981eaa400784140b4180b01510b9010700030740701c5442d50318240003910100f1b40681d8404541c848aa00620b490b240241000001c45200130b0804002921900b100d00e00040039010b13a000b8003902000141d403407256400d810700c0c101d48400c3c8a603003814084100818003400402036601080d055803a10307981803091203081d08041003210a0044003600340000c0e921080e03694040d0754910284000c0f0f862a510703423417207120807003440c0340c9040000c1c1e00000c15100b6143c155620141d14211a002581142407070398003e09405051182682912105c9001849034004201030301154000035005680a081c0b2010a102c1c1d94006401220100045d41c041d003000390035030040f24200c03a10340b0b4602c000403422407024442648006520740700b5100c0d440b400315 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 675063750 1250 675062500 675062513
    0x90a09032a02090a051e09010f051021031d030f0f0705010216060c14030909012d030206160f1e151e0c050d11090102100203060a060c0807 61
    0x40300c0074403503071000c01c0c820040c810802000001042c0c14500d504240500601060044c6151440e2442c01030520141d96451200707401080400701c0085450300305024000c040e00030f41040010340310740074070100080c891000325602000c429840100061900d41c2c040351a103c001680b001e0041c0c00400380c410840304c150000c0e14100a0340e83e144071035040248208a00d42c0c0400001c000c80780c00341030f512140e0380b8000000d005807202c078402814180441d584075a4802e824022503070031110003030140030035507120f0310407121003200d401c1791000d03611004c002d4144a1040325001005c0740e9001f02560300d400c80a52441e00308074000305c011a02041c400b0820b0001800c0b0000e04910342ca005040f40c1c01c001e01030b0800215166020305a245800d183c00c9181041408010710713203115070031a0b0408a40240000c4017180d040c404d200064000b103282c8031020300484440d000400840800b40d003119054071903411007000724881035410315840b41d0440e00402c4902c2c015402c102000e4050711a407402d040185e103500c03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 675065000 1250 675063750 675063797
    0xf0312050c07090c0e0306060906060a0504031a07090918140f15040b01060804050309060f040e090f0105102306120a090501060b04290c0d030e120306090a0903 70
    0x10f1003c5441d81e0400b49020361190032120300c2d41c4d003180100058103181d40030654081d8040c0003940200c000103011070613580070f01304075030045500c1282800e0110b641c65146068174000d030354140c00502030181c0000c0314041030040c0c05030b04901e0000c601c1030106980c1e0325241411102c0300381426005509016a1407401070003190203658003540b0042c154501850001e117490700580000702400f20f06030a100116000100766040c0d040d081d200c20761b4440601c860482180102c3d8048407464440130b04000c0c103140003150380700c080c40c4800b0003807016844404010a60b50814003825102a4100004084000c3c0c035544840c40c5080140c801464001001038480e1000720445030950280d88640041c4d0404c01d003403140c20004c4c580e0980c00c5040c141008807511800c2e4400000710401c000c00107400c0d211020314001c541c01070000100711048400e105101401800101a00340e0007401450b43c58240d0400c0303002202d22503040180160f85036a01c124008000307241e602c7c42542042414103004e4008042030001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 675066250 1250 675065000 675065009
    0x9010e04051b0307081b190e0a050c1207020309120d0f2a03090e100302090f04060b10090e0a0c0c0f051603151b0203042306030a0c0207060302040f0312050c07 70
    0x5038040f44c46c0c2602482a03100c1c4a6071590700094040c0d10800c203140c5104000e0f500540500030110b00c035100c008040c0c140c6c0c001c4500c15401002d150007030000494000001b40b402d00826201403001200d055901600c4070211780484001c1010110800d1465114280742540d03030444c0c00207803019070032142200b50218034001c003c6010807c0d440d020320250041c03400c8542c0c441645040345500790f01b0b40d808900b03080d50103024854440c1c40031011404100264000b24a202c0d00070349040d00304000c03100014228107440c4603900c1b940c0c00c0040420b516070b0b803902664184443c2c588581494290943c1c07540c0c0d210401c4401580c650180400c80030864100314039403002503000e0504000c3c1d1f151002c1b285000c840300080303005001007801c460b84440507004015102201c0084d840d03001e50214804000500c10440c9006550280d000410400920003543c42081d420009600f10340c4456101c00040d8100d20482c090300403100b111080410001d001003140c005400c00900d81581803810b42c1860b42c1c0740480700c0c4c00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 675067500 1250 675066250 675066283
    0x21306020718020906040909110d0b10060206100b03180d0e10030203071d0609041b030e0a030923030a030207050301200403083609010e04051b030708 66
    0xe0410840c034141542c920b50603005002103283c00182c0c000a00702c0c0c4030303505c1000042501c819486092100c04600d010190001500c1d0440046007450950500c030b5048035000f200c24030150700842d1003480040c02d140b0603403021041900c902e040100c90800e40d00028401d140f410204888441208814806000445880d0303c0d240c00400c464000c200120754429a07000c04c241c41403041000c0a07030300c0384410102e005042c442032911a010b20210302207100d0b81e0615500700303091540c42c000ea41c07484049000c01020a5030100203291100c58000e4441007001c8021300022800c04040c00120032540c003036070782401c4010a09a50005110109007044000031080e009604240030070016810280215422001c10002e142d80c80004d52100f00118092400060322805011a40c8410074500780301c54403102840c620400225601d0500488500354484e0015000d0080304000040e072400d81207180d40103a0f400006081c291000c1d81c10041c000384103252640e4544510100000d58041c284154455403980300f0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 675068750 1250 675067500 675067513
    0x1503040507050a03050a15020322060e150402040c0e010f050a030603020d0b09060c030610080a060509040b0403030606020d0503011e0b030c04082815141504050a09021f0302130602 79
    0x20900c2c0005a00e601287c1410b00400c100b054100d002c1000d103428000034001d0741205484c2e410810000d01c0171003a104258072039100b0702c40d610468242030701d114030320071502409004a00c440494024001050880c0416540d254214080340101d003c0c040600329481c00045050b502c1e00003643e02940c50b81c0544241d50441c090140c4640140911544410550f0b070701465401c00a0204941d448960309c0c80c7c7c01c210218010a04a4038260050030042100402400d140c1c18039003040e052180702aa01180401d00d811400100540042000060715046490b03c2d400c50b032801e1103001c1108012a9000c84030300655078003043e41e07a01c1d040614020160540031a4455080074003052500026081c000140b9510745c00c0d960240c10710310400b41c1055401001300800c1c400340c0600001400401d1050400124100100403015054440d0800000d5040700c040c025a100c51071003004803041100c0183d00040214114000c1d05801b041382010f9010900c0c00606d8107145040592141040380c1103040103070401d1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 675070000 1250 675068750 675068753
    0x5060102061f0902070804080703061407080f010e0405031215031b032e0c0509101b12020c06070501140609090304050d0c0e31021503040507050a03050a 67
    0x1004003a500c802e604054001d41041d004880380048400d2048400d903540000b00f407410040b9400075100103002e46012a20741c9922460510051b00a09141c03400490885001411981c0300304941070007020750382c0c1c502e60541d003402814940070300010f00983d82c0303200401c10b070b40000d110944914814400711040c6004207103c0c0c1c08142c00c0081e41c08800b442c01414001c05074590b9000f0072080e00341c010400768900c170206584070342c4040788190405c0004442c0341440d181881600240144860002120303030f017052031a14442501c4011601c660f18000d6405040c80100280051030030b9215611580115011340f500503000480300d41c00424100d0321a511070044146c0810384444c029042081100d03000d855190604625a59001d5031251a21904907982e440040c080c13030030302e40c03000f500003003031070001602d0f010041003400b1100054000505d070790081c10000c52984100d466181030f0b4020442000903100d035103c03245079040a0720584507801409030000c0c003559501c0740340e80118400c0f0043c1800d0a642d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 675071250 1250 675070000 675070003
    0x51908010609290f0a030609151b0804020109050616050105010b0c030307180902040312020606031c0c02040b0301051608150a0501080915130507080c090f1f060305060102 75
    0x3507400001141e0620505082c85441c030480407010150802c600701c1483c45038030004003102c0355410303100d402000074080801400a503401c640e25042c040c1c2c270103100c104032140c00b1070f04451640c140c104c98205101125030013644140da110380c0050051502c5480c0740d03154000184103902c0a040f00901d8070700c41170310340100803081c010140100300c140e24250404031007284840c1c81e84402420b51042140000d102c462046401d0140030103040c40038001c40d256901d914181d0441d01444070303070720050f04c0b0303020000e0028500052040846004c80c0d0b0641c0549807400000c0e52042021203040b6030090300e03084160f03c5074800340b00e030310300c103120040d801001071034a40006010281c028000e0900440e9602820b002504c400c0d0b8040121007082c43c00c1d008030364605808a06190b18250040b48000c000c00c240803501e2910600c07000c0d85401002580d8016a54215099941500d0034885422000d0080000c142108034941c03c0d5101200c01541246281c040a99000c0e0411a8000c2d01c0881c2c1e51703000b80109540d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 675072500 1250 675071250 675071261
    0x8030d0618050705091909052d04020303040b090f03030a0201020a18050609090c12180c01020105011802160605040605040b06090402090117010207050f0d1107121101030605190801 79
    0xe942010045803c015500030701520a5201060207003003856440e211564074198144028404260304216900700b03072260300150000c1c00349400265540180340c108401d04c88d0340341b900032a40100110310f02481c00681c0101030300110207241d885903000060000c1e1b62001e2008050495150b400141d5600100501400c80d15045942ca080b0545009003030185444000c11288004c0c0115a0b2500f40d503602c6c2c101c00d4461003080d40d00c0008030f030004207010b061882c001d00c44826204030815503100c50028401207080750024071515540484403240d4000b240703c00d40c01028400700d80d00d058103070b041003a00c640080d904103603001c44800f23075103004210510085144550308007504a0300c405031400d01d900040c80b445c6040c01010840b000d8a080702040716025411104e14540c008181d51080c040320708007030740719801e401c0c1140101d152065124165070380455810709485164000c01481c1c030443d2aa100b01d00e10a1001a060550b900c201256555170710382104000010000d401240c14140b0321030030300303541 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 675073750 1250 675072500 675072539
    0xf11011107260412020d06020d09050f0f010c0909110c07080c01120204050d20180115091505030702030d0e010e07050108060607060e07120b10060f200708030d06 71
    0xb4051200b40110100d1407440c003003942d01296040c80111103410004024410300c803040c45810f01d0526044104600450006803245409050b5004421000d0700e15003600c2d0312686c0b81000441443d003d1001c541c607a40400d0410b08078101e6035040400d00c44d50300d468240f450f00107050315480815507050942c2d110400c103030b0204d0140000c0d0b0410b4074110200f02031840e0144000d041001145208408170f44c43c8a200c440e640006103141c4052044030071141c03036400300780100d80754044041044c10841e8017844051040f140c0c42446207003007002c8803004907038680016041c0b03000c40c001040142034812031401210352480d0001c000141070300c000c180c0b040c5441015803280b41402921030420116648280645207059089800030402020313810201c3d05002072a0084d24000c2c0c030011210080c0040209118401c0403061f4607494100c0c1c4500d41643c1b040f510341e40d81c4002400711945500ea80e24030b82d1803c1c030100b600c0f01c1100c000e01d480e40ea9031811904207820210009075902c40402c100d4640c0d40000a001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 675075000 1250 675073750 675073823
    0x200f031807050901090b010c02031204030309090b0f12010209031b011e02061b0f0a08010614030402031b03010f060b03101a1806191709030a0f11011107 67
    0x15490400880c9103d0030501c41c240700c030f5a5030100d510a503400380503c86d806aa0090554403294911000d4a0998006000a8001511060010171008640e200d07071990b0340001040c0c035a04180010030081220299003c0511954003030000e00b44075102002a9010b0003070801c801504000600c0c00101031582d45580401002d0521200315102a0041082600403c8080b007489408418010713110207841904603451003144d00181660703c0550024409050340c09696586030138010f1440b1592881c0000d6402035815080011748699001080d0040e00103404003800128070706090986080c220307070082c1c7c0f18034003000340001000030899240310244054030101000c80441c41e0000c0d24440c0c580103180c07045040040314000c3c0b840c2d603650041a628102184170500100c001c030010014034601004880c60313541c1e190540450070120000c41501c508006a90f079507407100d03100c9202101c1c08083c2c40c2541416542c1c41c2041491240024002c1c45001c0c000d1085058104400380351200a41007840c000151 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 675076250 1250 675075000 675075013
    0x902040b0405060907180b19030c110705060703170403030c021606020604020d170a02030414010828020f07030804112e092d0e070c06200f0318 63
    0x61307a0f0511003070342090a031300d01764801ca884241b5003541b0134030580089101480214040c050a050003a02e60a40d4440da0b8050295000c00f140603a03040030140704030b5000e41c20070704090205041103009409050301030714041e840001c80304800c5140e10b0b0262000e0f00060340790b46480e030b40203404201c407001d000c40b8002c04a03103d40c40c0c401b0080d01c3d0440034100038454240c400701581889160010310030110414041c2270b0390307580701405c080d40e20360007403207196070b4828040c0d1152055030040400a10420440203c0c00c40c0303804003031151040c50044002801996400d00003c440600014064a43d051294036a002d9908040c103002220b958030110891045180c01480c060003007003558044100300403101e046a460f80015410385640740d59400911500081d1118040b00074651142215900c00c50031034400740070340341c048005003c08120303269008070743c1d04044640024003039840030310b41d0041d11303210080390b40c006002c00d90103901010f00c100461703001000307120040d61b00c02959924480b0420080c1107 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 675077500 1250 675076250 675076261
    0x41103060a060e040f0509071d04150203071809090309080307080f18150712030509061b07020a0314060106020a050c01120e0706031b091802030709180902040b0405 72
    0x1e01148038054507040140583c1040c0e41501c440e0400501480d020310284100d190003030b0f1442e44e9074001d12030b0a00401481800105500304a840c2c140160341004d100504040c0c1e5000d101c1c060f60014103100204007080e003844a07820301100c0c2c8000a4900c00501044040e02800c004050b610070f80c1010460341c00400c6088001807442c821640703640c03810035040da01c0f04031605400c0300c4182d942c0e40594100d03008410701442101040c4c0103000e61440b80c00354506031943c1c071504604464049400582da940610301007099044c0444080714034081e203074902d5141c0819a4049112400d07258021070b0700610f840b01900c40318005100c1c19024000c2d034802040603000580794160341c1d0780c41c04811418800d500300d00700207682c980d410a840c82c8501c1412264441d40e81c810003401040c8103c105c600004180040108051040031402d0480701011090f200c6203064800c1000254406000007041c001d000000258214150341840400a1707000310010700b01001d40140000e8032090901b5038820388c45c1608004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 675078750 1250 675077500 675077509
    0xc060e01052d041b082b05070302060f19240b0f0f072d03030606020d05030c0a03270c0b1606050705211b09010c06050a0b04091104110306 61
    0x41d445030704034601c101d0404c840040081e04c00310b40e4200754207034010380d1050054065550700b00c040b00030000d049448000c00318001242e0b0ba0069010040c01038200d60041420720121000b903540000d080c1581600c040940c1d544002150010011580035070b00c00703419200210800c0c60520002c142401c2110314007070281103051694070034018a484400000b041c100d082c004c080ca406118650315010380205010310000102019000c130600720000703402e004010030a1480492040c0440704980c980034115100c8108290480c0c100e9618182050f60720440010003060407020302410b607032a0204280604694107001014007125042848031500c10004407040f01030100d0f00d80c4045411684c0001c135034440c480111414440c9d101d4504880400c401c0b242c0a12103111a0700380201c1700c003000009164500030f0702d85402c0c024034100d05d001c1540c601200c00417903015089154045106000000d00d606594000f0f0111880680c0135110010303029451111414280300705020345041c45112419880c4c02d41c00034 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 675080000 1250 675078750 675078841
    0xc080f03030a05040c0b0f09241c09020d0308011a030705070206070f05011e06080d0509310204083a0509041112010b0304020d0b070c060e0105 63
    0x381d1440c1d40c0d9001800388a01d90990002a00f0498900ca61f501003504854501d600610303200d5125942002c0032100b00242002c846900f88204407a450801480d80b6410500c80c0b0403aa03030701c24003a211410a00144d40320030030303152498800c0d2101001541410320401440664828208842c8010402c3c410703082c1d040030540e000f02d9411111b195941d0f020f0b01d454a030b40401c0c0c18004142c1c0d070a0120040003205608142c008040c915041007003503070790b1101c1003507517091010300100c0407401c200124900e0382840520141c07860f01890500303802c14041480c81a0894170440c45d04c0345151701007800d0100300c02c00d000c140610080422066418401310038002080000d10785042d2150328455240ca0007a0300510581c2ca1465004104201c1c5900454006c0c0031075010100b191001c200341c2d0004a198404031003aa80030f1500a84103006114142ea02e055110038081c181900b40301d12a80004000b40e12400b881e540750102200115880c01c2010601740d04070b00c024450148004a1420210f408401e140403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 675081250 1250 675080000 675080011
    0x1d030a0327110d061514030114160c020315010e04063c1e0212010f0e010b1303020405240105090d3207060e040608060411150c07030c080f0303 63
    0x450500b0011851306000900d86100c104c6906861528005480c146070140743c4190407054000f482080c80184041000c0c50086a66615016000c0c0c25400c01501c59001145c00034406002c542071100c54014142a048090b4000b042c003159030420001040201d018149050500940c01d0103141c0c00030307080315134904601100d2a14641c10701032401d29507042e600810010003000310600402000e03010b01001030762120240c24a03060759000009440e58808054408a80c0381c2004c100741da908001801e40194000c1e00c201c030f01c5c0950303d68084050723512486090b0003049030b01070080c00c440718007040f25072010741d90b100c99041c0041401607128588440040300d0140764004003001140360a05000d01407012400c0b280243d160030b0746100402003100046040503128a61250f401d902c6000d42040203462450140c4143e0390000310128001615452051080d0f120080400c220090400d007120119001820203000c0341d0701c200d100b00180100b1226010240140102801d040d103011a0560ba4901c0702422 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 675082500 1250 675081250 675081259
    0x15042903241507060b012a02040e03030108100c140f0c061b1b010905060705030a0501080601050d020105030403091703071104050601320a09050108130309091d030a032711 75
    0x4000f40f05d40e20943c054804240140701c140345111044480720f02e120b9900c2e034202e000c0d070303e400c6460305034001c00810340307040b2000c9800030f1031228074810380100640a0303102450184201800940100c2a803074001e0418003403e420448e48455000c80c4062820102504a414102407201d10442e110606401c8810240001480305900c808404110f4010000c216010b413540c0503620900041503804002540110b4400c14107008030b0341ca40811513142c410a01c10305900180c0032024030019402180a143c0c00750103800d002110aa503559203424140c40a0040340c901d410000c0c20008009100c07507460041c42d03003914104a00e00d01400040d080c50b41440b050003400001083d142054520f034000381307a05800300c85100c0d84416042c640500b100b0680c0c0281c501041d4818002014030051032010f50318203416a0701d0311041840c1001c1c140082500354150394500344150544015104108000c15003448961b80005030b0301038640740c0003040c940b034400c0721040c10031614104002c5541c1b02000c9441c1e0a0071038 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 675083750 1250 675082500 675082511
    0x1205101118220b0910060503060405180d0e040c091206151502150114010207030332030601180305030d1a0306070806030c1504290324150706 62
    0x1000481c0014201c80c0c1e9201224140705000c2110b07655009902425010b07034066100f512441c0b49004a05450300407a0001602032000494034500381e08400d411400c40f0b11020313801d040c0c1c1d0300c441d401c00014007000004590301d903804000504051090207980c0d00b90f40380c01624241408961941c1d5104224090000394403480c45e6140401d0141c004401450b01004107150481c1808000c0c0d104c2401080101c0241c101200014110f014440c10498070081640901003041c01c0d070341c00740c03013040c000d010b0407012400d6200c180c405110ba03081e0501501d0000c4540948034a4414001050350039540d4995078100421702082001580c00001c1d12840ea0b100c24011900e003025174180e10000004ca080c01e41e06100310300038810b03510b4000085500444042e01a1002d00d0740c20000d21441203032046003d6080d40c02000f080000c2d01c01e10048140301c003044a10310f03100004049010040d0303007007900c0325801040c03080c008100035248074526203070580e41039942101c5407ca00042a400380525040079110f0344d240e0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 675085000 1250 675083750 675083797
    0x210a06020a02070509180c09060d0b09160b0d06080a1e020117010e040506060f010c030e0d02040912080907180903090f06090e060901030c060c060f050112051011 71
    0x80c001d0f2005000050000040c91400348001200f00e00d000464070010702441040f08000d04141c43c0051050030041e040902d1a0415078885d00ba04400a00088450151103245824840c1460a0100801c60b005030315448052005288007104c030700c6e91005180354420601314000402c1e00000c04921171214144020868090006072505078400d04012212410300001148030314810075064001c17801001225102e41d10341040c4460703c00035008960100d0818031107400028498840d000c13072100050401e4448450315800714041e02d107081e0080380c4020300c0c1802d902c020380d4000151380d80441c2c48030003050454600f02c42841540894180c031200c040e16244180d040c94000c076040402081d1300e000c545146a6a000024480e034090b01460901c500d107400482c12614000365050f060b0703a080b10030300070700915018003030341c000350f51100845031a031710340d82c8845903e2801d114031802010008403210840800c0e140c0203080543d8100401c802030312701040002010058000d4501c4c060301c1902c03200310881003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 675086250 1250 675085000 675085003
    0x10f020304080a0c03050609070303350a02070311030702010827070801020c1b0609091905040609020109090212010603050c220317030106081311030a030806210a06020a02 75
    0x200c2c0c000b14030903c11018400100106213141c0e504882c041e00a542103901c4001070386869000501c00503000419540c400c14a41503500442042e002c410100070150005c880e8808511220071201505030a60210701038080c140c000c0b21415010041c0c00245190841c0c2c0d50010780480c4015102d4004403c80ca1085c0802c0d411503041c0541d020102c2046507903140e0781300c41e01070107075000414000640c000c0c0694081626005200114501d40080245060081c424140710700490000c00c000c020380d9040800404002c42481070301c1c02039004030408244000c00d0300000d01400b42540c02407194520401500380307100700c0200e48a0640303200380341c049a07a80702d042284015004031400d00380c0e2152808200740710340c2240340c043c5044a2090a00c1a4080c401b00c1c00400c0600003441844040b807942c1c000512035607818203450f100c0a114110b140c1220501002080ca0640c071186c0c224046403680060050b20301e81100341d1428410300040d0310160700002c415490b16026102e4006000c2a004203468030100d00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 675087500 1250 675086250 675086257
    0x1052d07050d050a180507150e0312092101020a0f170f19020a050d0b0d050a0f02060f07050607031406031e070815041203020f120a0603060501170f011a010f0203 71
    0x20171000c5515165401c0c10b0070b40d01c8074024403400a40c55440d00300c8101a5000d03404540e0010b40c0107000d0040503a18003441c1c0c3c00c40d8820882a070380108617410130095461040303118001c60b5860000180c07140100385028140400d005101003d000c1420680d13125480c81c00344040d88901a0343e0b030100341c0c0d102c4105001080c0d46203a401c1607804c2c00410701c0040203034013802401103d00811070500c142c030a094280b00420f0282000605650460344916010525242c0718641951018101c18940300b030103082c014041e00054400c4030070390400014802e0316a03140c0214200e00030400d441c1d2a80e030a100c00000da031038132642038061044414401000f02d4a0082c020300d4010104d50003a500c00c0e5000410342034054004580407100d803090101c245201d03d00ca4420b41d80c2074151154500d10305071500c040554428401080d5083e9940c40c0c02c8080000b0b4070a0083c58020840c2d08030302c030406001d0f04141814100c054111071301c940e01d8103142092506006500f906404001e0904051984c04076104a04510 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 675088750 1250 675087500 675087521
    0x170c09030c09090a03081605030f0705040306060303030f0b09090705040c140706060617040b0c2b0606030e0303060901050607020109211703160302180301052d07050d050a 75
    0x140b050100540311101103005561180b00f6a0b03420480d507a451694680380c80c0301c00c00500001c0c014000036484504ca40d8101d5004042402c020381419540d03500c00095526a4104034002a180c410038003002e0801c2c000d01c2ca052104a0358a0003600d06005030640d200c0c07035441024410742c1c035624101d1102d4003079032030803135101c04000807070f0368400d103c2c281080545030507c14040007406040c1c3d030a0009110b104100c0c003c1b46d02900825540c1c44103000d84845410072004000a054801341d043c03415441d10880c1d00e1662079041c004030ba41482d050300641220200c10004015810400801c5903d68901c103556040d07500448600d600c0303503424001210680f4a581003041181200d64207000c5a100d114000700b0050302c150b0180ca206c2807a4807190346213000c169090302ca4448a07000c0041c00174000c1d0081d00301c0001c04d1000d040040880300010b800d46200f40d54009103c800f0000789500070b00c004d03540c0e6040e4084483d100c101812b14003c018400e11480c0b45820440d44e983c008102000002e400408451 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 675090000 1250 675088750 675088759
    0x1e1203020c1c0f050d020c0d1e030909050f060913020f0d0609081815090d11061909090b04050103031704050a02150d0f060803270301020c07060e01170c09030c 70
    0x1841d91301e04030f03070f90b1a002d201d100c01500c2140c0c0b4041c0c10340740c05031844001d580c1c00348500e0004c42070860100c0308962191800c800703004c002a400708856103644103242c45004210074223020760900c035082c800714842c09000b02881f15640035080c40540c59907401ca1140e00e406486280c204140760400100a14104000405040d0300058100c80f410302c3d61300c080c0f00c041046401002c00d0541000c06800c9120340c204094125040319020f8011a00ba100109030010024042c540b0f4275012a000e000e500101c200c0c6413020032481203090008900030310401b00815001e03070342000654190b86000e41003510300d10b038503040650b2100c0003908004e0305001100d0800c1d8080c141d075a00740c01d0158070351704940107a40c0712142c1615111500304030901074024001114403a6028502c0c103680c4001c840602c1030039118515a40c15003001302c01590300c0901c010641e0784502d102805080741040f000030207284680c100c01c0d040000c0b90b5014120120705159058102c0b007110320382c070756592020300270034141041c0c0d02071160722 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 675091250 1250 675090000 675090023
    0xf0705070e01080c0607230111040603060602060108211e07231f0e01140717010b0901081611010507031508011a010f02161e1203020c1c 60
    0xd074101d0021103058440390720680340c190609006022040c02004006020843d5410b64510310703065007182a006909507000201d554420041d03030840e0f5610a52010000030750716003082043c2d65062107101c0c05080820040d01030780a0518018402040820400c2ca1a40c00000c0721400c1051700d00d0307c40b0b280703003042500035181d84040c20448a1100d0040704284d18500f01014600095000702d6105418140300c0303c200750944040b4603a40027880c0c6462400c499650300d01908404541c9083c0300d9100d12050742d240020909050303401c1180c060306174485c4903115000d1040c41c20a82c1c01c040c40660065060581c20320700c1c2c034851000c0f107000403002c2c6d10403090351801c03007400b9042d581500f1008100102c0203140c480170380c3d075150280c201d521440404140c0400d00d181c401113503214589081c41c6050610440303c981e071002005180102d4140e001501e521348460586409032040c0d0f03030f410000c1040d12201e1110b0302e0345440103900c5030a59141180b0030201c03010340c1c00c11845523428011880c0d03040280c020300c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 675092500 1250 675091250 675091259
    0x10819050106050d0c03020c070e0604060f080106090e030a1b02010903080a030c140405061204020a051e01090e1314210408060f0c04330807030b060406140f070507 72
    0x403130340411810303640e00341084070b2070018070b01a00840e80d2218180c4001c04013140361003242201410003030601a4440c0d11034400280381c005e0401c4020240084030700008050f4030740503e5500300c5078480c1c01c1003032a030010f004101c3d4554015a64074004a038460190071091098401240c40f0f003c1c98200a0007100041104030402c1e5059000481c02e0400ea11075604940c0c01044420171030245110780d6600444c20010300032688800088207800510141c2100c1150740c6074400541e80c2076101d00e070514503c0c6000d010041540e400300d0814010402a941030343c3c5414a003004040301d401d65000603014552403480302601640030070460011048254000f00381681c100d09a4616a106201d005181c3c0f00b81030120b40110354600d84580625000318407a80340600c7e1845402a0007007071a220311031940c441ca080200b04032400c034001c0f1080303600d5545005600c1d052001400b190420840d29008000c1400244000d0b50440d03d4140c102d04d189000c1911140c482012802e1071040b030303000502c4c0b40a907510014 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 675093750 1250 675092500 675092507
    0x81006050313140a02090f091207060605030d020a150507080106111501080705041d062d0114180402060307120e0f0d020613050a030c060b0429041109010819050106 72
    0x72465108030760309419511b943e00d000c038003007d081d01c4030140c50300310107400500c0301030701e49c01000c03041d05c00c0710041803150356440003e05103904072132501d0240e004008400108104001004403000907440100501c0c101a98014043c4c1c2d01400380d076090040c203110014a0030001c100c0210407001c500c1e50302c1c3d095078503030124540310385080c0306290180d0300b0500781380c44103940c601002c0c1e4080380007401410140d49030304044d10503010084806841d154010300100b00c810788160540c0c0606254103052b007160103540103003c0b0f410060441754007226488028440144d650b01d048a82040300e0b4603040c0980106140070900400d02c3c110010094030640c101d0040f1070502145222540901e0303026683c040c1d5695003905044056581c00921a4001740c21180000e0700034206030740d043c2c1c0074400018030000060041000c03900d08091040c02c0000400440c2108104e0100040c90b5440903034080c007000c0c18000e1444c280f40680224107050000010000c2c0c4606030494502c00282614001440301e540e440394041c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 675095000 1250 675093750 675093763
    0x507050915090112090b07081905010e070e100207031b0902030115020f0a03080703020f0c060a06030c090612110301020f0d0603120f021f0b040c02061608100605031314 74
    0xa4041a054208610080300c140702c5c3c1400702c2d81001d01c5100b1039840d500c0440e14068018411603103c07050890f210b28000041c0b2404d806005c803000e03d0321203800c1200c4003908011550707003d14854101014060489540424404100d03a03018092242014640880c0080010705130441001e4030302c00f10000031122540d071a1041112165001d65810081804d020b80d124201c81002802003041c02c404910341c0d52290f0300900d4441034041e40c0741d00380161001f0a9080410a5490f442100e03216402441805500010b90005041d0b10340100308461812070400301000c42180301500150202c3c0c0360150b2a2000e40483d1079194001c4001580ca0602051407802040c1500050b0740c050900c00f106075166019694401294205400400310034003041603003403101c4401514540801c0d01d07400310346090788860155200c0c1100703503005045581341c040c1e40d010906009060b24004c100d07829007800000e00081c5100b03070130303030780c0320f21b0034039034943c1d0761441c010b1880000d4200900110611052020300c003c0443c29 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 675096250 1250 675095000 675095017
    0xd090605150a0e070c0303021e1e04050d140c090708090d05090105090609010207030b0c0d0f090c0501080a11031302040b010e0918120408070f08150601030507050915 73
    0x961034000d096070610503107030002e010b411a400d0020000c1040580982c01c0701c07005034802e14025203050314041d15102e9500010424007901b010101c0e0043c40c0074004a04e0020f44035640c01041c0c20246013000088902084d244040c1c040104811503800c0034909000720100140080c040344018108030100400c041811202048240200c041321050305220f00304984031403505a40300b0303050185084c00c0203095480b11101d070b41544150342d000400554000d501d54482d220102e081b03070701c52900e54807030000c1d920303940350032a6a90310341880240090a4403514030180d40080c60f00520554442c0c01680050110380640d030720040001c010000030b8498140c450032598420b0324180800000c3c0f400641d40c0780040788000364064400380000703045200101040091403000070031100e03180c0c180010440c01d980550080321131900410420b1200c2c0c160b00d6054801040303072500405550500c4140c0318008040034081c02c1c100f40d00c2e1404640e1103449181622a80d4a004180003110000c5000450240d488040c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 675097500 1250 675096250 675096271
    0xf12120f13060203030105010207180e0a0822031e0c0f090b0f031605060a091a03010305060105030715120603080d090209060114090f010203070c06020f0705150913020d090605 77
    0x700460024030100980b4102c5034180c00400226003000c00d6002500c0e0000481e600a030398a8a030340e50011801c1040766802d600400200b680d0700031200320142d0050110441400041c8060010000240b280707010300b02c102198481d180b54000c0501d010718140e24a94450003103801001e0b400f00e00200316902621043c0c90894200c2c1c80048490709040d200d109a0701120503503444038804200a040c1180240b080e640c041c60402c00c42170310349400c500001ca410030142c88091002c0014820800104103050243c4011001810654540f0f8010711400405841ca81e00b00a0402601040c0f030301260801d00c080c55120340b1450700d40040d02c91b01d000034440e2403c01d80c0b04240710804280701c5c4d4040e840405201c0c0010b101c10349400074100a101010b003d05042504501c4104401404201000340758400f500c3d50b50f01900c0044d0300307070802c5850503c090704443d1280c2c0603250f510811119100071a075005030b05440c22501d206401c03c0b0707030009000b00041c11a1490a003110001001510b43c4400e1140c0e00068 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 675098750 1250 675097500 675097537
    0x1103031608030f1005010e0f0307050604031a0105090405060408091801080a0501050708010506090402071511040911120105011107181d010b06090904060b030109061b0309020f12120f 80
    0x21001c2c4803004d061284e6804640d04030041009410803007109491200090222041030395100e021508541c4103520694020581408103081130700400341043c0101004c9610401a08083d00c03100c3e10307100050402040b140b00002c10b010285c0301d03407100c0d550882c2941c541c0343c01036030f60705601c68864910041c205c40c46c2d4a0407002039001ca00036050103050301e00161020f4140100502030000a5001d10826207190380c0e00c003000c40d0745441c20700421000c400c00c0d209d0316480724988000c45003039500d860303142242883c0a002d840b0928040110341e5045500900e400d040700b014085419060424503081407140e80c58001800914002c140c0204c100410040c0100004441030070916088a03004066147d200c4406c1101c8413082c5030003030205420a005200c0050080001d00000e4219400c28404658803900c519141c50010b21240c1c1000c0c2c4120203041c2488001c00940c0001c4030190041d0348203108415500c0003081c851010041002ca00c0d95060100b5070320302101c08202d546403c001200070a81000c103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 675100000 1250 675098750 675098761
    0x1c02061b010e060c0a0f0210020705030c1506090a090320210c070b0921070e0612060f0703090219080d051312020612100306050c04030f1103031608030f 67
    0x74054444c0325030b408054100940e202048420005d048908801c601c9181d415201d10781c007500c010302c1c100f031141c00115a60280354540500741f030403202303000101046400801009886505032030b5400060303030a000520b1080e0340780a44502c14518040c071000e2881c1d80d0710400140c000201700c085648803102a141488200d01c00489a2041c0030000c94680c100043c10050020f6850103408241d10082c17159500c11740302592801403041441510760300b9401804100807940c800e512007500083c00703440481c503541c1e0442c01680e81e0b41002d0700a900d0324950800145485d8840d501c040d08031a40141a003060300c00075088402c20180601940046028031810a049640541e040311214104000d50003001c601c6c00744100b91441260b00c05030f0300903c1c01c125892069000c07a412034428061104800301160440c10b001c411140001c055525203041000107001050010400c00b05030396100c1d62032074200c6403644c0441d046014942e1003030b041d99030440740801000800c401a61141007800181141540d07035 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 675101250 1250 675100000 675100003
    0x30b0a020c0c060c01060e0412030f0209030307020d030921060e0c0306161808030c010e0d17180604082104020f211009021306050307051c02061b010e 66
    0xc4a01c032071110b41c070550301c0d030b14981818409052528003210000a05030360351501041a848200c0e001c803116142650300a04036505031080c002403102114085042c110700d0400304e41d4038400d40e40040d2082d00b0140010081520501d450406001140c0a0780e00d0440c0c0410a14014280d22408540e03250400d99118080314001a0f03403401050000c009050310345500710341e08105210380c40c6810030025090540c0d0170440781c2402d900002c001305c8000310398038545808a9800c49140029070b0703403180c2001440a42c810307482401e188100c4406e03003802c0440c0d01ca5100c1d41402000c100360714005402000304102c14130140300081d05902c1d810300030310301c00061041400c0040c00b0003150000d501001803a8402d40a0030001c42c2c5181803030480c03401100400041106a14055a400e100c598454507941e040f01142420702850020940da503105110322820100000d407685190700030580507004030a04000100c5c0752810104502d5000303410140ea41c2da42203100325040c500c02c0304000745582002c0b03244015040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 675102500 1250 675101250 675101257
    0x60903140a0f1e0b1e1e070e0a0317070201021006030b1605090405150117041101080405070b0703080601111f02031e150a0f151407060f06030b0a02 65
    0x18054502c2540c070b011503641d00000110f007404490640f00e0304003400005488039241d41e0085050a091401007074000000003182100203224008000d0181d10013440759030000049604079144d800c1100d1038902003000f092411006e5440540200403800349540c039040c0a90080030800c0c000c1e0300392a01012a803d03640203680c02848002c2040340484001085042809094001c1d141c0f20700c5c003280f410f0f00e6040000c060342c1050340c02104404038403c61350031035030308221046000900030020360382902c0c103900c510a1080340d00040a050005100c006010400705225020140c00507410258070380e0003034200100700320b8080b584180841d078804c0d144000c0b4400000c01d13540340b5042d440b15000f41c0c40030043d400c002c0e4001402c400d480c4c2820340a0b4144403020304015500c01c00e040e50a0800400d90002046a205600d601950600c10741c0d0b04240104001c02c0c600c48640d10311070400305095030b0b091101210728464900b010340150300e4036950115039800360300700c6012a030140060101640303d2a00c498201c0c070 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 675103750 1250 675102500 675102503
    0xe040e0c1915051e07020f120f0723040507050f0705061b041220030307031115100311010224090d031104141207120b130f080c0c0a060903140a 63
    0x5001801c4014000e04e420010101e0a10140951103850540c01c0411110001d00e4408911078020300102d03070b803140040005100a1a43c1c201264139100701484114002e010302d1440e40c0030b41d0322007000802c01401101243c2c0113043e20280c8665450030313410900c0c0c803104191003907100c0072034044000050700d4003002038405807029844c880209148a40d1a858850001010540c0c02070400008168541d002e00c0030b450501d000780c4606044001c0441e6050501400c0c044001004000106102d090b500d0312000d842542c2e8403540c3c5034094509080140c1c038004a075002003001d40400e984041c11000008d8039140140c2c48481200c03500d00c0115400e074150380d82c14500079501d040912040024a0800c0d610031500d45020704806134000d8000c549070b08210042d0000000c4c100e0340d0321003408100c200d22250b50b001e810a40c1d521071000780b50780d4412a07105804005003140c04081010700d6101004e000700b0946010082c6610441995240003510b030781c106100035034400361140c0400c608141c0105040d00120f = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 675105000 1250 675103750 675103777
    0x40b0105010e0a090b0a0306020406111516050f070606030c1d09030f0a031d060612010902010507060c0e0d0b19020c0d1b080708030f010b0702010e040e0c191505 71
    0x840c2000c144d50002d104521700554030111a510001c08a0030700d100030406070581d5920300c984000943c03110352404031900c411348400b481e50000c1040040081300d6001c52040c95240c4142d03101103482c0600201e004000000d4802490710800104001000b0518000c540c905a801028090742030341c48141d50500b22250b802c90341023085041c4401c001400101505d401314100001e54030038003080d07602e17014401602032031070740e105000317114507803610000d2000322848080082c0210003865000905031701071880010300707054480110082c081d00540c0d40143c1008081d026903146049030518007144c9209603071a060500715188813180a489900888820501c60802000019280b00e022511084c00003a240142c0a4106440c0002002c0e00c1c0201a294081c6400075164100020351041030031041c1c0c86003150b01410031400700140d0b0080440070800c0c1040341d00180c00001070401da81003910b4401031325440340c40c00e5403069031696142c480100f96288040e0201d030401c903680d81540c0a114041c900150b2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 675106250 1250 675105000 675105019
    0x30506010903060507140301030b0f060a14061605061311040b0108041e0503121b0304050a0609150606200a03090e090111030108030a080c0f041701180803040b0105010e 74
    0x1c03c00d0b503046150800403603c0c00075810024099200708a800c20381040f100c20100105101c0003005208103150400000c58250600514101015481e1180024528012500805c002050003006101c0d08111504582591070324a403d01c2d04100c0841403460440760054040354030407481c00d0607c6529983c250603140e000a41c5c40d03640311008000c02004070b50441d0b051100340000019002d0016211b4064040344010090408030341d028500100c0c000c40480c8a41c0500c01c010100da8001218140c0582200b40010100843d041240040540c903c04030349030340c205a000201e0641c040341110f110604002a5001080604480e40e26141d0090004c0c0019a1181c4113200000d50303501110781041007400001082045581401c0554109912410180d0000b184444103250050071885c1d03c02c0c03000c0155490000014025003441c025401083e0107183e8008141c7d400d500b0940c44039058461110401c1e071801d8061800710095403046504455000711a400001c20394020306941e5902100140b4440311b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 675107500 1250 675106250 675106253
    0x50a0302010536011d07060f030207110d170c0d03050c0304030806090901020702030a03050705010c0e100e0a08060a061e080613110907090906080c03152e03060c030506010903 77
    0x3581141c00181240d5a5607104401d201c0c17280c282417610041120141284a18120000c1d0862142d0075225090500401c14040000c5d100350410309050000c680c1c0d298a074440381071070800e0b00148402036441100018500310f10701000180c082c3d51410641d410b204669807802e24150074007082c3c41c02000b00d00c1880101d025807810210030340d4019440000103041240d59000039151550040342640403a200103490002d10100307019035030b400301280c10302800004c109804100803003d00480541000200c0088900381d581d000012401050180d04480841c109120402c0040c400b9100e000c01807200c00342c0c3c0e0aa01c3d2880010314044030b680300d001c1c0c142c3e070b6100381d4034511400e4800001c5481800031110b29805580c0c9882c010b0050076295078818005080c640804100ca0060300210025030014100c0321040d58002160a0001c190342580d980f55141d00a070181450022448049003010b196225001c1c501c26080b44001c41e0b00668040c00004501c0c04103804403070b01500c0081c0017a102220500 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 675108750 1250 675107500 675107581
    0x60f0b030f0c190c020f091003110112050f01091404030c0b0a09211d0303071b0b3013060b01120903050403050c06120f090a0609050a03020105 63
    0x40e40710001c2c011103071400081c0b8031400c070320301c0d41c444140000c158040d100e0000d50912070044c01d611041607507041c8803410302014890705000d40b48401131544043c02851401d6074410319408005000707d60060185042c00400b40414030024024043c5051600707800680070040b40c1180f42c000c9426885008101c0c14580b00c080892100800350012640c48e906e81d003000801400598400d580f180610500d400004d00000708200041c0c1c10042c2d0503442c44003020515680401240c0b645584840d1076000d460324109038407085d1b0044e9101c503401c1840401c0da02c000e4002802c44550348c0400030b040c4a0344180c050b281c0c6100d204291604a41040704023440c100080007940003020a100c141800c1d40c42c0403840b24590151021b40c10207c000460110b400c10400c5020444403081c0e18085410509100e01c40b42a49520b110050121810302c90940c04240c40800a02420380326540005081c00100c4403420304507561115010202c0056203000005003603040005810800d800c2c440c0e446a100c2000d808400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 675110000 1250 675108750 675108781
    0x507050313151116140307150503070206160e01050d0b04060f03020f04051e0714070305190801030c060c052a030609031603141b010f060f0b03 63
    0x12222444100001d10070301d03452019100080c00c26500c4060742824240c030090400880c1c0c0420380b22684110359006404002c040e03100107540000c00103496004290f0700080c9060641c0d4441c04041c3e10500140e4141c0e6071040c015885042da07502103411680741c0a144501c0078041c017650341d000644000404010b076214800900b41c481101201140141805001500b20b5029500148030380c070904400300118148240740009a200881d800c00851800d07a02c80702e030145030b14080c8082d940011000525641c050303c9070116181011480c25203c20f51450091300c03030b0340030500542450424034032204103d8801c52a41d17058943c821140841f4503c3c01006451035403501100f16210701a02001c3ca201c04030041100c1c2d0001d50f2261000b648004c0711050609000c809001034100344c1041048182090800d428055400c0d454502800d10240c01024180a80541d40c50340360385040705250b03c4c0c1d600358150454400070842c00d0040203419640c0c00c4c03440d010141c52017011070008040c00020b0048442c450381 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 675111250 1250 675110000 675110003
    0x180405060c0705031b0f010e0705100503131a07030f090203120a270e090d0c1b05060a12050919060c051308030c063403020c0f0714060a0801060507 65
    0x80724100aa04654185c01210000c0100000d900405000e060b058090040070309201152000d04240c500300030104006504420305102403110000110710b4440c80c1d030710950601c0b138016034100b00c01d41145002c241c90400a0b245180020700305103058103000c3d080d109841130641d00900414001b076100b0f2030ba01a9400c1040c3c1203003400117080440790f003554441640407040e22100240c0c101c89040003075044c281b0001400d8181d4950044d0504203003150400701030880140c1041408c040d40e241c00e100b00700070320307880d4220035042203021491003040ca4100310805044100440140003654519900790340c2c0d80322200c1c200e801c20b80390182d0b134404112241d0010090801c0d42c40c01a252100c41000c0a455282c1c4d907004005550000580040146c17081c07002a4200248000101c04801204460b1480c42000203e1b071200101c00e800d03443c0042c0c041d9040ba00c1d00c41d00039064070f654003008001191500024415140c4801444000c400c0b00e01c0c0c020300b19040c442d99a10303804036a90030044e048501e170b00103000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 675112500 1250 675111250 675111253
    0x12080304022d220c050405030106090216060b0310020a110c0907020a02010e0d0b0118050105090709060f03060e0108010606090b0a0215040c0b07060b010e0103060e1308070b070e180405060c0705 85
    0x15a150302400c0ca016080c0c0d508141d171101c1c0e41d01c1c1e103820305160071621950701c030b402c0ea030b84148003280c4c0b260403000f0030000444e04110f020500403901d400007828a00120464140030303200143c100140794104100c2a1310500c213600340c2e541c400414003840ac03482c4040301c2c41c10068100c1180b5030300660081480b500241000340401d08204c900e581d8814a0240a800088501c08054114241c10010380603190260100ba07561442ca070401d00f801802e155014000d07041403080e081d40da881682d100c0ea03c5800107203114503200c0030310350395104140e00034101da0113000300107410f2540c0031910074030f01c0c01104c0c6000320300d5005194900c0e925045008041ccc01a004031341840c2820f40021b2840003c002030003003030380142c4000401000720000505803c59170342d4070790706041c01c02d01c0c10040c2d090061417840e44116142000c91584089150042152140050041182c01c0c5101800b000c11344c82541c498200c80709840345c418000c410900248500c00c00c88005044c0d074401e90000d010441c2690140c00300c42c0c4500f0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 675113750 1250 675112500 675112549
    0xe0109020c010e030c0c0913110d060f060b040602010b0103020403080702120f0f06060405090a030f030507140c0d1419030209010c05010c08060306010f0b1206030712080304022d 78
    0x40c03113429603000280610b0f90741d00120b807041ca20324001c04101d0304049481c0460b0161913441e03680d42403400040c0c2d800c500c12405003001c40244520354002d4024034440d0503081220303940f20144e800e601d1300300740201c600544c42c012901e80d00394060710071130f42900c1d04010014203040e219400c0208960220040402a021b40480055412001c20070a250341d80024040c14062802d5002d01c004c681c0000e00c0c04c0700503400900034001180c0c1104068607141220f00e270200d9a95111135080d2504801000c0860300406c3c00601035503c1034021135002051141c6584084401c82c290510403458004c881d01c60050041071501407850398080e50007407c9920040c10003165004498448901f1100f0788907440c000305400300100070769840e040c0a883d024001605003036002c50300344928402c25020752025008c00407030101c08034059540c2000310200404c151442d40c4050b016034500380c1c170650030944040780940011429011450903043e00b54002d809081c092040204061081101808522159103202403280 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 675115000 1250 675113750 675113771
    0x1d0105060a0905090117010f02040303080f07020f030a3f0213050411090a1703180d0209090d09080a021008040303060801050c040602161421060726010e0109020c01 72
    0x1e80f1001d001b4400c0002000d070031a11006554207490724108580c030b0a5104000c248002034201200d6904422940ca11600641d90b800059103048a1405e0600103444080f8240c1c001c5035210b04035061841c4c404240211400840d00b013006c900f031800f114281514580b0000300c4c0030a1141e8007812440140400c1c481045036030b00040b0381224461050403007114000510a082340c10506200402401015030005205140c030440a840707004540c0d480061000042a1090076960b07801a203c0c0706030018100406c6040902c0c015a45810240c91a00455100c1c4000521048080b4840d51581c0e00074000c0f6240d501041001c941100000f0b00c00c90a26a59210101300340f00e0034411244108012540076030744508100d40649020800e441d613500422516405124115060420500c40788046e40c501c0b1045118040f081403200c04092092103900c99181007081403a48409070039100420300400112400031800e074244100c1090003a10034103203605004218041d150f500a043c1d01c034140c0700004440559 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 675116250 1250 675115000 675115009
    0x1208070212030d050a0903020d080402060417010f050f0108120f0a050307021c0e0a0509010f0603020702130e060f06010809250305030408030a090b03010f0b07150e060f011d0105060a0905 82
    0x76111103401c107581d036a1b00010160100031440300c080003414585010700e45640000d1413072003640a50f0400f21004500e010080c10300b50040e14032007060355800d01244c0b070712407000c642c00c400074132039a840e51141c000170050100d0018111007024001c1c800051805000035002d03505503001801220851155905050000d140c401c0c410400f500580d54428030301060303400304108010103030407080c070039840340d4010804000d0800c190001c4800c0e41c10003680302c1c2e0890000800b034501d6090304034002401c0090a005001d4007003121445840094480251522440c00440300c00008881c0307080715070b0050722503000c50b0351007403412821607070504000400c0c0740d22952100d0464100d0b511000255002040740c507d090340084115000e06218540182958500443c03044400c11034800c4000d54440092002d00340034110001801d849140902807000c8a080c5010a130385038000c940391788040c8890400072410300d003003007400425056036410303103800b41e400c1c24104042d5900c10307514001405488000020306031107 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 675117500 1250 675116250 675116261
    0x90620211314070e091603060f090206040305061b031501031a0d110f060903150c04150c140c030c220507051c0c08190b120a0c1208070212030d 63
    0x21080c002d4900f042c5000b001850030380025150302c1254001540401e00319100190b4070080740d030000740104802140381c82281c010008810069040480002c003c0140100003800078051003085010792020780c56000d403030901d4003065412081000f01c82d140d40d52558481c0d0000014207840300d0351030801c1c030500750024003d041c0000c02150b1003051400d2040d00c0d03103001c10900074641010b0310000c1c6403200460000c1e8031070005181d00042d00792500003040100f40340e0402e8a0142451514881d40c811100c0070107002d007180032001301e50100b08980b40c8642030f03401180030180404c1c003030014082c00103014101310044030000b40012402000282d400c4401510303000342401041a500c50076554025440c080c19440200002040002d0400c07603014107080e440006250302c00d4051840480804042e1408400b81c416445402d5104c040007040300114600412000a40ba1140c0003150a007981d862500d5034a0346040d401130906a03061000002504142c110b2171019110307982980d10740398540140c1f008468 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 675118750 1250 675117500 675117533
    0x20d1209080607122f1c060e0105041a0f0103020a0c120807120c05090603040f1703010609051f0e2b061103131e02040906202113 57
    0x2d41907203134540e0b07809003445503101410004404100e83c051a286214408082c8805000700c1c41d40025002104124030204c01181080c0038000d10402e551001207120100080c001c51b03100e545407202984540000c2001d4400520016041d1419510940019402508002012003d001d45c180d00e44002a180603111085a4080d4596000c4c50806140c010316990b941e024200c1940d01d001da659140310380000070b813080d8070000c8601d19502c0c0d40c1da2900381c41044114100400741c1e03401500d40681e65100402171810798900741d40310740c28103949008000c0f404030f480f54044045202b0310386410415102c0d0701110003640c8068141ea41002d00441940d41d0811020440c0e0304020500302c080c401c00040340240c151403004a01c94900310300304280d85802803954100010440c0489203860ba101040d000d20790368595400510821403020300d8207008000e4a80c5122001c40b0340c0d0081400b02c4200465000e0301c45c11441c81d079030400302070410140e0044005018001c40d02c61503040342684001640106142640e0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 675120000 1250 675118750 675118757
    0x60e01020717070302060f04080405031e0c0f010504050607020d1b030201020618150a06090c2d08221515050121051005030102040f06080a09020d1209080607 69
    0x111640d091070807000d80b1800c901010b14000f00301c160046940020366030f4020042900790b101c1c0d52601d2070a80240c0c422070b8080e5403d40207a0f220100c9048401150600c1800e5550546400380004400c0080400b9141d90150128005120600c11401d150019201803803029001e89140d00f81a101e155403650711110912500140c034009008659041c0480354000c5000114064000340c00c1022036103c10156902c810000c0c0c60b400060801c3c44550041c10003000420410010145100401400000722600690a074500350002195502d2510b22100d8050096900c08806446490140c001c01d04131a81e8007400e500c000e40101e0110360501410300c17181d480c1ca48000381c1d1031030a0082507040c203103940c801ba041c000c40000010b1880050020303042c04603024a8000745660312003800030a08411600b04c60740642c800308011404000f019841800c0e1000d0f5114085560394000440c02a111000350094001c4620b0400f0070024541e10201d0702040510b0502050b11619407078800d1504c6021105407002 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 675121250 1250 675120000 675120007
    0x80a060e0f0a051b011404120f0b01080f12030108030406111501060e0f040e03030c0a0210090b09060108030a0c0f02241b0f0d0807140d0c0e0303130501120603060e0102 74
    0x803100700200a0326001030a0900324a03d0714032904800c1103005900c1020391041044442320100b01030003111410240d4000c40022603541c40300b44a507580e444040f0b203214640310302c240d007481048520040d0390407a694000214500350030028111003115820020035681d2081d1454a00c1207a0002d5840d4060b002c81d035180120105000d04019118100c0e512160085141a8500c600c400740030049a605c58851500d49a5400d81035900328507040350f0700e13004c40c0740700c0c84c1001250800038580c42060003902840100c0325a641c032626820385030320409041001182c2d8850031100021007010060004900081a40007121410030f42000d4600e6482c0400c00009000160280240014000180282c540c8401003223030b2000c1d041d41035601e2040514460600a02d04001080544107011801c07503185116031349a1521400760018002c2d100f8042e100d00820404604140b05050010032b8801c030201c06003003d00141d1a282c01514074805884040b00b0351781e02e805002c4049a03043c0203044020b012940016503 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 675122500 1250 675121250 675121273
    0x20307030c0302070302060403080618040f0b0f1005270a0504060614090a050a0b030f0604030906031107030c030e191707050109210b070324080a060e0f0a05 69
    0x21a140703249110103240c03050000c00c0200f68000303a15a8016454104441540c4400001800343c61362408030f040c100c0b486a0800c000c028840c22080c0d05c1a10400d00e07909182c803120301c41c40c40f105003114030342011101100c0c01c1140340f610700e8003c6c0d2040c40e80e6648510000e140806142d502404903245801180c070380301071208019440c41400000d007007015901140202c4e480000f4034200025104580c02600d0f070b0042180d5a0880e071104040c000020704942450070900b81c119200d2500301e50550100b50403100018000780603000718821564445030480c41c195559400356850000381105404200c00e00001900d41d0300c03000200040f60311140c29800d4200e1901d0801e1304041000800c00300b007904070410070002c0b0790708100703404199044440c213030031192100065283d40c0b9260700c2d0080c104803883c1e428400e0f0580c0607848250500340350303030340c04203c085227200b8481141d18034491040d2981c0500c51034000b03d032881d0b0000d90901c0507481610140038001c0707200703403514014240580d41c07500407455208 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 675123750 1250 675122500 675122507
    0x3090f081603110615060c250e060d12200106060c06151a0705030f31080d050d060e0a020a021b06040b0f272103070212030d050a020307 60
    0x43c64114800d0081000345803c5007580b11224015903800d020704000710764281d0102091000c1c030300c04c2004000400300842040c0c0300034440d80e9107109150b80044210082034540c04d01c54141b02c18113400001e6208503604581d011103407040e8010740341c1081c0000705c0b01d804034070f2028000c40006140f1942d41010f110b41f50b00381681100d40c10f070b0710404030032460042001f00e002401c9881390b041021210050301d039a440d0400c03e00714030070150420019400080c1d0410060b4400780820180d444403900a500001c01032a04450255280a4550701368088229102da56100380001c18141c3d0083c1c034040340d5641d0b640306c5452489402d079180410980c01050200840f6410408602ca64154107403402c0091540408204940300da0701901e40c1c00203001851003040848801210103070301d45250b100d840c41d00e0740884040b180d0400d0b00c482d0b00c26144030290041e908580030464103103042d03980c040d40c508980c1e54200b116001c440c000d845041e020902c4882540319051042c603100300841c01006d6900d140545004 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 675125000 1250 675123750 675123767
    0x21207060e0105040f051c1203050711190803100b180f092a19030b1e0114090a080a0605010311010804030c140106050d0804140d021003090f081603 65
    0x450410406010400c103105c0c1c00d041002c2180d609940c41030300351520b503111141c0040c82c214040c0c400d0b9491f2407002040382e0b1552107a41b11355001d41c1c8040c507043d041c04200d038540f45500a0030507031101410040000c120300b0b00c02550003000740710360411250758a801c216080d13040580c4041d070982c03602d100210301e801c00c000d145549203001c84445109250281d0b6404c415620740c01c056031000c0481d100284070040c080c040b1164910144a41f143c050000d01004001c0c0154480e158080d80b44905a010181d4540b2801070b80800c0c141c550b41d0340307040d0185c20031406130408003c1d550300401c480400160b80740c06201203040540101c40110300c56045050a946110030310140c2c42c10000300c1c408110201740d0000a2220055004900703281402d03000106501501c5950406079000325030900450801c41020300410442c1d07085089543c0170034044040140f17034086250081d400445d404241800c044c402d501c80702c070040c4100c513444982000707500e81c510360f0b402c2410051122080620f0780c03400d040d005401c6 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 675126250 1250 675125000 675125027
    0x1b130b13090b06160305091f0f0302091005160b041a06100c0206031f0803041d2e030c030f060b1e0f0d05030c0c090a0b030703020d060902120706 64
    0x6000902c2c1d500d000c20014840c840c101304035200131038241e0082500c10b01c102ca06482005000b0710005104501074801103401c07100d03000100e0001690700b0003a070b009009658603075000406180040c1080c00b02510b042d480607001c3c00750703e460086090001103043d0445401a0302401c50030022245000700b0002080340503118a00c5800365102080d462035100541900070f80d81075400c0341e142d84610182034403000e030610301c0c849090501400030544040010180c400c0f2a840f800025006c1c401443d031000164007a07950300f181e280d038075903890f00e003c1000c4104070400801e080003441c0190350f80c4030410781401030340048801d070000d107180c2e00511089003d00b5081c02c8041303a0948003201d5501d1818078190105d10b01c54019040c01200c482c0c181c0d642820200e040350400103481e50b9604030a4615140c8080c2d04441d03218a031070b940858041c500d148140000301c40e000c0d0060000908640812a04030b440d054111040703034441148500503200e42c1c540110504c121001040700c035041641c05022001034440 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 675127500 1250 675126250 675126269
    0x30d0c02072412140403020f160e01050603070225090501061b11010c021e030f0307030801140f040e07030606091a2119051903081b130b13 61
    0x10b40d01000904282c5042c45101d450800f1202d0611100051000e084156a094036180c000d004100a254002c9900d200032a8450143c1d03140007000c10284201d401b540c001e440d040b584140051125041800085801c0442801150046240f00c0241e80002c645100c103019148101d88007080f481e4514051280544040d080c80c0b165040f804005503071030200f851000d0004120740ba00c000d02d5034026114003c000d5000382c0031034240b0000b2009a11080444034143d80a403041d0031980020f00740220a842300580d15a5a540e6142d1034042c240d031410024000310f42d84001d1065900c0c206079594400d0f6041c100b54807014100b0b844c80d504020040386d5240c2d0040e0b0010741802050805006500c030314060020040f03400b0600000741c180309102c17024400711501d0261003942c02090a07001d004001c3c0c45007620902c2118140d180140e4aa560b10312202e00c02004901080c001c902d52409283c04003041b4130048520b181041e1440a18907030801981c2e201c0561444000b8041c90320b02c0032100c0c0c20010b004d8000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 675128750 1250 675127500 675127529
    0x108010905010510030c140d0e0c01110312070905090906090c0306060f0402160b040507030b070f0f030c210c030e030c0a0312180606090b0a05010f050a11030d0c0207 73
    0x74041640326600364001390403d0b81d203c103114840380c01050001403410380d80748002e07212403820350003000801e440b0b14001585d100b403101d802c01561040103030041403400b42016508200b40d880c43e244078420003411260611804220208040d16600d240a204242030070040c041424511891810300080d50140d40c0680c000d401040110b440303092445091a00640340181c0d22204180c641c030f110755040400600c46c60801e002e100034000000b440c601502e001c0c4c480c81e0f4090720381e04401e8403100080385604010400c0d030302c0195989800395012141c0588281402003021820688000325040d400080d2000d80d13a440800d00c06c0e0035030600c0b42d100e0781649400194642181007101c2d070b5849110080040401c000e200c491404038006070002c202c0d0401c010003e0313902403010318150001c0c140354011080040d142000200030b510b401c1410a00b2520f0686500b010b040410300b084800e41e1160002c84240034140f0115503207208200020f1940c0b40f03400000041c030b08441207001b810000b45501108003940c0b0721 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 675130000 1250 675128750 675128759
    0x90b040b0612210c01140106270e010e092b0207120503040b25051c080609041716110a050d030e0105070c170d120e06040b07030e0f0c010801090501 65
    0x15008a52540440f29610b07100c4c590402e500740909540c5550b022403104000c00021b03110b400c84440c440c1c00d00d000c412094404885209054062002d108040818a02e40c0040110b84040070389039070481c802c0025034070101c0080326007030321902d0008100304400b007500d204c1c000b4030703541846007202030180c0c1609a2060780e010303240d46959000f203005108a51100040400074500d96100c0c2c1d2005002c031283d818089001420815162400030b40c0d5500107a02400406030003030b00c60800340388039042c003c0c07210740c054440e81c0301c1541c40402880c4102d54608100402402013480c55201183da0703200d6007403080c062941c0c0f01481905003c41d880680140380c0072000400103908900d241d010040700f841c08070b4941c4d078130f4106030541d9022036204c2c030408469200300d4943c0c0903010038441c108200c1c0f6100c13208006203030300320704084642040040029400c804081400180d41151441e007240051802142d0310407811585802c00e212140302288560050412910650304078212034014101d0110410056150 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 675131250 1250 675130000 675130033
    0x50f011a04020c0c030d031b0c0201020d0809032a0c06070804090b010504090204060302030a05060307080307021512011d15010f082a0a02100902180a090b040b0612 72
    0x30400c0440c41103030045401d01c0032890400076013086040c01000c684041090399000380040402c4d51401403105600c04080108500405038100c1d4903034103034001d09448103511012640c2e130340050b042c849640010000080b01304134466403070354044c194401400000880000d442e00e01010b0741d003110300421080c030090300440c000b802078030300b21049100b02040358240640106c502e8400c80c1c100c100000e01c04100854006d5141d80613520400c080c800800c203588404e003c25075039002c00e01c07822980da0b004210090040c1060070b5007020350302c10041750b2070829180031091000c6407c242c001512246901d0018146010210411500802000316402c0580018030008001d41411301440090140000101e03e1907090059016050841c410106481c00c0d914450720070305a1005034100014816099041a40d03080d13403190b840042e500401464070380b007010315a220800e10040903240201e69a01c01d90010624151900780310703e02c00d100c445040e19000302040008107241c091524039621404500c240a1304 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 675132500 1250 675131250 675131291
    0x180f12070b0702010609021c05071422180e2104030303090201050d09031d01050c0312040305120a0606091707030312091b080d0f0906030c140313050f01 67
    0x100181c01000e66520103200340d000d0101030340078034078491000a1881c2c11004005c0c22000d1010b410704144200e40352078000b224100b00c1e400000910b00410001015408112540c2c2400a442d56030220085903490061030038103107040003801c0c8000e455031200842030030203000e40c2c82052242407a1302481d11114107854014016400001c06259441c0400c80c1968014801e4640102c80c1d010103100c5180180f81c0144200302e640c1104448204203c000d24083d80500305540c0b00840001c021410301c0f00004001e481cac0003025005800741300041046030b040e81c0960380624032888c0e1140002c14075600d0b181004044400950000c0ea202c840c08100c80194180032859400700d91300752403c940d0b20382100c4000ca0040520f080000c050078401c0380c02c040b034401124480b02c00c03281c0b000241d5021505030b1000740d0343d0840429560000450a850500145000350f2102c09041102c1c903120505849010060007135034025103900300024220340c403180030418108440084014024000c0c0301d0800341d0740b46003a02c2c41 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 675133750 1250 675132500 675132503
    0x70207050321090414040c03111e040917030414190b04030e01030227090a0903200a0c08011b030b030a0f060e0d050c01060e04080d0c0306050405180f1207 68
    0xc82c00201600142d481c0d03040000d50100c003c1c0e2000b81c41c240744c03a02c02c0818506203c221030480c800804c513101803a00030120b50710f03600e5440742e1901002d40c03032040000030300031800c2c2191807140030003d1420500441c00654455407242c4401d4050100d8a03522a26000e0034a990780c4001003540c006200240c2c1480c1d01030740059140c1070100e8070b1080a00141e02038024094844442c404210100407001c42c490301c0e82c10728484c01c0d2031004035611a14819010381d030754401c0240c0442d002910940a490400c540c0340150300064083d220000e21941d034400907140c1e60b03400705060b40c1d1900a1707010f081c228038110803900d0002e420104074112060001c42d4850b198084080c000340010244481030140640001054000010a403001c000e80c1035805407680d08520f03040300e4203629080b000f10301001102c103401d00868012400703900308500001c0503000b402a60150340d040545842d00040c1c10386540c02458002e40f0000045100d03010200c0000c0d01d070501d5518124515805a0300b14203902600d98112103006 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 675135000 1250 675133750 675133813
    0x211d060702070b16110a1e06030f0504080a0f2f0f07030b0604110909040501060303140702011202030402131a280303033606050606090f0f0307120b0702070503 70
    0x404885e0000700c0c0340f00345500006041c001d62121541201c440d0304920140ca010b901d007001507040c16003544040341d400b01c0c0c0003041d0380c0f01003280380b01c950b000302c11801c445181d030b1030003040f2400c41c2d8500384080403e1040c2400301d80008000809502c00c10300001a58681c2c0b0001011905e25580b12a0b41c0300e00d0180c4001c0c019a901c09040e061b42619400711808420060008800d13810645490f600804240c03009078005500d4015108000c14898122050b0b01e030165a50301280c400d030107040e00250b001802c12640074071560013002010b14140245528414800c40f880300e60880d80c414010011170240b44441c05003504864020500200540c80e41641e416140000f542c03004145919454119440d0060014018141c120082402c441c803007009a0300c131f00024045034440740103020030383c090b003600254085000b5003481031504041207800d100301c900a00329802c895541000003001c02c4020303400c2d1003a2900008002030a501002100000c1030143c0003000890003408990540f15010b10014150 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 675136250 1250 675135000 675135023
    0x40b09040c02010e0c09090a050f0601050f0102030a0509041a041e0c180b0703020a05251d0a0e1c080f13020a031415070e0907050406211d060702070b16 67
    0x72140800401070300342d91009c101e4503082030385011191754440c240700342842848a0318090001c2d500c04030a4815003142901c41c24180040d0608020141090765103549101a180c8589440f030b554a0050802e504040c00c2c4483c544100c3e001d02d03c054a20604503501880030103642d5000c405060003000d0202c4842d00d03c80d075120b034060318049040075030341c00d0080d20361b02c0b4841c01000705903001c4800c000701003d101c1e40d042c45255500608a40e1201c6404a0300b54009104009980c08003a03400400d105810f05056649100701055074182d48803d5900742c0c0001401e11082000c03011440c00002e030000148408050300c9403056000070485c411500009201014030001180b100d44c041209028444001010145c50310f0301000c010035942c0075810251288094401041100d400744084800f0740d545941c6448200c040381c5502d8110040c0d49100004c0036031745140c9003200208418500e17900c50300c140c020f00340d07605280031300070b00c3c201c01a04694820034080003144915128010b509010716400b002c070008 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 675137500 1250 675136250 675136261
    0x90d200616150f0e0d080109060e0f0601030908130e09160b2508030901050f1519031a06130605090f13020d050303090f0f0a1115040b09040c02010e0c09 67
    0x780c40c0e21003d8601c0e40341414004484004d0100303022440c030a15a441400d2a82d0780c01c40e0038141c407414401c0486c002d103150081172031105d400c500d00354000740606001c1111041ea544846440d84507002c00003051610349401c0c8010066800040e4100c0c088200a20032628564000040d0b840c840c40380c281c10080008881d2100714503035007504030060710506101d074154118107115074958000c4031001502d500e00000900c000b04200f00307141c054507101c0524041c441082040c002503011a01070314082d40381409001000030300034130148444688941451b40181002c00921000c17000e0f240900f001c2074102a4144407944a604006e9030100320030608001135124103003069444003d03940003030340069007410100306000c00000114015410318017180d5103942928001512760740c0080301150b0741e400201094010541c0701c40c1c00f00525500603c844d01e0400d942922010540c007550003200b1240c0040340860a5180500c2010000140e5000074009445144207094540030940449481940300001184 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 675138750 1250 675137500 675137543
    0xa090201110709060504182001111c02120705030a0c060b040c02062202150a021f0c1b1a0a1b0309020405101d0c090d200616 55
    0x501080800781500d07203880d29500c0100180c04980510360080782040111002ea240810200d0003040d0400f0491390017129a4840c0c0c44c80c2c002203030303402d0704006a60700c070760b4840300044c0030451405920040c5c00e8002d86440b40c01030300f0b1006031540d0902c0104140041404108044102c5007005498906920f071070060303140c400000c1c0600680703590007502d0140d02c9142150001107240c020b000c0da1106648420f01c00301c054150701d5003560025001440880740c1d50184400e00060300188246005882e40584403c1030255500e0300c8541c02c0c40d10315220700384104e10782c1d04401c00c40c1e501101c405100c2c2480754641c44005102c0042c0c030388541300194a00000786420910781c0400d00c0c61400618080d404040401c00401030a6204010f900c01c51070f090202c0e5400080001c2071040f5141503010154001100e400000703a984002c054210502081104107142d07a1641303e018000c0b8400e070b0340c1d05100070146d945006400c9581c9a41c3d4042d4170104503d022020720a01c1002034284d000030000001b20590500c0d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 675140000 1250 675138750 675138767
    0xf0f0d0207060e060a060503030415050304140d08070915050f07060908130306050f040b04031107082a030a02030c040902061b010b1201020313030e0f030607050406030b0a08060a090201 81
    0x150030ba51034461030051a00c3e012807664000c1c13402000500c001d5458900301505c038452481401d049110031101d95048900a40c0903540c840c2c007628030500e11030010324019082194144900300002c41e04003c021804d40c0003031b15030001d40340200d100c4102c50300201000e40703117214170548040c20100c00710703e800405c10540c01c01e07492280c0c0306049a0710303803031400c02000002203d4042120717903d08000c001100000d80444440c440c98102c80c52000769111a101601d200850000150640c06807100214644908100003900007014840c0700c0110206506c1000302c1d5074007881c210780b01c3d4101405a402682e0b00281440c0402300494002a142005100041841c41600900244880031110401408a040d130189600031000d84030710b03070540c0030790004c64200d02c01221f002142c031400700b8010001c40d108406c80300711148090f0605140560103000245800c00c1203481c8000140000740034040303c0d40c140181200d02006880c4034880f0341c10301c00c0040d21103000501c034821086d40d0750300f217a040d03a100e921031 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 675141250 1250 675140000 675140003
    0x31e020f0a080708011401140c07180b010c05030d020c1204140406050409020f130e010509030910211104050603040c050f100903172a07062606030c0a090b1201020f0f0d0207 76
    0x48a002c41d583d02ea941c050bc400395218800020300c2c080c9405101d5000d00f854104082d4008040c0d450546c6440a84009420904860342c0301e200d08418003811011040081001c0c1c050075807030b484481030003000c1000b540d200350050b80c02582031100d21001600d03101c059401158040b200b134898011681242001841c110203031304919802e2000744818240d011000781035065003501c150740f00140e011000d84240f112044410f069683c00344001d0318410b07599100c94080c00b1650001484d00796a01b0014170550002c0c0d8003901c2a45403035030300300014a072000700707020766520a6560010345104194040d1106005103c0609224004000c1c0c1740c0c001000c3c0b04481c0c40b203504090098903c00310324904102501040d91110307c91040c03c10204016004100c8104444000c1d40314800f1428410040c18500c003019061139058484c900d45039400d6a1011012400340c0600040001e1303c61b071500c20030400016841c480001c1d039204028075040042c1001c2110b07030a400c1e404601e9500d500d9124502d0003403059100 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 675142500 1250 675141250 675141253
    0x405130204080c120f070b0715050609011e030f0b101a0a0503060a0e010b250c050103020c100e0102070c1d06010c0f05071d25031e020f0a080708011401140c 69
    0x3060641c7c11201400b400c9028070040c10850320078006040454105960701907100004800410102c50718561030070f84050054001c4100c2c554a80e5840100007812104862058840080112917440013000308010445400d507803003500b580b10301c00c00b007921034190307074008220002001031010b8031a40c0b901e030000d100540c00300d0301d02e680d140314540058000050343e80410b800f00001d0381120b000c1d130f40003003401034015030300442549c078050054000b98400d203420401409540c0244001c11b0851143c0c0310384080301000981e940446250030040062960407085c01e1203801c3e0303032904200c013421501582c04030003803c080034034600758180503804116a40000301644288580172640404450384001e15070316400686500303403210380d10304d06903880e904907404041c4004210f0070003061080d04270700c0004402c1c983c03064618000c0301070081607130700843c03640c0d40da5040054030b042e01903808042941d001c3c5e07a0746001691541800450041d10300051015410008440404650703491009c0031140e51004000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 675143750 1250 675142500 675142513
    0x14040630020918060f041e090302010e010f1a040905150903090405010b0a1e09031b0f210f0212010c09080c010f05030f0907050d080405130204080c120f 67
    0x52400040d501440485008511260442a141c50b541d039015000b140f00926001001c079020b000c0c41b0041c1986401e100e5003a009100c000d80d41070540c030802c09054000e90001c10f60a01000000e801d494050780c0111400749840005031020401440300c00320084c0440e0301168100d241c0c20410302d465156104810b6001d680c6041c0860518008010a0032a030150340030b11603aa0384581002080c01840345050100305804001000501640801181d04001c0e0424420a648076142c40703201aa0040380240d005c40a00c00a2040d0042c01500e00000e16040d0195031040402a01280311100310781802425040d500111404540d41e50054950802007800204071039210084000c00032100b51141103114000d940381c20403254070600c10b841403200c85440f018519142c40c1880440154000c103010034030f000710640407829580f52098890071600901c0c001da1510b042000b00808403c0c01e245003054a44104001c0002810105444407021011504112a00900c600311420f14071a007806a81034000c1c84d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 675145000 1250 675143750 675143837
    0x9120d020a050c2407050c030a0f0918050414060c0d021e03040b07030b01030216140f25090902012703080406022d0a080a1403010603050115140406 65
    0x22040940c03030b180c8541c00400360717464591060b20703607214407241d41c80c258100300f1121401c50300440c0114000000c0786480c145199455001080e00c06507003a01c11072413511081417200340300005100007001001e103800781c200c60a000400c44034622500100d1038280c0d4021959000504030710025542003900016510755900c0c0c203162128820004030341c2c2c000070030f18248051102e54031a10a9a20b05000e43d8541c6a25101030303250884000429801d006040c03264281180311400b050080302c21a020060501c1a41125001c0b07651611245412071818589000c01900240c1ea210510100804130403500c0550460059038411210000d41c101410081c00040c2c000345441e0b00041c0080034644e90140c902c02c4001e07034400c0034003a5903440c0c0c3ca0192544192000070100700d09000604070301525091003800281c0e04042000349420980c0b20b07402027540c40004000100c0c000c24013404000030740ca0040f504280c4540a060310740240e0064404120492450804a18540c203403a14400d021404803441030034003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 675146250 1250 675145000 675145033
    0x1e05041505100314061e0607082a0303010e13021018060e1e12010507030618150612020f0c03040303110d0806150d09150509120d020a050c 61
    0x452103118002e403100d420036000d00340b203489008031803684400001440c0d2561000c2062905200400c1500c04685201000055036401c009003c814456104191a071003041e85038030f200c40312484c1030301e806804052000f00166010044905407942e42058514544074074003143e046000c42c880c025000a40403009a240c5134002410b0001c0d00300c050080e0910586850742154503284501100d41c10407074124444501c400030a451040d0703054043d000011603c1ca4240c00b0342500e00a551b0407000c05e544200070302003407640044080001c2c00103030050240c5210540e1070760060718180f0a5100300a45e10726030300b10346250b980440b419442014180d0342c8804021018540b2540240b0040b00030540456010200001c0480c290718000c0c015250308076550b50310824060500810040f07101142d00420010085403c00d22541c03042d540241100146000040e03d0070003203843c06000c0d0380c0075a00600750140010310440440315003049403080543c44020f010001c0c2d59a01604100d441e0a020315600502108032 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 675147500 1250 675146250 675146291
    0x12031d1809070b1e03310c1a180f062a0f121303020a03031e030b0d110a03140607090e0402090c070203121902070e0c03011e0504 57
    0x4101c0035503407081e5451036441c98030b102e049900c00031045803030015120000080d0180d40d1100800f51884d0100070000d40710a9002d00c141e54071b8190713089039691602401102d2131038102070302100c01000903910b0215904079460048000079182942d20030300b14040c0d0f072240e5010003a10075015240c4c949a4020750b4a01c1000ccd21151000540000c16001c06d0703000c0c1c0400102d801280c00710102400111003008540c0341103901140b64216860700040b400001601ea00b0307600b000445c080d80d1014081c448424819181c0c0c1d2a9020354000c26061800c07044d001e9450030048200340342d00c520280202c143c80008101d00030415440a01250181061200c1c02a0041f9050b4031880c00c41ea00c070944139071510b2622054031800d88003e500105a9030000d48807000c02c0300103082c00c60004048912110184e140c036900da6001d100d0078803030f000c4404140400103404000c54400b404c00000030f100e0924000e845d81119000c14490358410700d004191000c220700160101c00090200580148182d030781d4021a00500391 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 675148750 1250 675147500 675147511
    0x30705090102010b0904032106031211010f05090714030a020a080c10050f0409020f0d06062003070203060f0601170c04030c0e070f14160c091512031d18 67
    0x1401c0405881440c40c224071001e208680c1512040d02840075149142202015049102c2c1103950b00d140110104c1c2f4641002482c100165940c5040c4461080701e00b4250303031282c1415481f1038101400d2026042c5c012600c0750a80e02001740e01051179000e000028904410002e020350080c0c000c480c003040c20600802c900c038652409484130300c0110041c2c0d208942c05d01c15003c090401c16014082440030184a40042c450040c011110768200490761002c4400c441c4c1d168040c402003803002d5141101c6200c1261050448550703640510700b044d1300e5802085d1034510041002c4006024900000c0309680182100b00e1030b61080a030700c81342131a103503807403209a0744907000070f68801b0340390075000800c54410a030880c8100c19580da40808401c5681d81515244028491190628000e00415140c7c6100c0150b0843c1d5900030700010038280d24284011040b145200e103590241e811412040c4500c40c00c8441e1290510360501d4044004000800030b0700b4030080c600011030780b10340181d0107000078200301d405150013038 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 675150000 1250 675148750 675148753
    0x603010815011208190e041a0a1a0304080d02070b1302030c060c0a0b04080c0d020109020a05030c010801060c020303070206030a05061905010909020c0120070605062b0303090602030705090102 84
    0xa0340c07039100a000000b1030703c10041a001c0f00300070040d442d42d07102c060703c18003801ea030915000703000d4400c0020302501c410298030308910319203080b1050785240c4042c1c068002c0140b070301c01000a12080503004114840204041c00280c0c000507000b000024943c1214511502700c400002c2d01d042c0300385001000e103000c032400d91182c80b40e504000072a20f01030003103c1400032120000c02103c9280d9440a5044c80004d005403400001840f010724261418003d01d2000301d070941c000558080a071041103040c501d01d801a900a83c09200c80010607600b051125065441601b41002d042c6514800a4590b1041c000000e41126001c0144000c901c46600464013812003110350880c401c0e001096200b1100e00b5109140c00140c91803800c1107080102e5008020701003d01001290528900c0c52000407603140000341810030400140707010134060944a01600020704840c10390780c04034000d0141c052038180c03c00300550001003840d540100743c000e134480449598440010341d168508120003411580041c500f89025 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 675151250 1250 675150000 675150043
    0x272907081e1309050402040f06270504030225050307060e12010b0105030c070f0c06230a020303010b0a030b0d2111100203130804030f12052803020906030108 69
    0x403581030301c00d5401c001110704000003400d150484100c003400707001e002640c000756178410500101500e8022000501042070521031350207507461030b000c5280754882c160a80d2034580b9080c000001d50100300d184400c4400c20848000c0e50307094045804091b019070080354903105504c000690244c101c2d14003a030001040b00d800c41c00701d20440b5903c2c262210b00b485580001c00800010700285003880113460a640200781075031460350b01e0750700c0c803614140b507801901c0403411190420702d295041100c0c4100b41030900006605042d91140084e66078041070181d083e22107004a40c80185921a9200e07684e5400000e01c00e1401300803e0402801d854100300030180e1502c0900b0040443c03601034005e4044c202640f80082610320150b9020300d00941001d4107480300801d250040300d011550490240c40514020b103501004000b00f840c25080c0301c083d821400c0f0900c00d041c020501001c3d40c0710000392407015903804104a0301d041d060210000c1c4642004160f0011000c000031138215000502107005a511040341c098 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 675152500 1250 675151250 675151297
    0x35010e010605070507300b04051612021507080a030b01030b03010c0503040f110a03060e0610031109041e1110090b0d0b0d060c08040327290708 63
    0x2c0c5489888806000c9501c1070340c041010b03107075443c4020800d00c0d000d980c0d4a0000c0c0301100f80b08200c00d07200800e503003890100b800c2c0802d006083c0884100b0103020f4001c1e101c0c0a2902040900785584202c019104645446005245a80c4103040720402e41e4040012955207010b8400a4000c0031300c1c0408900003440c164041ca02e9080504c561081da0341c00e034aa050840d0b0b80c1d6520017040290fa220207c41c0b241c101071585900b5220101c086018510520012919082c00720741540fa0940c0141003500e0320342410020004035002a565484420060f0b90040c1260358504145003203510200004400b1186034619401344149202c0d40000d4210444009501c05c00303040040320381801c00c1c0a22541c418041081c01e40c41c203041ea10407456040c0c040e185c444601116141d80c800c44118201e400c0104030010104020190f0107181150360507219254074040c064040c449142c0810fa50144c08200344040203039102c0242c03590074a40c0e000320b0114907503581d11041c0c0740c940415003240701c2d62404c45011700031a00307 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 675153750 1250 675152500 675152507
    0x5070f2907020402300c0a120b0d0b0709030308060d0201050301030f21020f1005010807051e04020f07020906010201060e0c0a02011103180f2a040b13060611011107020135010e0106 79
    0x710440c547c1c0d81c54814080284421074002c04049407510781c800b10608415001605519005100d00031589541805c10325508010b0700c1081e004100c030f44190307507090700d03600141e80000540741500e406c8080c0300a180048d10b00044c0000609120380c500d4440083d0028501e5800600741c1c241103400002d442d88011001c20590590b0000e0090440f10b40050400348101c1c20100ca42004115480c040d0b40701c0400ca502c04136049034800e211500303921000069800c103604103020490380ac40d40a2008000321494580890000759001c1c00c680100e04d00000c0d0030246610035001410980c0c0b07515461076480c10040010311542c40240c0d00703c02c2c1405100040404040701095140c010350006040607070032056401c0482e00f0400c00410213a00c00d680e045e242d40952625400648112445d003030024006042c004054900000c00c422200180c0c103080384245141008000e41d002158203007419566040d4020201b000c82c0014000e20428900000c60503e62100401b811412669101e040020a903201c81045 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 675155000 1250 675153750 675153757
    0xc0c0f05180f07050a180e06040b060901020a0611040305031b0609060405060133031a060928050d0305040f060809030307140c010905070f2907020402300c 68
    0xb081d482c0d02c1440040e6500b4000c0c0000c240002c81407600350a054500d00d12018a001241c00214149444404101460806100e82d00384180201d80d0305040150001c0001e556524944000300803a48401c441c1c40d2907445001618040e681c400305480d142c50f803c040380d083c400b483c0b000c07041c0f043c0702c3c07980804c3c919440414102d01594002c1d003d02616802c100480009110f000f070441003100e0741902c120803544000090302e040740c10950b000b18001d0b004411200c491440d0f5400503205003000c0041a4003030390b40d1494400b0303092840c0b10035024404405400d1090000c0796002c6908805c50548502c20154402c0080098410940d49501007584030001142c040c2c400b2501000b2a60080000c150868090700c49c5078100300281c00981c1c0361200d080c180700d007034640c00d00b41115241d000420a100e00385c0d0b240c803031002400004c090403881c007051030326180c098aa681702512401c030300014540199103590f011910030384c038080801012034004001d120300c180c500b503500010702940785000c900410700d02c1d4100d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 675156250 1250 675155000 675155011
    0x27040504021503090c0a080d020f03041401120e01050c031f180209120726341a04060f030e07050f06070b010e060a08070807030605070c0c0f0518 64
    0x600c1401c50b00102a4a200c0c1d0014001010501c42e1011480035990b03066240d801078050013015242031030741808040e10b0f14181a2610403203400c00e00052101c5624140058000c00d070902e04108041000c031100d01c0200f88000301d401c1e095091a00700701020b64104002d5005002c07041005161150030211041c4100107402200f0700440d0703007010340e014a0310341e8015116008005040f03982c0103c03804401454403e407580400603010001c208080001510078848549140d94805080c0c40304810b4000b0011750030b00007000001000488160005030038601d071040c080e1003851700801410142d080c46d00c40d141c0103481600c0001d860380000c00c1507644280a10550100c0b118020b04181e400e00c4104000d20760198040d81c0c12800612104c0c02042045003514002d0a5030407500c44a8203102045c0a107031a51504241119449480100821040020100222504010000360607181c400089a5030351704100f0103080300380307580c1001c900403004d00501c1044030412590101c4102e003203130404595120840f01c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 675157500 1250 675156250 675156259
    0x206030402061803060924060a090e15070201140105030d231c06060305010e011805060619030c030b221a0904030f020706032d020904022704050402 65
    0x800c005041a0b0068030b00792011070208a40280e005010a203440800c0750090748551240804014018921040110950300051030200e2803402c1c6000c40e07650780003071040c00015640c23a6104c0f0380b6142c060058a0368400746070b03070800e1603040051009010b406d820364442c14008525000040d00d290001c0d1500648250b03849a45000106681c1004000d0101540ca1500c80c2e0422142108802c00020301d0101d08905e50b0014400b0f00f400c0f0001c01700c0781c05803c0080d82860480041c0a6956800114a001c4620302030214913540c030400412040c0c00f6082000c115905882c06022169402da04107590308251664100300b140240010805030420f03000c04a410006c1d01e051280760700300a80c000040e090300c4000541403044004011440382c0c80d0488083e400568900c1031042801d82c14050b00c0020582c91a0501a41d424083d02d01d04085c804c0300519801080180c11407418015901500d6080c48020800c64486180001e041d9414892040580c06900902807408183c0f416118113806181c0240 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 675158750 1250 675157500 675157507
    0x30f0a14071808010609230702190501060509180d050f070303090602041706010f080109030e0120010203090d090503070f180608012a0201050124050706020c030702100201090206 78
    0x200706a514180603003880d8200d034100180810b2110f024001c03540184441074002608005000760420f00364241c40c403c80d10801500180300c0da0035030004040d0210310201c40c00b561690424030701103005001c281c0c041c40c0c01c0311150080015810b881160400d034030f5400001da0364040126034044620703100b41c2c0d14414401c0b03002c1c4001004644242e21540007144144c400510703090720f03954075611041002c48452515030143c0014400c0f81103407444a4003d0812000a0040e2100c13503034080d00060104119504000d880d9400d036429140b6280000c0c03038000300300c000b155207090000d05141c07620108001c0d400850a0054000740c2814001041360441e48681107441070b407070800e501091100d00802e400d008254803104049105030017071007440300c1204416112000400c2e15141d901c071441004001c1d20940e450080108200b1000890501280d6010410700741016040c201c20fa0310b031300404034060001880461003040c20f000000080400c1da00846181c58074078008a412801ea4209800003500701000b030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 675160000 1250 675158750 675158761
    0x73503160b0609130b1b040b0f0a02070605040f0b033304060605160816150504152901180807031103031c0203060a030f0308010501120603050c13021e030f0a14 70
    0x200c041855041c06c000310519080d41d072004036015401009211110520006400048503010480840280641c2c1042c1d81050310301800025408a0780c4281d03164500000b0002c0c89141562a1581c251141407202113559101d003850001d00c1030025885d21b014030b00d0003802284040c040c1d015101942c12f80d158001072100d03d5a1141d00a030803030040d074130f00c0b003600c0d07440413000036840c000d18507010039107140003e114a840e0070008541d8030300c1007000f5a9a80742c001c44200305106e55141d001c400840b0350325100340340c1180740100c0e2507400d484040501400381e040d010070b0024000c00c502c0304a901a40181c08111080d5040646038826251590358500344845c0b00070a10413160051a4403010082c80010038981e29161b41c0541c0460810440c00542418014040d86da040820444171407425001000b00d541160b0302c0b0b907907030030164480b1485030050b078110b403060340e41c80d8049600b66000c01601580c4100185803080d8103400c00d60340e00d90101007010014895030b9041c8110881c51030041000c450729200c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 675161250 1250 675160000 675160021
    0x90206090d17031306060b04061b03090f0305031206040213092a02030a080117150a09020d03050301090e0a0b0c07020d05030a020a05073503160b0609130b 68
    0x11400481c1d807500c0c120b0059000b064980302452003420161207500480e1180c2c80c2600498450ba00181c80b000002c0c0030900000f64014620b101050000c1203240700303c040c0b420107807245042684407006940c4402ca000c006c001020015041900d00034550715181e88441d000c21040e80210651503a07500903002c03081000c107505811070400429400c80035207069407602070289034040c990b0904d078051382c070001d0717504040f80d40008a940148088951000c00f1b0805003401078aa00f03444032400702d03c00154000c550f10100176801001010741c0100640040005440c01800c0354000b4440c2c064500c3c41c10720313441900400450307a0860154070403096503695989150500058004180590308188c0d85466000023a00400050060350310030303002401c01c511a45403030303854454079401211040c4405c0240c04201016041c40c0b40c8651000914480701446032451103241d800751180e00203900076a88400402c9c400d680018501900741034881c0940d81c0e480080441540540c000d004091101c1040011291002e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 675162500 1250 675161250 675161269
    0x2010e0d150f06030210110d0e04181212051918051006080c0a0b0306040b13050115033803010902040509060906011d1b31080109020609 60
    0x7250501100301059000d201c41181e051001e40810703036903103210510551038001c000354402c3c0345030b24003444914503400c5540d0702c60031040c030302c00288840860b40400d1030b0b8498002d00285582810240c00100032820a61141245e846d0000c001c03030f80284c40400d1860050140900c19810907000d440046903900711080240030340d402c2d03800400111000d540010360140b00e5540002c550b000c0100b01103041132903042c10410350702c40e03007441189088810480f40d242c1c001640d9011004441c0001c103032003083c012520076100c01080c60301c0c2d58542170011581e1694006aa00f4104503541d0411006071031051a954101540648a030006001001500d11030f1030407103640e0207000080d00100c2d000300c007503010030141c7d4070555015640c0e0f000300c801c0200f0340c1c8040000e5401061000803500b06502c0c04052070341d0821000c1d01c124032401005038450510706c0385030100c400c2440c5070988081441c440d98055004002e00f590301001081d0b041c240080c428105001e020315581d0010000c0c0d203400081010810703440f4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 675163750 1250 675162500 675162503
    0x7080702041409060403091d06270a060f0501030b240d2307020304030c031e0c291c02070c0503072c010b03010902390c04020702010e0d 60
    0x152544010a9504030b215041c500420407030005014609007481c0203030019000340c200c05082c065070100b132200400c403000915000030082e14407055541c2010459050b00c0c40741500c10741001c445609026020f9026445001141c0307100101d640e070542c84500440646840452141d0710110400300c2040104450861a109252100d030070f91800c0cc0a0003a4425903903107003080030030709000b19030705c1c9001061100c01c0ba03403000071071018510b801c1c117507958504003035140c0c00007400d400d14542400e60801d12561301d01c00e56680185400d0411940d032001404419000b540701c500b010945603c580280d885d030404d841d407100310a806481c0b00000c25a1180003500480c400f921301e280d6075600040d094806014010140100c0040c0002100950310a2050700315404052a145a030280c01009010f040030240c80c1501c51008000d88d8494060851121401e0040b501c3d241102c103002441e281e684100d13040d00d442c11400001c0e62071482740e0b042004100d008216010f4045400f0900e07411151a044c0342d840c4095 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 675165000 1250 675163750 675163759
    0x108040206190c02120c010e040b0a1502030f0315030d021c0507020622031406040b04030f030207060c021c020c030304060f11010c031d0309030a0b0601091a040905010806010b07080702 81
    0x3411a0300000e84504105c248036078560014101d503011940d200302c910f0a107132405e90f81440040300c004c3c041441405a8458001a600301540d1001c1d40341c0300307004443d003a18240c8030304c41d01d0307041121104000c01100c21885219110306a2107007802c50011400b001943d11080c00c004461407540703001c4d03c0d190300041d02240d101e0b008005d00e14a428403c041100d60b407811019041015047d80340c00c5410500102c1d118040c0d80c0040104400a40843c0b03003998803e52602d4803905240c20b0b05400d9000c2e001d8481c1c000c1007241021000d001e440d6001500c01d101048804281204036401d03441030b80c84071051412603401d0303001000280040e6005200800c101c0d030391440c0612203000a07050940c212624004080000380d11a0460845d040401100454161200b009103144c0a10b140020f82d40da902c10000821300180c4400003201a0302401a44004204031a0f02e4440342d40c00c140414041d41c46409442e4002d45410004984804000340d203506070390004403080d10741a603070788950700ea5030010b540407680f0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 675166250 1250 675165000 675165017
    0x5060a0302030a0501020c251404020906120604050612151008070803090a05150d0e0c040f050f070c0c0314010213030302030a110105060f210a030f080105010804020619 74
    0x182c50800c03404642078055000181c94480900801d4184001c5105000410180741e0792031234204103901a400c04c4603514041e030003081c04904003080c043d0280781d10746c03584010040340c40d07000c10000015079846000e00703d80c00c00140c1d030345100f0019100780084e110b07480c6a10603605d106000c40e08a14140d04900104000c01032239a42e0710149241c0310741908403075080c1c0c10105091100d814810300803009010105c8103420f404000c0c0090103414094070003500d503856201d0624690480c000d0102c0d1300703030034005441889082c141d14640030203408191031400400c01c1c0240001c204a110361003058546130b014443e80710b141d1075503c0318203441040da40441c204ad5820400740745c568110114583c0154400d80185468040c0b149001d4003a0000e1074007101c0d103905100400203d565250703174809124400316848a03007580d6100c690100c9406c00701100c8007a100d052945420f05d1b400400032010501c1079036135160b0580e01c130001101c0c250025100250400801e0120304a90804e0000c620b10b004441d1400c0c0c0203 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 675167500 1250 675166250 675166253
    0x7031419021e0304143007030c05030309160918420f0b10030c18060503040c08070518220303051005063c07050d09050909070905060a03 60
    0x500781c1c0181d4084407116000321440c0301c0c0400a0200d1180c05911211001e5581c8100b0940342070b051503403203000d46d1280c00003152000c1502413888954041c1d0042e0440c0d8a07458440d1070707560717903506810038070001403208840069a2202c602030014074500850b0388405901c500d03a82c10a2410540580b41c503501001c604425a0540441414508c0045402d0b696040c2640d19410004c5a00041c40c0b048003504010324501c45884036080000315102c51300c3d0001d4441700d10401104d26560043d6120700302d9070b65900019510f5401340c081c6000380c0c02a200f40042542d203204103566900f041c1725294200c02450010a1102e400f143d0050780810341d88464140400c81c000e50119504001008401081da07a070180120b191044420501402c0300f544c41038a0810882818400c2601e040360700c0350444403034548100a28070480503464221141071925840b03d03224070b415501c0700c1000307981d8000254a400d000803145003900109000f00007004c0901242800d03c040a0007030000100101d13040503040a0010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 675168750 1250 675167500 675167557
    0x7030c050f06040204140426130e010303030c0215060112060b16050c030c0d1b0e10031704030f020f0f030f0307050105010b070209010e0702010f11030703141902 71
    0x8010024480a00242d03c0c0a104000458803040342c00360410a00208200008640000c004411108200d03a5180840c2ea888107460611514003102100078286800080c1c00038001e1040d8142c0e446a10140140810b00754201c0c1d449617005003144016103480d0204034694010090031000500715100401c0050b114200d100c043e5002c2144440c00c1940105120103108050001001e42c440850140050446803400181801c0302c07404054a8007010b2824018108001c400050040c1000d01c1e43e4001413070300486911055880e4403065810f07a0b45180d01c0c1d0001503134901110292944002d111116120940034041622550050142c205103c1c101c140d010399810420351120007003450003190b4544c0f9928025080d2901a408120580b40622202005030303a503150b498199240c420000005170384240c1e0481c0904081218200100d18088030541a0752809008600c60304441d2014021a020134001c5100f90708121000150703100c04040520354000643c004029240c44e440c2c1d503030001e15a2440385d0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 675170000 1250 675168750 675168763
    0x5060409020604290a0203040506090a030507121704051c0f020a090b0312040510080a090b010b0a0f1404051c15140109090515041e0302060a0e01021e07030c05 70
    0x250110000b008144c40d942c00150143c105030703503101c400f581c00c0c801d400780069604d0080e802118461100491046002d448000ca83c0e4002c45d0801e040354590765807a000c02d00c0900c0f44100c20354034101c0300544031021002d4482114100e81d03001c0c4c0f4010306030308500b5a4803404242180d00300c40d521485007840001d0783e03c0c0e425540c007a00c010600080c00008800c10145002171109084400a005001c10442903640c4d0900d046614000e0400744a6030780c0d1045428010015040010b14800e409000419604034910143c12030140726100d292002c0c0440d1025281001c0300082ca085100d0304100078449414110008003c03082140c603d44c03d00c00155036904e40001007401451616a039814020903241a0380c0c84081c0100410360040140c4081901c0307507511104c050401201c00e5004501007010401041c0401221703a1004003050402007041c0340007074407014291080f0700c3d0b42e401c0c90701d01e0110f010180f0880b00d20608180383c460700c01e03044130044400e5800c402400c1e0b0030300c010100e189001c20000d2014 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 675171250 1250 675170000 675170009
    0x3020d0e030903010b0102010b0d0f020d060c0e2e121401090f05070503070c0b150303031006081b0403060e0102090312120c071509021f0c1e0b0a05060409020604 71
    0xd981c0b640521401c0c50308480b00c040026046a06066490100340c4905101022a507003004807000c2444203030000c83c0050072851001880c0924044902210365030209905034000811200220445031a06011001e543c066120101400c2d00340083c2c0d141502441c2100140440c1034004180c001d02c1cac1c40000c079007132026445410001d80f43c010324001503200e8421254044440c1c00c06070706600706401b004148800802005005049200120b03104034082c0c040074001010080449a03686070460745030210b00d0b42c9103e801e000c1103404010654025940c080b140b4000006290917050520315103802e8050003001ca0006801d540c200003030344050f1010301110300c442c5000c4c040a980c03144401e030203181400740141390003050481440714200081c44140a0041c288a038003010524848500006072045502002c41c1e5840d040319a00c964000e410074186903c1500035004140e40c80b07450400f000b001892018000c0c5940301020000302e50344a030381d10458024001500018006206502045655016810 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 675172500 1250 675171250 675171253
    0x6130b0d03050d05100f060f02120414130e10021b0a0c14010503060a05090403030b041b0e0f030613050309060424020f030f0d0912030212071d01080703020d0e 70
    0x1280d03e19411503000749500002c94020681c0c0b2540b4086540c0c015410303034018101005030409510342414420002504901c00c0d61900175902caa564404031008080c0d42c0134540107082046140703c10300744070300c5200b11010888018011507003e01c1800d10095020454502c5100d035616510140007404111150300e80344542806600f0504280ea04030040c506601014100a800c00422045440b142c46600454a058500d48500d407254034003035026100125070b4940061501e50b0360b0304444040c440301040880285c9510581246407001d10003050042e407501a0594492000b18101902141054581d80d0050040d00c0c144203844000503115809030748214042c01520b54410241c1003100294040e1140031b000400014a00110603501c07401110540046000b010860410220460304140180c0350310074110140c139001a400038000b074010340c00d000c090480302ca000400c80c0d03010701c4545641080084800c4040d403013140c011910000000d182104240d000c1c00740c03c0e9182e14034007850080421400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 675173750 1250 675172500 675172507
    0x100c0806011205070f03020a021c030c0e06040308070219030b070201020405041a0a091122030605060a0b0405060a0c1407030b07020724020705030303070203070c0e060906130b0d0305 80
    0x200014101150204050b1449103840c1c180040c2541207000d801102145040250b00c565100030107904109000d8100b00c480b40e1200c03691404c4d145e059101d000800c2c156224850342104010a00007140920b0000030302c8070004118200251400c00d5441100f5070128030101502c945a0740d56100307640c1c003074481001503074010906105a2030a13000d01d200d090300c041c00c00d07403001964800165070805248a841100b95941c0007100c03050182d201102c0944440f1020b400f240741c100485000403410f18030064443d50b15003408645185441c082241c11580c0c0c42c0b003018103003420281002840e510400b5034401340131100c1030850014010a85203980058414003038a41e0520710b00708820010f60083c047c008541002030107222003c82c0d0701111600400a00554044170070819050f0f00d450055004070340d140c400441040143c40d4000300425003d4810103c0016082c1d540107c2c036403050064611070ba0000104000800c9130400c0b600d40e24a207000e080c4045621003031107000c10607920f09600300760001071001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 675175000 1250 675173750 675173761
    0x6150d05070f1412060633040314070305030f090a030204060312030e01152309010806070306050d080304020402030a0603060c030f0e0606030d08092b0e0d020a1403100c08 75
    0x25244020f01c2d0001e449507401000d10b4410b0030340b6a4401846203205000790800010b114103400e8003500034a00603900c4490500c800800c14945800601c802c54400320000d0f0104000300d0042091340460b9400002542490b600c0c910b12001600306a00d2b40d0b40128143d40c0000160340c403030103070000560240c100c2282071007640344003c0a965103904940440d13810311f001d49000302aa801c0a00c1107803000c1d1031911198a20034180c03c0018041090b0fa68400c10b20170011401440104080d4000c400c540c504101f55a0303a0130501008140c58000942890340c180005000341c202030700215480680c500c1c00050050320b0707aa0304022501000c0000c1c3c0041d44c1c9039410715400d0024840c0d1443c0300e0940004046900d0000c0010359038640d2481c204040012407408150349100c02c000e541c41c040b0540f491b0140404000401d07180d840c00201c0760703200155000c5480c140380c2c10104451601d0a4010744000d94071410700c4d00400b14000c180ca005230301403140501d04a0f40149900c1980400d048603911071840b401e02 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 675176250 1250 675175000 675175019
    0x80c061c0c050d051f0b09010504030506040308060306070f09180e011d0c09010e13241524050c0708010e07091b02030a0e0406081c081806150d05070f 66
    0x1000c022000d4800b2040050405c00001c084048885903d03000741d841101e038004844a004661000b00240b1540047c042010340000703100340302c0c0350107808450865545500031230707502d6003050702d00c07011410740c4800740f00d244003110010080c80940800843d5445040c010503003141c83c4039201c104098505d611044892405100e0010614011500c990031541802e05031004064042c01680c85503080c0b0104104106403085042214140c5a42c09001407407255506005811200000000c05110000c04150f16030600302030880107003040028401c81403a400c040d135143d400743c100700d00288184540003400325424010b03044281c80701c6001d40120f600d001901d100752142050101e0804000d00001050719a0000031f542e14001c05107401801c3c44070450208008100e141c200320081d0041c120034500d10750340d91145e00c04028003a03540c0621503480c0f50f80030745a5042d41040d041aa000385021a07100181c0030300d4003d220391b001b4007565850400b039469602e4070480394880141080520f404020345107a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 675177500 1250 675176250 675176261
    0xe030a0c080c0d15200c0c01020c04020f0a0818012306060a080a020a051e070510020c1f060b16060b010201090b0403051303121710080c061c0c050d 65
    0x140c03140d104440e0580d40d50910104a401907800050f902d10103601e417120914003410020741c0b0701403040d5842c403030340190380d444220003140c43d40944140707078208059040c140700b1a030b07c0210140344c8504250220904540455000c2c00101e81e88010701c4a0300a542c2e000c0c46410740c4070580b8504444609251034039288241c0005082c10f124071b005102d2000002d8020700030b268018a040710050f81c89030020400c1c0e640e4000d03041c40e0041c07a240ea04084a00072030760300041145901440c112420400140b03141c1d010780c41703802c400c10859040240c0035290152440c004408895174168003044403515020144110380100381b030480084001c4d6a007800340300d658891541141000c0c402401030200703c2e16445441b00b0041e00080c200a000281c07040c80040c1d00440f9000b46511400100341500c1d0300388000c02036525880d42028000a40c00400c030350705900b50742c0d90100c841c1c0750043c1284072040420000c0c5030708460710f1202041c02c403000d0b0303d051120a1266001d40d0603d51076080d156030b01100180704686 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 675178750 1250 675177500 675177523
    0x105030607050301170a051006060324120201110303070201050708010617130807060f020406030624050c03070c080a0b010603141b1e0c010e030f0d0209010e030a0c08 73
    0x3080001070045040d440412641594551201d040c009020003628070718201c4c0c800e102400c80d00541540f6540d01c4482e402881c01c46001d5502070064640002c6c0d4044801003c6000c412140b0071840200020151002c1c22030010303005050510841090042090940c2d0003242d46900503551181004091500400400d001d0140c528060314042e020304002d8007030031400f80a1000c3c803403151010004106004085a9001d640310f41d0030b108110725000f06202070741040c00350802082c1060b0f00440c070700012408010a100b6884a01c0d000b880c2c09c0070040e20300c0e0f84004080410341c0010000e50b404a60b00000b01c10080c80e5500007803c0d580290b0500c0e4a2100040c3c209108050410f0750042c0807541010a25401c007244c036058602c6001c10841c1a81c1a03c248207000d54042100980c0c03140c40301d2220b000d8a000c06000009010306503120103195224404d02d0440114601e050000441d050629409401c0d0040181400321640d65000700007854465020012620007942400520100300709129505085 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 675179856 1106 675178750 675178753
    0x3170d0e0c1f1b080d020a030e070b090105070f03090e1005031c02062829010905090406050a09141b0a080705130b2106011d060d030908030f090108010503 68
    0x3030505070141903150040c000300160002f141412506481c505075aa00d1804010781e49104545205010540401007041804241c2180d0000d080e40544030490f820060303149864101b5141441c1e080212441681810020201030380000300d054005041da01000c00d040c64640b03006140c0200d0200c0c00214034102022032007220038184004801100084001202c501042c00541d002032443c03080716000032070100040c0c0414450f511aa0700300c0c180d0003002c40d12002c181c841150300c0d82c101c207200c110f0350025002d0351000d004040d0703500781d121000d80303003101120700e00740c43c03551584003d1040500626017006103504024880d400000c084900a05e21036128400d82407401c08011000401d82d101c0c41080004030701071000d040300004084501c210b050195840344280700151a1419080b003d00801c0440842c0720072042c8040d0010340a500300164440700481c000414111040e03020300e000c0d = true := by decide +kernel

theorem cover : BRFrame.Cov 675000000 675179856 := by
  have h0 := BRFrame.cov_init 675000000
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 675000000 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 675000000 ≤ n) (h2 : n < 675179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
