-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0278
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:55:57.498551+00:00
-- url     : https://prove2.me/submissions/a90e4ddc-5854-4e72-8399-be0468485a4f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 49820147 ≤ n < 50000004 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 49821397 1250 49820147 49820179
    0x1050a0f05100b0906090105040819030201230c0a030621020a0e040209130203031903090c0503010b01020d12020d0204030609061406011b0f12090608011212120605030f0705040b 78
    0x1113130b071560001d546990f52180344000688403403080d0b6021135400d03c500c496071110080358030401195035102e58024444104044200205000b1018002e68070700d030008041110a5120300003040c107241c80b82000305102e6540e41c6803204d80b440341c038a207805881000c00142c08500d056404000a4030708080e40b54190304041e0041803040c68011b20035144129494040010340d5410019540030441e0408035000701c10a440c0010060801400d048800310310890300802e061906001f4102550010780c0203142240d8002000c5442900b07040d03c0450755582000132041c101158001000514080c0b42c020803001b1881c40d1030001c60786030748140c11032105140c0c24021a070303902c805550030241c1d94440c1500d00744d581e4189441031a41018000300501d120b10100c58030f198000c0c28200c2290b1507031b1a0824180c1e41c1d044080550052843c2c0100b4807051b0b0f581094140340a4070030905141c403942c0340000d00c9a1224007103840c180c483c40001126600240c030030851440c042c01000390b5002c0039902280b9640c2800 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 49822647 1250 49821397 49821419
    0xa06020309151e0601050319020301060e0901050a031122060323070510030e0f0102181507150c0e0d060f0f2007021519090b0a020a0b10050301050a0f0510 68
    0x5444281084400030105181141c040d113540c80c08c942c40ca0007156a560742d4907000d0461401001e041e4007400702c030000000c070342c0f9114070440c08a0fa006010504850480010020042c03103c3d0146410744404071501d800c2d07d60184202c1c4040c521402c1018800c03111600b0401402024001218541d4030500c3c0c113004540310b2341c25404020185003804907204c1c1c1003681c507a0170650480592403456102181c020b40074841d440c04140da00340241c600391482c4d404101c0482441c1b0951728090820490049100d80300d42c85980703c8032585203d840c1902021451000048210001c414203a0b001500c441080c462601c09124103080c00c150303000108031000541703685201041d010605259219030101c2d100e002d640300c008142880074035a60b40c4655900c602d0844040c034411441c0710500040800ca00442c2035600c20040b51001503807600107100d000781d0350380c0e10031018030018403541061940600025158a007409441c2c05000d1002c00420b0303040007480d411044031001407210b25000744403035041203546002 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 49823897 1250 49822647 49822651
    0x618030c140307060e0a0311060408041a0702130f0b031f050a0209060d2f07020f120a061a010f08040605061c14010c050405031e0a06020309151e 64
    0x269034089461003055066014205000d007440341040e96240b024000414681c2c80c01f807203074451118403104418120341e00d480840c1c0c01400004100421b111b0250a000315881c00400800b459140107240da000c00e00c056506621402269210b2007038180a43c49801100c400310400d03001009010012908210010208074407481c40c41d0b03842c1c0204511111540413103110382c0000d421141e40e10031551030900200010848407003001c000c7c020000102011007039002020200460071403d1041d50b408000325941680802c41d4800385403600d549444006201d91700300180500c40018a8604407205070464242003800709040145800304065065005140e042e0015000040090141e8640021800c480f40180d030041002c51001c058408001c049a224030b50740010740000d20000c12036020a950b02e01a0307005103030380358111003440c0c0315502207120740304010b81c02001222008155601c0d86e9040740e000303680d03001c82030300a200906141588106036a40181c60300000c00030b100303518000500d0070341c00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 49825147 1250 49823897 49823903
    0x402040b0d0501080c060a030b040e0d0f0f05030105090601030b030f160e0a02040515070f020306250c0c050409050a06111e0c0304033e0301230604020901050706060807030618030c 79
    0xe038824100407072b152940306c40110780c80d1074100c0c0c24000c41030202411404140341e01c440051400050180744622070380a1320704032140940406203d031607110040d000307044c5104415070548207141d005901c224040042113190310510000c44085410000410702d002401890190035600400c0100416140c0c4180b203030041201c0c007481e41d00c50503a031605c48442c084281e00694984140018031051030886049800030880c0302e0502c2225580d039800944101d40440030241c140e4202d40c900308210304040e0410507190344100c0595840d02c1070b0b1f40e54001154000300f80401c04100208000f90b40d45800000c010000c100400e8ac2818100c2010212b6602d00c620f0000034409034514000c80d914a1201c010410000081013000f561520401c0310040d0040795480e95034400c0d0b003042170981d079640700d452000840c40009180e801055440005000c046c1d8080d01c1100d0402404101070004544603220f01c0c0d014018000c007030500c903451800c1060036110860501202e08004090040010360071036050f42d0010742c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 49826397 1250 49825147 49825151
    0x9020307051c08040b09011e08040206030a0609020301120c0602070308040b0a0c0b070305060103201e0405030703030c0501050c090d0201080403030f0231060f0507050102090402040b0d0501080c060a03 88
    0x704140015203008242e0100516140c4086400300d14880464003801e54110282e907825648008007600c14040c2d00116000b6010451100102e00542040350045a000108040110300c40c2c2c1c0e528039030300803070f40245d2003030a1942d86496507008010b44408464020140d51004088030b40c11034031812080c0c429840f548800100001d007401d801e50051190204107600310156246924200d240500074100898201740007a24010400090060703030190f0400741c0c3c598054940c1010214034005001d02440b04c1002c04c64181808005a41d980070400d000c0554441d5032452a402d03183e00d0043e003912030281401c4a091424048188075440b6002d1602d103140d02440c140c10a91241d0a05800a0200c20303030046c03090b4000035189003058500701e00d8290203440c260000c4c103000d40a502c209400c645030301801c40014400d60105880c41c0c0b2a01c0a400c009018100061910030720304001012030b0f029522000310304c04e0229035015803203450301c14580181341c41d0700907025050340840040d007503100382041e031401c0c56 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 49827647 1250 49826397 49826419
    0xc020601062c0402030103060902040506060316031805030a0903140703080a08040201090317040e060306040309060c081303030e032a041d0d03020405130902010e151306120f0902030705 81
    0x501840c0c00c882e02c014004550300d50312420004003911445074260300460a0001144050400c10212845005603510304184c00d85415022400b50141e0380c84100e0092504070b544005c9001030004016901d21030f250780c6000d174554074100c002c6120090141d8010b40120b1001c10200c0c0c40e203412181102043d2034007c1480e59144010788035413a0540014100390f03110006080120b1100004100b0303116103900c034005664441d4201555104101c03002000152221010403046008480a454940c45803084074204001c2d01d070030014107009540245d0005805080c0a60b944c2002e00800c2c4142c840c40904203c10410301008150b401c542d542d5050103240e07540c00348000d030070902c980c1c814809403000030355a0f0360414620080194005000e0680703e0802c2d0b203502d1600903a58440d040b8465810b840f001c40c1e55118804110f000564801d40010b041e00c200519220310003801c4064014000c47d8580394071030545940d0700301c21590140c6040038280d00e06143c0e1000350354001007640071510300b260320392904 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 49828897 1250 49827647 49827707
    0x6060a0201021207090807080c0604030605100b160b0c3405030c03070318080a0620030a050708011a030c0705030403020901060c0b060a2403020412080702040c02060106 74
    0x920505003840c5074440c40f5810b1010440e4044810005c46941300100c0700380546030300c00540c80303054014600da0b10140412081001a2444d040260300440381100c100303445680340032080c03242d0300c42406151402c103204a514108010b481d130260700000204031703003800c1114004800005d00056104090300c0d001208200c0b2503900000e128240c100e61190540f600e540074505030940e00d4000c080110003040c031400d0080c1000540414200403603034800010900d0b0703440e80d111000249501580900c03444d0031006107a9811501c1c0300294000c511190002a0615003103100a040e500c0603040410140344050407800c48005400030351b504001d06060300d079a900911704d403d91441c4580d6200030340050488000003010340c0c20000208000e40154820f6242e6501c02040002458050041c100203502804144280b4041102c0b40d103075884980c140145170030303101e513500400703814141b5040780e03010000100602141406d00402420385600d00007840c0d2541003a40162030004101041701030304100e0340c1846e0310303 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 49830147 1250 49828897 49828901
    0x90303020a110f03030f041404090f12020304050d050606091f050f130c02100f09020114030402040915021c0204030506060105030403020102120c0405030c0f011b050109020a260c0906060a0201 84
    0x1c0c0031070081c100e9584074040350252642c0e40081c400d00c2d81d100c40395024234405051030b002d00a00903520404418040240d40d03a06400a02d41c4003c041c110700c01400301068644601092200085c02200109003610b801d80801c50007401c0203000c110420140c043e01302d81d1070b1400c603404091302c50484070203000104801c0810421040d54a02c40801c86c10207002024007900440e84c00c2134103200100a020503c0391803d850250741059200a000880f101c8807000b521100a0103103030494801800413490022607280e098103010311204003540c0c1c41d4005005805406e881c2c843c1d21240c05151402d5003006e241d5142c0503181e80004007614180a4004005804c01d8400e50442e103510820000450345810586144002a00980601030080c0300d0031400c0d04091410a05100c0500b20581d1203c01441038080310219540e02c0400844083d900e07612100c005a80c0c0d0040355001d0886001c0c0b4940400402009a120340b44200740103030f403074204d464500d17070f181c6601c008183d1096041c1c0c0e140d640d41488a43c01c0780 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 49831397 1250 49830147 49830169
    0x210020106032001110303040c03020108090a12030507030f060303030c1b02150307020f030a0206100506030f07030209010e13051e09030901030209060d09050703050d020708071502010908041d07090303020a11 91
    0x5c4076000020405c000c1000c0b54569005480c001e0f40c071400182e442035056590785d503112001401e00c61450003151412842904190741c000c00c90b01c0c0218194a080c59294150b13242a0030071400700e80c0f101c0041c036003a03501c43c15a00c54182c6046040c1c1c111001034000c1080c510281010703a019070000070004e041c0b02c1c02040001c241c0940c900480b5965040940001c0d142c81d810341d0405215011228001141e1810406980c01007028940364921610790580540080d80031941b00350502c60070a070740b603a050303890f5070500d06003c081e81c0000c079a620300101c40462644c0c5035056060014640c0d030034480700300300000c10b960211000b800d006030b64600c2d40f80050705038003940790030422031410045017204115003c148202280d2103901154103100e00ea11050362503100a00403207200c1e503c002d6003005080d035030620348003008032180000699a201c1d0f1b01c0741c50307041d4001d80141c0c4a01e100c0c6c28501140c80c40700364003290721010381e01e0021109030541d98001e446a80c1c480d40a4568800e8400c00c40c01d941d11440481 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 49832647 1250 49831397 49831427
    0xc030f030216060b04021b0312010509041e11030f160603090b071d0d060903030506030c0312030c04030c080d1805060a05130f090902030c1903030809070b04030804030210020106032001 81
    0x5081032030081c0030140e482d4842e681d89900020127400020701424400c01950240340d00c10310085000e483c40d10142d110000c1ca400c00e556840420200100c1034405020084082000d0009480c2403920000a41e140070803660104040514100c5160003007201070700320725004001c0785400300c480c01070711042042800f11104016400b6401c040305030100080c980c400010107100c1c3d1001d01c40c6540d58810981c0300c0402a0a043e0550407070880001d2024082000755400700b81821054101500d036118006840c200b5002035405a02801c40b622115400c42c0e10840d8203031032800805e04070303801c00c13000c03c10078050614000e0038044041140300c4c0c000ca900341d103200a4011840c0340c0b4081c80d0350307121031000750190035000d038020b00580d0400840c2d401c20784d0340c4440c07200d682908110000d26560741207483c001e00070450f240c14056034202060592641008100842c001d000841d02c841c1907004101c2c40f0f0030a50344003019a0f161200410000d40703d00006041c40018000484910002d2801030b82c94107583c955003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 49833897 1250 49832647 49832677
    0x2120c0a05120c1501081906110706050118091e02040b100e18060604030b0915010803030703050129090f09040602030405010b0907080609070309050303070c030f030216060b0402 78
    0x9001d6455842c006440c3d005280000c503044096418114294080c003030058100300d401403117010341e20500c441c185034800380c42500001201c1c8400c202c50059500401c40c11a01c05849074010080f074215465000303c0402c0420082000402560318101c1a12030007124020b41014445094103558583d80300001c8050094441c1d0080c02d03050398000d003d6680d148046d0300c0f40c0010354541c1c2d4203078034950480b44600005003810703242c07909540314402100c000800344c81ca144070f128002c5408540d0446114001c0c050320000799105e0030301107809800e58038141c0181001d40304624500c0c80034161010004904000403011507a60551070300070a488444c0d11910130f0300050f118082c032041008503402144664000c0008100301c00101040000e1500142e0f13454001602207004910790745002d0540d550480c9071401d001070384003032503a92070b400c1d500102d41200120325060096001d040d001802d00308140c84514046103402d407107628100350108000e0018043c00d03074400702d40c001e0352241e5040f210221806500 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 49835147 1250 49833897 49833913
    0x3120c050604060f0e0d020304180b060a030606020c01080f190e030f090307050406291306020a0203010b012a0809030a0804060e06030f0112020a0b03070302130506070302120c0a05 79
    0x1252024011000221040301c1c40c5c0000141000030204200b51002070070b5001d14502841c0c06000003510803e00e18142c0c100d581c854410702d160361f030040100005842614080342c032505e000406030a20b0351504082d030506c001300e400c12083d50052410164000c51007011448090031907842e641c0105185102d441c003610000510540603104440500b202110032001c0b15403840d1114244001d40d03032144903071002c500b001862001c0d0a0284060081c428681841d0203007098031091600422420f84c0c1e0000c40960805c4082c4410741c1028011070f03003000b2007030800b4005222007405448840b6010913024010309041c100f02000c00c80041d0440d00a0721000341101c001341181c1c18281c80c542e229200761000301e940f034905000a400c1200a613880b4640c10550f140c43c980c030300f00b030904a5200c40a0200e9205245946c08100c034a0210007441c0544590341d401030300c80610102804070b80c6090340181d8421701c3d040c85400000303640042c10280c1401c111206a4842c0380c2481501d10f0100c004000400d24080d44030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 49836397 1250 49835147 49835153
    0x518060106090315020a0e120309030604150b04090506010909050a02030d020601170c031009030c15020c070e010b070305160c091a0402090d0803060f1e010e03060f0103120c050604 79
    0x900c101624060a1041194402d00c101d060880c8195006c02c0f01080561007059182d151201011414071142015203280c56044000641041c00071075049481c0b4080444080c1000e41600c1400d8001000b99020003030702c501ca4541d29030380c440500c507202c8025100c45540080090070f0103c0701d0034a5000c0e048850044180c403001e5114082401400145011020464098403000030300d10f008010190107002509a440c0880018102c507070016404c0c44241d03019100040c18130480f0351502090304800584801c01c602c1540d0034203034283e2008004103100300c01803003140e04840455645035814280303d03941b080d508102109105030f18001800711282404009035604031a000b06c5201440e0041c128501196282048124000d014880c1d4007c80014401c41c0019420301c000e41d0000380040100c080c000c4814005100d10002c880c1e50951000d000080852a5030010900303a0b00c4002140940f0181c54510100a1103a005101c0549031030140c2d40f4445840e4014011014240d030008160351807490242 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 49837647 1250 49836397 49836407
    0x20030108010209120a03081b120f090d02010603390b030402041d030313051c02011508010903050304110a0b0d0e0609060118020306041b090306060509010b0301090518060106 76
    0x1840d01400344100704132207201c1d00004a0402101c99140d00d0380c0d503a6880340080300340c0300a400d000d40100c200c03040101d00740c1d0503d0050418891040b03405a07100034680745010078104025078074200256810048180009101c5450200c8556100307140784c008000310301c0740d024210b075169130300c46100b812040c404605101080001d610440c02a141481119240b00c0740b94074900742c00303100d0001c076042030000c42c8040030810f0b05401f07020f0041c0200d44500002005c0d040009148000741070242c2c7d9500091018031200b03540d020010400e0074000c21035200d172510058500d12000b4001040c0e130403141c000c4050f41d5180048107025005104c8140d441d040c01c041410000c01100040c5c241600c11000058050074000559078103030760070382c2c5201c426041006012006500003038641640310f41c44501159800038404000c0340812140c0ea643d028a91640c109a0100c900c3d9411803401607941c9401440b50701110b0b42268111040313208001070b1965088441600561804002d40c5039020710790000485603880 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 49838897 1250 49837647 49837657
    0xc060209181b0307050a0c030201061e03061505011b062301050916020c0d03030e030c0706080c03010501140c03210105010f0201051e0601210f0b1012200301080102 72
    0x110442c0400c02d404801c1250082c002140d8500004034200118000a40b003128100f203d24070034000800d0460300c4504540c004021030260114100000c9010070a010150003a002c0c41c0310300500d00c81c0c8140c2000c00003010081d02008410140750070040540800c1601d034041680b90350b0002c501150440e070300d08900002a02882407074860300d00c0002150f061940040d141c4040c1c02950001c101d2034035000b0030310488031800324064007031564941c1801ca002c402400101440c00c0135502900043c1d04000000d40440b42c094514214000140014055642c2003603034800044c02103d070241d2104118000b107803452088030000c02c2c0c01340400d4035540f181590141c4850503140243c90300036080b2440d10049003221411110a15104040740c104d80c1c5e000c243e0605d01e038100b0f0701031400d81d240c4402036000014418001e03150a44003542e038141c198182c0c1013841101c24a0104880c1c010803a206248014444101112540c200c107070754130510b000d840c2030507440822042225140c29120b40e9501b021600035080 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 49840147 1250 49838897 49838911
    0xc0d08010504231f030803090f060702060c09011202041814130f02120c03030c06010306150501020a03030509011e0902040c030509060a09060207060f1b0801150c06020918 75
    0x14078900740003810040c1000034198090039248910f9035128455400350320090040c41d03c0b00c43e42d4507004004036005070b00a5100c3d03001c2d03c00400d00025003515107803070a040104100111b403c03000600c1030000d030311030440d40c0c07582091900b40d072603240e4600040c00900c02c0da4422031800f4044d150784100543c9940040a00802048158440f50388440c0341441c0710514910041140302c82084c0d5800610340504105102c0b80c50780101e440c801d9000300864515440040560b40303e6001e500100b08018403401540380c220b0f41101e0002c0280d15081c0086d50360703040d0410042c1810f4580c2d001031811642580441d148099241c40c05050140b141d401d0700c000c1c0a03080c02a0302403030a01e100810b60a020340100e43c020f4014000078019692140c14000c02806000012507030541c0801242020420702d00036510049590700c070008810310920204101c8400f070f01c04071000d10980c0c9004120601c545640303030f04402d426003071501029070a4a0420000c1c81000d102c140d014410824030402180013001d440c1c0f185c15 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 49841397 1250 49840147 49840151
    0x9062d020606040f0c0903030c050304050d0f0501061d060603062e17011a0304050a06020d0204080c01030b060301050f0609040203070e1302090603061c0b0405031905030103050601030f080c0d08010504 88
    0x7036894500d4191617030a41c2040c082042c903c1c0400009104a0071401064024001e07030b0704003a00e40340051645071014034242c0d1381c00e1203110850180302c02071103440001c002500c0350f4000c0e040007003060180810010b20162003401c1c048000b417a40d880d030381d80c0000380c290010302c607400b0a5108581203c0481d044103202e030010f400500700c6105042c1002001c1d05a5014400d42c524428501032074034842c0d03200520498080c0205a0721100180d031600103800e803c804540701503111400c0c0032000d481e19076040c6c00d0b6410541000300c0c9000700d03200d900450341540c009881040c4003181c208082a45482480c01140c0c10901c00001c02c603440b42c0c06410b1108481c07080746d084034204445c55419050f07001e94401c0a612007000c0001c038265191101c0503012005001d45c4281100015031184a130f400707812241940c1c030390000a402c03159011030181a00740812142461401c1d5415502e5031580c580701400020400020829844d051000702403ea842d088951001c9449442065400814148080c400d081c0114 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 49842647 1250 49841397 49841411
    0x3100e030d060501030e070e0403021204080706120209090f060301021c02040602010b03030c0d0327030c06060b040810110906040303020c090c19030902040e07030c05150a09062d02060604 82
    0x4d8424001ea4072107145500003450b00c0350420454040203200a8811400e500c00c054890003505c9601016200030840c00003d807910714a440000b502e202d414404a0030304c0c40c03040103d80c6556548524a94019907420f5103003225540d00c2d404240240b1852500e200c540d030403a400d1010040044d0010700c181c803860b60007408140c90b0242410340c2c03401605e000e83e01c16044004006400c40c400e61004035508c8110004800c0c040c441c004c412030343e05203240b00760009403a8440010501c0741c036028031001041c190b4401c515040c900300d031b01c507200c4001c8481c00e19515292001d6594000300c41081d102d52940c020902d0750749a0341ca00c2c010750b5070782806559600402d40b041c00180d124038000c059881c2462244845410400c44110440003000c45060481e07115548000c01800908200401405181b14569940c1d02ca0300342070030410404002c0a981d451640308100d5080b8650380a0484000c445650415206108010102107003002002070f03000340303202d4207072803070340390a03500196150003108151001c02480d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 49843897 1250 49842647 49842649
    0x40b03120304150b030307060b040605060403030c050706020601060e061309060b07050607020c010c1211011b122f0c031c050609040c14180c0301030309210201030b03100e030d0605 79
    0x15850104c2d003164160401e1001501150480e04146018280140005449521400010041e8000d600182d0004a00b017074001c00300141040325801505880c00144480e45c98010010420411107454501654011401110000b04c00d0601070240155507010b004a0ba1944203803402500030303800a403042d01c03904000c201c0860010807004600e040695170a5a64000790b100e05c0500d42803000c2d21000c00142e60a9081500b6083c85544401000b40840403108203200c04020b084148c60031005403035030315185214150340400481c00b0106000b40c0907a00a40c80002c80c2c1029902815088083c24040025441031042400e0100700d0000e40e40c8008000544400090150b00e40b0f0856000744107500f242c6081c048100c01030600910082e004000105910921050440d40703403058aa201c04604007100501c00c040c0c0100800707015041002c0700950410300111104014180f2890190505640302c072160051380701441441c4480c807202c80c0c14405003070342130115070ba07961018580c00c3d00d00f40b0b840342c00315407 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 49845147 1250 49843897 49843901
    0x10807030204031502070305090d062003060a060315170304050108130507030204020c01090f050c01020607080f0106030504030302070204020307080a0b060f090603070314010602070617010503030a0e040b0312030415 94
    0x40c1ca4204002d44001c01500340140006d50001000b43c00b489000e105131440e036503801202c2c1c8162880340f01c01042e8200c40c2e403010310000341032842e0035090910038000c0081c2c80e200e0780b06600c11a6150324010030103422070062903000c900903420800c40018243c0780c3d4460740000100400444000781d0390409039641395184070802e280400b4000b403e40d04201b0040015140c55005052217a0000e800081d0801c81c80e03079041d1000d8180901100c0070b4003c000c03801c0c40b540e014007005034030018604104829146c0300c0319440b02c001c0140211030034156200301003020315200c0d07419100c15507800360045540e401c100030080c10202d81203e11094007030602c090341c030b81414010242c9901c18500440541032241080c1001801d4100030107203c201661f030003e0001400504180134020401d503000f4111150420308000c0c50509017058104d81e404600c1c00420240e10000100c402d101c00505c0d069407034004050005020380381c1c120840b81e261085201e411900c0c4540c400850181c2d105424a60710355882c1c01322042 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 49846397 1250 49845147 49845149
    0xf1009060b09090403141b070b0a02070306230f0906010504021903021b0105010303050307030e0601060e0d0302100c050a030e060609060618090403170f040b011a04050607060b010807030204 83
    0x142961007440070b08000d040c18006550818400e080650b03999050085010300364105524980d80c82401e1201102410070910942c00036000c0344005900c1c241392000d010317695000ca484010710083d9a619552560a0030184103a00c0410b0117a20708010f08003000906c8201100759590500780c003800000003440d280901c22a0303081c01c0d1a444400b0803c140000540080d00074000080d50081006d000d240c0d050030a20909028500c2915059181d05001c50004d0803034100c943c0d03104d455840b40c4014865103401c1500011454811542c41710600c8261500700d00b8000301c0b00d40e0401036030170145003480030703a040006001024074a941c100054180002e040303646d11002c0e00c0746504218054086511400d28400a10030004000644004d0300c80140114000c03800803601039001030320141d04a100c0040c60350308107805c0f2104090415030b5080c03584a1018040c01807041d010385503222044031404007001c40a55004000050241e511601a401c06501a0040900103400144450005030b040e0380280300f520 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 49847647 1250 49846397 49846409
    0xc08010f140a030204020a08160908030403080d02130303020d020c0402040e1b0f070c0306060503030c0d111509070f0e01060c0201030902040e010203071d0a030506060918060f100906 80
    0x21500352600d1030a03400381e04056611078000303000c0140800503071038600080404c034501d666111028034066102e94512020030480d48204152202d04008a200c000252816280c000c0c000e1075031154010301450080c454515004254016500000181500841c03030b810340355015001d8910701d10302002080124452070084900302c4030360402284950811401c01c0300c21191050006203007802100c0520742d03a400581c0c084800b00c012030024410003990303003d00e100405040d001507080110418191361609580e0840701c042140f0721207a12900c01c81000010078410281d911403169003082c09030288c0300c2d50f45000f25000f0300d41c5510002000001c41c034100e4103c510a55034104000e00c240c0c0110040d006200d826a405a00d81a0030345015a00388000c40c083c0805440d41800030224090038003203a580e18110324424900441c040003c201c01241040d40300c4030842c0e464009076035000c5213071003091b10944e8541652040404010030380b43c0c0030581501800c2d5101d20710150544d00d800420586078580582c03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 49848897 1250 49847647 49847669
    0xb09010813021507060203100b12070e060d0c030207020405090a020307030f020301020714010207030908010216152003090c09040f12120c02030909060d08030f10050907050309010c0801 81
    0x1506840c025000c00901c81e10040c215460541e030024948090740012a06403006a4000b050100b051481c410000040148401e82e03402d01c0b4491240c04075040b4020301e0301c002d00c40100e0100c803480d960001200d003a40101c400070881d514090200500a4200360b0b03040303004034900804100c4801d000513640203c140e0007402460110300b10398030302c200c2040aa000b2601903409002003c006840782240c80b6025845400040e111486410010000c0c42d09a04c0560140d00c1040107203c210841c50381480300c603400940c1f04124040742e040c40c8004011180c0b02d00c80d03060000342c008001c100040e000b035000f1200c410495281211070710401c50038a0301900c00401d94164444068006003602090b4039191710709061255410380c07036250301c00c191120341480d000140c1000030701c1000e9261900f0074a802031005d4903400b03c06001c6965100c0c040c84050440001c213240c080001d220303038a01041c901b01810000d4880030441c1829034001c1d050340c00948010b280f6500706900841d40d14821440320b81294000154 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 49850147 1250 49848897 49848901
    0x1a0603040b04021302070b0f1f080d03110c070303020c1905090a090318080c01020d030b03120702060c0a0605041502030402100e0a0f080703061d0c06090103141603060b090108 77
    0x20440c4c8003820444680a180c2c09000020128102852141c0305040348480b840e0240341c403000c9400c00c0c2010300e40418040050210520041c1000141c1c3d030502e0314141030000e0100240c000340041401180002c20407840385e150007004045c1e0101c0c9001c0318040a4440403049035070015113160f4540c0c90b0260719045500700c00000e2168001380c1220341c1c040d0090400007240c3e82c031010b080d2807208a913002081d00c2e501c20003040c1c9565a040100106c10411450204040002e600019480e801492104130601202180b0300b4195a505001c8422450002c0111014840300d40340410160104440135204207020f01c1c04201e6080d194001c83e4403d9a0040550140840c0400161203a0b8289101680c0181e04100041035040001c021070b009402c1413002081e80900c1c5162000540e035040c03030462041c03e00c050810b80000b0000074081e0b01c000d800c5503000d07282e410070340049000344003807945803040034149402c1c4248909141000400ca6000c0e507400c1c44865151103840c100c0e4031407801e4190005d002100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 49851397 1250 49850147 49850149
    0xe0a0b211513050105150111010b03070506030601021204120c0b0909041b08011a100f0f081b0313030306060302030c09040209060403080309030307030506090103080304060b04060305010f1a0603040b0402 89
    0xd049603001c10108981410500541c59803800c5800440b40c01c2a01b00c042c844028503581c0040c2c24140002c0700100034014900704031301181e2100c0840c403900d0701843c00800454001c1c1e009002e08490501079081d07150715242d5034407172071070b50540402d41920440c0501c03802181c1507038000c0803220141d038050105201c640f01d517514103080b5124200c0d044842480311001040c1120207000f400500e0000e000039460403043d8504000d41d54601180c411b05204506d00b0104446030041c04c800e188401a04010669994408584d14044000b10200c1800b0324000704100807e1003803002c00300a10b029642c00c000c80c1d038684600b40c0c201d205c140c4d180c41c0700c6403080c4200400703031400d90020200c864000d0445404d20713030781c1d03654402540c0050b00c4440050700302204000d00365a2505c641980071400701c1d13101c40994556210748100b440302901c06054540c1b1502e0028040c1c8994104400860307000008000c113003d0f00181038000c0450240d509100040791000350a50b1906c9c9040d00e0250303801800e90a00d5454540c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 49852647 1250 49851397 49851433
    0x1501080706140702030114070207030c08010507090501080705090301061206050711030f0a020f0a0305040513140604020705010912081923060a09090f1a040507030b0601090e0a0b21 79
    0x95012a03142d9294071440d42c0f0360311f09495650040e40c00c1d400409600703095161581e141c1d82e1507040030425070b140804001603941c2c8603007040c0443c0d4007820004000e8a03080c0302143d40d0b02ca02040240c00d50700301f1600044030300446d44241e44550003140200302c0754444a5040300c912080a03440605c982c41801105030a540250003040e10f00c1c0c09004440d88142564410b03420055220f000380c0c0850383c0401e0800850812043d510040700c85440200500e5403a0010034140b0301c0090080d5006a5021842c00d003000025400fa0341a00d8200c60b40c2920748007100c5004000010464502c2a0214185030215802403030b4003440c0e5a041c2852401e00390300c4800036503d0300121009000c203034010f40a01c0d0000b020041c43c8101840309004020601c0204514201808030b5082100c001c3e001d101100c00b08408104041140c0080d250700955403482900d402d030040340d011100ba004200740c1c11403103050008517800350f071080b160f0200c181c0e02900c40c554880e000080f008400b4503c800345402c01006145028008 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 49853897 1250 49852647 49852657
    0xc17120f060f0a06051b010e010e070807060203030106030908091315120b010b0a09050604080705040c05090105182205010305060c0c070b0a03020d06140906040b0f0906040209040e150108070614 85
    0xf04081b040701c0e103242212242035800c5088040ca00b030f50b580d007400302c400380103200b400d019040c405d0040c901c070780c07a0510080d5248014410442056582c1c40b0a2080112842c205c0f03290380001840c001025650780031707450040010070b05c6122650600040087c0070301c01d902c8452200c0c2d800c60b420103603981c6021482c030b503c0d600c20840441004000940802e0682c0c400c4060300140c051074000f404c12600b014140400c507018445108240801401450400e0ba845400c454100000c54905d0700041c9100340895104100030410304080050501006c51482d1b00358031240c1242d0082003141d0841c0c51f41c0084d42101d110b91500121290000f0304240032003244e25000382442d070042e140042c078140c0c49004000c101d51040c2c0103490000360405081c01980303020104d80ba0099400c40d02013284891880020f640c40c800500341600401d101c1e4000340c0c00e65181d6043d21003c42e4041e00c2400301480c200c1000da05c990364209036506118061001041000300001e01d402035036260f0b00c8007105450380c400080300c16081 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 49855147 1250 49853897 49853917
    0xe040203010902030d05040e011e05010e03070302040c03020903121e1b1005090c0406050a090903030f02030c0403050d0804020105030105040504230c030106060302070f030c17120f060f0a0605 84
    0x25103580100513102003103a0509101c0075075030f8507200c6003000c0241e001c6c0001a4004904019003030741700401c0c6041001520f01f160401d003080703210f11000d5404641040c1d030a6001a621525107201086000d8050b001440d29520880a031425461540d480001c2030107200744802034842030036140000c0d401c540000700740582010340003e4600c0080741426203132180c6950035144903500d5806010b00c0c1c1c4410040c0e00c107902c02c110380034401a410140071072135200b940c1c490f402055031102034110526000381e115100905861400707660b42d00d001c116201481c2c0c02071204884510821460141c0b03107100b6056035016540c140c1da50307840c40e4030b8101000003404000d08241c4007048200341c5030f20203076205906440c5000c1008060700c50a03030044101421182182c6c4840e09040c0100081400194800c845101041c0d15041c50b4210181504020040303040007030b068410300e00d00242841070345c00030355481c92040112a442d80074a581744424400005640c00d12540c00c210000d1007446090701550161121000f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 49856397 1250 49855147 49855151
    0x12030b06161b080607080a020a050f0414030c0604030804030b0601030f0c0810121a0c130308030a0c140a0c05120403031808071a0a02070906060e190803040e04020301 73
    0x1c954922100c4500340010100c0b4a4034841000005100c035001c0c40d20700509503a0080c1c01140740080028088a100400386842103900140d090030050203482620fa003100ca00300516101c545800c0e8000151201c00d040e80d12901c2100e040d48c1c900e03d01041200c0a580c0d0191203d401d040c696a1003003040d5034050300b0315062540706c400c4c541d0484028440e821101c5800d6541032000d0a1100d5950003101058015402c041d02000420002c541c075800d070800c405111203a0f900c01d0780e4a0001c50000b034010411103101c1c00d59054400006d010642c00910302425540408205400c040002521540084400f1007960041442044aa980941c081d41540350084c000e40b207000e41d803810f0303800d55030f0b100750011030100e80041030030360003c2d10000c2c0300d030702600c03003603000f41483d500b8090240c0704600314418480d036030000092800c40652081c420b010040543c44014001243c440345c0c054540104101c40a02680c000f1502c000c030008a001103004994500020f14501410b00c02056140c0400500a81e0159 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 49857647 1250 49856397 49856407
    0xa0303020a170c03100509090a020f04060503030c0d020601060c0213090f06020318010605030c0307050d080705010524030c0a150507050a0b01030317071b0615090f0c050712030b06 79
    0x80305907554910580f401d0202ea83e481c50241c038191881480b6401075400f91340c001041040602c030001d0b814018035011595081004081d900003006001150001c0307405000215258001507000200e02501003071030340a0f903800760f0302c96104845400840c24041d43c4505032502c4088105180c1e401040c000d40240b4101c10800b500f078540200303030381c4181e5060428600d084205001007100784515005088100c01074988214010000b9a8074a03040c00703030070704c2009401000000c02014004641842d6031080007805070b440d000c0c400300300303446164500d000b03403030280c1c0c80814807840e01142540d5040c00c01010400207a0802810b0308600400405d52014400e007040000c0104a0404c03411071002c0c45101e2181d203644c11498000c000140f1000159201003569040c1b102407a00500010710150b051041400fa92000d802c00d80040c010343d40040c6002ea100c0d02c80820010340d2034101004442503050180710100718903008441c144641c01006e0100002da02aa030080e074030907000715a403001c000302158204 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 49858897 1250 49857647 49857677
    0x301060809210c0d09050a050f0111010f060302090c09010c060c020f03070c0f06080c16060f0207060b10050a080a09080903151504060510080414160305060109050601020a0303020a 79
    0x1244070005450302d000008030700b48926103810130020f440f030b00051826003451850709021030441c0486010b490301c80c2c10745011592090344a1b41c1416410a001340c000c3c03104031114040752006203c240000e034054103030a400180b03d080707100708491140c001a500c2182410154442c10010480316640c407085009107080f450300403030104054400280210000c00d50a03117003181841403281191b00a200b801118000c01c031010030072a042d140440c0c400301451010303131114905a80204911010612030600c045200e60500c80d031507100d400320a60594920081031040c5c4026252070060f4a0003900003050040004c2c1c81e0302854215480d103511440180d81001d6800001900705a54041a000c048012000300012800d03040943c00d5031076006c3d1400c0040905100210f0300d0218003002d0942409800b802040030841d90400240c2045885000d403403002c1c2441001c191084883e11040c1c1e0907100d24000407c4415181c85558040c04c0c0c16001000c60405541d001e038040c0d0010400401400480d400c06850 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 49860147 1250 49858897 49858933
    0x10f1718101a1c0303050601020709020c010b0306090606130905120c03030a0b041103060f210f0114010602071a070c090b01020d020f0d03180f050307050706020c060301060809 77
    0x1039211000004614488022a200d00040d00c0350880c2e4410381c624202104055040f0980e540603a42514022a441c0d070f60b480141d15120195106000300c91000444d5511920190310207111003030b044003660040d441d0700b641b0b103503100c006903081c039408210400d0011510455606c002c3c442446801558540000e40280d10000d4100310000055908004200300e0b10701680d00c10b4154607207084904004c4694803110b080818000240401d005c1c48100c0d2074403069664406040c0707008004440104101815121440c0e16140d505c3d521102e0303903081500ea030b80c1060810b003403541030b90704660003442810300e40003010360750640e0440c4218054208011610210700700d40c440102400c0342c281c0c0415442c08103400240703030205460102045410421460300440d402107075208410341503203000700b808051416584034a80d0440070042018400c04000e804114000c4050701c44940680b00740e811141d40c0d0300f026621001070102003580303c0700810050050070302030180c098102d0480011a00d6420a040300000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 49861397 1250 49860147 49860163
    0x160303110a0504050a0e070203070308091e0d0e0a0e07030b060c06070c12050703081b043503070804050603040609020d030908210301030f030224060a05010f1718 71
    0xc00100009414002802c205e48100014002c000d295541d61400e00c0d00251640603e070401001c001c501c0011800042003041110100b020400c4500881508450410394a41603040c1840204003071a107280c9062806100c044200c840c43e00b07011407660b1f42c080d1300301c000700307207181c5402c0d0301a10a00009040c081d0400100e0302c00c000c99210301c4070065039400c1c003603291140c03501548108007040002d40e0000346d01402190f000940d040c03002c02d5043d84952042c8150041d40c0000300701036621480d8513820b407440b21140e031801c40c2c5130340d0402201041c82c20180c1c80c1d00c030b1000041c02e50b8000304010001d505101c001198803d000e00d400040000c4c0303a9002902070001a20194001a4070a0081c0310304202071062001d071000b0000303510310b40070310100070708540c0c081484050210481c4815400c10301d0300a0181142064800403040041c030003c14400398031000a5034024090f4079400070209503035000300307580044c800241d01d6100483c0080032007071a034104000c107c0c0108540080458200c0303c410031403c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 49862647 1250 49861397 49861417
    0x2a07080c0409050a0303050702120c070e0604091707020604090603030e03010b100c11040207080f0a0f02010903050313020f040203090c090a11040b0f042619030516030311 75
    0x50151810024614040141414510a62601099400080000801c4807080b981410b020500d550744141c103a040401d81c0c000c0400005e000104044100300c040780c443d041c0c1e03519000d84481500c075035003800100ea034113400042c0980c44010900d5900209140039111981c80140850310301a220828181600c009600442c040b0350303c07055881c00c51400703018803040a202a02c106400038100d1000a1104140140150034080d014591542d6900c45804550150760001c01a0b651f03696840014600d9030f00c056040000540c90b01100d06146206010700b0801541550300c0b6400c40d22122103101e9130342000c04040340c1c8241c2001803644c0a49481c0003461180c00310310041e0646850344001c0c440e1000005005032135842c07a00c00c00700b5030041c11030190b4041d00c8081568a445110400040788644a5504a0040e500701d09185070108078040c452808141c0b0f179101522201140070710485a159290702e40240421003c3c4410111000d0800054164900030301c0c01280c0e266141d1120140340d4440f0b8404 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 49863897 1250 49862647 49862653
    0x3120e03250e10271802030615040902100801060f030e030a0509060c060a020310050a08120f0c01090f140309090103080a02030403021302030a0c050a08160c0b090d1d03070b2a 77
    0x40c131441d099501ca000598500b0800b00c4c0901401540000d0700e07244014003400708408200306202c1c6540341d40c1d02c41d50015a014102c1d5080030080310307010303296403070900c520400644012160505640300f030040740a02d080d0b60008508000407408203403483d40001e0352240c0c110340240020034044804028960140078010780050b50303400d04074065035241e802600b080380184800030040010748400101c1e141b03840b07000010a0740300e0b1003a0900c50007500c40d00c171000d0a01d40c01e01108100340031102040c800c8281c80b608211301d03007000302d00d00e407038aa004619416602940c124010000720304280010416801140705591400740c0707035400110201c500300800020345502004110340f900c101c1c4912a031302c068504280e401c094000340c00812095008002c00c0d100d0703005018060b0264003401040c6c02d0942e220070040300614044081e2a070701d400c072200c0680011040c540252040d1040b1024400c07483c0d02502a02500713050003900983c6038080d01d80352141c00340e260003001c5130038000380b58070017041040c0000e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 49865147 1250 49863897 49863959
    0x60c0f02150d02031f05010c0302120703030212040510050618072115050f090910020f070c06030c0210060602070302090405030f03130308010503070e010e0403030603120e03250e10 79
    0x40b018901d10140c0000d4140008d18111001181d0002074601800c0056880155501240e1404030060700605480c0c221038221031003032108010000c600c41d0710030880d501c420040c0780d85110801a071099800101c05482a1040100d10210311403c400341840d2000320380041c2400d00b019a1504440d01660b03018554854a01c2c18001e500e001c0520501c210b0003242c14101604200f0945611503454039051a201a40000c1a0543d0030380c400c2640d00003038028000b4481c2e1035a0303c00c09000392801da286480107018001da80150b10351544110001d8400c90340c028214103045500b4054400d10107001a5818801030040003255050385000358401c0d0760a5964046019203850080c113800010b800092080d000f01405104518014102c1411140140c8882c5a01c1e140c0741015001422190030151042d03940416408003140c104906592420080c0c1c221000c0c00d1340807109011882d41000300b108030800141007001300382d000340300c465002502c0400d41c880e142da440610800516200504202c203110001c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 49866397 1250 49865147 49865191
    0x21f09060e0a0e0c0715020403110910060207140a03061121060d0f030c060c030506030c040605032d03030a0c0906020a0c030201080a0f0501031a01060c0f02150d0203 73
    0x303104460401c055403121191414014680745183e001811a508220045100c00600074091050b0380043e10080e421580e994507428103d508009440300769006a9009010480400e02401c1d020201c13111a4054281d01c1d041c00010003011645032030090344064541c2c00440851400e129883e0644900b0451a503901c00c00e07102e1180203020785c44a2041414080d04202c49610340369021001154400090900d469030b07840c1c00c0c2c81c120b0000201511603803811070310041150b0035a00607800b541003101180c10030030f040da003000151070190103810381640000e0905044600f5074404d20800303103032040c8241d404084807520549103400841d00c04940c03c0c1c89410816805d500102d8000203059a0b202412500581f51a045011000d52000030304200500c00000c0e40c44505a20010041480c40d03824040e07941d4a01302107208041500642020b4001e2000014540d4080d80c0b003010b07825813250028201c0032494003001400720341004076000c4013504118000764000188011441101d400c0e8401007221131000c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 49867647 1250 49866397 49866407
    0x120201020d020303070c030e01050c10050a0b040207020303070605150306040303050a0b010f0203071b151206061814030c04020a030f1a0604170a0f050f210703030504021f0906 77
    0x1c0584065401c10000d02001551007044c0050960b01802c1001d03110011900407604c80c428508410407500600315005804080ca811090080030318413014070031050003004110403071041c1c840003581a8410000800040e2460f042036906c01d11a14944070122088008203044c140101c0c0d0480020343e6402c1001841c1c4284c0c032504840b00d60a2814440c5064a010003954074880ca21010b0050800c4811030205817801d032100c54003a000c2981d028103030704202c4001611030306040007030760712460501e540840c0843c420345001c005174054031111031046286c2300d452244107a40c14200340d0980144000740c000340d03c50303000074001d040d01d88d54005256008003841c00708a0380ca0070b030181140309041307443e4003465842e0003d4030166800e030091010001003040f04e0b60f00c0c00700c82e207034020000c0815070300803800c1c8079001c20b28210a07401c48055408a00751000817101000e81c40b01c05480b4540140710030741c0424803d5000f00d51003403001c0d00c009010340c0301c1e800480c2044260300d0700400040c0c5844090110030791207 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 49868897 1250 49867647 49867663
    0xa0b030f0c0403020604030602090d0606080703031101150b13121103010b0102010902060306100e0a03050303041a0601021911090c03070207050303090603010e06010207031a16020c090408030a1512020102 89
    0x403a18042c1014250b03800104184198031016108a8010400031115500c54507a14422a4010310821865640e400a42d80b1807031580b0080d40400c40e46014440350348818040c1842c801c4558140070300b000e003402905842a04500e425403a107010200010820415080c01d00c2e4001e402580180c43d4108510109800d46580c21112411641801040c0006885100039203030029822a21840c034040707003540888400c082c030010700703502a400140000c14010b0100c000c40c00b0314054051484000902c2d413484126004c2580e01c030f40140c0c80000600074504050304080039542c85220800c214030010400159811016165000b40c510f0000500c038900d901041032000400056000e10f090510540c00101540014171413100003100b05000901142e10a100080246500c01c510a0010060080000450344100c55142034400640e2041500307600014006104640c021301a014640c0c2e603650700e540703d81020f810711108a0319071114400300b03110140050054002514074620620b00c60000900d00ba44d1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 49870147 1250 49868897 49868911
    0x2031b0711010818150a0c020703080304030804081c0b0901080c060706020c070e0403020304080601170303280f020d0501060e061917090d090b040815090a020a0b030f 73
    0x40003040c00081184422210039982401c140c9203035075071810070407440e4941d60302142007400383d200813800d458011980300780182081d50703082202e00b0b403c0c00c040c0e99800e03040c0006800341200780000340001c0e204009040d4014825294a03043c00b000603119003c2e5544910145002038540b80080880e041c840040c3d401080f5007030050002c9041c000210b00305104002e00549031a8001a80c103910250410100d0004c111021200705141350504009403290070502610f081e5000b0480002054800030102006054201c03010f14a5510340f900b04c5490303440205540705850092141481d0030310b0030f40c4900c0851205020b03000d40e803030140e500d81204891050f00b111042c0403043e00406560349990054440034409280380c0e8001e404034480a4440d8504181554100c46074042042007144011035440d1a5a0310341c0c84108020341c0781c0041044501030b40c011001140d00c0723803d61039401070704101c0307443d04400b040055400c1404c92350046007c1c4100c5400c41c3c0031011f0f0000500802000e808a1660b02c001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 49871397 1250 49870147 49870201
    0xb0a06120204021806040303120b040605010807050a020a050618070816120c0b040f05010f0806100c170d02090915010c06020d020d060303020f0c03010212130302030f040602010203 79
    0x108016540d21004030114000e4002c660106500b01d007182c5030002c8454004004002d10785887d174a282c01411020a0f0303125001d040d0070208207000f00e05047c040c4005603a416100c8400951300d001046840380c0050701c40c4c1d0114030512030340502280707040c00514010044c1c0d090310000c00301c412841e140790080c107030b2211140781e01001c02003c01c08070071403021b000c1d03510403908884450a0f41c01c210b081c01d00240c000c4608490300090000b0303a810302e0f01d01d034401c076202070b03e40c0700c000307445407005460100c400c0341c4042c0c00001090005140601c0f50f440d5080040c07184a40d96a044010b051050203174005041085070076a0000b040c00c814a070250000d6402241c90f6070008050b034000c00001c1004214080040400d500820880c072600c800383c06481c8a101e900b6410840c4560340d050081d030f41d032852141c040781d034040c0030690340141c2818002c0b1151400303143c990010b252a40c8079010041c04019105038114001480640701d5020b4103002007000f400c0703e034005a1681030500000c07190b0340100c1d0a501241c5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 49872647 1250 49871397 49871399
    0x26040503030619080706050706060509060901030b0c071a061207180507050c0f070501080606070503030f181b180906130c150306031707050a0b0c04030204180b0a06 72
    0xa1400030440768040e20503103111040085004461480d00c00c01d8001c00071902402ca00071405503401006040801e016290034803c0540c0c84052100e84c0e0402d80744d13150030050042c014004196071020541c4c100640046542c640740310303619202c500c0701e0111031402c03507090170307a0900400349010a10041800040300c043c040492400d01520803074000790030080f1680d03455400068009006009403015034420100303941c01c4c403a0840710181c440c0d4a500400c1e001c03e601c00080340380e505081d0300340c0701002d46c4000114555250f0702c07080484080c0040c41080ca045801000b42107082041c080360f11513111552280703480141000401000411311790002111400c0c520030415402130014015030460314050440c0703041c8406050040d1100c095821074000324107207414410810f03034158032510482e4010b07460402c40c1c8001ca03035000941d1050842c05480795000c81341c603d01080e1078080340c075000384841055919160b03482d80818151044d45241003112000c4000300c038180100c045555520405140c0c00304025 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 49873897 1250 49872647 49872653
    0x4030c0e07120b03070f0b07060608060702030a0c2901060206060405040308040209040c050604180e030910050f04033c0c060c030c230d030911010302071506062604 72
    0x22028101620b280c807500c0c2c0740002540c0d02c0a00108000d000c003aa480c0c1940354403490781ea00180d20101044031114580140083c01d44004a902e9014502c41e40c080c4d031500704140d40850740610900c50613524075420b50469419100c0380c0410a41c10100e03454403269562400a020781442002044180100d0601c001c01000030b41c8561841e82c0264102c03003040180e20742c0d00381104114507a8000f11782080d80028003254400407420301c00c10035105480d041c42458001118079459000305210681c202d00c980d14050b00d5540540050441c040012200a05169030307603d031031003000f0301240e0328581401c0d8068a48180902940311214640c414464032003000c4043c1d035840c0740702015210f00f00800483d074060001309841105071201003074000f01440044040010b4800d103886c00c288644441d0b21840103194142c90080c000c5066540d04200300c0c01030780c1016001907020398801c40c0c0854100341c410040701c0042c200c0e84960030182101e9920b03403410552420559028000301d88410084e01d100c0300401c000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 49875147 1250 49873897 49873907
    0x90b07080f040213090209040309080118050618030d0903030f0606050c0a080313020306040b0906180309040c141207110a0206040314191a070801060804021e060d0204030c0e07 77
    0x2c20350640c1d03540040124507010b07000809003a80002e50050610081c0802e0683c0f03d003120060b80c071014001c100d810510b684941c0112071040e0002d00300c0e000000011506116810010401750700c3e0000d40b45444000c4403841c0071100c03550000c40110307940d41036461411a0078030444000d0149428281d141c40500c407900d6584a1302c1040c0100410340c000001b480e140525524050301503400750444035036003043c0c940102000d408450b00d0a0701e22400c3e0000d04e05c00d04101580c1e0b03882402d90f02451a2174002d800740005040c25200c80024001d0f402802540110404020035241c030030350b8000012410030710001040c180c81141400c1065110040740300c00360380d80c8422142140c1d841003601340d070324580f074044134104074088a400004418020070001405050a4031498406400300d049449558240d0305441c281000e0048900203540200080d0041c10a10105901800030844119002240100003030469202c00c0d40d4000c01c0350042800c200308040c0d8a411405881c041d03440c8812894a0100184 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 49876397 1250 49875147 49875151
    0x90e0c1002010f02040b040e1501090608090c0d05010506040f060b120604090209010b031e070e01050d09060203070f02010b0a0b120a09050601090b090a0506010e040c11060a090b07080f 81
    0x84940441040030030014000d41c8010100802100c055455030b5449043d00c2c0301e5042403245e1044e80c615000004c1d00f0b01e0b00b0318a00d5414120507110154602c1c1801422221160014224080e500c00c0030b0715101c0990311000904400d81c804c0001080500e80101400305840341d0080d65110503082c101c040c040902200151600442911003484091b40c5101c001406020304410103900312141300008a64a00340c1c074010b5104542c7e20402c5444404020740d020940301c5c4c03c0342c24400180c10041510050340c8500000c2c03041c031083c1400450306110743c0d2240d4040f40e000340d0700c42011400d100b045012198081c084e4140000301222007100041c0707001008030142c40b550302442c01c04251040083c51a0000ea8444c40c4400c1e0031808440031503031501d10000003407246490161044141a002a028040c1030041031b00c1944180d45205082513030a0038000603184000ca180700740103a080302a090400c0401545100d070804101c0814904011304001d650058003410076010000c600c1e0402a440402c4042aa = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 49877647 1250 49876397 49876399
    0x20c0d0b1503030f04090506031504080301050904030309060e01060f1a0301050105090a12050307030e0d020a0603020d0204050d0b0402010323010501230315030c030705031e070e010807030c090e0c 86
    0x88090007a100000c0c114820f000c2110b640490104000c2041d00c41d651100c0d05c150000d0741150605180302c103400e10010801c807030003401013a08100511490400b03a0b55503402034800d082c085004000d40c1e03101c400b0741c1c41c02600030155a540300e02c200500b034045410f0400600b24030b000d058081c007404244017401e100500580707051180c00103688555444440f54032008000030740d00c2c0d0041100340e00d8441c2d107070b030b00404051b400100c204402c8009490b154801419081d07008158205840c50580150040d4104d410000c041c160700384400112611070250719a65148241c0c00d40d581441d0502c00582261580c2d28040e024030040c2c40709098031800291242c2c1540c0c0300b42010200c1c40c20b404244107040c1c1c01c0452010900c2004000e001007100b648808811444c412411f8032486007101080c1951940140319141e8540d10032504007010800f5410700d031003202600010350380a070b0707215083c0302c50380c100a038040310700c40c2d00ca05003c10a0240c52101c00d005001000d0b0709001c00c49924614590780e0010704095 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 49878897 1250 49877647 49877671
    0xf0f072f060703080a18051609060504020a020c09150409030302070209070c050a03080a021e09031b0109030809040b0a080d17040c09020307020c0310090507080105040c030b0408041e06020c0d0b 85
    0x301210000d0001c0854840d408002c0381d84885508d6944007115400d841038461603800c000003c1541d18142c0240c40c0d900070140c1c003d000044950081140c5000050700598035400b02d500442c02c3c540b0f542c01180343c0c0901948001da6100054411b101c65610000c20030030800c80c2e80c0c001000003d42c04107603158581d415280107a00e5440d82c0d80381100910a40d000d540455078102000c002403042c41d40600083d00c01202506e42c42c80840104103640496030740500d0000c2c410f0113003880003800700c001902d040e40c0080d100145100100c03001c51040c2846400041b42c66006c0249c0c44c41860744281c5404084800604464050034999102c0d0612659030085203000c0d60040000b4843c030f17100304001407482200030200e8400c05030700050700c0028015403c0503a442c0c055900c011810308014001d090060364004a268229451500c400940d0b000290003225681c40403c0001407250078502d520f1514020700d034520446a1422801134905000001c000d406034412000c80c07808590900426948907110b00c8078 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 49880147 1250 49878897 49878911
    0x4080706021309090203060a110405010f050d02030705090a14060a0503093a03050c161406010303030f0c0c02030c060c01090b0f0103050c150f0f072f060703080a 71
    0x10a1001c1d000d10280e00c21a031100c10300019583d00342d6081115010f0081e8141c40c06a182c070140d0805484248200c011451402c00c402c200300c5d4885c5c400342d004020b01d0301d0402e050548042a40003a681309940103000504003042c0c0304180c3c0fa210410324014000f180c2e1340c0f4042289000401e0060007589100c4091140110000d0950f20090041400d1a4410840d40d2901004001c0018405d4034000d520380c0181d104140070381440d806072040030301803810f1400450170101080c1c0d10754480038001600f1a820700802035807003100d1004120050203140f094401196103c803440111040355085480c1400300046a0141030158502081038031402d40180d0f0300c56035a1140b0030550703000d048034480052603107198400b0450003012401c0428180e074880d101b40c810703401d00c502c10400036950910303000d0b4039045d080003907030450b0031104000d00358654100c4256041180c0754480729050014226101c007040e03100e00307800780510b44040b22802015801c40d00c1d2801e02c0800d460080034132034014000d083c0c5640d2600 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 49881397 1250 49880147 49880153
    0x50a06090309180c0f020705030703020909030c030313030e040605060a03090503160308090c01030642021b041109060f040312020a110102032b0e070803041418040807 73
    0x10800107428041c0f00342c0101109224aa001018003000100002c2e40c0c01e80000c0c481d600c00300f0a0070403190020018140e042c00e42d001c11403050005040094544402c2048501d030b03a01c280007561003007160784107415501541b07040162407a01d400c12850f1040c1d04d4104140a50394464090714040050381c9000658010705147c054a144540040c03880710420541e00b0a04145e488068548510898019903554901400040d410340e8150302402c0b12100c059852001303a00c1d9254036075000440d10000088864981d02840c0c44c508940100260040c0c02c600001e0120b0600502001d030101e2040d0b4003001010007202d1810003601411442c2840b604001920300302001c2484243c50107035420160441c84014007100c080d546100984003295136040002580d0043d6001000751015015040460046032211161a8040d204035501d8411040d0366011781c4246003200700000d5020b8441e660056540310b04058007800e41300800f044031841030090b06c41c100b8049140c0c00109070842c0d8070001c1a5151507080ca = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 49882647 1250 49881397 49881407
    0x30106080609010204030c0e0601050405060a170c070b0708010501091503060801020a180602010b030a06020304020d0b07050a030f20090607200108010512070618180b0109080307050a060903 83
    0x3511081492184105105511030190f0080c070032a84a5400e02948a44e2200f5070714240e00211001400700700248020070150030114010b20404003d840d000061141e400741341900c1c1d410544040580308404604041000392982150b80c01a03a641010300d00c56140100080c642d040c10301404004030710542815500500a8010030083d0406800954684152000080c160181c21198036000c80807000300190040c0180301e582891000500034040e1208203403211006548003520490304184101e41c904003140203141e0807405828150785940c0c0c5c82001c504020262840b160034005850320304118030500c8001038082d00012013411000e1902c030302140000464900840e0f00c06010745000c95011000c1c5440c6c03071000c540d1000240c0759640181d8854003030000044140b040c02c5110f51040c0004c3c00071a00407035100c2c55184038072800c05102615201841c1541c00c00a031107400881e161070014801750b8218004002030909040110304040454680e95a206900400500310326601c5490701e040c58452 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 49883897 1250 49882647 49882649
    0xf020c2e0204080a030e0a06020613020607020d0b0405061806130515190c0504060c02130b0d0b04060506030a02060d0b1302041e050f063001060804030905010206010b18030106 77
    0x4100115210b039034808603030352516156102100029964a0284124500410510305940c02c0b40d0042c007807a0b94000703070199882e000c034105a9100100344107050050b61030100240f950b034454002c2c20003c2c1841c0c640035103400d1000d844210000c086003071901003e840007900950201d00d00c51142c14040706400c10300c4c14459001c10b1101d00003681d504006190001446864055454090400c00070b80240c0c2c0894070750240b8080d00d070015019002c030f1805031500c02c996400403d045440099400412400100c9201049804664045124040105101c0d0710f01c1801c0d440203054010b025040e40b10b60020304184a14451006070759a95010f560442e11072198032810380c11017050442d900c5071103051845804250f40108440c00111080124060500080c046060301e00682503506080c00c2c0103182a02210740303000100c046a07228641e40100d48059007160080140f903c035413107203080a050081c10a02c590300052b0565104c5001001031080d14000c60700120100c1044071503080c41c0b10002800340000f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 49885147 1250 49883897 49883983
    0x50a020702092a1e09010e04060909060e030304020108190b13021215010f03090609060f06050108010b030f040b04081308011b02010b0d020405100b030c0406030f020c 73
    0x100c0200088043c40321001d81109110000f06511003440359070703c1000e8802e0b0000b10200483c0220980c82084450014142e4041c05050500c0180301c2039000c5011078600341e021206a90725240303000c0c00c1c04150310620608500c1140618650718054002030190100580303004842401c1e40c2e80d4820951140d0f1042c3c016404c0180084406090380780c0c0d5002a421080344003c83e04000e001240d00740d988420216050075042c0c44115010291480aa0007460340003404d0b81c403582c480d83c18000180e030a02c01c0000c03c0b100360800182007030816000420000058028002c044802c0041c041c1c0d00b444000042e500c1a4420325441895489240c070719101d004401421044003025071002c58219019007080e81241d441c50b2000c6030390200300c4070880c00c1c0c0d2084203040c0e800c0100c5000072005414180c0156038040e0741d00c02502c440c141e4440015a043d401120101071030300021605002d69a494080c5500390f1684039015818045490010740d1501088225248408103000896a010104901841000c90 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 49886397 1250 49885147 49885159
    0x9071103040e0403020c181302040510080a050102040905070f09050f060408010f1a03030703050d051305030a030b0307050604050f040f0b0621070f080106080a0204050d1a0912070303050a020702 85
    0x207052070040c0d55001c02502d22881f1790404141a5041c0c04003116141c821181c0780c250025441c1c0300d400b804010a8050705d04000c40c00140e001051000b4100003a0b4100d511404c00180c1e03e614004607074048032000740504d010070a94410501003107070f0001d019000d580e400c441e4050003580010006040e031140342e1007038030503508000b064100000d160307001c60322802a507040300d00c00e42070310020152070b48511640240403945c10701c94a000850343c0d5200a1340309110300707200c0c40a040360380c131010300c0d58124200d001d00180d1100c911121a080038841c0c00c00030081551294149403c00000400c0c0c0c01600d44001d0095994200b01c3c641d6841e182c101c00145600501595611b03059240310710f9103a040031404500b20309424011460152107604000e04840103035840d00c40310390815100701c0c0c03802e0b00501161200d0f40c0a10005ca26952182c01149103107100700303045844443c600c03c007041281c0d00280b00c020160040f42146480e0781400c070031100302e25414030f0b00140c19600c440200c4001e002e80b0b00040e410007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 49887647 1250 49886397 49886401
    0x9060507030b03060919030e0312040308070c060806010e0603070306031407140f0319030c02150307020105090c0a0b130e090309011403011d0a140c0a030606030b09071103040e 77
    0x790141c1c0901890807082c0e0985a903039450004403940c03124800c072101101e0300213000c00b202007171060030b800f215200e0003002d032115245512030445258000d0340041c0c4410304000740d45010019080c1d401c10042c0740908001c44d49140580001c0c2050400c0103105015500001c0020700c8103100ea40705034041c40e44032254100c0320141280040e91130410b405918621201061008141d103010401c030f8000b02da000340104a040080000cd0040ca115680110140150f43c41300c0c000581e5045c00c05244140d2080400361a4940368034000e0075a100981444d0554000f08041d20710303a01c5104046064890070740c00399070345001040b202030004449501c03240300c02c4410400e01c0001341010000f000e41500036a00d152882c4446e04041059100078400c1c0c4140e0340500907002901c4030b00442c0c0c264012110440010300c55501f0b040c481c020308044810900148002403040521a0141300340c0300900402d1404200200d05c6601003050910003a0290040c0100c4020010409808000f202e0107032070008403081c224 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 49888897 1250 49887647 49887661
    0x100507020c03071707080303040f06020f191805010e01090605090f060415030c1803030c0f05030706050103021f050301050402030901020408031201050a21020d020a091409060708060105180301090605 87
    0x814000070004ca410300403070314001000840003040d1f031301640d08503134007100c0310110b80e0710040251b00090509408040c203004060302a9010022a081c5000070384550942091400e80c60b0301490072500200d0500485034241d000990b8081800e405031126070909983c0c900c0d8510015002d828a101d04540c464000200460b254078480b800c90000001a1010300c02c00c240311009031503c0400e00c1d903050042c3c09054007080404c2c4190348035164a80100e8008041d4090ae0312003a055030b0113000d0a94180d600e6100400031070508421180c5a4070703211401141e020010000280144010300ca541c0c07182c0c0e000301c0454040503080d412217005000000860781d8034103850a19001e0020b0912420b8401c5845200000d0181c40c0b81074a82901007441d00a01200b200e01e07800c00059020444090380c011a4908005c1074200c00c920801c00b400c071840d000c286040c946803417820320b4004020f002004201c4450f00f840881e03600a000e641542ca8200384181e054545280441c0c01410048009850f16042c9400d20140c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 49890147 1250 49888897 49888919
    0xf071407081c05040203120307030f020301170f010c02030a080405070902120114061804020a030b0301060801060e06040207020d0b040f0506070305040203010c090302030304060e03010f0501080102090a0611100507020c0307 97
    0x401c0c0940009000405064203008040f20400c682c0070390160414000b4405143da040c00855001199080004507807450403800022a00241c000089100c03080103001d0303c0c007508000000c6e02c0b2000c800240300d160b43c00c001c001d4507802482c4640c000e104003d00030504018050100c4400303008861011500d41901454100701050300b8820144007903500c5038020907500f020303011a0341d0004001c030600c1d0300c2504207040c04004d43c00340940c1010555211410741c003503a02030007403c000f1305440e40045100f509000424a000700080d10b018400c92042041e000143c588108a264858014035486c0b40ca95450030179502c03420070040002c09038020801000030880c0c1590015009500036402007129080009069840c900b4038000030350b1641c800d000c1000058840c180305a441d50b8058000309500c60b0413401c2c002520802c0c0c001c840d003a5004a451046401d08001c50001482c1502c0e2120403002070801d11625400901c40007244a5100c10010b58803e000700420b180c95400901191030b82503554496000d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 49891397 1250 49890147 49890157
    0x1b21010921050705070e270c011d030705060901020a06020c0a030801080d120b0103060306181a1306050717070e0112110f0714060c091c0b0f07140708 66
    0xc100300400c400724a294071800c10b881543d42c1c07020007044d0150604600c201807400c01044407690900320100c810907040c903501001074200c0c2020003041c1610700480003504c048504580140c0300d40136100c0103000b03643c001885000f203900586e0034640e140f0302840100d040c030113281d401400c0180000b07450f550055001520048560080d5900fa010b1398a07041d001f6254009003039540002840034032a01807040d10759009408040b030504000601d01c0d030703e030707076039002e58401000d443d03a859a0408000144140a0004448151000310354495460f00c50000e0048405e500c801404023035680700016105c03409030055191004440c1103840542c504104000c0003a00e18403074541c00102d0b078042240031003119002c1e0b29800c404a01d40310b1b060080b1203c2801c100d410010054030031464500c0c0c0d65041e4001401518040d40020b004980d860403a60300b844124211070482079010404488070501040b601c049040d082101b082d50303598a6200e07141c044841800e0003001d40a641c00000b590300c10840e00c240101 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 49892647 1250 49891397 49891433
    0xd0809010311040f05090a0507020303071107050307030302160801020901050a030b0d0c0b031608090d0503041a0906040c0b040f06120f020406020c0102060a090f02010f020127141b210109 82
    0x11b42d583d40141040a4400a40b101e50150340180089121a4021403948070351002180450315166901e90000346880301e02d51007030740540c2003a98600000d002100e0f080025006000082d03241011060000b0040d00c2170810580800d0f50f203110032032a45d81d60507030141089030401410321195880300070074441a0f005407608621162003507a43d8802a01030306080744209900000751042400f0310f070055030a68002002100e00b038815008440d100200701d211240600d0040c00100110f1900d442e224680680320b4000c46400b000500c410400c425071041c109054a03070a16112401b08000310001002d459040c0481c50745500115001c40e00c00da00141252401209a080314060303103400b42040c04454041c080600400001d0b00c04c0360255002d42000345a0134035500c000140788056803644c000c1ca550f034954881959402d0581181809010100c2032502c100c3c01001d01601d4102041d40d1100070480c03480300340500f44d1000c80d07900d95a50300c0944c41010b0401d100030712002000d464000781d14182d00d2082 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 49893897 1250 49892647 49892659
    0x10b040603061b090506030c090d08030a050603100e10020c0c030a050c040b091308030613050c030a110a020a02010e06040b030a06030b07050c030307080a0603020d15050705090d0809010311040f05 86
    0xc3d149582c880d4540108a9801500c01c0e45552680b0300e0780d2401d540032441050f0000c40120706d030000101c000c0019440361015100000c3c160802000301410000320040005000b8105001000700c6000070842d0381c00400500300040e40e600c6406001428042884103499140c0071340c104140c280000407803060009403044404012005030141001015281568040000308088185a0001322004001c5801440040100c9200c80c2d6072654442500d804540d0544450400700034421025054051a0000c1c20304d088a2420152810702c000c0d5590104103002c0d0400c03551308002c090680351613044401809140c641c65650b8030748200c4c014060720f0548822100d82501c00001280307a0710940903100066098005503245032104e02c0c0c11168800c02504903659039948400000041e0b581d001a06013961081d01c0c4845007048912000c000c60b6030040540d003e011040101180716901c0c411000000b1b9404050503840340c42141c0105d0080440085069840000280200c2c024405003544400c0340c60413604 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 49895147 1250 49893897 49893941
    0x114010602010c020109030203041a0702150705010c170417041d01140103060e0703020d06090e0c03150601020c04090c0806070903060506040c08060f0d05030d06090515010206010611010b04060306 86
    0x417400c03217402c9400a80160024001840f040700507a280c80d6440000c00c0c0820300b440c005400255000342c03445084200f43c407000461400704903081c003800c4400171160420100401d18044c2c420b041c07080080004004000c01202d504900100c030382607501508000700d1710b0520500440c1c10750498002030080200c800355030002c0450070341c0b2a0141c40141c0700440c0034840640c4034000240c01a4110310302c1103441c161540303c04222150180701d2062142c0c5000010b000412058081c98140050480000c605035101e074200011a60001610a604c4c1030076500060807008900b0030200b14002034000c2030386801101d060200d0781d68030580c6481035900400e42004203865603804c0204646000c04070390049030013803000500030300d00203603001d44440c00030b014000480142d03541d2508580c0901541000b582d5900e03420f1110310318500c58964807074142d0142070350054103000040e659400c144a40307010481200c807003a20404081d0405895000301800070300c03080391245420005400300c5200003400c1d03a03030508 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 49896397 1250 49895147 49895171
    0xd02060604061d0a0e030304030e010e191203020a02030604032006060a050d02040f050a06090e0604020d12090e0c030403030c0206040c06050c0102070b0c0702090603030a05040504180203011401060201 88
    0x81404101c8600380e61100d50030251803104640f0140041c141074a4550f109248480d0800a00080d84154800d5a4046a07aa240400502841100842240130b56400c110008042d04d1104117202038541401c8407049581181c238040b413038030340c203640001d4160140310240000c160b086080176226145101180c03c44044062041e40da03890101d40d01984002c0c007420403ca2400c000f414a203203940041c00c0401c00c4108104101c040c0c1e0750550308111601d6440c074041040c0000d40c0300f00300c020145103028154900b8079400241c0c480c07100000c09040c00400d000c0f078482150044182c68001e1030f91500340b100d070340780001071030203aa00b01301d4040d00802e0420f030000484074400320300e02d032045130b0011942029508004044810b90803404070040b466500300414000b06080300c0c8602d1181c41601c180d1f40c2c0e1241244107110500101405207030081c0e0003404240041a0004251403d850054034000313142442d101c0c110350b0340f144055020b50154a02420606800c2203040702c64143c441d280c0090160200c140 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 49897647 1250 49896397 49896401
    0x203070b1e21090a0f230105070e0307061b020402030c070c12030201181a04080904020403080c0d09030b0c030702010207240b01050301150e041104060503010f0902070b0a09050109060e0d02060604 86
    0x8980181006071080182000486c1081c03414480404d07200c14280c0c8034007034a0203030f085650a90703441c000b1903d10784c8010040d03d01040590050181860840c01c464001b10710490f051448a10083c880c2e42c01100041840a000043e20750b183c3e084002008480e5923034581c0600124540015030042d420710f00c0c814000c02040c4400b4141c1e691015107198001d2141c0418075650002070000c40d07440b2820084840f00c5e43c3c3d18005070003c2d50007000c41a41d162028424030346402400c4c4007240078400130341e0080022a03100304080354040f11880055540b5070358017034100c0c0203114545006118119020750104a80c0380c40302d02088405518100b0131000c00381400540e4140024071400c0c0390603210b0000108241d00c60340c0d0b45034008102400c0802d01d02c1201c91000100d07003258000d90001070b00440100011009400c01074010300c04403070214034116481c2c4a10031a840002c260324404d40c0c03115138250400201b5072103401595040700040200070548032406450345a2a169000184616400700c4c007146424 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 49898897 1250 49897647 49897663
    0x150a150f090b030607080402040509010e07060509030f0f030a0c0309030609030e180c160204090c030b040c06050406090306020307180803090a06180302040c02030d02120f01120203070b1e2109 84
    0x42e0706e80314025580ea5080001614000f400c035116552039210000080c1403c10400015052a03220141c0760800c61041c0352400305160803204099004202c4190204404822550b40d0407140c50310265104030b5080c10342d680c0d402035100a000e40c1c0f6001012080c5540f00300c64008075001240d400d82290460114048003031000c1d110b504400a081207014401d0035030f0040c0900840c40980702184030380d22503c038540d440c94070303605c1562071640c440c040008002c44006000083e01c074030b04002e824a414007000070504200360000503d941e5000001c02c503c240502c0e004c2030320f402844e0f590b20603284c9070a4881c0e1240c005000c6140070b40301117180407480c5400b030134503000c200f02003d0700e034503046165808200240c10040040030031750008008284a00f00c1c07600092284024081c000c090f1400d210b800341580c03000507440504070601c0400e018006a0300031805400f102c01038410642c446025170b09900094403e800320071804500003807904007403141d42c0d590040c0364640180107240c4e6520f80c48036030303103070410 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 49900147 1250 49898897 49898911
    0x20303040209220503030a0e060108060f0c03040804050910080f1906200a0f14072301020d0c08060405012c070509060301032003030a02150a150f090b0306 68
    0x9410009140c0715070080d9010f0b0002070314111040d6000d2180c413854155072043d280c40a040d5180c914007040e0a1007004124010010400241214540501441c0050902500014078000f002010801380721544050324081c08000b050b907a81c60929528003140744510740300d00c540c035001d02004081032003004a06008080040d01201402c85105e03079840c0000e211074000022651840c038000b501e00400d25025000d1032000b0b0321002c052845141000e041e031040310280711000075040110900003045c090901030104106060441003030404a40c0b240a40960b00110b0035542c5045400641c09502a443c0c9000b443c0a840c2001203981b2201c01050100300b218071900311039036545008404621a0403c80e40c80841880d05508001d030385000150380d64001c0c1c2c41601c0e0302c003903028426220141002111081c40d4100e00540c44c1520281007c0e4481604000e0002078045030301c00030b0f0a408141d0451a1903d0090342d01c281c1035619003100c1503440e10103000342d0b69107503d003007000307425403c001483e140101c0d2 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 49901397 1250 49900147 49900159
    0x9100c14091504030503030c0d050a09031409180a09150603080f03041a01091b03050609270604030f020610080c0d0f06050405010606110a12230f0304120203030402 72
    0x402030600000c0010b60600c018010020440040424800e03c06103009116920b000383d500c0c518090524107544029048e04480c80c42e28100c14000380d0841011100b052000200540b102c10200000e560310100c840d018030481146420000b00d448641e1129404c0c600c02c41c1b035091340302d100400b51011150a408010441c41003000b14480240c00900a10303031151240a0102144450480c1c0c00c10400080e808000002e880e2090200e18034510304844051103114601000f281ca0403400280180c8005001a524031400ca800d041036954095413410845800310b0807650203052601d4000c003280f0b13090050100601a1070b0229503008207400300001218807143c0100294807200b81001000c0d0822902101d1041c03100c800718000405a018491081c2d00070341c000214a4074050307015110362645040c841081d0400000c07140050003004280e05142820310740302528100d20026102080c030b1100c0d0490b030480d40401c002a4814101000b036200e0352142c03000c0c0c442c400c401c82d42a07907a408190740081d4052 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 49902647 1250 49901397 49901407
    0x90e0610051b030a050a14090904080a03020c0a0f0203071a030a0209270702010b0402091804060207020d1101021002040e0f0c040b180f030f070303050705030405040509100c14 77
    0x1d00c5600544450500c03440103460180c1c00500c600e00e1035020000080c00704001042c004d0010b070b0402c580d40c0d0740742c1d03e80840c11300d0a0a01c40001e04039000080002340040f00202e410442140700380c0c150b800b04e088600440d0f441030075034140118000209070f002ca10920034403030b003c01e00c030b03841c0e0100e40c4803a9114246907040d41c40b83d01c4004084e4200d60101074020040c840914124558444001c1b030380120385420016a0400b01402820354402c4095140502e004000114507520b4500c0c000f15000f1000a21800e0f44c2c56624042c0064800c01401961280f515585d1b042406960714140344004400d800302d900007140c03000c1400990155118140b0f000340c080c0c00050814004c5500c045d40a0b141e04045460152141540f608540102210300101100b00c40c561041e0b013058514011001001c03001080e484040c1558142e41e00b40c0b9000080801002290200420404105031006084010411702c0140740c24001250741d0344034002c4502045081c4010040c12034010110408100d51a401c0c180c0b82c2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 49903897 1250 49902647 49902679
    0xb04050303030a0b0409020a0b0c0c090112030809151e070305102601050a02120603030c1216050604061a010c020a0506090d06050a061a0901050901030b040e010e030a090e06 76
    0x4002c82c9146031703040740c2c50740003060040c1e41d80e04000e0081d00214110946907258056424681000e00e84881d0045c05000010300c1417480b84c0c41c20b0030b1040c2d0f03d0724010031030340c2c1d408039040d09200842c520740700c200f0700c02800d0000da01c0004c05806480501c1d0b654180c00c0380c0c1c402c1e5041f17041d50015241c8251003a0f402d042401068000b0b20700c0410700e18202a03070480c04018080b803030b00710f44d4100d40640500e907002c5408011a11401d0880703401032400c600950600407045011629010f1352516002d0811000400c003034000b221340b1030301d160181c20009503106440c00742080c101802480c000001c0c0f51000080d000300720b40c0103407418064581c014080c00e9500e410f01e018806158807401c0015400015079040d0f1002800901419200d0f410440000c40ca0700c0c0b07003241d0007510003082450b42c03c1124090260100590340482942c0502209103000716801c194400481c004140321141c00009500b081204448207100000810ba4003510303683e40c001042c0e580c0541074100005441c2d17654000e00d9441001d0b48 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 49905147 1250 49903897 49903901
    0x1b0c011d0d18031e050a050606030c0609100807020a0c0602010c08010b130e07020c03010f1505060a121e1a15040303020606040507112401090209030d120618150b04050303030a 77
    0x70401003c1c0000d07075004c25880f030610740841858100e0b11a4045400c0102c64103090140080c040c5c03050303a0b214200b1035050f0024030404040c411050400010744002245136200b000608020341d0081c0701c1c06240c90303d07010020301802c000c11541d0040f52006000140c10340021045a01c40070f054910b41034141d0604107030813141040900311074118820701c3d003560a5070b9020300c01c6410000c0e0b1001d00240e00e6001691441030030b11250b100700d110701340c24040c959002d500169440d04108080704000780d0303e00d4600c0c00816600c0580c4231650902d10380b8684903003107010b804840042102c200c0e10040080c2410324400024825030000400580210700450581e061507000260043c4150400302c0e034007407012040a26122003ca200c2e03203201d80d4502c1007010440140e0700f0300e01410902509620301014000030940d11030707e941c0100100406c0703140d080300500c025031158010300b001c000030141c40240382c90030304003030001b01207041c80e4854110800074114040000701c40031200050b01840c203507a030380b40702d40e00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 49906397 1250 49905147 49905173
    0x60801120317060301021b03030103020901050607030210090203120408010b3a080d11040312020303070f0507030c0b0702030403030e04050403080105131407080a050601030c05031b0c011d0d1803 85
    0x501503400380401c401f80709812030103841e843c8442c0c00440d1250301d140100500c403003042e4407143c01580200529008a5400306e03260441002443d0080340da0080c503c00300780380001c6007c050b10b0b1a5808140460728075810341008003180400c440d040a10300034100708042070103000e0104080d4000e4501004203900480c1c130308000107801148410b092802c44508001aa01030400e10030342d04200203020320400031207040f80504451603100860031480c02c07120151980503498060014020301003003010030140702e0380e8000f5080764407034a440080c0c02c7c643c46c0a5529085404104c005c64003003801040942070500c2900c5c41503405503181a080e9107840c081c8042007544a082c0d14069440b0851900340004403070301c0c0ba01a51080e580d0b00348a103000810f45c0c0c1142d10250031241010f081002140c0c100f548401500d8015600105040e002601242010700c54441c1400c240e802c3d500300355041c00251003418501981c005040191050320809403001c907040566003050011081c000708080c000300d007080045078 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 49907647 1250 49906397 49906399
    0x102030d0b030c040906021c06030b18030702040c080108100e0309090601050c1b18040b180709050c0703140a020a030f0c1505041203020c1209010c02090a020406080112031706 77
    0x956202540b00114041c2c4609017019920b080e000181f1041c3c808268000200780e400e424001c20025055940c8c0c06200c0d80040c00303080280742c00c84100044080203008840e400d42d4000c000b0007204441c80005040c04900348100c645078000c40030041c40044190142091903a0301c00b000d1403074840c1d494100020502c026040300d04001d4280143c107000b00080112030100200364490204958401c0104042044802c07140c9482c4046581888000788004000c2a00112605506120710959024041c40c0c119982e2105c02c401d82000284241401c1c0300d8000c00c141c1d170107aa20071110120841e41c2d100940f240d42d111000690000d41540046485414000000c8103985400d920420755601c0d402c1e44a85051f40c8664031990328010301c01001070b070075001c0e034540803d41815403c2044203c801030f00c41408a40440100c0000034408025a03c60301c003450802d0782c02005005103040c4507045200a4009024100205500d03400110762034090140c043c80d0346500d43d5400203540c102946413542c41074060b08107 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 49908897 1250 49907647 49907653
    0xc0504080a200a12030f0e03100e12040509040809030703120e0a0e01050d020f030115080a0303060905040b1303030b060a030209040f0908120405120f04060f020c0102030d0b03 77
    0x1103814201031101c08a101d00070a00c2180b0140381c080801c1e204065050000c1c840c58000c4010001400740d14007180b00540c041c20f040350701802094061310b0a01084802c203a06000b402040740c1c5250090f40080e500c81461011181900a40c01c40a8154411409041d0340b02030340d5030008000586540c02491810006800c0d01e20a542d41d80e111016143c0710349000300400d1034021341d54110300305208940000c11285585074265450800030078100e0b058408041d0003020a08004689501c00350490b0f0240c030800520f040b070031039940300070740e840b0900403108500090804000040c0050580612400b441e003000f107050558a465a1052940c030120a088080c140c44014086079551204041c10100c0c00988015030340c4d180b1002003008442d5240c0d513070a1003a2400031000c01159001050750109002c940c41d9075615161130034805e2800c600344000c00c81c24900028010405200d04019104903400c40d04c40b40b009104da2101a62501502000303d40141e109000b0070710011020f1708551282e00e005815 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 49910147 1250 49908897 49908899
    0x9100b030705090d03080f09070f05060703020106050303040b0301210203060c0702180712140114060703050c070f03060b040207050624030f011b020f0d05032d0f0105030318040c0504 80
    0x8a0310404113014141c010541200030040c0c1c054120400c40e0317026040c18042c016403030524642e8490002d0303d02580340a00c1d00400c4000805000f5840b400180900404807901c9503a640000f04c00c0360300034091030060000008110409503800c41404040781c1d40100500059591540503075615004184144c1e80601c000006d804001000c40800380150400d0340c40b009078a490180e10b10076201c51150380082c0701c4040d8010007801302c2051480908840450b03c840d0f0b900e9841c1012034080c09031441b902d03124000c40c500007420004900f442811030f4490740080c80955007910400040b8010243c0203070454004500042454449641100c01d4071200500b20362840c900310013191074082c003a24812401e1f9034699501054042414901d00b004203a40300400c00c450703081403855203441031000a402800408404192000101035003490350450a03655402c1410340907222100700d2034290f80705880c0b00f546900100d45400e020044074001d03540e4101c0500c43c1c4c032000302848020110030340c0c200c0402c0020702c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 49911397 1250 49910147 49910149
    0x30602070b0412020706020a020909031c06031502030622060f08010e01060f080a1202030f0307030207020f06160219080a050d02060f060a03060b0a0f0f060e09100b03070509 76
    0x80980000d40c091092074840340741520b4101c0b03442c81031000d0318003907600550b020410700d9400110300c000d00d41d05581c5241d0390785a6035407143c42c4d03001c0c4131225400707690340c0c00c054034542c40d0540c40641180d020302048080505010015012480182d58080e0086154200501c40000303501564140f00200100040e5160380c1e140040c211076600d80007054941d448902a4000420074040c82006e003000725106040c0a10f004801959018150002031040c0034580190380b02c8d900070300907a2070185103840b2040d0b4a00e0007203c000d000b9400190300701d00c40c070300c80e94810103c1e0502d40251616101710704030488010007141c08114107440402c030240040d940b182c00120f2a45002e0100602c1148110010300213680c80110180c10088010301c1d4502842540007002281d40c0c07000d0001040340d400403400503d408440380410b5240d881d0380c000d0341a002a0711030014861840c0003034003048981d42d42e62168000700c800c04000d6a08000e4402d05a03098a03010180b243d065050011500110035080c1146400c039048 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 49912647 1250 49911397 49911401
    0x3020319060803040f090c08041e05160e0f0601020706030906020c03040f03120503070e011d0901060503010801060602030c0703030f0c0b0f04020906010206060d0b06130603080301080106050111150403090306 91
    0x1030004407643e0004a070030440110703e0380e0310201030100d4803410300040c1c4040d02e008002c5600200080c004041e04030552b04441ea40c2e812030b40949800005844d01d4000c40001e81c10821101e02c58016440350240025002c170310b48841c2c85004141c16409029958a021070440140c910343c0b40c1520741c958204103204c0c442e00100014002080d0340242100c82c02e255080150b001c8007810440002d2000070820007480c1c80c0e2218407503404d004242060703288e20240082001d200790310417900d213410a25100010ad09181c108000d18120341c3c02c10000c0c410151035060482e1030340540020160b1a034444030741480028002e8032400c080c4802031420347c0180c5415151166006015600894591081340c140400d6040c1001036a50140003800105410b0809030049201c000715902c021304103210792401308486640d01205298044139900d01480281e8503401d140d402d5500030b1140106941c80c2000c00500e6500076960b010500307188401610160500f070602d0840504014021401c11150100200005001d4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 49913897 1250 49912647 49912649
    0x15130b161208130f0c0902160b090c0a09020c0c130c02060601082412030a05030a05130305181516020901240521010e091213060302031906 61
    0x1001892003940d80c00d08051450003a000001010448040b0820030105079000440e50855445007000c0d50380050fa040a1040c0010b5410030b8551500000e0200d1405045165858841d8001d2860362881d8840e4049150ba03412100301d12038106a08841c10800c408003940a08282d000e1030003580d080e44800e40000d0780080d41c40a440480e107a0321500210b040d82c0c100082039000301d007800c113040e990400c105081c204801c4105841d00c0e4001c241c0c0324480c01d80311b0030700782403082c00e41c102181e4489255140140058004a6840040602c5d220029041e01c01e255900226141c15482d0707985866142c200050481c800c010500d60400380b0104000086240000103040207200c0300410031380c014039441080700405069105441c84c0b0442d58000034a1080911030a14244240c102580d0792040a5200040d18052140e9540b5040c8680f000145640307283c84010f01c074994220075500c0d41074601000c2d103540e02800c6600000e2002c60701c0240301050088d40255000700c04420780103a49443c0c550344030181e80c0c003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 49915147 1250 49913897 49913917
    0x30a0f06061e0306051f0c02062d03010302010503071211040905071106010f0b0c0109081201060f03050c0d0902061912060501020c030a0f0305040f030501060501140915130b 76
    0x240c90b0600010385488440360205a09034941801460b192500203203c1d010850451460208010300002082c3d005440040c1101d60107040a52034402480343c05c41c1c0ea02094100c0c2561440d0141030341003c094110444e03050341d0303050711303510300315101c6241c21245141001c0c0008800c5648101681c941441c05014200505000c44040b90502c1c205100030b15240702c205200c5050340c401c200602031140c2e43c884060965046008031a103a442620807a405400048000313415030748001100703103296000c80d4940d4165142a203a1500540c0712810440c201ca6045030004084038040c0302000d080750300f5030440c0c42c0f000d00051455042c08140303c2e50305c402604202000c40410302d600c3c00c0700500502d900810b00200400d0018122001c0143c02003512000c01600092112400d0070682c0105801b40041ea0003505001c3e204005c0c9503102d16010780200780c01d01a180c00f0a444006003005000698211046e01d200034240e13544040d02191400e00301e4203e00e4501c18000d0540d42c02040d8022030002500302800 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 49916397 1250 49915147 49915157
    0x20c07080609010f0c0c0201020705040e01021605010605040b0604030b0a1d03030f0601090501020f0303040b09011e0207020306060a03080a030b0f040c0315090501030803130618110901050609030a0206030a0f0606 93
    0x49440c0c4c203c2c125415000480301b400b5042c0b00d040090b0382c02045032811560107480106603c0c200c0c0c43d001c4c1c028820b03185c00100c100c00190484003407003815400503003685c40c251400c00499138070000f041500e00a074071004008151110000c1c8d15405940c20042c00003029031101c1d83d02840c4a440780d815030300f0031140e00c0b2071002e681781042010760313210440400078023081c00544600011030003000d440303100c010000f070308078007440d0040b4114040950010f0000c02c1502c8265406103070901e07012001e503003c550142d04c00e115400201d541d03843e20006600c1200e5108074403e180a020301b03c00d0b009041003035000742e88414451040341254a44e4050301c03070904100e42d03000503910110241c02464513000d4108800c0180b030900180000740b900c1c821a500014484661034415132180340140141000c0d042c14030414107000c01100c200010309407a0054040110707150b032001d81e00c90080c04914000c1c0710090b90f15511000c418805400e20340011a00301a4161000c1601c0c907200322040c00341c4029a2001000403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 49917647 1250 49916397 49916411
    0x210050c0d06170307030518060c070602060a0b22060302090a0b1c0327050d12030507020a11040c050c0a03020303220308011502010f0e030418050c030109020c0708060901 75
    0x71125104000141140c0360449201c840742d4111160b5a004052004082c0030002508900021040300c041d90b0416005042c142c1c2c503007540c01c00d251900d14a04c58040588500d02c0070a01d181d00c140644600c1c8a00903107810207000140c0040c65800385078001c450040e0340c1d64040400580c0320746502c0e501c1049040e0010640c618100140110601e4241082c3c03040000e04008000280d071011b20588c80b2088001c0440e80442610780d0200300c007200d6480240d002c21401440e00c1084a0800540000201500d0403c019611804140c0e100c102c1804010828071035900000d12510b440e50201481c5c19091070b049040c00130b0382207014585840c192098002d03901c003204010214075001405130199454001800e0359003150fa80c00307000c0f0351042c020b840c0070303400c0552450380c814400d40c080070401c500c01d0310500c09002400540c0d6143d60090080c09030100c4280002400c2c0318680c01850b01030004030043c01d1850f840d10391010f009400c19130003a1454000c0550010704200c0820100d0f02a0207840000100d403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 49918897 1250 49917647 49917667
    0x30e0a06051801050306060d150e07030606030b0121020a0e06070c05040c0c12080402060c012406020f060c07030309050f06070801090b10030b040b031203090105010602010506030d030902010210050c 87
    0x1410b02c0340c2d1541004402c20400030385840d84002c2e22044010b85402182a40c12211020007111550b0440c000409040d010810f040754160480c04c2180c0307541d1420000c181408004407140e2000141e1017800b420706540d03d8110108079402450700c0c0c805458a4001c0d40000000100b42d94400303001600c8a1000c24002c2c00985014440c000001595040400b8082d0455882c0803c504050380c1070400d00403500002015511030f0003c03a080c0303407101c0c00204149000800280015010300f01284d8030015411400300d8174500006824000d0300491004203640d98071000740b41400da1100d1002c40c02c0640b5080004c000030350802038989118950b8010701903038509008028540725050703200188081c00c00141c852151180ca4141c801c1078010310b8003140c9101c2500104000d08114540c05806101d040c0e8001c0516500c6409140183c048400030310551b6a6100100d0a03204207413101589500420b09085040b40640d00a0312940e206006941d03010511140385011203008407240b050101c4005000581 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 49920147 1250 49918897 49918927
    0xd0807060b040207151107021507120315050d020a0306140a05061e010302090a0e0a021b012c0708160510030504032304090903020c031605100804030e0a0605 69
    0x91507006960440c2400004c2d00ca04001840300c462103154142e03120b045005078443d40080300c200380d80140c4580c030700b102c0007440582c8d079500400d000d03a520031a06403a61b052910900600b0000c1c0343c940501d942483c2000e0810018950b40b0004a034032200f0385400200040395400785454410501c0c0c0c085009141c00d103183c0c4195030008080d07900c03a0a4200400d2480c140c4079111540d2a002840c0050319180364402003090b02d050350f00440d42200c10700c0108030018255070024005003045102c4c1c448100c032039051103030a030741c440c0c41d00850040d01c42a0b140f80b00d0117610240c440782d20380c0c107044441e00d03039944400c40e0a140780d00c0c0c00140e110030b5010003844a03042121084250603200c0c130b010032040c035090320014031402d00451800b4440301900c18407800c0d9814502a28043c5c0035807803003041041d115103030182d5a188050401c5000c2d000c0d81140b0001004030385561001c40718090f1415500905c034080894201100030021000c3c40115021044140c440b002310070701a04040c3c030b031a43c0e50201c2c82c0c90248 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 49921397 1250 49920147 49920161
    0xe060705030c03040303050a020d0e0c04061d0c090d0804030609020109080d09090e10051512070b090603180d0206040309080f0a06020906070b07030603020a0e06011d01020c0d080706 80
    0x144039042082c00000802d00d8100c90784503800d46000a03a6482d440c00c0d003001380c0714040b81d500d42581004128440c002000c03038401150311040f0350030411540c0c1c8041d8060080f9000183d403e09684050000c6d0b4042c5110005002c4e0080003010318a16000b00d0340d17034034ed640d00680c1080d03d005035580783d404115604860b020f00030b03200450041032600e08015006000610b00d0182c001d610303466290000401504020410003039101010600041c505400c0800c54190b450980b188a000441000c2c2c883c40070100b135410903118034207003452400c4006010b0000561014000100203080d20901d5040204d0520075510307810320640c0500001e08240c1801000402107402004042e08080491940035800040c840c0c02c15501c01405610380d444100010180d015510003e807041c0f514000f00124a641940040d00b42c80c804c469450380a611030b013142e40c020004541c0140400c0003050038902c400c0c4101c0c014100c4140500c1200c03201c80090000c58521000c624080f1001c0d107000c03c5801c10000d582c01060 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 49922647 1250 49921397 49921411
    0x5060910020c06070c030e0d0602030a0606090506070803060d0804120510020306010207210c0b03010602161a0c0f030f120609040302030f0a121e18200103020d0e010e06 74
    0x541400594036410743ca4401c054046400e00007602c04c50820540510468103c00c0d100a1041c1440786c003904000010b07510031950147c4c03072403800401148180c0070b0503c507810f81780040c1ca014149040c1da0354805c200d600241c01958007240c265401400210894020f0014000e98102442d0b040a0391500034901610304044103035450040c004c2010a03640004c10008648070448424000e000900e880325188040410180c8822440540070810001280041d4120b4005500300c1c0c1c501d0a000d00044035070606070107070b2401800503040c0402403c04050151003003200c0482a28140311400550910b950b014440c0500384801c08513a02d4007000f80310350450b80c441c2c01601c04a915203050354009440c0d104100391002c00d04008102d400c00e030b92003000710400240c00c0100030003040440030301055032480491980b081c02030511030458402e103010882c9004060340400c419215a04a4040803480d100c80e140050400d176007131001b1130b40c8010078081c0141c00350074040002048a05038202d5400c10344010802 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 49923897 1250 49922647 49922651
    0x2091509032a0607020f0303161b0303021005091009030207091d030322060e031e0a12020a140d060806060a061b1a250914060a02070302060705060910 66
    0x8544100000010b14021102190910750b00e45052001440038800c0c216159050307c00401c9000da03000c46890b41c410024094850901c101c0800e186105881780c81e404000d005800080d840c040000058000c51740106021090704c50000c000303102201250340500040d07006a020001c200b01084962040301c04440042c441c2c0380d082182844101c1d62031001805810446c1e8200d08080b070104d107008011240698020402e0241100442504c7e9480d080041c0002c2d50030900f0503008541e100d5407086580111940d210303160f0400041c10003800a4106480031014000d071008030501c02d211020040103030f138610801c0041d049040c4402c552402c1d00c002c000502608520704c007409078a403c14943e501d046111101c86000c40051b180441c1006d11469010500c115200e0070300400c02040d074010702601150307400c001020050091704507900211449800c54401c0651080359050a01c20018403101e002030046130251a903e50100d460ba5200440a4400390848014414422020b000141354442d1003082 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 49925147 1250 49923897 49923943
    0x6060801060f0503040b04030e0910060e060c0c0d051006080f0f010c0504092403030e0f032d0f06040f030201050606180409060b0907030902011103070507060f030209150903 76
    0x1403d1840042d1003c6c0480c000e600020341010704c1010000540280075010319098200200074075503028960281c40d0114090a0701e480c15800c048054507081c3d00044001d108503148401408140c0d81440300c103451500640160380c0b1a01418000d00c8020602600107181c03030401540c80c18202411300480100c1641400d1415100b03940c03003003c0e501950701c07170f180001d03103628030007441d000e006441c001d01c40400b0002d00d000001d1603004014000e031001c0950359004a800c0380400c140e164003004034100486a4511081120440352544192103001404200d43c030300d01040031401c0c50010704440440304200900a0841050740c207028075500010265400c500f441e8441c6040110070300301c818080d0003181d0300e10b00c01c800c2c0010b07500144101c1034007402070b003c1420646401805070088041c00e902003580c844000d40c422a00004030b40003684c1080262a0140c149881290721840e0502c020041607001c0c01610b03135542e5410050140440b080c81030350760701c44448050604042004000000c0d021003048 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 49926397 1250 49925147 49925177
    0x3240d0b01060f02160303090512060906240d05030a02070e06031902010e0d061b170c03090f070b0301061b350301030803010302090108030c0304050d03050f0d0606080106 75
    0x118192407843c10083c50444584000700d103080d4905102c0302c1d0001c001d16000003851307002210076041d00c0d0290b82007041c1d540b60001181e40c4500a80f05124250301c8800043c1c0e414007503d2084107150b015003488040b4445600c0003502c0440b03408020385450b00000384d80a2003580412100006103280001d01515140460009454001036021204455511101c1d001103a01c565103541d00090010204903140401e0306201c80105130742100807658071200081d00740540e015940442072410b443c26507400b107999284824600e034201500121940c842c3c030940030821300c0148900000380181d20307005626585814001040c2210b01001059031180c1e11404e0b001054410010219400070000c03e495150002c046002c0c01081c03130f411850b00c071100030001008010002008604a81c02121000c034180d0300c4020706920f85c4100d81040b43e0700c1c0d008120422040c1400c0b0644146c4a029091190500b1205000150940c3c012a29000f070141d45007400d0244a800c1106640902450319064614030000b407 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 49927647 1250 49926397 49926413
    0x10b0a030b1302060f0c0a02011215140a03021002030c06060d050a0b070e130f11160605060a12031707050415080907030f080309070e10030303050402041103240d 71
    0x25056142400440041400f0f540f0760300200d44001045854103907840f20955030039916259800002c80c0080d0b0004601150998a0b02540c4481c002c44020040410300d8050303190074034900d040010707400940c0c20100102503030342d08604108482d0746030080e5603079040311010b0600b0324400402180c0f00e5500004da0501181c0c0009a18584a9010352070344010f4503011015035039550194040f0764040d80d25500c01c4c1c0180440d0300301442901d00440240021b1000b0070303117040c042c002c00c010f11001d1958120210041981ca42005400290181600604030780f984251038442501c440d040c0c02160100340010803030204508090391107560340c80c00500781801e0071045082501e00c01103200c20000541e000c64030107002884410700940c0c4c010390f066207181d210314050380c0507001100c000415000710000001d9920b020507242c0c0c840c0c2c4540c4100742c003050a603036094008040103030059130029a540500b02118038540000c6d0301411480a40042548500b1708801001c030231410b6a50081504000d11000185a6 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 49928897 1250 49927647 49927651
    0x60f01050409120513050a081005010807060e010c0305091305010e071416140a060c0207060801050607150b0a090b040e0a0506070f020a0503040b1309021603030b0f03070801050108010b0a030b 84
    0x84d03d4421342d28040c000c8a800c0c0c210081c1c02042c2d120040e0000002d801d4400502c90380c08001c010414445a83d039a1405600c0d021184615800f00e40042d58020701c80d1301c00d12a503902e542c8241005806c000703100c80402d842d0b020b5000c1551819684034014003401c00c2000b160340c0e021660703180c00c910040503525141c0f51401031809240160400701c90010030000210358030004011424101ca138a240d09040c0100586000034408001d030040c01c0f00802e05900c1b8400140c1602e0700940320920341245070b658490010300000d0100d030015641e04426980d0366811103044010040d010002c901c046100007003104039000c0c4081140c05900c000840d00000381c0214005504c81024100800390300c070300c1d1070164200300760300400034124000040c011030010901c8025004100030b01006000c4c250321341150708101e11a8103501421245541c0f80300c070020b4400e8209a000c14406409540c1000d0000e020078504003440c3c00040041e51161700500a00344240b02e0100c035500101c400324016884d50300d071250817500c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 49930147 1250 49928897 49928933
    0x40504051b03070302040e0c090f07080105010f03181103010c090501090e0601090b0307020607080609010b07120504050414061003021e03070c120c02030706050c0c0108040203010e010e060f01050409 87
    0x141d40806421680c041c05200d009540203481480102c60000c040c949910808005920603501c02000c501603901c010ad02c917100d6965610390541e1642440c0064512101000081c000c040c0c690400380c0512400d0851000c4452007421107800d02100b01d030800d400d4800840b108001c000032003404115503a80700c00d0000c1259084526412113413180d600480b0b0b502016000b25a17107020010601c22001d47c000340c1a07201d5103c030741e101c100d5900d1314403c12015001c01e11440700451001c0c81f90f03c001c110700750700c840d21034070403424014a003542c0c406c0420107481d401402d000291203010100034940c00c101c154013079000c029240c01c500d000489030500340030010540d41c00b4641c0d000400000e045502030b864000000e500300d00400300002c0d03050001001c0d2a2400c208078001d01541c24009030260050080d1361980c0c2d41c90010b40031240401d0700440c1c44e407238020030a0b41e0543d202d089552281c4020303c542606620200054030b150f15104181c03c0711110183c1c01180a02e00d84cc80350008140c0c0040700d01c1d145c0c80c0c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 49931397 1250 49930147 49930183
    0x1020105071d0d0501060b030f0405010c0f0e09150306070207080c030a121202040b0d020a271205031e09150c0d030b040912020601061202040f15050c0d020c010e04050405 75
    0x51030071311074010446900003034044900007082c000441c0300c860407580b00c1c0344504000d020350070907502c2c119100380304440d1440c080303540e0608000e4a480c20807403059000d41a0001c0d9050a0807980000346002401d580007405601b003181d05000220b070a218808c1d0910302034004000c1440340c0c2d52801d1044055400780320400140c1720111400780c500d0f80445008100c541146a1140403403480180254400600500860341070078512580b8000e4050144580d03500400d0301001a240c000101d200080d540c1048401340000c00100060319400c140320320101904120321915440b5000503c4091592030095840718a41480754502c40f107400070f0310a004002a00d80854421071600100340130b4081c1c143c000700f250040002065156900040e20ad04850700c503a0380550850020180c402203100794001c41140302e14460b000e12940d10300341040703590940c040c640a0b240c00300c40324507241001840c604900c010b030003080301f01455603070208800040f80c4048804210382d042130b0741c54643e548030712031007409114 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 49932647 1250 49931397 49931419
    0x50109030803060d080c030c010b0a080d0c08090406090f020409060503160603110903010c02010b041503020a0b070317040f020a0501090b0316140a0309060614030a080702060702040908030601020105071d 89
    0x80c605c1e041e15001d5801c0d1040342d442c1c1d01058260303070180003c2c0007400e0050246840018062000140c070340d084404035111044034444079210407020b40d0148520582141c0c95030000201c0c0e141c0381c4500d040744144242d005844508090f2884280c9415038040c0b48030380c0c40728484803d462181d00e8900d00306c03482820001440140c0f964821803600501a400c1e905500e001d01c841c0440390190040f42011804480401200d54540304502044c4000c2c04043d40001c144c2005102c680c80d08801004d00600a0415130440c140311600c42c180b102c1e0840e421580c00c88285948411400c00032040c04c050142404e0600285062890110407800010101002581c1c0c20034011a00b50044a200c2c480342c061891352540d0750a280c030050090240c0c01000c41c0c5643c40c200e00028100300b00070300010403800060143c101c41100d40c45008180d0040c18042c0c3e480720b010054034005944900c200310400c0c1c441d4003125101d00e41500007908680e8024001010b00140d04a140304103840500380103003500c4100c484000705 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 49933897 1250 49932647 49932653
    0x6050d0312020309071503020c0601050a080d0305060607080c07080114060627030f01200901020d0507060b0a0612050a0e190f08120108070b0f0301060c050c031510050109030803060d 80
    0x4081154410040346c16140e81c41c02000340e154000b000710a141000f00e07241c903643d80f024088800034508c00ca0312190400105a4030075031081d0400394114400420507802c0009030b031200800d503031044019661550140c08100101c01c428081c10502c211903600d04100d80c90202c1c080f42c001e200e00c2c0510f100c1d00807202003001940c01c25503100700c1c1801003d070841e2524504218014000e0090310149004804458080d0307000500c00b000311009540103074054041c504c410041a9101e07001408121040d0b23031a003041c1394840e16000c003032000a000f5541c5003096121021400412240003410040c0d8241c102640040304c8075000a04491140601c00ea1000c20303040c90914a0850702c896100500349180082c4040c03002c2c541c100c405060303800c0034040c2c07100581c0e00d600348041351150b1020080702e0101880100500340c020302050007500e008078242d500030301901000a0420010080c00c0305481d00d010140590f02c66920a1040500b000b800c0c8900f50508540320b8400501004000a01c6803241000c01420 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 49935147 1250 49933897 49933903
    0x509130e010f0507020f0304030c091d030d0501091a03070b0a110708010501031703010f050931030e04150510020a05070f030203010c05090105070f05030f07110406050d0312020309 79
    0xc03410080002c014210710390302c8200207000c00b601c1040062242c0c549081c84d091010007207504032a803280142c0c2015240c4031004001e02840d0309848008584e54803c5c3c1c3d220002032004090b004040a0300244c03640c1428810780072940d010603145039442134044030310079507140083c3d284262220f440480782c54210f000c8007100c4c00e185c0b00c0010f01b80c500a611000a281e4415000300d4140c9120705d5600c0040c628642000500b400b0911404800301c03c80c0c03004001c2410030300d8100750005400d02000a07198021030701c0d04070b94000b07281903c100a149094200c24151700481c0a200a1002c450500020481d95181850b0046600905102d40800c06203050154001c000d2074200b40c2d4820b0559a4043d600c003440407400801c1d02c410b078003070350800300c11070106841407040703c0046905864035824096030361a210310010301403404440310f11017000500c5103105000003605403240701d89928500d40c007203d400d0006440c0680d01203030085d003006280400203a0010f18009400a070400016240d80c1d60703007201d9107 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 49936397 1250 49935147 49935161
    0x6050a18092306030102030c1806070204050c0a080601020304080c0613032306070507020d0f020a0305120d0605030106120209090c040c031b02150c070303060b0307020a02031507050913 81
    0x1140d51802e0310a0959200e02c034000048400300c842d00300741980d603040626084c0d20040360480c08820b4104040050020643d25400d00380d1005885681001c0e0303194003040444074151202c4030519800300365440415030052030790303611440c03c2c4051030801d4a0191100e03a0f80030341c000102e210300400b26146401035180711804000f9074010810b140004140a81240c800d0448480c200c0c60740584000200054090030854041540c081c16015103015113880d00b20a149142030102d900c540405030020108200300103070380c41c10880c05966a51400c600842d1011680d05910403406641421410041000102c04522159806441e4582c282d60b07150003d03820481910b070969802440e1603501000c40b94154030581c00003c064010f02c4070a9003141d41640e071444003080d8004e0800d80c103030000300c0d0803030380c06c003d0000c03503109003000300e0301d140c071019148440e4204440c0240140d10002003182940360820100c010410035001580b42030421020080041c451400154003414841d42d11548000e10b03940550 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 49937647 1250 49936397 49936409
    0x3010b091f080403120b0303030103110301140a1e050c0a080613060605041d1302040f02090301090503030703060f0605090d0c030b070804060c0f0503040209060a05030a0303050108100606050a18 85
    0x31820703501440702801c400d00544090380003901a04800c4c1c542c2c0380300d22421041d490020011421070386140e4070504450709100171035401d5501c03440c0d245402d1686084c00d9000340c007040c001241c000780070030b00140003928003424000c0d0107081c00300b0300c00903941550845140381801d20b0050a140e40303034008034690841f80742d1175910b000c1ca45540000c0803540328000c0c005a030901d02086107541c00c44c44002007916425035000a080c44071394004801032600c1d901c55903100142050142c10000107400013230071288911001e03a101d42001042007461030f490310546000d8020540c2a444d482d040c454005e01502a40050501070000e12000000f4400e49e24031410055038850381c94240d900d0070a400038107403001078504591841c00d081c507030301e582030180768031598084a55603040e08554440e02003050b440d0015042c02e40103002c968010503640c400b809200c0805000340c40c04116549401181441d04c0b507450392039000b803842e005061000300c1e4400104c4645144c00c0c81d00d000c98000241892240c03d24540c040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 49938897 1250 49937647 49937689
    0x6051008030a0f022112064e0a1104060e0703020c010b011112030a0207050703140f0604020d02060a02010b060c0c0405010f030b010b03131e02031c020303010b09 71
    0x20300800c9500600000707002c000c90342600c1784206207240700604d80c0c088424058240c80184014075001001d0000da0354441001814903910b603170305003486514203190040c0c080c0802e8581405040c0095101010f103d40d0b100c2c0b81c5c0071650007002030b2219845041088005100681e203101d410201e0780d0316004080a41613102030220141848180a00250300020168031a542401220122580202000321381204484054400b002c540b0a80c403280e54001024010300643c20300c4403001043d410003502000c1d51140303d000e807030710f051007000625250b0083c00021080d4088010400142c5641c0748040401d64150346640d100c0032007000c241e01524050314500c5c1c0200002c01e114980c3c810015051302649410369080103541d80b01c20504080c90324a0102030032580411004203c4520031200440d481320354074101c0b13a0340c1040b5503100070041e5095100100e07071602624043c0b0075881c0520207945000c13102d034000902c01022031000380d161300051041480b49503011440e4401520749034110602c1000f82016 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 49940147 1250 49938897 49938907
    0x9070c080a0309210f050f04080706020604150e0309090411091513060b0a3002121e070e010c020607060504050f060c0d020a03090803090c040c0e06070605100803 71
    0x20000c1c40f1214055803601400114018850f43d007400107030f19500036969401205114250036175503580001248500d01d00100400a940700c0e06010301405071800b540a0140c2c1e0500c1e0a03d40803100704040144062440c140b0b091004110010468802e202c09440d000700300c1c0e44504104a041c0700c049031040c1c2000c9001d0401a03000b501c28040b445a54044424070a40044900c10804640180c01844607542c810040e10258030b0199542d0089642c2040182100081040701007070700d4400d44408410761a0046414102404982c0f002030b840040c2010040c8120350040d131410f0f0b1401e020304110248251001c040e990b591040340d45445468003c2d0420782c3d11001031038018010302c0704403410348240c081c0314440c50100310045861801100100b203481d040c01140d6403120000c1d03121142031024145d44c0c80607000040c02180246100c2d00741d01015110020281050006407001c030104541088080c6c4100c1081d036580005903840c064011340002003079902d0b400b403006032201e680c125100a10010030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 49941397 1250 49940147 49940167
    0x609030604120f05090a211a0402100e01080a0b03031b0f070f0501050a12060e011d01090203010b0403080304020301020702030a0803070f090308040605130b040b07110a1409070c08 79
    0x10b00120341c04000d940e844050f80b0396a0301240c8601901071010380c041082e64007003100b00c03044d4200c00c0050002c021403c05145a583d501d440031202903011000000101c0104400c4d8a4001458145104542040c0368440002c2c40020100c54008241c00c8031303a551401c01e8101c60310b040081d102d80a110302d90b000203204002c05596030b6800b071185200b516105221000c02c2643e030401501d0b00b12201a1070300c60619810035810b941720382c03131030520381407241c3d452034002009440d5040f0903000f011040c00108503108004408429800160400c19400b801080100800406201100d04a0b03030440303055034803501d0724800240a4810300303001962612441a50000b4031480d58000c0d4010402c0d9103171000500e0003580142c4418001c3e11001d032101c0d030140020402c0c076028600410030125118a075800a545945601912390082d030000101d030720022911a040200e01340c0c0306501b555040750b0400c203552070090300c12058140034480368080c84204010030358041c0a400d07004104ca0b4408106511050011 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 49942647 1250 49941397 49941413
    0x203070602010f0605060903031603020a1a2d01051201060f0b040509010f030f0210030b10020303010602070f05030d030902030a0f0803040c05040b0a1502070906150e0616020409020609030604 84
    0x40e0f44401500d00d8400002464075061007142c1110b24090090340c00d065109400c0c01d100102460264203500800c80c0d0340b000680c0ba80e540381107a00b0507500d000040d0400c81000d00070542d00c07402480320810180545030740f105031080c0083c1150030840d800d00054507440d6405016008a600c0008807100c1d2080100d188801e030009817040d80d409076841607043e0380c0c0e900d901680c84480d2002800d0126200c460b036016081c681c4030380c14503a60f507041c04200301465102059010702d2503a400c20040e0008001030040340d50510190005061000340b104841e400e0100194035078220b0001b070000d0595408a100840d14240000140c03150048445445400ca50811401c6903104580c125666500000007041503d8940701e01e8900c080050b01c0440e420b0b0a0080c1c00f80d4000342030089406600c240c0c400007600d003445000e40c0d8040c00d92203e410300b031810184000390101e884100e01c40d100d00814401014400b650107404003819404690205d824000c5d03001184440c4929810942c060040b8010403080c09070031 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 49943897 1250 49942647 49942661
    0x110c010207120503040c050609061c0c0e030f060c130b0c0c18070c11041d01090b060108090a061104030614070f08092d0307121413050616020307060201 67
    0x54000c0110300c542d00e0304221003502c8102ca00400002e0038440c240315500f4904051701003071a010b400c0c40e04d00305208000701c010159410004103100d861baa01010401d0740001070001000042c3c00600416081220071911840c00401c6094001804100d107040000c04a4904c4000c00701106000d584941d0515441e0719020b0310340410b40030b1170b000007802e41c51850580441e40f0400e0b0755681c441c098051603945860413040c101301182c0c0151940c41036440b0743d44280c082070480410303100004000b1407030719140050f210000d2155050028001c100022003201250900700142d00c01070000e4400401c1e00640c440d4000d640001e800390b0301d012014803201e011207410074059092502d070706107080c000840481700e1030022944e20415800c00031210f40b24220320800c81d00c81588159403883c20002c4103402510703507084008140c6a00f4140f40425800f1034002c81003000e900e40082c0702c2454000d9804000c015552184640d9000384000a048890001c04d040d0748103805034003c06441c4115560280203018206c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 49945147 1250 49943897 49943903
    0x403120801091415060703020703051207060b0303250c12061409010b010e120a080c010504020109120b01031e0506010f050f0109080d0c14010203070206160e0117070201110c010207 79
    0x74012200c01d82c20311045005116440c2100304c5846858a0002d1004940004100f18158455070702c02000089003405403030308420120383d019031944640d050142c00d641400044901030b800c03c0110030011409660071001040c41c020101d1105850344c900045201c00c06d60040540c14212407010041050300e420008030358080d840f0b1000a515004103244c2200e50480c1c055010a24006681c10380e4201408422001183d0340c09582422040b900c0b900c8555100203a16200c0c0d0359500304002c119070300f10704540082c180d0480603070165501d80e034505c09200c1041c00094010148840d40d0604002000b160b400200e902c84142c3d0483c0d695650350000681c068042c1074810044120b200121303500c944c0d01c82017140c5050005002d05903c007003050b111184050001c3d04d840c1c0c1d200c0030343e0030101e17400d000850107002c95034010030244c070b41840210600181c035401d403400c00581c0141090582c1e4420f00c10010301561240400c0340e600d8480e4280c0c0180703036018011214030f20220340080100c4045d8080c000c5c00740 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 49946397 1250 49945147 49945151
    0x20a080f01050906030604060f02041e030611031902070f020613140315151504030804061b020d17090d050c09010e0106020607050711090a0209042406030203060402040312080109 78
    0x600d5404020104208451941c4c040c6d208400050205282c0e030000d01c2c00b043ea0000040c42c094407400e18610b030b050340791001200100803007001c10402c4041d01c92600c8522280150a05505245003008450001d0103a50f480d0203402080700028002c003a8003024101e40d004100f165246584070b940d0341c2d00185841211401070540301e104085003808100d810050442c80091205696580520405004084852904100d4890503540700341c00000091010718091079486840d20710f08200240600d01480d680003505089500160068407200340c04031480c0c0e0b01044040e803504010714504c14501801840962007040d00d003a02007071100c0829481480343c0c054230a41101d1380c03106100302c00c0d010b084c420100143d05c100001b90f882d030f00c140040d10106115076001600c188103003000a00c104016581840095400a400040ca107010721420300300001030900302030f00e000c1030a840c001e200894482e040501d9000030006000b1b0360303107504a170050b55000c19110b0000c10341c100000c180c01001d00801c3c403624 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 49947647 1250 49946397 49946399
    0x80a050d050f0907060e030c0d0c0b07140609030a0c120320130801092105090301150e0901060501050a0f0504050301092d0b04020f120114150103021204020103090c030501020a080f01 80
    0x81c6c0b10726403260344100080d0040048010481c14055105c50707800094401d0314241300040703030240c2000010045a40100d82c0d100f80b00131510f07801d6041850103001452158802c00403a24140c0d0031140140c8070641107a803101a5a4451400360050050304c1080036050243e0b001c00022924800d0141103220208036410382841e4981c0444c81c02c9407104400600400b03000c0100725506407410301943c203008994900349007400803040201c0c0c25100c1058180e120120780c01000d1003660100402c2c0c5034452134907402484418038280000c0e20078440c01140a042000d04024042d031580120304880041030050020000414141040350300c00341e4807609200c620081c00708110400c41030b480d5004005810002d401600e84950382004005180c91000a410207035200d51003240220a110360800e4540541c40b02d01c4919115042005880702940000e040c10b00c14002d440010094070050350388070794217082c0042d80c0d05a07800d1068040d000b035880100507600016400907810b030300403007030750085990703090301521a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 49948897 1250 49947647 49947659
    0x309122a06030a050c04120515060d120503060102160909030e0d12120b09070e0a06050c1e030c06010803040612060e06011d030a03050c070f12080a050d050f0907 71
    0x141003000c00568009001d0012400f86801644039035000030311030303107100d140c60f0b51103050803450651400113807055080901d44140c229030407038030346a0015040b1240900c0380015944c1d0f036020360f01103a40c9001c00c00003100040007640200300143e030750308140d500101c8260362080500081c091400d8100d001030b00c2d20040d08803e081407003400841c0c42e88600128509031142e0000c80e058108141c13056901a111040e25042d51210302c6214010b00c52952105181440c000501c40158080c0d407000c0c041000800c2103100d01c01c00898441502000180301115010b09001d805185005401c00004a405040000592820004010000c039102d03070711031030000540010040c044031014800d01e0741c0110707010300140c0c203580705d1003603152094218000b0034289100d4401203858003000103c00c801158001540d050102e5041081000031302e8071540c206001800d01c0c11402814100c003200502d2080046a0360758a20f00034803d0392003490a03035004200c2403428802109104e44103a2361440c050007405008110 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 49950147 1250 49948897 49948963
    0x60807050a030b070201061214060106180e0402030a080a0f270902030402012a0203060c09010906050705030f16060f050606090f0f04020706020c0d090608040209040302030912 77
    0x200c0d10010840591607165844141014800034100381c1155038402000c92a0320f020b6903020702c424061602d0290060881c82c0161a02c1c6060708940b0a211208400c034003800b0043c3d00f030034156120103c40340d210362a148082440d055a040000700403420200f0030070105603000c070102d060080c242d514181c0c0300c80c500551000921403008240c0000031100001d01240c0c1d030b02d030003c542142c811b14010f02d0b00701d580386841c1c1a4000501c0056580c0718517100a0040d45010442c05070408400b40c500c5140024000010380120014400c04090007404181e2000380715003801903c2803000781548641d910380d05100301550402521078226070051901072072003010092440b8040c4a11406400c013450a0604010848500d01c00800e123640140e400ca1000a0350f15a4000340c10300310301c581d501503120304400181e00d080a20184544c02006048442002080e90190b01e19411170707016540401d258980d820124198401c008030582c1009000c040070300c500000080003824201c10202c4000743c082401a5100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 49951397 1250 49950147 49950149
    0x312051317070314191104240e180d0305041401150504051008010e1e0607020c0603040c03060c0806120106080303061201091a010302040b010c150902040e070e0406060807 75
    0x5a0301c05407007440080c1850928001c070020b138408541c1c42e40d0091000c07560b402d10743c1c030303080741c2c01c3d552800c2e1500c250078039004050614210641090740502560780c0e407a0702e00050f10074401c0031050100480e484045c0d80c1040760003190b800341924403c02e03107040b01401030201079408641044840b010401c100c041031140c03050664400d41e55082051031f10041001908015000503110381c1c0c0701d003000411060901c02d580c8100b07181c102500012806007182195000c02008401c00c80c0c00c100b08202c90750341c0c041101007ca40d0116034035600c984460502c6844140e490304002e0000f85072115248005070849842403060b17030300b1038039411203009040c0070909848051003290302d03503070090020030304502e05052150001440e40c0000903104135036407290440400e190720b0f560613503c171820051040d41010b00172082810420300b01000c010b03420380e5504654201070090900700380c1d5102034440c11982d03160000904119204100c038541921004400100300781a00c2c1150745901e81040080d52043c04680f00c4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 49952647 1250 49951397 49951439
    0x521041a0f0f0615040603060812090604060c0f020604030302010e0606011b0201140c06100303030c02060601050a030e120a02030a08010801140402090c0c061003020f04090206180a03120513 83
    0x32079680c0303919490039103484000d8032855001d142820382c005841e481c0e80103000184000c2c0e402040d9685800101803d00200c8001c807000c10800300140e01058680c81304880c1101c01c60701c2e01f022030945600b00f0b02c203400e00018000b54030207000a4000b043c5035054200e0007110540f4026074079a502c801c0300554800e007031440e5110b900c084507105040998081c0d0307030240c0f021299a41c0d40d45484112808181005412181c0c0f0703005802038242402499803510820381000b006000034a482d04180c4c001030058000c0901d00000c0648400e2640d076510300a002c82c020105811040c0c3e92030b541768580c0a5103d8020802c41c00015400400029450070705021380402000180c1c20062151129028401d640a00500200da0000b04001000c203004040000910402048044001d460b00714410080f41c06842d2031480d214500341090140565901c90469180c0c8501244070700d1700d01c80340d1000c10030b100b800ba030001d008558038043c105082d5030403c008000407000c55560040707440c1c50313181c80b440f6881d59011903 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 49953897 1250 49952647 49952671
    0xc150f031407050a030e030d0e06090109080d0b0303070209070f030e010522020a1518090b0a1509030206031005030d11030904090201111c03050105150f09010521041a 73
    0x400d207224050350013000303040080d24001c41e8240c0804802451940038080289040b9520342c0100010030713040c041c494004c9943c0000b40b00340887c1d03403640b034410b00800900c82145507032605d428060b580c0c1001180c06003513000e0100c10711850a002c015000c900020740040c0468141803c0c0c5080c11010b03c60144591402c241000e0b8038010203029581580c0c824000f26001004140302040103009980c2c400c00c16505959951101c1c9004803105018031202d5015603900c1e8181141541d05540e43c0c0b01d106c007507801d40401070240c415a08001c68448ea2240d00281d00b007a0300205000d00915107508410550303105070300710750f10074040010441341840103240c203100035001070054440fa46020740003840114014940100008045d0501500706200880e04003a048030398848005080c0d018002c5900605040b1200405460007869540e0240b0038140d04095001002925a500b0380c000d500743d450a14802594280103e00041c440086d44e00584054441460904081c610700c610503000c07030f120b800c1103580 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 49955147 1250 49953897 49953901
    0x50306100f0b030c0903100504020418020915041509020d061202030607050c07090204060302030403020c01020c060409090633050a0f05091009050c18060301030203060c0c03070c150f0314 82
    0x42c0d0300d80c2d0f00003600b0000841c0c410060040385940400c889010015000300c0065142064810042144c0080b011803c0107440240c404000d0380d04c0e0000340b0341c070248000c0c0722000c803045180050000c00c407000d40c40c00700c0c0100c400f000c10740c0019a40034040e03035080f85c5000c1108a4440d42c0d00d003007281c80c1e000000e601d58800000942100c1c03240c0d01030540070a28004a480305902e900d14002030f608980c03c48000a640481000305055041001840c00c0600307001400c00b09078514003182c01803181c0d010b02450305840340010000c02c1400c1d03104034002600018a65440325181030300040e00303405082c1c200445a000007000c25146800710101c0c0488544524440744685400207000c0003140090100110141910000840e00d425004862196400004c030b10751342c20540d4000003280540c1d0482c2c6000781d41c140014030060300d001903600d030010944585151541c0181682611f544a010402440b24030101d900003480b075178040c915520a4216101c0f0103103415142811001c989164205a00003402000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 49956397 1250 49955147 49955159
    0x150c090103180b270708030412050309030102030c070308160806010309020d02040c02070512030412020d08090d060e0f03030c0d0b1906020d030506031902060c070e041101030b120706080606120907050306100f 91
    0xa80c0c2001c290ac500700b624101801c050000342241c0040b00c025070790300000a004010503911074001640080070706c01e20201801c0042c402440900e0040046040c59a940c05072010340d503600340107401070b546c028030600c02c0100c0c2d0f0344000d460b42410300c01c16000b00360304801201490750100c10f9500344c40c414503100e403407100c00c2e03001c1100480e0103680a03903820004101c1f51155846200ca80b07180f8a0040d04003003016120141041d140030096002062660000d009111600b46144100d50070940c0680b03010420381c0e201d0001030b8482c1010351a20100b0340c082140001e0107600414004518019510100195582c0c0307010306495841100c01185507114003100d070070040c94001d01400c83c41180c0011506140d88a1400308258001a1815144142c00c640c0b03200181da81405800b501d000251580c0c5566071070241c40907504c000e603005002c20301540d6400100c00c1d848035015955240c2c80e070320001015040800405841d9040343c003601c1d0281c090100024482c0101c2c0c20424203d4155409202c6a2490f0403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 49957647 1250 49956397 49956419
    0x70302060c0a0522140303070201090b0c03210906010608060d0609150c020a1202070b0301150201020d1b0e060910120b21150c090103180b2707080304 66
    0x8100070040c84800e02400f5450629600030840d075240e030f210100c1c1c0d0142052003045c003012032000c9040c40781c1d20030404000181d03032001800b001c130f5000001071030721020f004580d00d0840c01000024004140c22004203030340100381c400035074010484a0300780d84141e42c1300c2c1c204076071a640c01c8603056040b540c80e1050100203840340c1e0052905a020b40600d004200040c014081520582d865590060340304100742000d00407484110350b01d0700a00d000a00e02c1c103241041c614014081486071980a482180108604034000c1d0100e80419003029000c10980503001030444801b03501c1d4032501c00082000c0002440da040c40411aa480c09008202e007404107030301d41e001c031136010302c2c01c0100844c030b40c40e507840280a03101c0101c814040341089140d29802240340c5409464003c4920601511400c10400d2141007261101214183d400a1a0204020301185111a283d18590000615050321071080010b07020441c44a50340980d030031007001d15540c00c00d0b20600d6070f40c2d04134000c41c2300e40d820030082040940420 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 49958897 1250 49957647 49957657
    0x7030807030905010c0527030a0807030e0405040b09011506050f090f030303040b1b032404140108030c0705040b03060f04021507050c04110703141303020a03140f03070302060c 77
    0x3074500490300001580c0c559080d11078001c4000003081c404203049040b9281c0140711407104a200030f80c02d40c80e00c00c100003e66228152480600a45400100882810710885d20307200195030241041c00141464984480e861508842d000040c0d403a148900e10707410011001e4008443c07143c0c0e01c4905116800d0b109403e0380e407191201d00d9105803190191059a03c0a2024500c035038000c407000300c1c5031302c1c3c000010210310b00791060103140302c0c01c10810030a03c12203103414000702c81d92031042c200383c2c051120003050080407080c7c04c03000c0c0c16268000014513500000002d24202441800f079480340355650307043c001541c8403180b19940c1500400000307100c401031585d1095101d03000426540e14045480d000c9542548464410b4451342c00010854405080c1405000030078068064618602416034600414900410a0400c030b245000601450b041c80791804810246070001c09510700305a41345032022280704059108080c60003510540040258040155088a500f40d0060403c6540b0118140c000d5489 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 49960147 1250 49958897 49958911
    0x3031b020306040b0f010e070c0305130e04060c09050109120809030a1208100f0501050a111006060201020c070f0b070f02012109150203010b0d0b0424140411070308 72
    0x60246a1009690200074071030240340180422001400d0801a50b8032000c016003007040c2c107060380c13000e008c049503000b40c080c00d400350103150150710341035a00c180008400340c607071018600e900100144001c0c40380642c4001d040c00420340745d0400d55943c920055403140302074030a1081070030f80c0b04d1145010440c031000400120900406440c2c01c0f038034640c2d82421280041e030030000015682c00030044c0f0200140404000351920f03480309101d00385400f0008149200311248201004501d00c0398031190320b42000f60a440d000a51820302c0b40c6038075003078000d000790008000c850040c81003400000c3d842001072083e00035105c40b006114500311043d10380c4801a04150801c90402240d094040f002c100d042c144581c403000c4c0c03048080340340b4006043c20781950b241c4010a40401e441080100810180360046a50140102001044c8030f56070000150062091a40e0b58040f54510403a03603070148a1404aa02501c030384c0c40280a0955603003047c0012101a210342d0450035504000020120303020b07502d03150780404 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 49961397 1250 49960147 49960187
    0xe0c06040501031a0301050103030809060a140601031a06190909050108070605070507091d011b0806010e0609030a030512090c0d0303020706020702100509130203060315041704060c0201030c0302030702070303 91
    0x500e40105c0c1c2114001d030700c02d138009180c03481401001002030181c1908649121402d2081c4000551060f1310040b0207000d040c18140d131107400504162a54a0502e00110020201c50f2134110121103144005500741900d000030b400020045407880c040e10926058030b18070401442c1c01820490144c40780e500503034050300d00303200d03051b800540c10740030b802400c880d50240c4c04600b07508440d221a032800d40701d00c507181071a80740b402c411b403000c1241d125203220380c0154240307890365041d002580418007620a0003411501400340c0380d504810b15401c1802040694141440021a0707034400d03501c586c48001c2c80701260340c408208410800868800e4010b0401c05010b003170014500181c80e8002044462060b800201044000c1401c250a00e0120f11a4107500c803107a01c19850340c90f110300000d86405003203c0d1081442450340c007140920994207030300c0045203006619130342d481f501c90001074001c960b022401c9000905000308500300f9842402900d001c0c1059030007c0081e5411a581035401440305205201041 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 49962647 1250 49961397 49961441
    0x8090103090515130c0b09010806100903140309090601140d021308030c07050f0103090209010302040e0307080d060e01090204061b1b03110414190504020109050a17010e0c0604050103 80
    0x314181d024000c1281c1c03d1500d044c80858a0100901d6056600c000d0006600703100e6074400d079030054020340e0f1021088a120014400003501a2440641500301406c1030164078606000e0703d00001c010881c92004841300300d00c1c0d542d61320044805102200c0e0b0200ea4032001d22107100010168ac000c2c0001c3c0e01304d244581c843d107440b0b1143c1e44c655044000881d0b00b641c0850307410422800c0070901d000c4540d0b801c3c81d0500500e80f0310340200f808503506201c0203025a6070358100041e514010700a9a10243e4404201c86c1e91b0110300ca001c4001e00703102c3c016148000300e0000005880007181c802c4034102d411300d84802c0c1120a0000c12607107880303803d4109440482e002030b0400c0c09002c820301c00b20301840c0301d09403005004020009200c2254120f1117042c1b0125510300601c0b04d04000c5008000b18401542000305490b42c1d940b0040301c4c204007603808560800502000880c2014400d4035141300050200c00070040503000f507201584d64403004014a4001c0000c001c144940c1d40310b908405105001c600d80360b01c0360 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 49963897 1250 49962647 49962673
    0x406051c06030b0915010618210602030c0d0e0105040f030f0212041e0512070b1c0f0504050f01090309150306030c060905031006260a02040509240103080901030905 72
    0x40700c41101d030a07409420001e4005c0700d400020f85291b014060a02e008003506807008801c1040102c035004003008110529440301c141c0c40644855055141d00400564980c100041c080a190304100c40d0804031504010120b005510148281c45c03056070840c19840340c0900f42d4400b901e0f0a00c10007103000840c01224962021120a10000c100401218a0540c400e0508407034860b00140350343c004034403130541e64100001290000074014280c0d01c40b840e50641e200b03290319008600070100718440c002641801c001040d202e1090b403000348207500130015200368040c450807190803aa00c65070004c02050b0740320000e0051101c00c02c1c40c00f646036000d040009503141c0f01d8441140042840d070114001a0100d074040c040c60030b041c8140381015080c0241403007000d060042d00c9000c8101182c54454401500428501801d001c000554405401a20402060924844103520345190b00d2444070641e0b83c4100d03881840b01c1101015040b250000d0340c0c107007041c0b40140118060200c40301c00341c59a1150704843c1102c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 49965147 1250 49963897 49963913
    0x4060b060c060c0306010f0c080f0a18030c0315020c060f150901121209030b0705090f1305040b09030a020c040b0301021b070e0a05090c10020f070303030204050405010b0406051c0603 80
    0x40d50702050f1151a4603002d00010000c80c0c0002c2c110301085494030000d400200031105883c40b00c5200000281c0783d4110040031220b5092445100e00ba403262f0721000014003440d140c1c210140c902411290001c0b489684d0640141c1c803903d40c0074441a4405800224800742840460350803d6120f46401e5000c000711002901669003030704640c0404484080810802881c1c08081800d1501410302042d140c2c9142c8079003109110080c80501441070020b08001969542121404090f10051160030703072000d17211142000703210440e4100d48003003480e4040b440016000095608400301035004008102800d010711018041c010a0f0f0303078141d034090060002c0d01c000c0c0940e0b144035200d9100142a014078024843c0902e51000d00014201483c0c1002d02c00344030710121741010100c1003903c250741c501c80460412031800c5c245400964407402041d8010040552540042080b038004032424455647c0b00c0103080c80f1885644100c00c080340741000403125402801700c0306480b090f001c0c00f002484030303500e854500e0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 49966397 1250 49965147 49965151
    0x10c0503070c0b0613091a15060d0915020301060503100609050f13110a02031206100e06070201140301090e1b0105041a13030803180601030c050105071407080c0307060c03050304060b060c06 83
    0x5080081f51422035060200010f2082d840400009078032130010010740828264400c1504950140340c40c0c03c402c0080c0b008002000d010038950751011540d80da92040c00a195810a640380d070b204500b519800148540b0483c20102503900061100ba80b050200c3c04000c8000c0e07812101000141d150a400140300d1080e1026100303840c0c0365009159542208000300c2c00080c0e008100328800d8480c80d40200407264402001c0348000e40c291291942c854880c001a40d90081d4032445080c1c421001001048001458100400d9036401000300d079a4183c9003444214944460b0104600081c070a01c0200035130398210721003903141010005040d00d8031509041101c42034915130002c0c3d40c11040081403080410101154810100072100900343c55411a03403510700540461040a042080104640c42444002d0002880200100d0202c80215a681e00e465031218080f480c030601c40c1c0140d04002490724002d42406039030603459070b5651700e50b50f01e076a03909009110482010750002020700100c0703020403041050134 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 49967647 1250 49966397 49966403
    0x503010c03022a10020f0712030e0f12191809050402090112020102070501080a020c1506030f060906011503090203010f05040c050d0201050d090311031b010c0503070c0b061309 77
    0x541d480d10b540361009100c3c90310a0301000016141009004010000308101514100b120303005a0790340032060072510a40140140507000d08030598000d454190185e004c0080c0d200c07940705684c611000c0508254844880001200c0d03c3c0ca010084034405003200107040f443d10510381000703d284038890052000c5540341d07030040d10b0125a01c40c180425890120300d158010280e420f4200d4120b91144d000070344a05c401d1160a0512007004045a2102c22540540d06099605012101c04c44d61800403d45110001e40c0d94502030702405100b491158800314038241b14045103001090709034a0407105e0085a4600e02c410010942e48005030710041c1d80030f00030310401502030140402c5904003420f0031241010241d00c00c40c030501c0304240100050340c11006071028004001c0b0300183d000d246085c10313a003021010a00c41e01c00d000000e441c0180c01d55034862070301c90082c0440200305201d400d0005030748520041d902c1202003510400107900140840302040c0d80300300d01401450003512440292810345058200032 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 49968897 1250 49967647 49967651
    0x30807050607020c120322080111030a0c0504050108070f0201060b03150f03010b030d03020304060209030604120905030a03080105220c05120901060308070b041a0a020901110705030d0e01090503010c03 88
    0x1101000360f0410240c1c0848000f10b8102d401040d208031032070b65038031801603103009009240700c035610305000801c1d04100900c05030380244503402d00080915404ea00448800300171f18941010180c0840c410b1080e1001d0302c0041e1150460b507101c00d00c050b602e60b800007206204542d210381004c1580180440038500487e0041000000c403551351041100c3c0c1c0d003002104600070717858480f50500d19500090b810108294909005941e9207540c2002e0005c0d11a403082035070984a01d0003070100704049600c403000c00c1c680513030f28034209a40b03880402d9100c900743c00b4060001040240140800d2400079185851b45401d40250928081c2e454005810f031400c00081e00d002c124086011124056000d035455888078600008219a6007181d6032843c10b409101d42c003900308843c0600180c00c02003000103c900305100031011081d00e2905000400c040d51007100340c6400030b204620b07240c1d007140700004c40c401901c900802801580072030f160104c503441810301115040154130900010261420720412541c1c100f548c2e80 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 49970147 1250 49968897 49968901
    0x4061104030f1103010504031e091d1803030106090501050f070f03050a0216050607140304030606090203220f020402090307051507110616080f070605090d020706020102120402190308070506 83
    0x403c203032050551046009034184803c110009500403076161044c0c03080320b40b0213144c5c4800c0c041200c0c40c00a41d000b2419034010001424401d0452400e040c0c4550000340982c0400f1070131100041d180c1c0020300c0b51030041007140500380015802a405060100b0301e841c40b140c01d100c3c5680b1440700c03420003801c01f80c012400002d2091205541801001c41441d11010150070151401c0041496480f64900141c8492142c0300400d00b0100244201c40007160807607814403c0b1a190100354000750f105568000070344074030040b0b500c1980c07a1521340c5810300f40c11484080b01d554054091001035407001c480a50325008914000c140781c0d813050120182c00e2001c103408c6848054500e84070b11009403020405105403001c1c003540d10800c400c031822249c00ea5002c0031107500d074510844515071a000d0101c0041a041c246000c0042c05a40068011807186940d03080718581960b0b02410780c00c0f4881c1404524443c103d460000e005810700c441441203012800640d00307074007650380d210de801c141c101d10001c0f5155049442 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 49971397 1250 49970147 49970153
    0x1b07210b04020f06130302190e060603090106080d030e07060807020a0308150612040506060301090b1305070b0a030218150904050c090306040302070f0807060804111210060306050a020313020904061104030f 90
    0x2030704048c80440180c9006207003009050000c0b0350300104154411600000010344075402034101c0c100504c0f115045920001c00070602034042d0000405043c110f03c5002c000240061040d907810740200c0d05900601502d5800351002c461001703006013500070146588040b640315490b800002e21516001c40c90104d05418980742c070904081e00948128441c0c3e040002000c08148140001a00094800100150b109161400600f4094981d000c030442d6940411442071050301900141221404840e00c071061804050400c102005000401784000009000000d141d05056104030342140d04500076a041c580400c00082c03810703908072000c50043c0c02481041289402c1060400f003e407400b44040d0078410306161b03009045440051015100c06204075058029441c0d041300d80c0960784408096845844a8242d000080d080501c0f007221000e25190002c0d41044492096901404c40f000340e6001c0000241c0030801d00241c007501c01c3d10215500d00c0e100c3c0420f141040200000c40c030a584d043c140c1c1c00103007 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 49972647 1250 49971397 49971409
    0xf020a141503010e07050d06050307060f02150705030109020d0902040c0504030c080703020f011d09011509050906030a02010f02070f080d08131511040305031b07210b04020f06130302 80
    0x102411007402400140200090118050360000f078620380903485145204050014201c0341c0d0190307806000e07012010030b81907481107084056000a408032050300c5d0341500841600300f411204040055818001800016aa80c005002500c03d8481c085140b5660341c000504076064954a00c010030300004080040040071800e1074003c250360409480d549203180c020400c02800a060b00e4104402c405e000012110020910841120098043d1406603142c940070710020500906407808684450000102c40c03800d048024443c0401901810000406600555009441034440000e60150100129418208920135030003070180400030420210709403005082d01e074028080c0000484514100c1d40070801810b428409491724900c00102d821004542c43c6403800b858000130300c140000070720707520009851484034112070070a90a543c0b40b156500c0c406010031540805400c40c500d0315080c0d51001c40e00011130541c1c45400608129541600307d0000f441ca648043e060741401000c482003030042d0b08080d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 49973897 1250 49972647 49972669
    0x60301060e070f080a0204080d08041b08071203051204050c0f0405070c11040209190e06030a021008061c0503070c06090b0904050c0903010501122108060105070f020a14 74
    0x1c0d0104254a04120500034520700b1424030000500511501003000c5c0c0300981d046070001c0c40c1410a0720074585c00810000c1071004259030a0b21014150f020300b568041c1034841309404c940381c6800402c0850328051804031401a00c0200f54103110381440342082511803001c0c4184202c1c4a038016142c40c83e807100401a008501007009801180343c40c040100c1a5009102c0e44401074004204d103c1c80030313003000080c02038420b60000c00d030000070300d900c0c0c01d07420354016000e0030503a9400450040e450350348000b4140d0722840180081c3d0700c00040380041035014000c03903041d604044040c1030740300e201c02e0400b0407140080e07824200700c495520000d00700702171140211a0201078600f6103001d2582902e00f4019440310f00807968003a1140703503110013203800c1c082400203c5280c40070203402030103e5039540040a8149995940a07620364200c0d000e4135070108080340c60b01c42440c80d10781b101180b039261f00004503151b80161b402111100d5103040c45e4400760341d400500400070f10001990b840720703a0348541441020404 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 49975147 1250 49973897 49973909
    0x106080a05090c06041701110d0b030f06130b04030c051603110a1a090402130920090303030a0b0f03060a0b0102010b010507020a1202130204030803041e020901030803190204090506030106 82
    0x30400a40607903604c0045504903a280d800440440003204002c40c0102010f10704001e994000054000c3e8098468104100220049050b500d81a94214280b0340304c1034101c8050b41e43e403400100041c000b03031052050b03035049400381c80e05283c1e81c0070641e80c040c540314105026500c400c40040d03081040007229011084041000da860413400d80c40c052000400c000e5800460f17100301030100790f4644507155941584c9035042d2025030074240d20f42d140d04150050100c01015501a82900010042c0c1a04081214402d40d00076006500e540d4414007403c1c001e100c2c3d012100d034800b2800710001c02c01d90b01001280c5c0200314040300081c2014551001a0840380503440f501c1c1401401d028039800f680e1240764020403a00028020215441c0380e100041060765254041d01c080351001c04d010003030000040c0510701c128032800315002c000d0010b14070115511340e00703c00250f00c5050301c1c00610020b101c000195030410410801800811310001c400801d03178109800030440d45039a5801c101c81c501d0240115402088 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 49976397 1250 49975147 49975153
    0x102030f060f010f030e030d15090606050403081917090607031a01080406020a0e06040306020703030609022b0b0604170d030912030b010207090e0105040201031b0203090f12060106080a0509 83
    0x100440007034941d000e40101380060556821040e402c04105004850b809041c0000800019070a0740d404103155605000f0106007074a44840420720b10300410885068075048203002e424034000c19620400742d4124142c000c20440a017291400341400c02881901031301d04040504414904480000c00716540740a162100620799101200e8903600303c808590090380041d800b607074074a490582a0751024241c1080d58108100180000501172550b001c0c1c0b00b264440d650070b11801c0c0d40e6001c01402d86c020726a0a0307540350312240001d0100d80b202d64001c8680102d000000c500002c1c4e0000007011500035038421340c0c2080c59162074076001c41e03080c8003594030301c0c0070781c01d0800c26003641e6101c1a61242c5040b07064820b1554840840400368000c01824008004440303090014030004050503020704010b40c1d080340403e081a0307013814554107244200c0c0707000e09580d0065003010100c0c0c040241d4000075480054000806402112408100b4050f280c0a8181d03900c0b00d0b441d03801c000d621a0101d900c000d00100e1250 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 49977647 1250 49976397 49976419
    0x50610091a160206030907030516050f120c040608070509090307030801030308040f060606090509090d020c0103092402030f090f060f0a022110061805010c05070305010e0102030f06 79
    0x20488020626141d015006042d0b01c0380b4a088410b2160788164a01a50010000c8100010204002480c50540b0720813070540395010b0442810743c02400032070080581c0204c0c42ca070700790040c0c00c0101722052035050700021508000d40d21408502150665004040c4942281e00f042c1b2490808001c0c0c550050803d9005614200c81030b203005182907010700000303040003440c8011406104030010140c01e640e40001080002c503544440281401c1040c2c0b141d14010318501c40003460850000c90b00d90142d14058005d080c0001d2180c0c0114000c2c01204801c40740c88005407909101c2e11282c007200c506200711080b006a413810200204419100000d100c0003207580450000000210081461078100b02e40d5020300c041c540311452682c0c082c0c082c4407a50a0081650150400c900300ca0180c2c0d9406000e5500304600c10680f82e407000c540d01034910120b8090041c0030402041554803413604c000700701d40183c0a445c0c0050702d980d01d450035070368035100b42c1456030340200034403285c00c0402061941201044540940e10 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 49978897 1250 49977647 49977659
    0x1b050c01030e03130b07020604090c02031809070206070f05040b0f07030e06040b0409021e0d150603060806010b090301060308070b07090b0306010c0609050115030305130b0309071205010b040203040605061009 91
    0x440b028041c5c4c949580010600104540b200300c280c8010303184401040c8100303420048003c0d07aa411040c00b0703009843c80888c00c004281412881b26004414070742c00340c40c045c1d803450742c10b0310101415130b000c6007040000c00000500e0812400a46110381d840d0041654450160400400d1065480803040c45560104020003071541100116011a80f21a0025848603220351070618101544c0400310013030b650018018800350110b500800418103003000e1500042c0c0c42d1441142100c4136030083c10031540c01400144401d0441d10080c1031802d00040002c102c0c15141d9036445141c3e0132050080303902c42460350601c40441c3d04118144003800070725124500303501d0304100080c1085007141d006088503981d0f0040c901030180039081003070140301c14800e000e019541da1400602d5130707100c400030030407a103101d10b000301324080b0b5482224015504480200074250826100010f1b03011001d40c11a400c0d0750340c0d140d00302c40f5112800554802d50003078000140b60310b400000d0092000481a1200411525000078440 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 49980147 1250 49978897 49978927
    0x23060303070b06040906020c010b09010b0306010504090e0c1005030f07050f1603030905010c0c0201031a0f1519080115030c02031c0608031602130501060e040c1b050c01030e03 77
    0xd141d080881c482e401e803910b07001304000300800361010f130407180002440d0064200540200d40b80350416580445a41e0b6aa9402c01c80c0740000e4828600241d41003004104a01c8107800c0b42c46044900c50568096026103c0015480d00b520ba01c030b0001710700c1c08002c010454031072028035948400b00303081c05484c200e81440015401e104070301d4151044d4010000e21014144283d000c8545140e22a001304590321458270082c0c0b400d8a801001c03400a400c0c8000d2050010703c16008508a44000c1c1080c2111440742c0c080107003940b094882c2c00005e000500c02c955080b00c00c0e1220031011a081e8440c8082035046c4011122080b00c89105202498188018030f04020740c000b0840f900303442c40384084550200c00e608407002800d41984100d580c0e100100b40030090605114101c010030f1310880d041504580e03403000440a50b0003d11030400400e610151900c41c5040541202c0e1040d030302ca2402d200d424680c1c40c1c01041c00803c21009450316841524400da003540c161080316204c80201c0000e42c00d005042c0c03240d002c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 49981397 1250 49980147 49980157
    0x30201020304091119030f06050105090a0e1e0f012c0105040e03070206070506010e1e0a0902010c050a030c121701090b0a0b03040602120105120c0909190623060303 72
    0x1129550250030191325845416180041000070f402c410511039500020040e0640c8006104098948040041c0541c0070324101d40541380003402c5200f8491030512903420240300106080182010054000c2010507032041040c0724001a900718185541450030041c0217281041d4010440140c1c4800c070403209071b2500c0c0b202e044800446010661044e620123007415806181d40c001d401c0040400e40d101041404070700c090503280088030621040d41ca503181c400d00403d07c507592084800c0800081410b800094122545550040c10704009d4440559122460316503007200c02c0d80010718801c0150304000c01e50740300513400211850306000b2020740915000b40004107115505150b80d5a156580300b46c5c40714001000103000c10030303905d0307180e1500e03042c10f1000c0d5011018804400c220f00300045034900c0e240c05124900c0003468020a1007041c90406d016a816020f0580c10b5031781b03d1004030504101c0402400b80b0b105100c0c06011810b41100c030b01c100509442d441d01041403154560407c030080c1c0b00002515 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 49982647 1250 49981397 49981409
    0x80f0c0108071d0109170705120d050403080901030b060f0717030115110703140a030201060605030112020904020a030203010c050a0e0306130803072c010206090a02011e090b0d0605150301030201020304 88
    0x400540c004030010b0312000104c3d440102200da040b0095241e000c0701080100485134242c50138440d450000518540b6090ac007025180802c0c410b020500102d005040a02190b00040c1000508200300c075000407116009070400c0b0110302c1c0009103690030401c1400d0000400d0a411174001d041d9414003820746850316110503d01c1c1080340080308070304200000c0240c82c00554002c4076014bca01e441d101403984540001d082900550b0800f4400501c5078440e1045074101c0c2c049034582c0c21070820036401c1190b14280604182d81c8079100020220241e902886240516081138856030381e96651614003034400020880300d030384030703800070010170040c607040020381e40075542e012000035560381e1001c0c000c0d105030400305441e1520210103140c0790080440c640c0c1541c1d909009808654807a42c800b4a2142d0382d48550000900140c0c0188180078210704000d191079040480742402403c16846000c80d00700b540200c0c508008483d21008200154100340b030180e01d08103801e8002520795819500007075500e110328841c1d0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 49983897 1250 49982647 49982687
    0x20d09020112060b090111030f0304060b1212090d06020702031b0a12050c010c0305041a040906080f0718061211040509030703020a020906010e030303090d14040f0b07081201080f0c010807 82
    0x50307c5c140d001842120520041a0852600d03410182003e038010f10040c419140a090f0903546101014400501c000c43c645107d8522442c16000f601401110061030100b1580d0b55024400100169014000321480c1c400031002031000b44980030070480040035075405010344540c0e072100800805c00220b49502c0985003805d1008a099080c5011941d910440d03204124024030500190035014840c40184210350300140c2c140001515069800c0d15030741d181d0f0b008952580041c00070020b49543d0301c10020801c078100c60018803540e603450305003142c0442d40c008035070790500701c0003407080741c03820340708041c0c0100d031045c0194201404c5640180d600d4918040180c451a0608006202c0340e210744444a021000078098035201e0030411003c40e07a48041114a00108100c80c9a1b40759900c10301c0c003550110341040d0752591200740341001c46040782d0710100061751071200811000341a0004984540d0007044003030001c01a400d4485082800d00388050600e1303042110344000c0c8200c80c0ea0041041300040d07a00496 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 49985147 1250 49983897 49983917
    0x1215060a052e090509010906050102150601020d0e040e030c0c030f030702030d0c05010906090302030d0b09060d0204020705010b0301090f0c050306070905091305241305151504020d09020112060b0901 87
    0x90716240f41d1607101c50741c401200b800110f4000b40710740200c011548280c0880c0c60040f800341c40c40511450454200780142d00107540050f81a100c2d200c540101c0c10080c00c005913185140780c1540c1194403540d6101c405900c0412800d94a0800300081e01b03841c51000c02440c245103990340002c0d1540020601c030010040e0040342e110600c4000c1d0300c8441000d502050410403200c2034600607449070080211203e1540c80c0c24040d83c40b0703003400e0300500c0c8611030080500150000c40d034200402500701002c155400c3d980c801b1016842e440034440c541e2600c0c0a00c10241100d0120b140c206204151900309074040e400040c00d00580d203412101c680c050b00d0045440002c950b588036040501152040b10140c03091081c2d0b054140c403c05003003600350460b01402481c903580e980da001e0022590b203c1e204004e009030710110041440760720740446507800c0031000c10081c01001e03a0b1000a01660407032a04104c060b55509030720021907030844c200702005035102205011082c0303000b040c4040e80c0034840b24203042c0701007842 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 49986397 1250 49985147 49985239
    0x303070f0e0316030201080609010302091902040305060c030415021201050d02300c01030b0d030c030207031203020301060908060603120c1203040c09061e06030b1215060a05 76
    0x20300d00e0488014049407407184211103c1c9003a89124401070780441c403840086005c604019640c90b0580380c0103400c00406e52a01e01c6511912101c40c2d040342c0c0c000d582403101000107007090042c0780c065950340785065100d007418100b0075015403280c01610540382c410400708501c2a0036110300c0b41120011101881d506000740046030841045440d00d00da01c0703c0002200080f021032341c0c00031b4400d507058011202d8203c5602c0042d000c0302e0410a49030741c0404446070440000303102e00c400720f01c0103101344140c0714415038a650b4a00441d1009000202094000c801400640d600004c104001d0100e0b60080880e07080c8100880e0310740400d4111a0b501060000311400102010054005486c21013450b850b524500390406d0020640140940c0310f00c28240900064000c0043c290120301c015440902c0b440c05142c41c00540c014414a9040341d081006880603541201040c800242901c81410a40c12145408070403c0250300c007a801a40c4584410341c0200890b039084141e88050f5074040e040c04a005000b24 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 49987647 1250 49986397 49986407
    0xe0c07060914070303180303080c0c070308030106020105060924010c0c0b0d020403110f060d051b0d050702060709081203061c030c03020d1d040b13020a020c0102070503030c0303070f 80
    0x950240200166482d2050030140010740316007100d0182e81c41d0100c170000b4260701c0154841a1001500084d61040460840e5541c0001400891131800849a12a40d0ba5940a000c0d802c240d100802513513441c42000443d0031b005417000c0e032002c1d60150840002500e640000c111490380400309040207000c4e401c0c1c400b00400b0b0202c10001e03201c0d100c0c8442c0c4500403082103d01079070040c0012540031a000c02e0060142c1021712242c100410020003407800c0c005026070800080c8802020000c6000210380000c82c28501d400084c8404014014003040c0c903d41454081d180c004050400003c1000307500c8200044c0300b000c43c40f40d1640d8162510f55a036070b21505c00003100f840a541210583c1404030b180d150405400080e180c1c0710500c00d8081d1100b1985118042e0307400c4101c01100b00304280f10740204802c034641a0b1011462140080c148060800011100b100320780103213181c1c0e800340c1e2080302031311811b607010002a40180310840045242c2401818459203030301000d41480248810403050f01030740380c028 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 49988897 1250 49987647 49987661
    0x120302010905070f03060e0102340b0106030509011802060a0309020103110a0320030919080d060311040e1f05220602040e1e01060807110a050f01050601020303010e0c0706 75
    0x109044400044e160b06041440c54a035120440b001b5203442c41c0c8251701c031010b00950b4030a21306440142c10300403501004054450400440040c039813117804400700091880c510340b50181007103a40010301464030f01005800c4035002e5a409014034514000440140e03110030840d18a41c507240303008182e00d1240d10050340075140d5200c1c84440c08002080704444164158803001002c1070b40c0c287d43d030241000440110807884296039a51144c1c01c90000417207281c0412050508c0c2c988074207407441ca4500800d51800c11102d040d001100d28a40d800138080c89442c0c0350085610344020a00503202e8080401050f11050407403120498805440e8000110b0035912030754410741c03681662200008040051400400943c00b03805505545080940881c001d04c0ca030070b01c81440d01c020001c0809203a42000d0082d5120100201014100049120000301d044418825201024420b0009000c132039550382c58903080d070708010000c5045520034001000600120380020390803640c032070305c015540c0c400b40c00d00720080d0a031 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 49990147 1250 49988897 49988903
    0x60d1115040b07060b2704082a0609011a0409020604050303120a060b031303030b0a080d03051b1c09030e0409051c050f041436010b0f041203020109 65
    0x458002007002d0014014169944182c104210300c3c08000c0c1044100311071940443c42403401d00c10b4a5415102e500c010070f4006000c0c00040e400d18000d00c2452031409410f40c0305040c00034074024201a400d10400005d90070200d03c00080c03040c004500c0c00080e420710803000d60f520a64a90040000313644940d0210740160102500b03581e07443c7c5420170002ea43c0d00d0700341d5001200c0c5150401c00103c5d000d20314203032801031207101d401081c01c0322261402c4000d010010a02d42e4404003400c40017130340c50401c001c2c039040d50405450210f00d0b4500714001c0018035000c8d01412003101400c01140d0081c1e032400c0d00048004090903000104010281030440711443c0e007441582d00245040c000000344180000c80c11203c4000d00c42415a0715003500d41100c00b03001d45140090031000c10701051014250041c02202c40040180071840c2c039600410680035244c1a03264030002d000c007090000c041c2c8506246801d40036226181940d46080550b0846051a210724800e0744130b403036488510f01007054802e40000c0300c40340d0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 49991397 1250 49990147 49990189
    0x318021909050c032d0705090a05060c070801050a09020607080c0312040605040b07110d0c05030c060c0408160f12020415060801090c02010e0d0e0d05010c1e0503060d11 74
    0x642003211030f5450b030083e2580800007a0a0780c0d82d05242d4064003582640c415a41e5001c42d90f03889001c1d003524142c01080880782e1104001101007402d07140d0b103000e00b101207a4480109101c500d44020142110b07000340110503000d0600503032402580380d031001c035802643d0154200f81d940440749032503420b5000d00c41c20155140c5501060106100307140d0080350103140a00c20702105519041c8003524802070b0400c1158140d00000100040c60740220000c071000760140094a107811620348005081c803804584503180e029000c14180010039042003207101103002e1003105545a030a041d82e02030b0014441c0704203803001007000c0c0700383d04540f40e9070000401c15944540700c440700b603114100640580710034016420f00600e0b040704540c200d071050080707503040001c0d58040c0812924411007296540201b0b070a098004504c3e45804d4005030092242e800b044007103a40d003820014081034540c0303000101d1010b0b2000c002040c401e11415584c0c04091107500341d885041c480160604a010400030380ca440102c20f19a0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 49992647 1250 49991397 49991401
    0xa080c04350309090a05070e1c110108041a06040e10060302040b010509061603020c06030106020703211209060b0a080106051305010308030a0e0c0a1e06031802190905 73
    0x26919158021504056003501c036003101159440c0ca0ba01d00501c080590b0000d0b182020514405540e488150000c15600c7c00c1c964074010782d00401c10000000003000c540d44040700e111028040031341c1200308100000d1174604110308054403604c0035039034030306a1068007140c1440030800302d41e00c0340e02c181680103112080d280e03010050f8107410001c2c942440141d01490800d242d60000d503101f001110010800186401c1c100a003e10045c08000d4210170200d05510070709908404564802c40914000c1c01c02e035004100150071483c02c851084581000884a4a90b5019551000d07030801411080001a2003000074504640c2c10820f010306584005982c00011218010801c610103421017030686200f611489114220700c6008021514248800b0348030b0107090011800302d00158001b054446488802c4440d000480000204100110381c00ba290343c000c40c1c500d0600c03401443c0f4298000300303040c1c2001c0000a61201d4800380080c4040310091061242080080402c403210021401511010008000d28 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 49993897 1250 49992647 49992689
    0x3020d1a06030d2a020415080f031315020c060318010506060403080f0a211e05040b0c0f0706020406030203091204080309090c120901020307030e01060302060a080c04 73
    0xa510064010040141803000046090400064111028003036946440c503035160101100340b8604c0702580e01070b240ea0f00d880e0a50150b03403240111002a0741d9201146c03545854001d040c0d10348266403013101c500360020700600001404030f011060455a1680e400200c0b04102c4000f00c1c2404008009035a200c44080140203110808185c8040b030003010000030012902d4103c00c209060249103c000c2018200300100e804030204139000d030103404012304222401c40305940754928020b4000d99941c0c0000e07510915a8642c02c4c10814032100f5a40703845003000b45042c50703240c60b2a004001000c1004911000401441c080c10314021511001d030065802c5481d00d84800004010f5071003039503894580d104545d0168000c016100440703080340c14450003549040c68680505c031203a00001d0944981c007105212090784030400c400050f00c988008000140daa141c050340140031542c03076807584400c0782c0c50a82c1c144010f0f120042150700f401150300b03120485903502d0600007002c0c801d0360021010084200010441 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 49995147 1250 49993897 49993913
    0x9010e0115090606080103050a061805101b03090b010506160c0e01060806011403060112020f07050d11010e1203090f3009030a020103110c16090509070305030708090102010603020d 79
    0x10750310305030b0007405480c3e90b51000300ca0b0520280000f9000b50444005600000d0075907000c102c0d6100f580045160844031910f409050800040e40d04082035100d00c070117600c96402c1420726101030200e09040041c1e402648484910100c14044c1a02482001842820907448100c003001026170040c04030810303d4a50f0840c2c10181e1080c4201c4001c25070b14000700352651b005007500e0321030062542c901402d5035118001103951403102800f402409500708000000c014041f40142030040c001c2c0020322886030303502d000504294100300e0000460f490002c4200c051080440c0a080c500409020a926a16028552400d012500d0342403000c40c415488a201001c9011b03040210140d00c554002031001d404484513005841405900d60341a0047d0b1a04801980254000d040002d1090b10a030304102440c1581ca1400610035103071145150030380b10412080d00c9030301a00303511101660160040604d140d4030b50fa40c1c0d000c0c00c680100b00366000305001c0c000da40b00f50300c140c00070758001b401d8294140141c102581 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 49996397 1250 49995147 49995149
    0xf2906041806030209071103030a1503020402030420011103070f142d010b0a030f050f060109020409150b040302150c0106090902010f0f02060a022208010c1b030e0909010e0115 77
    0x401521890300082c1baa40c081d10f202401601510051859991010912001081a80380f1000b005e0302030034001c07006d41c450b407001d90720441c85105083c151906020595039050382c5521621704100360b00802d822214004025148115804841c4101341c0d549403519100440100400c100c00340701d10f102051015904200c0801d03e0310304c07180241c140d01424211142600c1c981032400e40c10100c11402000080c00c10400420080c0c0201d06907001c40300158291030403e40281e21100c1034a8021a044c40609218407070704004134051002800b445140040000840c01103100c003030310a2000804c0020107185a8003140e4400080c1030003084180e8031415903000422032600180c0c00036100d5003407814960302404400001940c660001c000507650244008080c5d80300188208405801844c0110610075200c403d40c01740c5650400450506c140d140300510102c1175aa960300c9661050314028007207038014110036400801550a10881e03540e1640807809000010660b125540c030b01204110841d0011034960 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 49997647 1250 49996397 49996399
    0xb18060102100c0915230f03071d040603050d1202040e0a11040b030708191401150c0b01030b010302030d05030f04030c02280504060501030903080a090c080f010e010f29060418060302 80
    0x9100d06886ca49050107000304112500c0e488001c02c041003581d405940c0629003420712404216010b400c610216098403900d42c01101d103940a400d10441c1190009200000c845220804600b002d107041418401400043e1003041119601c0c84106603000b0658200c4015100070300400e503403030414410003010341c0030031100c45911100e514107817201081719000e2000c5003502224401844c0c0d00b0041010313182459a80b400003408901c08441c0000f845003c0000e000b54000e018180254ac55401414206085200c400702000350030020049045040c019054000d034040c40d03c00100301e0b6520215414035641080e104074503800d80004480f40341d000c58401c0544000352814041c0300e64030340041d81a9501050000e0105208500003400c2c0803880e4010882c0364001d280c2c901c4000c1c0c5d01d800440c1482101d01c90100d159455480c041140c5209004d255254a0100c108000351010500300d607040030a4507d0684080c0c4498030b412540d60b13030b841c2c00c0d14050403c029040140b070b203c088441009200c948412 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 49998897 1250 49997647 49997687
    0x60102011506080703050a06080703082101030f030804030c0c09020309010b030d050409020d0908070302060921040303080702120a021e0601030206040b0c0a0f03030b18060102100c0915 81
    0x141c0a401c0c103a03510a02100c080e500d9140c419160940240c010b420010400160140c0c0c41c00c0000e03641c241041010020750003000741a82c4d901c0034090040c1840c0c891003221000c01032610040000a502c01d00d000b60140d018903011171580c81e01c0c9000c49800c401d0031000b0700505040740e00840c4840c7e080d8010340c05403c0000081003000003c1050548801d0444140d501164083c40304100c4811141c00a06213075074070080c0000c00010541c0c8032001900030710811740c0107074058401c0020440c410404084130600151440015943e00d10382003005100c0c900008080207182c0001c24202402001040c40415401a2050715000603000003555000a9580030300c0f500e807000d40b401c000300408281181602d401a02080c58103040a807a544036074000d192024980c40346003410b00108054003801e0300740314413a0b07801180c1c04440d0020001d06140c1000307104160b5005170180440e6a80018010006800d03207900400c8418551409460b8040c2ca82c4c0048014030201340070251060b40001418481440764410b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 50000004 1107 49998897 49998911
    0x140a050f1302060d020d23090307030c03020c09090309010201060e06030a030c02010504030503040e040c1409040b07020703080d0501150503010b070b0c0f0d0906051513180f030806010201 82
    0x80b070b401c81c1c80c0e848a1103102555042100d02e47c0e0f241c00c1144070207508000340c0082c1c5901c1a00c03001024001c12a50078010540244844202000024920002c0d1f00d440c0b92204e03101e80c09150a03a0040d423801d0310214541030003404541c000d200140c0204218501c03a502500d201d00005001e905004041c440040060401c01c001c2c0090201101c1daa6120308007072803c0b0340c801c00150001c690a0000006143c0310346c40300041c1940c000e0300701820810b01d40b036071081a814546a40c20141142c080000e5040030382d4650b40005048440b000724100c401e1410b0a030445042c0001c0c041c85080c403c00308800404030700c00c0d18000b80c11a142e5900149450080e032507400c0160f200c03114101d8030544034400d02c028016a446441e501c02100412a000810039800048001045800f0010b0850792809581c241c0d22000b100440c03115401448800408183c0c00c02914a8208403080f600640c01c180c6 = true := by decide +kernel

theorem cover : BRFrame.Cov 49820147 50000004 := by
  have h0 := BRFrame.cov_init 49820147
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 49820147 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 49820147 ≤ n) (h2 : n < 50000004) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
