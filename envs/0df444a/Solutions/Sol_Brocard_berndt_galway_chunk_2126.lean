-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2126
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:42:32.971083+00:00
-- url     : https://prove2.me/submissions/ce992688-9a16-46da-93fd-529faf55942c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 382194244 ≤ n < 382374100 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 382195494 1250 382194244 382194269
    0xd1401081b0907140d020406080a0203070c0b04061b021b01080910020901050415120605120c040504080d06030308040b07081b090301091202031803011104060513091404050d0f09 78
    0xa0490b0b02403502000f15541d42021151307100e5900107a00c0c004e500601032040409c94142c042242d98a4500c207481c0305000c1078503101030ba80130548400c4410900200201d60441d12565501010410300d03007421140c4000c0d800801c4604100402403a22031644e10303a050422604008100c042040020001e255a000c01d00041e5122001c0004880600c02d40c1c000c0c10f882c0160907c08045143d1200303654a9000301503004001b070988a00c01c114149914000d544000e60058860484038940f950009422510078020700c0e1511854206040030742d402e40e1301c1900802c030400100000d005103503421b29072241030303840d03c080fa0345003550701c40c1050258080c0d203080e403020118006605407001d512460741940c11221407403c80090150095413580900d56071031802d82070121500950505001e0342d443c12034292559030400d07007400001c8625400c100c81d04049100c9160000440c64003130b01ca081144144d004e4140c1c0d6034605824100d103444c140700d52030000c00403101001003201754400342c0141036828070000790 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 382196744 1250 382195494 382195501
    0x7080706060f03030804050d360504140403090602010b0120030d06080309040e010e030d05061c11041103161b06050c0304050c010f02101805030d1401081b09 69
    0x240d00800c6141c00c180442605103001005054200008512403032007002140d611111010049404480c080c2114040c3c2c500f46032010004e0400c424542e49103640d11000444076592400041d0665507002410048814290b0511090550120300e15002d008940002c2c0070800c0e003100002c2c8810b85120082450940c0d080c0804860750081c0105c5141641f510014402a40c40344100368603a031008031710901c5a4901a280c0c07000440c1030007107448003c1500055400c2004120313040c0041c1c14020592584800400325a503500440d001814007040e000700c7c03481440000030420b01c42200d41c000c5e0b814040d001e003070081105481d110881c109440904d481c0102240c9001624110341c01540740000382100e040c04200031000d003080002e50700c158091000c4803130f403510240c011b40300d120071207420300c0058001d0440d00080c52000d0304400710000300304607403122031a2180c80d110b0a68002506c848141c030340f030b110748091034119002804c0c003500c003680103000c9003100960341202ea40c41c604660790182c00d149000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 382197994 1250 382196744 382196753
    0x90f0c03040f0f03020c01020d0212030115090512010615080108030d0f0f1a03071d0a0c09030807030302091810090e070839010c03050c0a0206040626070203070807 72
    0x40c60f901502c0c0c0e200001c01407402a448182800c2a030340144180c440000f04d8901c0003a0010302402512541455031742000a1668410010749038a820700203821400945510b035240e4410105d40720000004610b0f00b40b4100740e07201d0089070041e10411000d400144081c0801008442149807046000521740010703220110180c6100102c00d031459150924181c40c040c85240c0f500c448090880540d4070541e00c40150240e62410202010003045c001c100103000c441c0380b07a04c0300c0741e90462802c1c03104915540f40e075030314001c5e4002c4004a0002e40c01103003403102420000d10300c101008110030315122902c1c000c54550042e0f905481611800f5884507111868107030244081d034040c281d5002640e506100180f0f803500320300490380842882100614241b91643c0107901f80d00d244960507941c1005900f5281c400321a160840c4400c00014000ca140480050365184001c000500d01074892151201c030803a80040320700800c1410b40c140b014528104214103038080304841005502003107080e2141e0507801c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 382199244 1250 382197994 382198013
    0x1c02120a030e0a02120a050f030304120804050f07060f02060a11031302060415030501170a0b061201140f061002120405060f0c010612060e0d020705010834030605090f0c0304 76
    0x1400f030342101644001c20603540700071581ba150140103c0440781000c2c0d000741302e00d5403880308070b501a2480e000e640c1c400e00400d06c55006160014000d904603aa11128081194102445a80000003066035558003140780703901401100c1c7d003c1e034054001c11140c2c86c03d081c4001140701c010449141c01d51500d01600841d520391081d10041c0480043d100c450361000c11019008050038011982d11031468840d5a0202d500005c410181c41d5201701d00c0c8049803211414410070900422144584e9501c4408507040c414490228030310031340d4a00b621100070300b404801e029a03650301d005800c045401c0109803a0310b40303000b44100c6048078000d4400702d0766400120b9208a03140070740c088140d42542000300c00500d248600c0c40c1c80b404280601300410004104035441d980d03401c204030461015070001d04003000f4960041a003183d0040045811440c01c0d2200451600410340030390000b01c544040381c00180078183d2612a0790040c110990300001c2c0b40c10442031940c02c100c8024071000c1004030000004081008110 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 382200494 1250 382199244 382199263
    0xc150b01030204080a0c0503070e01080a0f0f05150411040903050301050f06070b09060703060e0103121107090608070f060305010602100b0f0604180e0d0c060e011401081c02120a030e 80
    0xc058403141145c41c030b0306000c124600e1148921a214007c0c000c10b5000c9030307010481c12520b503103004000e1450a980d82c9504280c1e11002601c50103c1c203030160000c108240b0400300a0441e50643c001c4030300d058684403405003120700d02c2c10700031860500088c000030741050490341944d600312400b820304006500042d0080c418140c0c002c040c0000c000610458400c0000c2c094010407031510184901d075102e810900c514402444050008210100e40d110514068000244a2444001a9445c4070340782c012140550f07000e640301f0400c2d684a6201001080c900758031a03006032103103141c280003951411038002d681354041e94544540560700c4001702100da0760107100340404440a031145883e10768504c171080c2180c201204da10700140c10004000e182d440044ae000c0034500c0706880d500100304070b0780c90341802049a41482511903507a40d0b034102e9100c04c000012802000312074001c04070301e480c0756400079800003500c2c0d000e0103651025203100c410340c001c0015541c460401d4236000540000e005030903885d00c822031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 382201744 1250 382200494 382200509
    0x10020319060816050f13020c0f060105061303030e120d0c15050727030c0905060f0d0309060c02061c020a0f020a0302060f0c121005030f0a231f1406010c150b01030204 73
    0x423032201204010401201d443c2d9148141c0e24680e903548207002603807140305203080e08441c1c1c810342480040e000e9029000160300c05003e5402e801487c080315840c161010000102280c104808401001008000641c0102803100e042c05182402c56000e00044500c2040e0b00d45030440b8009050740c0c01c0c00720110380040d5005440440020754510800c4010441540d049011302d404810901c958102b42842c1c01c1010780c950364070740505e03290960451321407500030000c90784140c042151060040f2824000002545882801695200c002402508002d5001d07200800e5422070340440000c2500852403e5001080300f500e4841c03562440940c00031885012a07002c4c4202c40d440510070242506030080041d04c1e0180d0448100d24503409041740c6d03a00c2806d0005241d10412580d080301034dc907002207015450b41000844216240c500501c40c1c503407003004800219646d84030f003440e000c06205022150086030a0a10b80901c4000d52282c41541c040424005090b41e11041c0004080c0d210740c0c1103d00070f002d04c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 382202994 1250 382201744 382201747
    0x3040305072118080105041214040902120604140103050c090c0d050403090509010b0c071509050d061407140324031608070b13031410020319060816050f1302 69
    0x403400546a030143c44441c1c400801040d00c041001c82c01407240c240290740005007100300035404002101c049080c042c0e4102040c105000c00a0341308814005040c490540d084607202d9840c1c24001d01c0211016641082400c10401c4010004a980422031b5600160252141501d03999503004072a094030640000300c1500385000e041109050380001b007042503039003c94100600c1d903a60742e242034080c000c441006849400201e402c21401001d0410b6081c4048141440300b1a41e583d000005c0000c0c44008040d00c415032a441e240070701501201100b540102c1e00d0030b04501e04019420010914080142218944000000381d040c03814180d4507604500e180c001c00301e50780300043d24200340817212144107a103900e104d010000300d40c8540301c02c281e070b0308400c1451407440d0851440e10340503982c1c45c80d642d81e402c150243d2095054010124001075108402000c02d064840d02003000a001b10741070b03903100380380b00e0b001041c82c40c00d0071131807404200845400301c9550310141c2640d00007900c0c144d803007010410002d20 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 382204244 1250 382202994 382203053
    0x6030c09040c0f090e18010509031b0318010e04060e070c021806030316080903030d021b0109260f12100f03020310021b0a08090a14060304030507 64
    0x8458010804204160380a020701055002d0aa031650b00b00603a00020502c42402407201c0d102d030180656000d0340040240a01468a0040c035003112401e41d58895039401c001292003c94580c696034408800c0044c000b03607c2d01072407811182141110004181c100140c00c8101d4140d50340e00d42080002c0e2201032041c04290a10001c0505020400d4008034050340030070071800b24402d500b5660314032556000d409585860a0014020704075201003d0803119000d041c00744201e5a10104040e02103541c0400d8010303916000503a0202c500355002c40c50210507814078001c01d000803182d00a90f0800700480030801d83c1d1104c00c40300040103024400100c0c0c0d14880200e4090690800880410301030903081c2c248140054948250301180c1c04103000c06501a4046400c031030411001e68000e2169034184460340801c4510000c49508200c07501c401030703800b0319010405030a80c0c039250b20082c0041c003612b840d142400b01071401007441400010809020300002140340000c1c42a008030600101180107908020542d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 382205494 1250 382204244 382204261
    0x90f06010e010f0f030c03110d05070b0301170c150906091c14060708040b22060507030b030a03201e01020d0501211704080a0501020318070605040306090f020603 71
    0x34003d00c19050740000a290029202c0e440e0b49840d4296a08195612a01c900f140c54810212205481040d00040350f18920404198103003c048003074107800401301d50300d5141420f1100340c420281021091900506884103542d039840c2c11080000310b0880710340d500c3e2050b0500180c0309008011802c0c1c0c20005022800c600c900301503107004c07081ca00ca250310708026480903016540c1d5080c02c176413441c00b0a0852000c1070204101040c030136485410808000c00484015030144403c0345a440101c81e0305440b0418801c3c49a0140548022038109900a281d40091510010030074030300340703400c10f8110955250000394040e050200100d08004004000f40020164081078000d502007104003010505e0003002080c1e0502121404a022400d0301a40c42000d11503241e0301301c1c0d50b0310b241c083d507c0071070100070002d012a418808500c1c1e07540170b1400143c8a107401ca03e020a050005405143e190704008130603c90301d40c1060690b020360360411030006801625140405840c107034500060750015000c0100030722603 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 382206744 1250 382205494 382205519
    0x10021204060f0207030c080f0d0c020313060f02070504050a0f020318060f13120905030607020f0c0609030a030f0c080d060303030f0b060f0a020109061401050a0e090312090f0601 78
    0x80d84036a20801c075988446a16000720301131090001c001640140350480410340e0030380078080c96441e4645103450302c040c030b940140c2155115080000980c101092004d40301c600030032814000d080c82d00341308000c0303080d865000303440c0c203210b00a4902c9076a0b20700c08a03152210360f60007811110445d080456880c10000d07007606a0508005c5401d44900c148400a09000b012081e400c0c0540303019030945008000b6650750603403182e0b84005580402101e01c41c0051582d5040104602965254010300072a03070020012074107014040b00740b54010034003000380d0300003170b03e000400d0710017503815192402d0761400b9188110340c6520004030203070648001240107110700d200d580c81002101d100762000c0080e145c10740003000940d19440d00c2c2070340c4007409100352681a215103004041450841c4000601c83c0b141740c2c1c03801c04840143e4105160071a0040062000341044403a0f0005015280304c0c1e0242c500c7c180c500c481d902c1c859044642c240c1c100000200c0c000403410010709034014100000d4503c0e035a150340014209 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 382207994 1250 382206744 382206751
    0x2c060120060f1006031a1203070f060b0a0501051606091a09011d0a200f0402030108030a0327021009050d030e0a14061e072118140f0102100212 63
    0x2183d00718000100140244205002000382d21048000580f05000304650890141e0060105000401076103001440c5420b10f404584c1c814000007540030120003e00c10190721a03049507041c0706042040640940d0b147d140c00d004039070b12803c04610555a880d02e05001612410200d164061041c05d20103070100640160110801c0080c40107614145c04201c1c5035200c44042001c3d00d186a90000188400082c11a200d60198090003a0789050071420209080741c0c000d03406044680c10105e01e92402950502660032500b084615400d0100669080300d01a0302c01003400910070319000c0003441200e03000f044050300908008250740c102d90040c5c1000f50000c14244102e43c8249491140424500310312040c00801032400b0f008541480940c520f800500c0c201581c03100013102091050500003643c400e50012000c101c091850708290120074080d10740303070171000a03407010b0302158400d00000f45140144400030703000702c0318041800c420b03100617400d2200c110304802d03c460001415084110550100500 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 382209244 1250 382207994 382208011
    0x9060706051e040f0213020f04170c01090f2c0903030708010e010b1c06090c050a03050c0711060304150c0c03140c0c060c120706062c060120060f 64
    0x360355102d4046a010300030200c60013040304526421070301c094103203c810100c00c040c40e107000603c0c1103164100715105800c140c0c0800c0320704841404106840f04244089201c400c002e0030030010190428001280707414035801016104a040c48074910b0042622120240b1031046481c04403407420000310080d2694821911080490390340b000000341d83c542240c05a040300c500f10890f82c280214405d0083d4000e0307900c0d00310b0710040d40798400404c0801603445280c00708000d6844407aa100304600c009404d6580042160452110a02611012408418044000e1401200c0c0140c0d690303101d00c4c080b08021041446080c0d010b180406c0c5200641d040122200300c0750080e200c5000300b200018000855205054041485410820a02c4203d08000c40500303c40701d080400d031520316200f40d08802881d0000b4406452071621810100018880c002c2100d004540d9034244c05035901550f019907000c2100600b4140c104130304952440040c420154100c1c050070038880c20754480d410b011006108c0754805941005 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 382210494 1250 382209244 382209271
    0x5070b101e0311041d0601090c12020c0703030c23010c0e090402030a0308190f0606090504150501050912060c0403021503093310090606020d020a020609060906070605 73
    0x580d41c500c56201103079400302c0c074000051145401e000c06404a20203000e002c0620391010f92048a0910104c1d000e0308025070000741c3d10140a030010400c103c0c81c901082e05900c1007040b959400008102c08068a405090540d000c20480c90141840e0103040c0f0300307610100c25801074251041064104040c100c0207541c80403103144001081141c0c071002546c0c0298580d01941180b800a170213035400d42e51150031408207054440f5038000e5003082d0f49443e1111000c2e2641c6403002d12403681c003e01228050001a03c0c00c00042c14002c1c1c4811042045000b007506011020481c01c0c1580e403504c943c1c036810210321051b140103003014500c00409070420b000c1244140104625041310400c1c0d0070a0760310450010005101450100803441e10f1070414040347c03028040c06202604100c90880300e040c3c003500300c030000c8048a524000c00d0100700d60300d5800220454105810a1000300d5001030604500c81c2c045540543d00c2a0480010301103104000059070170520100d0714005010040d408a88210507020181c03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 382211744 1250 382210494 382210529
    0x9060207060512041104060e0c040e070804030815040e010908070c0905040503030c030c09060c1e01020f040608062e11010501030206070f0221071706151005070b10 72
    0x82e1603e02616000c1d5081603480310025000c18810844101080e4000e800090103e07200c60000010074001c03102c40700044400101001006040c200581d80940680b0300981c2134240350740e00030320404000d44035240340c6040e038090040580e1940d000d8182012824020441d1541e14a4905a0703500142c1080d6034070000401d0000d50380840f402440c1c89a94401c0186240d691520840801508040d101d0f05000c0800c0c8100035003038136a00001c0404071070b51001080b2001c088024001a900070040c1c0f42c2803640103204030100003007400180c82c1603400034200440c7e10794034030700070032a44040c00d90780500c4c0d9034040c40505a20f082d1000305666409441d03a0710019548000481426030f4400e01c0f00a410903010003c003030114510800e1801e840380300503d101100e402e20368844076034241f40c519480080c1c100d40300c100030350a200c1500b400030796810ba015041c0e510301181204400d0502c0e0b1100d40c002c00d02c0b41d2426000350f114008880c1995440803030712480e800c0c41c0f9807140e403a240e24040c404421500d02c074030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 382212994 1250 382211744 382211747
    0x19032304241409010b1f050708030f040b060d020f010f110a0309060207060c0b0601080601050705010606020705033013170d1101020c071a090307151b0803040303110f0a0906020706 79
    0xf4917400070006045000117005a51521040e900c10000040400c6070500c440c01c000b91b407120056000c0c4451601400391420b0905010010030000b422003849050554003000c01070303c80780d0300f2882900c3c00742860048844001010794800310000855241c5004025144d001c0607003000001c0c0c01e840440c0e084800407a22801d0036079600c808035002600d805000400600c0c1036102e103070203550000043c504242020380c0c6656007801d4880d990002e0000d038102d40c20600c500e00781041582000c441840030102d2554084400c0c0700d9254405e00707488a00c900c009003840380b0300020410705008040052041c1000002e071000b050b241e0039018903500010f480d1890310404581c05000340d440441140000c0c01400c3e10b490105c007401500000f0040140314184800742d440d56060003c02d0051078048044c41c5c19110b5604020000b5440c0b52420b29075400000300040851312480980b82c1c420360500300007901210b040c2d425403c5005c0c50318160f40c1484002515142d490b03122074030700101c481a400700c4504a80b550030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 382214244 1250 382212994 382213001
    0x5040f0501031704031728090806101802250c060f050426011d0601031104050c19021e0a03030f050105221506051903230424140901 58
    0x202814401780200014440c0c8641801440200c6003500c0050400791040e00e2147c00464802402d400310341024000c10505a0502031154840c18480c801d4000c0b90500b030701c15245100c14100e408000b9030118202291081e10f1413041d51124011500501290403854050391b10142402084000707603054103800c00c1c040c0a64251000d40f42070400301d01612000d00e5104007025410b64050f4040c1d9200c0581d00c0c0203041c41140c402c220b41801c4090304243d8194140418248074190300345000c0c501e400100700e4010150001c0c0e03040314640309105401d00c0b1240c00b04900e40000164000071078201ca9490080003c00050002190b030b100c0d450030b001c02c1090070129411030f0000d01c2010380200c400b000050761040e6250b02c580204012010005201c4004507c500c00100a6000725012075400140c0182c800c000c180e029215072041d03e01400700380c1d604668440c40e417102c544090480c404c40008039040080301054501010741f1610559280d0740d000510101429803d034030036a42994401c082041e44c0010700 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 382215494 1250 382214244 382214249
    0x7151b140d030b10320310050a1401080105090a2a020d02061005060c01140c0c070909051203190905010f0c0c170a1b1a01050d20040605040f0501031704 67
    0x100c602c69408a46124800030070448910505c0032012000744400070b60b8a800510300a88071010b42c0100e490510f41401000314071600700c40d1a40c104105043d0301682d000b600181174039001e5840481e242c41300c04254016000c403d05031440c54400c8150001004500c4601c65140c40c40f80e400c55980c00100c90703060340c83e00c005440241d081403c040e001c0c0039609204000300b09000810000083c00040c86036521204401901c040303140887c00240283e02c1502001054041e0021400402049481e56162561001440101c00103114080001034545001011886d820340c141c034030910901c80c0e2403410358004c2c5003110f12041010324000310120005c4c4030b01d800c018907681c0b08440c141c405c005d0804003032054110603000380c10003118441c0d050440116140c0c103010303e031085280c1c0a002034241151220030005030441c90203071080c1e190b0300300850920120b4800170b202c81c10884cac1c09440c4a0340818081d10240d00041c1d00f05040190002504081d079202c103048902a401040b225685142198503601c07503032 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 382216744 1250 382215494 382215497
    0x260f0706030f060b130902090f03100b09011707060e010504051f080c040f030818030f070f1401023f0d0e060408070b0604061d04031107151b140d030b10 67
    0x44000340051b1140e0781c010040103900401c2007000d60b648d140064940712403a441c0b6003200b0340346c450f0f5100f01e04110441c1c82c0904040d0001011a2a040c1c01700c0d99501c02602c03483d000c1200c41c486a00003039000d642200c028207130180440b1586500c0d03072844680d03040442640d000040900340042c21075060b01d0103035001da03503414650026451a42d00c8400640d0000f018800f8114285100710381e40769410081034003411385000c080c0c8451450010300c2c2d0303400b4980da8400c0310704508025503c0c009030f0340491a02e4002911003030311000443c80804011004940f206010314141e55100c030b940b68030001038050085c988000105000d80e0144404560700c0c0e4400b5138008210017001e01c0038000003002203540d20342c0042d000c3e0000543d20b0351a00369504030041242c000404440040a0004cc198030040300780b4009a0000101961032a0a4040002101b84c000200400030807555440b801d0610038001107525410035041c410124042d4405901c1d400641c04540c08a4603000c0c007042e1505111081e6032684540703 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 382217994 1250 382216744 382216777
    0xa0810180518120d02030a0e070602100b0613060807120507021b101b150908030a0c230c120c01060e0112020a14010c0609060605030c0a260f0706030f060b 68
    0x213090082004e0740018100002e800e03214400d850641c3c80400080008244941c01460a860030210310412204100c0c0f10380d0044008000714003040111084800c121090392408034a156207400c0304440501c54403c1024604e420007080c4078140303500085510181c1205c8074000303951480401081901c203002107001c0046030000079441200a02842c64001003801400c0c400c116042e0701a1900450b120404100d41c1071001105002e100c816500c1401d10305110b070f0a002d00c00c41c0e052810700000e40c1074101c6869000f500020745821003a000c2c40300d402c544211017411500d0340509007119010b013449000c1e0701000c0815000000d0700c9000752000e4060160080c1810a10b40d0401c802c160380701c40e1020701071381800f10603900800010441c1c4100c3c0030190042c080080c5046c1004105400c01e4014900140f00e01d200349001d01007542120f400e9010300300780601c0c041c1c00c078940c3c02a1a05140702110009018054144d0004002d078140d00b00d00b5000b820103c04014a5403a02c0c082c0805004d4602d03910740b8101c2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 382219244 1250 382217994 382218007
    0x905010903050706081305100c0824041802040518010c0f0c0206090117070309020f01020a031d01180b0c0601170c0103051915080d050705030a081018051812 69
    0x1000070542000c070b6840044004c2c4255241e49123055003440e8060b8543d5074810310880c0750740e13011240d6600803450644000984080c824405440c03075980c8141b9101c2e603542c80f108550503c00b100c0c120402039015005014034900401440b045011090000484c0c1d400c05d180400164811810000c1c1c059140e10342c5040c0c206950244002504504002418055103240c0700044001540c415449510180e43c04180c1043c1441400014099000d01c181075510418030b00b000a50081085050016040840a02c0a0551004071103011100e1244000c0144011010500042c0403004055140030001100c0c070700e9907154945d000000030700144540c180c219200340005980309800603038002c81c9107a00c1c3c0072101c00502e00c1300110b540541904403007500d003000400801000740f14000b92801c1c14100b1038107260841d143c150301ca00c90f8026290400820100040c40c0058406c0f02d10302500104078499080281c04020100070722080d1210f031003003015000040050000000c5000d003032100342004504204 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 382220494 1250 382219244 382219247
    0x307232509021b100203060607060b0d02090f0f060d08370c02030601092a0210090c0303110a02130b03010e0d0201022d03070c031b050705010905010903050706 70
    0x954a0030081840c80d211000000c000704980090901104144682c8600700448040b19213400706580040c240240140704012095a4080640e40055080140814000c84030400034043e200d8825001394003d003084284034450764090300c03075446003000030a0100f00351070388020031450740e100c0e0170f00810240040000c0311041109903402951081c840701a0b00c400c1c0a4420350001103881c2c40c1d014400a45450140703030940c51f040095500400206000300105000c505800800c0d90110000070000000040d450120b14801c10405442030b28900080104410524004a00007600c0c4000e40001e2042e925510300000b021480740c013a1a0700826418a003a800241c01e00504441075245515545e48c2c0c8444a94071020700014482e54056800140c0c1c4da1081240011a0059101e40703049220601c1030f8001e4103c1c40c0c000312a00300d2440d060030f0800d000b00c2d01c1c9c02c5904c03913904800715400f000c0c0e040d1316a080000010711030098400988400a040d615440111642c19881c800903000382d00a980411005 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 382221744 1250 382220494 382220533
    0x408030f0a020f1f0c03020c0705270411040b010e010e1207080312010906080f1f020409150f1403030d15050619030f0603110f0103021b030723 63
    0x20141c9005994202d03499102041c200420fa4407410520159180c440f031042a882c89094500320903030404605212513903030032035a51103141c0901c42c094030b032144248202840350091300c0341100641429004503e41843c1443c000b8802d591303039130700913030402050304c000358003910102402030b0060356510701d141c03ca03030100000300102030361200d618003503c0400701f01c01c0001e00042c2080e05d4084101c01d020b5240a00800c112072656100c0205600850901c0c00c1d56170010401c4605640100305902400f507a030400d210091041d540840e5045141c2099100f10705c07800408101104c408114015000743d0713615108203020424078042d03a16030820480700b051898682e1018180000164075504503c0e01d94010490f294001d5072400c10155070340c00b100311540d03414003911048405041081c0311461960f035900c00c0304240301c0b5015101c0c2820a231200c0e650b901c281e058442a180389040401184900c02000d0b80f2903000340070555554900150648062a040710030441ba03001220051039000c0d407508141c10f41 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 382222994 1250 382221744 382221757
    0x50609010e0a09020c0105091603050a0605090c0d050c0907080126070b1209160501050403030818070609060e09010f030308040503091009150807020304120201050d0501090b0111030408030f 83
    0x10410b910b81c04180903451384040c003c0300c00040000201410b20041281c900420000301841c0081d41320030a00005902041c40702a0395401203002c9126160140460b00b072294a20b6410341018005010a0622000140a000c0000e0941d040d50711620754500c101c880340ca090054500b84828100c160042450103086500c0c00d10145003900c1d851611203030f880c500e1307521081031400704101398018080d11031024003403000c403007400e082903002051500001800c140600d100260074800084d0002c2d0020700d441400901061080313061381e004544401b000b41801c1c0450140f040080c80355000707003000703083c00e4030329906031351100c2007400403d0310710b5504072849000100219200c0c0014170001d451038468003000410035440e81c441256850410359204c01280303000c2c010500b00701d640b100744040c0580100407034059990030f00120f0b202d40c550340010303180c074442d0102425446142c00000143c00f800d9034080d503039211003645d9903d195080405629034074092402040c440307800c104031400814a510005004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 382224244 1250 382222994 382222999
    0xe1218030705040203130c0605071a06120601170c0103061212050f0304050c09070315030b060604120809150a02030a030b130e07151d0907140a0c0201030b0901050609010e 75
    0x940c4a10101d0f090781c00a8030140c0c2e200343c2e008004030420052601c0c2802410051516a0070072505442b0a5428060030003c903400202100c0422442d0b2a00b90300c004044181c0c204403089940c0d103598110011004c194880600e010f030b001c40340401d40c842e006800403560361890300c042100032a1074000b03880184e03454042c14010200894910480c500d0080c5200380e01900c00b03482c0b0103405d07000340319541800801d080c08052400c2d4100c8041007040b2031140940341c000d030f540265580c42501055840c0310f40d4101c03003c5036034510907840c100315400000700b02c0e038542510b030351507103024940c508400c50140580d400090382051104040c810310960240c811510020b16000c070340e140d0019204220784c5411142886604408002d009964000108441d074031b0142c504601c009024410004142046050f501c0c8508041004070305103921500c03400c0040c0d490028220369403003400a01604040c1d04400c203c1c0400e007000c004418528025420904940002d851070b49400180300044502d103e030250780300c0e07 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 382225494 1250 382224244 382224253
    0x1030b36070f03110906070b09010b0d14150609011a07120302071205090604061d0a12050c091b0918010f03020f04020712180503150a0e121803 63
    0x605603444100030380c0501c19544801c51400541000202501d40c04011a442d504081001d110f80da1140300403140420307002120750015171107622103240580000c0080d660b020311500825001d2108000012090742001811181100c0b500e4000c004144c03070072206c540c4d2025048004101072119403489040350003c03000c0c2d2901c0d000c0c6a59480e111203001c0208100001e0f4041024002c200880f0710318828030303203d4205030382480302034000103080d4852401148100205055200100703a51346038030b0340113424010100920240c840b000307404c04040b00c1c1d5040d02c491240b801900c4550404603100c500601001d080c10a031130448000c41f4a585c0d00441006030800b500c14620050b2003401c9050034082d0040074413054429246004000c515a101844144510b00c100407003000544074100070001c5c50369038107101542c0442c04403034940741d140340e030b10003901405031a003030300d00c0c58072840545445801c400c603007080101000c01c10305650340c05162000b0f0309500c0c20400c0d1382074010600b100001600c0028110b5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 382226744 1250 382225494 382225579
    0x901150806282304060308090d03020109060f0b09070507050a0215091306090b0604050303030a051308030703060e09030c0601030201080916170c031f091e05100b01030b 74
    0x20801c0b0301907488000c10742004407100c1902848200303000400303001201c040c04a02c2c01d54482460318030402003100c2c0700320b0107402007004140c002c0d000b003286982c120004004410305081400c0203000d00340b0600c0d124480c1d840001d20020f001c4e0007a9421950003074001c0000004641c00d0100c1b01c0b81c1c2c4054000c100400b44080011681d9145884400c25141e480101c1e1103403070f2a080000784c40c240192148215000c3c07005100316200001602c0d404000c08002299540742c15000007100d0740070000c040c200702e0340002046215034040c3c12200c02c490380c40020301c2c21a521030000580b40c1c0034103910080590010801000558410700b80705401010081c1610421030001103100c0030000c01c1c0d4045623443c4100069610145400d0080c440c03d00c10a501038410600080405410925003120f6051265540d02d02801405145501c001c0390b2010107440d41202d1886040039aa00c10203011908112420b29010a6065100c0d0142c0c95003c240540702c01c40c03481049154040c8030002201500c0b0076901103404 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 382227994 1250 382226744 382226809
    0x118050607020f3003070218222a030f150f0c0e03070605040807090c0309200a050f030c011209021009080601080115030303020d15140901150806 64
    0x40641c4e41c8038801a46062280fa40c03002d405142c101c1c1c160109a800034811030380585c0301d42c0c03071002d50b19079040c004004a54507808181c4050688031882400800f26403804810015851140c00310031840c0b5010040c004903003d26403540416a000041c07000c440001542c000a018000c50400701000c00c1002c1042c4860742e40140481b024558004002080c09220f40c51504080c07208202401682c030307003103207028244070070603581c0d82c40c078403a181801ba62810b010030002c2c401e502548125900c01c007011030760520f840e0000c41400320b000c8142c0c8103030004100001c071454412400582c590000e4050164001400300540304802d4030a0b49400450301c41d1700c00c000595a4118614078103c43c1e4548141c0f450402c06054941681600204070580c034000066203038458001021048a6040c50b000d40d4902a400150028260103110401e1a05802c0c2003c9190701d541403200304050380c151000415a03a0b10341016040401c40d029a0020525030030204030b15080844440c6411001c0303030b01204203070707802881 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 382229244 1250 382227994 382228009
    0x40b01140d060e13020d02010c050a0807080c0d1715130905060405060a1404080702130515181b210114041404051e0f0a05100b0118050607020f 63
    0x7a40d40d41c25600c1070b05002e04000414102d80050100c40c050804050316400710b9030148002c0000790510106061800c1008810044059103552144800361180d200c0d01d0a01419000004030a02c107018181c880201c1a10070f08440703550081c207445504503522035410740588240e0b00201303581c01c907030b8600303840c3e00c100317540e0080002d40c911840c01000c6910302402c24504002c80544070740c480c141030112101d030066410844a4115401904080d035403040d078400039440c2403c039206008003130300380340401c1551002180810315102080d04c80055070f640c1d0010041c8061411140020314603009070b405e05c05500310001408050440d034000f10030724014100c4041031148241c0c840d040c9a00c00b040c000c412414140515034201121a24466039401c0ca544c529488000d200783c541c00c1146c068880540580e000c1001901c0400b06500340e0307104d000c0c0b6080c07650311034201911058101e07080a0401042d5442200c2d61075522600c0c06280c5040d41c200000c01403d0b61010800360b912019011111406584004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 382230494 1250 382229244 382229257
    0x7030f2f06010e010e01181109090403020705010221030f2a0a0e0607050c040504020303040504060303081b0a09142205101403031b071205150a0501060e040b0114 71
    0x8008140943c07404410358400b0405804c50009030001c080100a2401d945160101341200e07554082050008603104501c030703001740440c051788243c20700300b480141900420344c1c1d01136031000e0740ad071004490380c3d0200d40b50380300e00c0241244a880d01000003440c20030310070700e0143c0c1050f122400c03100714181c80b80b40c0d2440c0091000310301d4812180003441c0c040940e0400400d03200f91030103030352a40c24450035894854a07004400051400303103441d03900003401c5503824011503001d0708005008000c845d440c0e04000f80f2101084840d00501328a51083c50400400c22060300d003207010035030b100002d1a0800a078030710102c1c1c03114507041d04940d0380010101a080d02c03610008014140010024440c6440d0308001c0760249590300c41d80000c043c91286859030b450101c04c842d100350fa080301240e2401d40c03030f00c94980b80079036682c40021601410601c0d0010840c2c0441c030a040d0a8540d9030391102603e490550000f216428402d000224021642c100703006c2c20030b501300400b00d42c0141820341e498040d5804822541e403008 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 382231744 1250 382230494 382230587
    0xa120b1908030a08070f0504050607020f0616060b0301090221030c030a03051501090806010506160212150106110604031103090a0603150e1537091107030f 68
    0x200e94920f80301d0b800034055601001c0f510306441c0c1e0a613100d101601c28402c07400780c180240da0008600b02951101200540582c00280c551aa83e00c03001142c001510080d01086600a0805414400740d03e014060009215001020704004040300e56803106550036420628003280010300040c5070742c14060020341070a80254901260a107094581490701082c0c2d500501d040c4100c1c03201c140918580051034506441d0140d0f001c2d90744400a20758015003e4600c40d00a503c51003941030310240e120082107030044c4668803061175403241d0f00c40781c05444c1034981c40c141d16035075401500041e02086c440c5204980220000041e00c2c0f81c0120f01001c2440c00c14103402074004251680160784540f003180d001040240300005099011b82400030380c80c40740d01c07a818000b42c814224040c1030352100c0300c4810308440381028250f02421000703400040c0c5890021504c10a070019240c00019035945113604125a111345d410380d1403e10500d403902d02a51030f518141c01554001113040411411a84071040311035801e00103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 382232994 1250 382231744 382231747
    0x61c0c030b1005010201090b160c0c030614060a08061501050405100207080601140604051e09041b06030603050a023f12190302030a0212041a0a020a120b190803 70
    0xc001104010742c0d03a4001d9045a25001d040c201003020781c4040b9401403020b03080b18003a5451204101d840159504018200c00c00702400001080415400040c1e405040444442c1503510002080b072000c0b03003481582240c0d00124009610190482180c5903000c105040c1642440d0302c840103d44002e01300c044400169200840c24001d1843c02c000080c010412252203c00260f940300103e030060181c3e21805001c2c1101008d16860290041264030740b1140240072000b0303520301401c00038074003a5512646600e5907170001c004140144240162419070750004020101010941c0c00d0165070755a41a0707407061034402007503c844406501c48203400a48614000032554007440320b00c41d04100240c480c0f803030b80040030443d080c00505540042c140f054a2400d0058807660303138580e001c02a209840d12488800c0b810300c00c000400c0440d41c5111811a49601d010030260f0300c009a050132485068035050116000514280759100541c00000e01000050040b140f0803041c0011000801030a4000c503100b40c10 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 382234244 1250 382232994 382233001
    0x402030c03010506030c061b1203041704030209010e0a0b03010f0b030c0a050d12020f010c050403120311040b0a05070b0907030b07080c0304080f1b07150302070209061c0c030b 77
    0x1020424800c051608900800181c180000069540e010300340d0118010000030031460030658440080807600c00001c4241c03041403c41c4900911a0303442180c3c1211512509058528800c944800b9074050b00e038050103160145e400c22905040b143c20042c820702c20305440d00d0303411450391820f0040d0003140c1020240480c1d520800c01c101402d0820b00c0700d550740140310316401004243e5481e034800c1c40e02508001c0710230b01000c008000b02d0503c0200c00d5808035540c2404501036801354450020802c807400788040d0307686010980c3c4100d003521120010900954014002803000d2503008004003800e4030103040181c9446015540c05100805c100d0b104042500995001c1091142044210360f00007000c4c5007030961403828060954250101400190901001007200300f04c650048089802ca0060003041027840001021140e564100740c1c0035056503d41065455100c003802402542d100c20b038001d1810000d44e80c1c682c00e100c15003010100c090070ba80c00c200488030100e030500c131080c00a503002d51080d040758035 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 382235494 1250 382234244 382234249
    0x6140c0a12170c030a050c2203060608010c08012c0117060601090b03070e0a05060c060405071a2d0c0307020a05010f0c1101021e0c040b03011b14120406050402 70
    0x2160b03a1126000303044090b0400c925841c03510110303603008002c45000151500c9035009a1031901450b16180c404e12101c8501a81d00c055200c810001c581c419003040c0700b516204d520300b80c02d80c0c040425540104650a0041c0310600306442d458020a002c030912142403911032100c1507043e0b800ba400351056042c52802d00829031014080558400001e01300b05c10030600e0114907218a101c000c1c000003c008207a01e1101d8a95500010f0000a1900a0400da20760b07222007165a1100c0c1c0540341140d140c820560005802c100411910300310070610700c2e01500b4003900400140d4801300c40c080000a1021485048100302071080103403802c81c0a03070000303507203d00291060215121507a08060705025801c807000c2c40702e50b4488501c0c92466444290810b91018500041c1e00e030115807000c0b14040f16050402c0804000c001071303c41d0024900300e07803d00081c0500000d050032a480c107005024980c1028840c1d050300c90050111031100011000c581e8500400c910481035181001c1da41250f0054880e8188415403 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 382236744 1250 382235494 382235507
    0x1e0f030c26091f05071401020d020703032903030706050c090406061809110306040c0210050c0c1902180702190f030e01090b09041806020301030605040302100905030406140c0a12 78
    0x880c8002440b003155446021307103580600100144103071b103c0c840c1201880000e4040c3d0307a843c82640030540d25440b41d40780180142c02921410900900001c102e851000c490a011468441c0081c0265142080302d850703101c064030006100d41c10400c820401d41c500c54540b48a540000c044a5030790070400e8038122030100070903d56920028959040881e0340300c10340e900c20704072600710703400304d90014186110380020782c03d1544a0100f800c040c0c0c9402d04010f000d40a042c01801540d2480090b02c190910011149e902e00c0b202c21006500038104c0c0240501100a44518a03088110340c0100c0360000b042c815110003030001d08400701d03040300304490340307a04040c1c129403071041c00882402e111407030a00340f00c4408410301a940490384642c1d22084180000c4c0d0001102c0c0d09403d0f0040415940c030368407810300398041c0c0000e442c01c60040c4104201025800300502c58101c2880d4000065454149000e004a4030012548402001c5010401416143c2c0d07404100c401d0b4100d2003031500d401d4001c91400003a252 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 382237994 1250 382236744 382236769
    0x3030206040b09031305011b0501060608011e1203050a0207080d020d0305010b0c1203060402070606121712010e060f060a080702100c0c0813030f0b041e0f030c2609 72
    0x95813040c03080c10700b0103410081c440709070b410a103001790046001090300b8a18490102001c1d0907075103070240100b04c850303104038034a0503100d030100c0301d4047d020400503191141d8107a01c54014000200081c90001a200710007c0100600781d2040b00c0710103031615100303814001c3c17040c0e0101c05640810102d40b0b40d2a010701886006001d051540e42c02c1c014590402c03502c81c5840b0402c4d410301c2400000081541d5140d40c142c81200340c00c00c07800c00200d6158182001c0e00480e030801611a001c40010000d0550026008c0303c40c00c202c00f0400f1205e0b0b03480c0042c6050340d8400908001e5100100c1101c1e1201600c1c0e03000a01a4000d09680300b440c01d0400200181c100245d41c404880503e0030140c1c034504050b002224140941d0340301c038140380c1da0860000c84441400c0d4a0300b00400b0410300c20080c40502c083e9201d41401503009001c001811a0345800500420f10304680c001c007200f80d40e030000380100b80240408442d007401403414100380198030000051410340414450410301003c100d243c0d41d420040380400e003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 382239244 1250 382237994 382238011
    0x30507030b040e0c040c0201020c0d021b060f0d090305071a0402040605100c080f04050a060903030e041415030a060c03140c2b090b040321050f01140d020a03030206040b 74
    0x10740160201c019407100e0f08460700b2402251031b0352240c29407510075411201000400000e40703081c0a103d0303e0003034507005048510140540740003034410091404600311240c5a02021031039281180c0403007038102409240e0401c6d81440824041c3e0b4001c00d01406104007441114038980e652840d15204002c219070f410b0300494000d80c11002e00d0711000340c1000510440a0300440c0c03c90716580003030b0490f4005d1046800c0a600310146040000724140c204031000241d030300c42e03207a0b00b00c1c00c60300405000446807a09941c2d005d244a100102c2c008404419804111403c0a4182c1e00004103a8542e1402d55100f91203130300010742d803458000700b81141d4695090f0003102841245280c10300780a10b816040d54030700d0300c0070385107415141ca040d010240e5900905005034002003440746482c0c1410050240381e458501411940c142c1c05140c900508140308141c41120220004800c6074240000c28602d2005000c080390400000081360025984d003d40c00c800551017035004146510b002d140050311050007909141e07 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 382240494 1250 382239244 382239251
    0x10507020c09132102011401090903090501120f060305060601110c06030703051009050411040c1803061a0d05070614040f050d061103070e01020106050d02090112020f0a06030507030b04 81
    0x810701d0395003908881d08540b0302003d6011801080c00c00d4400c00400c1c0001c2428241e038a802c1074100c5406400c00078000400001d805841c0ea6140e0905082c1c1d1106180100012102c00c070500c80b640c06588414808040710a00103481e43c2d152a00c3c60449105400560f12a40706400300411503034003c060b0708905401802401800c1400d50102d00c4600016007150181915900055000301c04445c640008150803002845a4249410600e0348406000c031000e025504003070b1000400d5020f40c40f000d41140d540548020032602e1601c650006010541000e046050004850303a0680c0e650030044507141e0050000d404054500700001e8403050140c0030404a1007010b210030001d807400c3d150100d0898505464004e000751652410500420000d1101c000b003800c04420f02c90090780c8242e034035150103401e030001c004554075002080300042043c000254406c1040005004040fa007092500000344080d208070302c90a0740d00700085600c0c1c1d098004000190351103040203a03182c0c0c1800b42900070304003a034041 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 382241744 1250 382240494 382240513
    0x15030e0a06060801270b04140d09050f011b030e1504030312061406070602071704140a0e1506070602090405071206150804030302030403230408100c0905010c080903120c01050702 78
    0x104405d01100c1d03005801c0311001d90014091054212082e07100200c2c1000b0390350301d45058074000d00303240d1180c002d4174028420490350351910350084610f401c00139036070b008181300e45200769801c99000d074a900d411600f020041c820403210f03020b01c1003d00051442500c82a00049003609500f0481d195544161404255aa00170500c0d4540350304a50000d604040d015039a160141407103503568903103810003070206000050024000d100800c13448020f02c000c07509500060380d00c2c09624090300c42a5201c43d002c000b40b11076a411440c0241c024941280b01c1c3e00b0241c20324000200007800c0703071012a03581c404200300003500ea01040c0184140401b400308800c1154002c404040001d02601005100500b8951b0000204040c1805002c2610310b0120940708407482202c5a4581a0355400a10800050740300d4403a100c0f00400e400d020b5008100c150b070b60b032040b85600d090011900e00411120966a58034200071410301600c083c00071540035403101c0c641c0c5590700c14030b00756203086a40c001e0030001190004040c4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 382242994 1250 382241744 382241801
    0x30210020313021903021807030b30100207030906020f03180112020706052505070f030f110607080115210b031f0507020706090b030115030e0a06060801 67
    0x4211081d010740302081e50200c131141c1c1d82031440c2d1079040690b11500c0010000c00c1c0c0240120118400c1d103959405000c081d140200780300c8811303040344d042c0d504150150003030780600320304940c1e900c0b920402e14200e490f4081e04609900407039001d4501900090b5107603009100c03643d010444030f0041151000118070344506d10040c0c401a0200c040468100009010803408400d01601500e90302500810100a14100f04514420350303c07100c1e110707205200300b03545804026405001a00c2c05940c1002990b00d00325480d6030708503102c65a010b5000248141d618074500e0500007000040d21900d91034a80d429503505003d07500061001030f4001c1001c001c0744d2080708002c40804c400700c0d18042c0c0c0e0208003140d45c00e005000242040941003100b4144842500b0852881c4481e4001d00d00440c1030341c090f903401c00d0712540100c500d104c0c03500580b80036420810041100084020314a940c011540c60001400c00b20581028101600c5400550751591103401c02d01c00c0483c2842070000011420118082c0e10896012 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 382244244 1250 382242994 382243021
    0x1b0d05030f07050715050906070914060903150a0b090a060311040b0a08030f09090105100504062601030f21090603110706050f18060f0412090f060203070302100203 72
    0x11540d101e80c41c0d8010440b0301e80548151012254800d1640f5000d40d0480f032181c0050004454001091246401049000c4e004000b920292400e040d0503c42c0070740c1e030000740441070703014040c10b941510074541ca49a1982d64a01201e0055081c40000f1900305401c0c001c01c1000c24001e8400c0c110a8544141000054401d05840c04014400c1d24007042e403665450000f20740c0129030344a81100d020001c0c1030b841c1007000a00801552030200d49001d01640caa509100c0544403811300c420210381c080205000403030003058014101c034509003007030b0400c450803000300094100aa108486c80000d0102034070800c9600c58100d16007040d800c00c003128019146100400c640345500c502c0c1c040c10303030725030b014080c0107040c00441751012340006050009007080140300020302821510030801896509420101e503c000ca0341c90b010b01c011071103601030b50300c0d02c0e114903c140002803549014050031400004003000034905000c014020f540255484590302d00700603080c0728a211003c48028070410802c84400c0c40100c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 382245494 1250 382244244 382244251
    0x5090f071803060510170123040c080307060c030e0c1005090402040b03010b09030708010b10030e031605010c0e0f03190311011803030b0303030f04020603130807081b0d0503 76
    0x340488070380c00c000180c941103280350740010b04454104002c00960780b00410040d42242c03c0d41c0380c844441e114040d01642207e02c0346000001c0e1540581c038640056908100094100303000704441e2040d141e994268500d5680700340001c4440e280c42d09400941a9050f00c07519109c9a401c83c00340c48852091070010304030308150910034051000100381143d00b602d403981920042c1c0136081d4000c0d625610f030b0390300e1003940c2c1200b41150b2081c4100710000c1812201809006e0302c5030400b030b22100c1105200c08096016240700c040d1140d60388428030410852600000319a603402e03001b18000920480da02070003d0000c041075011f240210010125601d00e61070008810a44028078012000c0b0031003a46000c6481d90106a002c054540c2040840c2840b110540126817450340700c1d8604201c2d0b04d4811003896203e000031160040107044d000005009410110011a0300c40d2804800752003406c0656585051034014940503030706108041452600d500a104410075484a048010172010002207001441440001c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 382246744 1250 382245494 382245497
    0x2060f22031b0b0406090507050d0b16050904050a1e06050303250218060414010e07030e3301050111030708072409030e060a0507030c050c12070f05090f07 68
    0x4014000c07404029040b2018400d60000350b003840c03070a20f8209080130b81012801500c20340030381080040e82c1e00e40030040c894403940c0480300100356603a0800320101c0340ca00c14011340031321100b0003400302035580b80c0c0304081c4200112103000900d61011008103c091031840401c410403407802030140b200e030b9000015505072141900034034000d05410f8010a04010203894001d410500072a603220161000c15502442550300355010001060000d607003246415003803180200c085a00800711348214440d4001c1c855a008000850f0804c1c1e040d1040c03400c601c0d1448108000e481c0c05581e05000d03911031703908900c0c0101000d00e0102c18039001c200d400e41d268815010020446100020504204071520840b6141048400c0840030300c42080c400c5100a440c0c000821000110008130071038407807428809450880809a65050914030140e4042e180c000e20f4500c165000d00c1411281b1b115641e80c9419102380c3d066110180492519010300080502981c0d0801480f4030800000c004d0340d0141c1c1c09050b644203103903 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 382247994 1250 382246744 382246757
    0x16050f06070204091e03031b0804021207180b0111030c03030c0c0a080712030c030c20010e0109030c120e0603130f0b0f011e0f031103071502060f2203 66
    0x89100040c010704c00000c00600650500079542d400c000d90040700a80c0501a403001e0005400a40043c110480547c555002140004020030b0150600c2045031f400d00080c03d0494080c1c54403116101c103001441ca03150f8158a844001c14421543c2c040752201000200c00011401c050f10320306681d40740d001c011310745030344080c000c1440f02804000304140b54107550072204042d0b44404c1070a100f95403405034110344021900b01003481160511034400d007100400b00765540f801030320b0600c2c0c00c0c0313401c2804c540440700c0325901c960080c2c1c84a2420320032081074601c65201c8640850b01450404183e80c2c0180c02e88050200c0440020b2a94a0305011664465414842280b2802031442c00c0c5001041001c4041d041140050030481420003201065043c3c42c034011403120031540d400213a424032101030203640c0281c5020101040086d2040c4018140030a0044c01d55400546a0420341d00b0070990035062001a8421405e20075903480024005401082104031580031141d210408002c504503944001c080025 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 382249244 1250 382247994 382248007
    0x515011403120427090804090b0306150f030c0415030b0c0c100c111005040c050301090312020d0b0603070c2f1009180608190c1a0702040204090c0216050f06 69
    0x20000c02640c45180d451030104450744403406c5c9881e107500300380680c062040c43e01c0d400c0c0c0098034000601c81d02c585c407424031060000c184401400b05042c21054005d8141c420204488034585e2140078102c40e40000003685001c4528502f0a0021808081c040742c43c1d840c001c010500c68402c0205220b5040e904500001c60186000c02080325500042c082169031800351010305240640741c0c0d081280128050190314030041d468008044c200c4d284280014041810078900400c40c070803030b402404082c01c9005c400501d10700d21201181c415441101ea96000170b404091000800c507800707420900d0848400b013040d42d00136609050802c030f6901d20f1510b80c49411590102ca0001d80b10310011360141940442240d03803110805a80c0c0c02401c064010040c02c0e016a48501280d00840c4c01800c40e0103400c1a9a40c00311441c0440141800503484000d0842c81c000704040805610307140004c00090844100c005032404041c0302c02410081d82c1c02d406806610490307005c10846d600ca24900880101c01c5540c1c980d1004d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 382250494 1250 382249244 382249289
    0x702010504092a0302030112030e0a090507020a0b0a05040206040e1504020408030705010b1e1c080313110306010e36030a0f050403050d120905150114031204 69
    0x100d9105a51480c01c004004000181e0300600c1d03184080440341400f4021024038080e0140d0009002e00d44952130000c0a520100744641490340c500e82000d090074400325100c40c0b11100b560b01c00c0b2500b01c0507a0010041408000103448269401020303964108854101540080e900c0c5c8074500c030350495840f1000110b110341103080c80003840004010801c640d036603503c1c0d013801e440c0e13080301c0342c20355503540707010003400b0a030602025a9400b80c02c2c1c11881c1e034092080380c0410040c244001800c5001144080c8500c00180240c0b00640c05a4213103040c864000d82d00b41f404802c90598240424040c1d00f0106c0108070a850300c1e00103070b030400c0300d5122040780b400c12200310286500c0c81980181000711080228050340754080700070064841301d9503600c000700640712416240c500c2a4400140150b1001c5200401c2074810300b00000f0104003c0008921280c4544509207810921940d24041034940740041110140e0106240c07000c1509038042e00042d80d500c0c0c5c507180756000724410440181c0081c2e141100e0503 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 382251744 1250 382250494 382250497
    0x90a0e1603051e01080c0112060f050121090309030204050604021206040e0f070312110a1203020d0207080c150601030e06221205030601020607091217040f12060b0604060206010b07020105 82
    0xc1031070f000b60f11400d41e551410b2a82c0c0306001c03c2d51501003113204507078903aa0740e0765014800540c0c410058011000e40740c03800455000070074010f2480d0115402e911820040000e005401c0c06030f0196441401031421401000120f490291001e88124030402844013000d9104082c5640401c08440004801151840032424081038a04411071806400c1002c0704104041d0703d00000c110305650381c4c400c2111920f48999684100840140c42c4030025031150403118820b400a000721984584098280310700c82e074070700d207046d002031400480320b41005540c648080c00c03084065500040902e400c2c0000081c42115684075540900800f1004c210201302c241640d030240c070801040b641c40202e00214443c00d60b40200203400980300d030b90060140b10301040180b885800d1200542d0603d5001d0340614840d9911050300b5807070401072000d4400107000c009040200c540203d0010891040000d10300012072410a04807480481d001c2c0c0305202c00c0c03005000690380010000d054500e08000c060382d03076410340010703200c3c0d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 382252994 1250 382251744 382251781
    0x30b0f040609050405061612051b0c0d030b060412140f0d1d060f12060406050a121e050304030803040303020904051501180602030906180301050903090a0e160305 71
    0x142040c81c0010b460007181c0c8120b104a00034015900342e45c80e400c00254145030b600781c2ca4000152220174a4800e040c040d03000503007110b8075103a805a042c603048401c0003a60402d084460044d0071002100c0003050b018065110702d003c4c110341041ca440e040903c46800103245400c00303000d0b503070403e582da070b506074082207414060000c9000300d075a0303500408030007011001e00383d6041410700110280c00700d050500c0b00945650681b6241411306244488481e00380042004002d9075000b915030301c0000b260389a20300d8203000340003850761103400c9080c02d00700354407988802d020040099990302e04100200b030002c0160b8054940c480142c542d280c0b11414224042c2c00f4803407540e54494a420103100784002242c1089800106c203803180502c48000c885480380318500f40c8a030a015801c200010703203451401000518018900c148007544001405020a08681080740c0042d5035600001e9151041d00e0455010310040516050910740c07480c00001d600102542e4592107400d0503141c0c00450954403120503489072 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 382254244 1250 382252994 382252999
    0xf060105240f031003120302030606090906010e12030c01140603120c070905150f09091005060a12050c0f12070909170c10110c120304020402130b09040f0e0a0201030b0f 74
    0x2c41c0d0901400b40c4540210a1100300d40281805c0c407106e00c028024025640714442c0180180d060461150a001140c58000c1200b4104910318031824640d64030700c40c41801c1c01c0d007010002d544488141002d0780c21602010003070034650b40c8540400180c2e0741d0000b81e1404000d1503450068507032043c0e80c5082c0c0f902c10103400c020b80752070601040103d40740c00070104074035030203048614040c0c2c8000d0805021821009440e06d40e01c6400c1003401d50354405050b00035a4201c5c2c8003409040400d69543d01a100d410504c200c111241d81180c0742403d0545000004100c046202700c951109030200584035a5a80352944510340d412a251450305e07003840039199050070314081500c00c0300d03662030f002c0701b0aa0721258450a4900381a1414400c00a075407041d04c240c8580340343e4280140102c804184c2e10048581000300101c0c0c7c010340811144046800e1443c0302c400602000c1080c03616101800b040105171111545445482c61511202c1522813800040034403c082e02800c000a005103d24040340712a0200540e068 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 382255494 1250 382254244 382254247
    0x2042309121c021201170606061c091103031c0e07050901151b030210050c0c0a140f0d0c0308060d0b0f090a06020f0a0e150702060c101109030f060105240f 68
    0x145030071040b1b45807aa116a920980f0580e554a00c20800c83c0d014800c415422641d8205040214040e6a40001000d038014210f0360100c03014a400685035611820003000d0451254020f42c00075409401105255050a00917014040c20b105c08540981014458a40301303184100d4625500c5d80180400240b004c0d40829a410502490601a5a58410070021400c40740b50600081252034044140e44201c00e130704018154042c4913442e008100f1018803040c3c100d90013846151404003408008040c090340080d22044205001402c000d840d4840c01006c00e070142c100007045c00001900070b081654020755803e0341c005142c441542c1ca42c50021500c5c001421940b00068411140c042c081c003409103910980e9404000c010b104086c040700000f204000b243c10f00c5c0a20601c4010701c1e00b10f002c0c01800540d60200c43d003082203003143d10107403540c4001c90300d07401078000303001388080c24241304446000c0103403070040140354074000c045070000050010680d003040500107080030f0081280704807901d8988646841c0d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 382256744 1250 382255494 382255499
    0x70c030908060c040e1f09090c0e2503050c0909070516030908010c090807090519110702040b12120a020106030b0a0c0e011e05090a0302042309121c021201 68
    0x2225981d100740030314030903c002d520021b01003113600e0600c09020b200d0705181d1800e080c5040031440c05040701180460321003409143c00f00e503c01d4079041140c450143c4181c4e03031035084825240407041c888800c0048082501708000c01c0303481c07506981201d2600005a0340c465a035500e0340c508903024000d41c5040d07590045d40d0702480080c146c0c400c80302c0c002d40d0104070081103011a03400d41074402812a1107541c00f550840c1034100220480399000035400f5805100c401c045c0100340c4a04001c450016030315103208407006c241041581024841e07242c0c00c0c6003c3d01c084000511001c07256039580d00c070000c800d10704500010020440c034800e4018000071507100c0380c080050700781810244080d081507040d0b5400902c0d54603040d000d135031241d03981c1c5502c00d5450000b040704283c82001158141e01c04052181c020221802c000010786580c4500c02250440c045903110039011013041840242014004145580c0040041c010003000541210785010440c80769084d4403910381c2908000e401113075007101d1100b0000000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 382257994 1250 382256744 382256761
    0x6090c070f120917071806030206040303020f010606030b0f0d0201030f09141005220302190308040201030b0a062705210f0d0816021c0c050f030f03070c03090806 71
    0x201d0340c000031922500d4125459004414442e503207070740813040c1ca5000306000c000303e228040111045682802010501c103807650041000380e4010f40c400c9005030700a44016407080300038410341004d00340c14034044c002c5419000001d102200d072100f50134400e51444038203108687c040e0340413190b040e41001003031180034490b043c08601c00108841030b0080d0b00a107400e00003c007885114061154100070101d41094651180c00c406d010380e100011402d610901c03005c0c1842c2c00ca80803003403900e1442903540421070318047c40010152402520464019210030b2424802c041d00070488049d1086070300f00900f411407140c4c1400b1103021a542c840c9800000e0a401e21100315610000885440300020032110140f000300c02181d501c5800e506610700048000002c00d074110284086441c011402d84101c2d481680d0103c6c01c4007414030b40402c0403011980c000300002c00c0100501c0042c10784010800510f0803c50603803403241c868030008000204200b0103007910402c140c0610007241c00341500904540161a14501 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 382259244 1250 382257994 382258013
    0x10c0b0a0f05060301020a052d0301090507021e0c041e0c0507052b08131205040501030b03060103050a0b040821040b09060403090e0a021204050d0305090a030806090c070f 75
    0x115071041c078206400105582814001c0f0744011240703542e12445c0101c52041d04042e00202003440302c0070354210396101030484810001e0f5000c1c0c110760400150364200030b18040e1409000c1550900c140c030110002d000140c402007060100c2e403100f0703203021508110854618460020700c0011003201450040f4000355944e02202a240c62881207040707500000396040217440c1001c00315402d1314044100001c6d040168400c201c461b8100140001183c0600e00b19a111440b00c452003d503440020030101c0c0401041d80d02d4000c2c40c40a900c1900540503a50454a9883d1a00d0001c0d002601544004003c14204400c4204540c02c11200303a820640c2055a0303032000c000b21000342d4040d2030b01200361010608080000c02d14a000d1039240c1c84124409141490451083d0402404004201c3c0d0030f010004107160300c02030b000c5c426440303840640300302d401921024048400c00340c0113006992080403204c0000c0d420207022500001e048403211042d607a50341c0740141d184980c50300100001e01d268151800c0105821 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 382260494 1250 382259244 382259261
    0x3101a030a08030a1425030f02030f06090c120c09010c020603090604030909020a02031204020111010c120c0207150507050c0a030609020f03120706180807050a0b071b11010c0b0a 78
    0xb8018080c0b100c40480b045d44a03001510314801c0a00030305404200c44074030141800305007005040118860301d0340101030049800451780c00003929000c40c1000160303e000c0100e0382d401241a520381d8248080704014040019000341405803290001900703101d107a001d07000c8007050650003032146551745044504183c40b1141981c4c100c01240b160700c00807031400740310300941d0490800c0368010340c24025080c120310540f400c050800ea05010300c1007106500724030280200c40802c81e454130750b4019800490019030444501d1400c4000f1900301e02004c0c40030a0090b14100e9072016945031054541e40d150600501b42850402110340c407003c1c20b40000204260750b048075007038074001c8464260340751800041c50f4940d50090543c1c000704408103c81400a00b042c5c0c0150000c0c00c4401120101c0c0380d050f55a9001b543c805c50059034154407034510035040016140704150301c1900d524000d2070260030f120015070650000c42005200e26850b030104102c5903c15514000790540140d9000868100b1844c0d074cd00034003644 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 382261744 1250 382260494 382260511
    0x3170406020d02010c0819090b0c0702010e041503030507150c080103050c04050f0a0e030c070602150109060608070809010b151c05040804030b060a08010c0306140f03101a030a0803 79
    0x10260b0020690041c441c2c8003000ba407540b541691542ea450050f0014007d0074039100718140d4070003417000480c0c03040203400c0c414034005075030307aa88820900000d0440800c0e072003c14440d60070450b0400f01c4e240354040390400c8941c9130403c941ca038000e0340b070002e940005100300360140030701c0c280040c01016400840c15040b070340103034183d52902c0d990005000541c1d0b0200c5030102d0501401010a0040750070fa40f04800039042001030703c0c2801003c18215042000e01ea00080041e40519840e0690b001081c00e0b941c01000124020001a40303020009403001c1c90051400f018021802c0000f1180c41007074000704000107004280d03a80d00c42c224000a40140c001d00301c1d45e070301c0b101500140d40c42c19002d886410702072500840080d080c9861640c403402814801001d160300401e10708400030303100000340101d1103003442c40e80740480e9541c10710310b030440c403240780038552441070b90080d0180440351000300782021a01c21001000c250312030f2601690110705d41006a0582500c51151040e05020030b40c0b000c0d60083c0001c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 382262994 1250 382261744 382261753
    0x1050906091506030903130b070605011514030402041803080406062115090209040c180b0609010f02160305010603150c0504090213380a020705190317040602 69
    0x3004144004240111040070399090b030010001070314641800510390216403001100e14006000e45e00301180c2c0e0043d84060903c3c000441c84404100d014000c1d40d02426003c0941c0300c5500b107045004140a60718410700c0e0f080940040410150b454079000f0500d06090075910f079100001d01d14000381100e80841d400c3e03901d40e1404e100882c0d16000d45101d03417510107005da1422084049a1180d2018049850703458440640d981d00020050700c9180010f840b80d4050307601181898070b8a01d09440c550f08414404600f83d00e0007944081540d030700c1040d561081001e20301004400b030b2540382a442c1450070149246d8406010f1800010094150021405c0e40e01c903200c600e1001000c000514127540d05846050042402448103101003c9164042e201740d001c1517080c1c000c405d60b5880c0306680880840e404031170a0642d07401c078518183c06203c200310200684503d00e8500070034001c002f51039030100d002c1d01d842440b24480d612501c1c2501400710014507000f10203008021642031045925920074070400015005 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 382264244 1250 382262994 382263001
    0x100302090705030a0e240a060305060f0406181205030402030109020319291b120a0204060e010e06220510020c01020f030f041a1b010b01030f110a081e0f010509 70
    0x400f041403411b41242c803083c107000e800b01c000752820188004108040c8a0755503803001000c900304114150142c00d0451140800c1d0a2505040080d507801d224045204003400c0b500340300054910f2400300000044c0d2030107649075100c0f03100080c0980f51600e00658103208000010300e0401b01080700034465485a0428441002482d242400182950701107a46915000d0006a8182a140015003038461001c2225150511004004146903415101ca07501c2985c08202842259044034150501d04001d007400070492980900185042c400d0004501d00010150042c1d502112841034100282200412484101c08a07c000a6139020191110350040c45034100e044c09105000c01118001e44207a0761240ca400d05041450848690100c84810020000c02c40300072110b2480c481d000c15408680004980320008000050aa9000c107030340c1014070f031801c17842c402c0c1030402c4005c45411905905002c125695100070440080802241e00c2d18442160020400941003100c1541c0c1640d000301d8050002e8bc9 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 382265494 1250 382264244 382264271
    0x1e0d0302010605041d060103030c0f120507060c03140a11071703061c110d0f0b10030507060504080a060b0613090c170403020c22060914010b12010905100302090705030a 74
    0x351120071040c5d2036044180140003191040b0640c1d10f0150080ac80b8400d0000d00b43e403040000c044e41007513800014808144041003041034082d45014038014030317040c8060a03119001403618000500200e4140ba61500880c00e4205170030141d071103258000907040c0510700c2414802c01d1341d41c4102c0e84a0b12502c2c03224228118001c1201d4070b1089035400000c00e8038480b008906004940043c21400e59144025880c990f00142400c03061a01c602c4051103044038441c03030340c9402d80c40c1800c150808814050140401e001200000501c2111f0f60380110300480c88404e80c03004104280705004040352914000000401e0980c0141c0007106201001d5562500800c071202900303070072240c1520010f0058002100d00e400301c0c81d01d00400c141d40311080d910f14809444000c0300004442e550752040581d07a840304240200c08240301040fa0042c50544941803410300091041500100305020320040c1591341d9021641d1f003c0140c01490155501030504000c60038010300140c229003044805a109600301030381c440145 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 382266744 1250 382265494 382265531
    0xf070c06030e1209040b06070f0c05040c020d0c0c080a080c060105010507020604032033030615030702010f0606050301030605100311041107050109060506010f0801060203091e0d030201060504 84
    0x108a4003000d019a0900c83c045002e0a40c051900c5641c0503865881c17140f840e03174600000384104c1c0d20a40403c0d00d000d00d54030300b480080c2d090b03500140c8554500250a18141d40200c1d60815942c06883c044441d4807052500806031400d54001034424480c010100f8100320b1003000802031540b0210486000d0381e80c89004544510030148001d4012005110410000f8103080c50024404c8980903196007002061000c214070440f0100c00708000001080000041d00300788042d4600d401c0d8040343d032440c41c40c003a4046981703070441100c1c9d001448400800652118401e5000035044003515209128080c0d807510024150f4000f800151181458900441c20031194004010212684013031420300d00c8010f2010003000704850301110b0010300c010884400000c40078464249024070420000509041c0b540005104c0d041e0003074010107000d02c1000600265070000144d4040d4201110080702181400ca031398284226104847c5400c4400341604204240e0107400c20030580f002070320204031003080b000044400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 382267994 1250 382266744 382266761
    0x6130b15011211090d200103060308030f1f030f0c21110301021b0d090806090a02040c0e03030c0714060702010c0f0f0203030304030305010602010b0103051e0604110f070c0603 77
    0x407a02d541000150078101d0b0304110051944050840d04042007103001c01d903480030680301140d08181d0752408900b04e10f610303229401001401c1c0307801c00040e030841e90303006c41030720001d80703c1200c00c20200d0008600e0401802c0c90320300c5405046c8c0704400c03241d90740351008201038040c0041300c2d003003015080812030150310074040000c2003445081600320b40f95a2240b80e9459401c26240b501550204010240b912490b020352000707a401400510b203825030041d004118207a00c0d04802c019802c00000d000056100040481c015a0115400140182820700c20f03250031103c504084d8040c007000c14107107108800407a18034111403c1d0011010b160080c1d808102790707071007500070080c045481c44050401151041610000c00f5100700c600f806066007680000e403440d0805c50f030490000c0d49880061005031740c28040c000d103400003820140207500b00b441d600c1c11216200781209000e1103031640010240c0d6503a41114101800d201015561180c141c6124203065000420503201808060000200d4034480d1007178282 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 382269244 1250 382267994 382267997
    0x30207051c0b07050d061404140106080411030a170703090503070602120306030322180b0a090e0c060d09022404050105030403030906060b0901080912090609040e06130b1501 76
    0x12103420599072140003290140c603c1c0c0402000b4000403040c83c0003485084083c1c4100550b0b045d130140b60508000035119101a20031050442c200100034603600409500d811507071088141c0b02c0d6010f280d022a241520903400684041d4003000d2211682075000d005102d814000c1e0307142c2c040103441e001490703a501280d2086d0001a401f00d0b20f4030301002c1c0b6030006150030a40c001c081d01d00d04128040244564103a4100346081801d2000701000442a03110480c0e032090b2aa00e010301101d003103003001841e0314030107101c0c5155075511040046d800c4242230204e0310389442c0003004940c0303072840992400e00410703c0b40310490085200441d1080b4907010707241010886040d040c000380c6028182001101c1d40d0b003002e00b04809264503031520400140181c01803001600d40c0314045620350524100040c070b001c0024280d06400d40254031800040503001c01200c0c40c9000c02c1e00d4140d624946680403034010104c0c1e1610098a00600050142e0303040d0030403415480da40503002e5150103403038141c08110040c190b00807050 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 382270494 1250 382269244 382269289
    0x40905030f070c0b040f0807080610030303270b060111060603030a0e2e1e0f080709050a0b070203280b19050a05011802040302090609040f081603020705 67
    0x40c084241c1e0010311490380300d100c015401ca6620180c00c0d403e80c0207500940c804120a0070184a40e62040001500502807003005103940d0034406002c4a100420380006020551110004a45124071044600181144028107030124205003040507400e00240ca08a00150b0080310080c40d440300003952500a4030028041e520301944410296942022098160340203200341c00c0e00344822054000c50f43c010794100c8200c070441e01c0400c1e0010888103509000c8601000724201d03c03404981d0155141003001c01c1c508020030386459202d0155250000c50f841541e002c103000c2000310340c2c2512140500b0b24944240c0888050020181701020444060b28a00c49158002004080030039401c404680d00481300c82c038486612500d46614000360b03070044070064083d540312001085510103400103e50300395100d180440c00c2c2070440c0e0001d560b41002a00003032003040c0384000309040c000080d40ca801c245074408001e980d0742d6402c00901d15218000e4200354054000c517000002c1c90300b0001c500742d07040d80d04102c446 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 382271744 1250 382270494 382270507
    0x1c09050609030a0f08030718120b10050d0819050301030b1603090212061006021b0103050a020909011815030f02040903030e1603061a010e0d0305090402030a020403060b04090503 78
    0x2080ca50019424560305210f18800040411080c40300c2c0700303c950140003031964900d492a4083c01192071429141d18a030400c14007004000c1090213280070941c1c1c050180700194903055070a036800520f41c3c10017540154041105030800a5010003425004110425808140300020081d20319010074030002d400680b4103000280c0c84500020b00e012101d140c0d013000151201c4c690041441a16074841800103688000140b08410b01a0483c050007080d540c4001c020980b252101c9001c04007001c00b08a0501d6195400304480186036016642d41c000064403410840d82c1d00d209036402401c1b80d2190b400c84524040b4201c56140d115080702d400e403a00201d014051808550a020003000003180036000c042c3c1e6005400d41d102d50034462a40e07030440e40c659071444a0305501300f41044a000ba42c4407500401c08040060080c4d8002100d00034185013196040e41c01100c90400792494070802c400168030502c0001040112041c0364023804c16030b40205c008005180a0400780012200c00e14000760a0b40c2c4244090f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 382272994 1250 382271744 382271749
    0x204150809160b031e07020316110d0302030301051504050a03150f05070503070f0302210655050402090303090904060e01180c0509100503100e1c0905 66
    0x1600050207008540c400341c01c0205551001d0065041609460000400c1c8254501c102c0515003812001122400003424840d0380a584c0b0721401d01c540340482c2032024080180610040014981603001e480c55040c00e01c0e501d4001d4a0350300902030684035084071405044200040c02c266015903001800c2c4107111402e54070340034512a0303240300758101161070b2421000d00440c1401203500844940d15220740b28200140d0141090b4403000a440c10544113110042884201104000104802c0f812441c1540c0300e41011880e0940201c20342c00602c02003482c80080003000001685002e81000c120904800b2440d8945441100c001c00c2400d4100380d8035024030041c5406c2e0b0080060000080c02c5030710380780500e030200f214110211007e680060752a0843d0a15207001c0c058007203864000018503c06002660740c0d85c9a6080c9405500d000c0c0000d040003e41d003880c0000a08003804000b011141c0003001d444031074016040083c0344004078020440b46440c05d0f5000c0c081091491289e4a070000c40314201001e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 382274244 1250 382272994 382273007
    0x6010602070303200d080610030b0a140301110406020f0d05120a0506010203220512030901020a0f020d0215030403030c09051c020612040c080d0e010c06020304020d080a09060e04020415 81
    0xd2504c80e00e004510003000080c04003c1340c8442d02464a50304442d103412000c225281031044001130074513048c50340c0554a507403925640310640f4902c1014810005200e8082030041c80ca03015034400ca1400010301040440e000100c04000d66885c0302282c45880102c00221034074013a9a6a0210344030031100401e0840d04d0540105601000605c1260b0415100400d00b225898519030800b500710308403942485142001244200324042c054021403500c005000000c3d038407500300e0000381c007001e40c51400601315039464002e4214550018461280c02c2440350322800203500a81e000c8010031b2401c413802d4621409661140200c402c018800e005008100301014801305101c8012640404104012050b0000c028000e034025401583d0144c215801c103060a442d240013400407074140603c103040b404140e070707100d10301d4110a548004056140e444038400700c0c40402000000070401c1c0804604100c031558031103041000c40c0c1842c1c1e2181c4111203c0c2c000d110881c4a9405696008510282011105406901c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 382275494 1250 382274244 382274267
    0xd030c020f12070b0903070803130312120218090907030b010b0f130902070215070c091e0c0206071805310f020703080603030a0927050903030f070206010602070303 72
    0x401000001c40341030721481c2040c040f03801c001c21305080819180032504040245c034003d00301d0000103510f0301030a8203ea1100504510000b8514021040c00008140c80b40680c1c0c0800751042d4019900d07102da8111100528011030707081d60041d00103000190260400040e00f03802c40c0e1f000403803148542d00b04072548003260b1000300300b4088bc5808025040d4040c440140f50002016a4080140c4616007031042150001350798001556218051003035034089000e560510048a0641c90002080404102c100d6080c507220001441114074147d01c0910154000c00c1d218407480e82c682e1500c4c83c45a40f000210401c0d80c5600508c1e4100d280042403008480ca1a000502882c1000f4210801d440150300200705543d12081c00b801010b401040003010160484507594000c07400310003850400401e407070002e160703411510551070f9241a8202001c03041801da403036042451510350040c802d504d0903101c000e55a42c010b80e4010800300540b400540a00d2000c200d03181038844507800ba0000602d10749007100c403100002d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 382276744 1250 382275494 382275499
    0x6140f270c090316060905030601030803071805040c0e01120212010306050c0903060709090c03050132040906060305060a06031a0618270105010b0f03040501090b01030503180d030c020f 81
    0x80140e501d00383d404124031400c1c901402c00003240c240c01c0c010004d01a03c4140e100c41c0c06030340540300500001d1409030507640d00c18224982210714614604041c07042907240d6002940040c6000101036165078442803200c1d14040a032034500b03140210000d4441240710303d100f42c2c0e0303123001d2940040c40001c956801280d00000791064141c10640c2010019052007000ea6164020070703c00308003008401001d0042e141c50300e00a0808019961601d101128084405151940c1c0340c03011206240002032070a1144100078405002080221610b24000d0003d10a50000755010310800000540d850303000d000b07030400e0b60307400986010a0505060400d01c2004080c02c1164042050609e00000c0740c80420350a10400480d40c01800400c0f055514101c04064043c4418440c0d04050040c000c0c0c1903600d0443c1c200e400700851055407580c03130b4148103004100d4101c2c0100703402e10ba070b000041400300000162502c0c84030114130304446010340c8200002000d00d082c2c02000b00d1030070003843e80945007004c0072120380c4002 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 382277994 1250 382276744 382276747
    0x605070809060c06160206010e01051023040501090f0503120c1203070c06050a0608030319061e050909160b0304051c110c0303041a130906140f270c 65
    0x101d0001805904070784100303e6140c0c03111081140c2d081102e0050210100d2500251510754109400c1080c551310501400c1e002e041c4110300c0c0400c00e4424034002040c5411203d1020009940407001501d40c1d206209050000d03505030004141e420b14110250f0458500500408840071403085c043d81c2900554901000d0380160f001607086401c4c071000652080301643d441860780d403c41d28105085035009048081000c0c80c00d041407280d0074001040b2504803100e170214104007414094808045d06c0c0d10303089486040b075000300340c81070007030380c00d4400007550812200e01ca1039941e1102c0403956200310120154034414410820000b4a0741e4030015a00f0500920540e034490071000f9801151003841c0d1070318800502240c0700c403411a1818081581e4005d01100a90f160038075207040103104031003900400c061003100003803814000b450340c1e5800c4000c04510400340301c0c04c5d41e142030030100c11000d500064000c0e030030b03484441010315100c01c0d580c99040c000b4480385440200f460108031082c40c01001422070003030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 382279244 1250 382277994 382278007
    0xd05030f070305030a060e0f0103030503090f0a0803070201060b0c0a26120a06060906082d0405010504050706080403170718170d02010e2a2205061906050708 69
    0x101030000340080c0d4000c0e2203c554a003482a40e181c00c4500950040c180304c0610303014080380c501002011411290545843c40d00d0761104182e9504000c0da904004000f440307000101c808004104003d90721406080c0c00070002c0310b58445e50507030944100c10024038250041c00c0400e0010752071072004031310b41d9400b0f60a0891808540284000c5612100c0c0d4004541c503d40100032a4528030f000d0b03180500400c0c41c02c008018034004024014801c05040780400a2240d10f025003030403d031a0035008a0810100720f180541400d040141c000c2000351002d0342d540c020304030b01240c16402042c500e03000d0350303240d0788200a03c11a1048240d010038080c10402c2000b81102d14040801201480c01c00902030301c0e0428026080542d0302c00d850090f050704020f080d64104292682c410300302103944814458200d405410f20310224a49080c20000301e20069800300e251245000040348611070b503054021074604c10081074842100f040016042600d80078401c3c2400c0d041807000740d01c01c42c09000c44130311440c12141402c9 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 382280494 1250 382279244 382279267
    0x603120f0409020d05040507080f070605070206092814010503010306020d0e070807060323010b03070909290d0206180609041a1507050d1b06050106020c03070e090c0d0503 75
    0xb030203440850743c400e41341e001b4032051010510000008000311001000d40c07031070494420361105040d20421040c09400b154600079501c1e408111007480070006c040c1c0ca0100d0707142002540c200d594070705008181c101c8140115406851168501c01800141c4806055030f207540c1d550300c0603601124214181507150121542104403c114070703005041020064035041d41000c1e001000c440c1c01500d19800d9400c90303080740c9508480c1c10a014191070141c40c2d0240d0b00d58500d60300b5a0321040c1c0e07a00c0b41840302d207400f81c0d00c2d03110780000c4001c4404003d0702c01e083c8070040750328080010360b5907034150103980035030204100d5000002d4428490002c03240541398604002004001030304440c00c4e95900e5120780980040c40f2554a02008254604000304170743e2410b100d025110241d56140d8150203c0520000d9244411b240d403260451071500d0b944070409000e00c1d030b1200402501c0d10700061449002c0d1080c1c403000b0460300070181c6003512070301e035800040c0003409001040200d0841c07000070588890000700507070601c44 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 382281744 1250 382280494 382280497
    0x6060d030314012c0c030403050c071a130b09010f080a090803040506040b0105090420010c022815021005061c0308070206280b0a0906030c05040506090603120f040902 73
    0x901c0d1341c42901c0100c0040880c0594401d10072400038040255220030008501c02d580245c80d00141c242c544240c0301c00520003040d1414503241c200840c100c0d44000080c100c000102d004040d0f42d402c000c44034101c207540d00300000ca54042c80b007550b1301180e40030045c441078501c01c03078000340c0c44060f210000c0313030314100c645880f01d540c0c0c021784054500381c0104040006110301d10500c24018401030354491071a2805841300390140b0721803103060342e00b070316009078640d4240c0c82407030183c0d005900101700f803240202c42c03040800701618862811820350f20704100001c1c00382c00380d2038109404001d40c01401303040d01c0e0707054800020301c0000c0507160300034040d8000103c4909000d50318500d60f03200e40c580703411030300300740c0c0c0041d14203600203062000c10014241d12241004442c00640910f1215007808954020030324005405c018241e08107145051401c0c4000052181d1100103104503101a9010070203611160103005040b14220307070441e01940321139050b1440749007201c020001622903846450602d03407910b40d9030059 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 382282994 1250 382281744 382281749
    0xf0b030a03081f0303020313050109080303041b0b0c1609060501140c100903050d1104060504030305030603100c02100b09060a0302090a020702030d0e01020d03270f020406030b01060801140306060d03031401 90
    0x603800070601845585908c10450044c02090a04441d40751400010641d05d210080c0020036002c0c40c0c403906c0007144c0c1e06088140141040f0400d80c0d40340c81c007400c44241d03681c0d10f03103a4071352000d9503040d0000b442611b148210010b8070010b07561510701ea54203590000301944400d000e62214450707902c055494160134842e0850440c170960310980c1c1c1d00703919001d070b81c1600d40c2c4e038040c481d0254007003104205080e04801100d013101d41c10700307000e074880c1d4440002174280329588200303c0c110b9061500004185a0101341d0792084003a0b0541082801c80c44000c0c441c400707504640c0c542d0000780c07542d81400076143c10301045620062a0744094900049603000c01d003401c80340038600d004100a20700e111845c0d038050001e1b09114400d46410040c03800d40352801192001081c686101d05140c414a09041c080e5110b001002c03150060018410941e4901d071842135070100b4400d0703c0014203881c1c00400d01085001c4140c0d29008001e0041070181c6440040165122809008030b0625540c0c81e01034180f40d40c3e00080500 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 382284244 1250 382282994 382282997
    0x5090a0303030203090607020c03100902010e0a030507150207080706080402030a17070b090610170c030111040f080f03070305160b131407061d03031b0a03030f0b030a03081f0303 78
    0x312410034149092400b10061f0050081d500040002c0820361000540c4c107a50345210b0740040f405013007034001a43c0d0341c54000e40e00e9411005018008c82403003000203080c0c044400121020b50b007560604c0080380c9034100f03401100c45e190002d40041103005e00c01c4060542143c0000c0544e8071040b079543c0c1d44c0c08440c408600c50034001502144100500c0341d401600d9510070783c03040160800d45052554543d0810583c01100100c2c50b8080221141c2c00c0200803a04002101034020031020350601c0c44050160043e2090303401a0300d61050110301d05c0404038036a802c8041d44d80045003000501d0f40c060364507800c403c0c1d00d601500c04140940e0301083c40e1242550144503c184d00044980c600d09242801d203204140110045d801a40700304042584141e68044414034001884c00c25403043d80000c1c254442d800c44406a002c0512050400306400f00d044018075100383c80403c820b41e55004d00805450072101c0b2079905800010f6000c01003801112110f5015100b9150000c2410203245c4504580e10f242d04240e0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 382285494 1250 382284244 382284247
    0x5030303150102010c0507020603060918030f03040c1401080a0c0c060c11010f0506130b040e03070c08060702120a030b030c1302090f0a050a17010204210521030105040c05090a03030302 81
    0x3078980d60213208143c0960b58601d40f0034a00031070350300410064840035201034015041240010140c10485129404c20140c3c1d0090b40e82e5441040000d80441d0020749060701d49402c0c06800089400f841001c1400403c0182c403220a0f59a540e945080100602540302c1d0601c4401940000042c0c00c0340b06112440b222901e88403110207903220b4080c21110b42506010b1403d18120921030300c0c2d5900003102418881d1480c01040b111903850101e0060000010001894400420040e04220b298081070040c1c0b10004204e80c160784d54803208990b40d024103840c82500c0f01080125100803403098101c01c0d03906a0240856400011040204030035529441c0039000041c0c1c0420401c0440ca0284004100480b046a015510303d007050001020080548241e045408000742d1284c4002e07020740580300103002c025880160000e9910310003140291000049030b441c0140c0c84081c0c1050040e1451502c0c101040241500716030a0206000081442115040900c803050181c04469a034460420020714829600507 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 382286744 1250 382285494 382285531
    0x50a090603051c230d0f36020d2103020301090f09120503100b0309210307020607080a090b0109091a0702030706020f2503271e05030303 60
    0x1d06016103074003c1440c0003a03040c140e82c01650b000040300400b28220301d1132140011010200461440382141c04010389040c00301c49000c2c241c117944020000030001000346194026400380200d02051078103607104c4030440084810150511000c0415000e10424040010202d08203281f802102104d06402c0081c6c0c0010040c40211914001e0607079141c0c0d102070a1080082d50f98520b081419502485000c201c0040000740004640722101c0006124026186943c2d0a085482c0c80d110002c140c0320080d2280c1c126180c2c0000c1300c0d0001100d2003180241c2c003800940e1203600e01128012000f40040b44095120f004e400301007206214514001d1204c902c00140091451801c0c0c1c2d801c800d00410054826030b001c3c10441034a4011003200d001650081d00103a540394143c03070103000e9002c1d8481d9058448101444444c0c14504408020900d40c02501c031044450b034000c0c0b4410050300b1400740c450700e940342100c0c10440802c210028500703049105084042803600d034404249503030001c589035007415401d00b614 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 382287994 1250 382286744 382286753
    0xf10031217040b07450f06030b0117150f15160b060a080d260a0c11030a09050d0807060c050304061506050912150106030605090a1b0c0606050a090603 66
    0x4c020f03640309501c1c28000107504848064111000c0c1742c401d54000100c80801c4407100d50740d640940c0240503817240c6000c0b65520b40d24014018503400c40c01c079002c64907040712041e160b14600318141c801e80003d200c9158841410040c00030702107078035404c9070300214a005c03151241d602c0c600103007860f042c01103500040d582442c100b0002001d4041d00351406203c11460512447c8000301d06424241d000d400c1ca6030020391040c0900742c0040c0d8401c1005900003180e0103004181000e038000010f0030405982e005510009110350684070b00c2070300380000c0800da00000801041c01c2219240d1280380c0204401e0b030409240351120310a5034000c03010000081c20000811080104030312a0f044000100c044040249003440005001482014241841203542010b9102d0060003000102d25030030341d400d81c0c020a5691000041c0240c00300703000360740c0300780b500e54001504c84005210750b4508400340c2d1a0f148008001301020340b0b41c5840c505040c0e40d03594403908080780075240d501c000310050034400400508107245060 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 382289244 1250 382287994 382288007
    0x309030711040902180403091a031501031b18080304090203061908190212070f090b03030306030606040e03210402010306170a080315030a0501140f10031217040b07 72
    0x41c039110380e00d003548080c00360b01e44a40210551411003004601a205e50406484c1141c81d640000340c0b0307201146c01401c0c030f0f54040c009140110308115010510386003440040d0152840305080c1100c4118141c1d0441c1441c1c410420031200d1075074035509200d0b8544a060441c01c66000d42c010180c82d40c0c001052101c0f80c00d00c2200121014240000100e4403400e1070101519071036460320044206c0680c1650300295590268030101d404081c0040340c0505552f142083d404418510070040c00307170700d48a5014107034100881282d10440005014000c0b07581ca03101008001e03c00b10350354007120304c0b080c400300880c00360b114030074986610840031002e040d180c07520005007640c09640201100307620004001d0221000003594284440c0c0c0208460303102c1c0c0e12907059011400c12460002c3e8148616107066051110645c04450198404070f2400601c0d034507881c501d0a015016107841d00b50003202602040411901d002c0040810300c18500004407404400000004d40001d48007034604001140034498000d42100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 382290494 1250 382289244 382289273
    0x7140102030610050c06041737020a1110180603060e060a080a030c03020120031f06050a05090a0e07031d0613020d050a0b07020604050601060e13090303090803090307 73
    0x50024501480503517007685484001d0b00050080c42007284c105000e001d050256000340d070580b9100b0714540c102100d1040c5070034880d0703ca01116141e4040c1518054400300e140a40d081e08040204882c0500c02c05010100ea0008041c0040001c900642c0108680d11042074009000703d41e4003280f41ca0038108482e6407072a002e442e0b10321415120074104a000d20105542a00310b8050500000c824810b080c10b07405004540b00411400d103e8090070340720610a480590b0242d001c00c2a00c11443d0440c0780074581c004864018500030480074032528510503c01d80003040c1c48034011f4142203586540c0c6020000d400f509660241c042034030b6200030040d00320b01c0000041c0403121200140038130f06000650046200741094041d00505280145a0900504014034400554007403105086450400002034483c4002d640c100d070b150044034000100184224640014408003e0946000303c04c0c2c1c0c0060070040c00300c042e0031003e040d2100403010101d110703400550311070b5019601840e9100b84929115401a01e441d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 382291744 1250 382290494 382290497
    0x830040530030a080109020304020f1f1205070905090a02070510020d140103150b03010b090a0203071803020f040903110f03220f0504110705030c0c0111190305030c07140102030610 79
    0x1449540e6030f155011607013038119003a601c00183d4903161070000c04c100c1d1340710416231600205401c07001a0031a4141026141c0303604196541510301046003800000c1d01d00a40c0c4a80000e41101c01c24003591034111403158001d0304e0b0034030061038035070700f0707641c0d14103258554545000a42e4007140ba10041c00040c0540f8001d170101070521707441ca43c11030740c40200e40817940400c60009a5030344161003158809521042c0e00c503000601020052600101d1000658000c80300c1038001400003d040103007482842441b4243c039070052070112100d00c584140002001030721016802c0007140c1c110004400030a00082c1c061303028003805155542603540c04003064402d60aa0349400c082050820003c8010005014003a580100c3e000300714840e9817290391025024104014115000005901001c50320001e81980000001e0700e50100b10b9404e842e6113904e0301c2c00d045200d91145800c0015400180c455001940e010322050804d034107114071038450020b4114185658a01070390b0000a0003e1071411020780c0700c100045 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 382292994 1250 382291744 382291747
    0x30201150602010e151b1c0b090108070902070309030614010e0907060516020303121e0601030b01020316021203040605210402030714030114090c0406083004053003 72
    0x781003c20b030b0b071662540d6005d9105507201000c1140c08480b4600d801e0600c00012070b19440d40c18201000c1d03080180c1c0010100350b149040700381c42d414100307141864126000c0501401c0b2007481d01011901a5001c200b0403001c10500200101c001b40c0729100399007840c0f1480c051303050703198105490102d8103c00900070160341c1d8000c1b0801c008803907004c2c0844000150003028100c2041c41c03807011030301c0c2d03002d504440d4619120480400094942c030a5081284804c9201e1401440d01c41c9401542140d0340d640500d40183c00c01c0040b000c94000c41003d4001c002c0c405462404e040f044808003500319000f40c1c124100140b40050710a0085074134000404a80460040000d881d00341680026a54201445010034400e62001d082c50540d4081d4801802130b1840c48041200b460031061254441c0e82c0150a144114544000441c107440005009805010500c421041081d9811007400d042c4115803408156040100000700d000d44843d000301c0e1040c1240015100d603041c442d0511030705950709100542084c3d10 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 382294244 1250 382292994 382293011
    0xc0203010e010e0c1203071a070210020403020901290a0f020601050a0621020f0708070210030c0912060914030403020306010b03040201141c060b0913090c03140a0f03020115060201 79
    0x20f001c20010803400c1c08440241d2000c0c49900101c1c2140a54040604400070740307000940030b25084240d07544141c9459084c0d0b034241d2240b0b2460012805180400780d0807070303600801800ba401d43e480000640c4d6071140e88140c0381c0d8040d20640c50035548041c030b605d0000350700c0104001400d41c04102c0203000d00400c88004100341e040c800010138800e426a0b00100c154203a20140314104010790413904652031a5031083c0e561409070500d58081c0e0b000c17000c103e0140c02031100d010304442c0300f4461404088002d84e40c240c00305141251142c491050f010050f1180760341d031a00071000440140010340c002d98100055500d40340741d0300400d81410b80503400391001c0d4004004010041c4c2e802262240f1144090090989030601403290700041c011410b00c404009250280208a4004844c01350400b00c10446501d0301500320641d0600035207149050041100440d0348090001482a0714441c020010000464000b0364180d180c031201c01d1044042076025075524044004035602d0300d4101805820180000c1c4802c2e1f0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 382295494 1250 382294244 382294271
    0x42a0909091a0c071209030b161d011107090917030c030f04062304060605040605030712030e09010e061804020d060506150a030b0a08070308270406060c0203010e01 72
    0x3910b01144182100346800000d04042e401001c1d01c0701980c0050340032868044e008070140c201c07031290005a600c1c490300000140c07012050684086c03c05050b07903c0f071141d401c0c3d0300e00032a0507881c540710b8141400440980c0d8001d442041081800a1215080101d802542410000340c40100c20b504150f040008108004400821504481e00301200800ca038035a50340310304104004040d00080a441c4400014560414001c010b0640d0301490207a0010414140e99104100413940c080c1319958054010890402c01504035120f080c02140c043d040010144038090000340400000741c100810f034108040c1408203034200800001c41c10307040b00d64101b80500346078000640048008000618603600c540009116444800b8581040000e07440c6840c1c03154400000540075102c458003071401000003400004420400142d01c00484e50030566840c501003080e0300d4044002c0400c0210f2400c3c40001c0415006900c2e9071040800800441da940061051148101401e449000799610799580c1400d00e010b0506 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 382296744 1250 382295494 382295513
    0xf020d15120c060e0a030204050406051905100909170a0f020705010206040209010506030a0603120504030614010312050d06030f0b0f06010908070b070302150124020d120b042a090909 80
    0xc1c0d0b03003400e1484800204e040001c4050409420003500981408240810080244c03c0540640c801d48120b03603034031142c0100e207021680c040b180c0000806500904115850060b405402d800340155a690000f88110034a40700b9507000241000001d000c006012000d10390600000d0301401c401d102610150409800103507202c517042c082c0314841c0c400007006c60020000396010400541c0d011b24209088004120094600d03042803005803480b508203400184a40c1d40c41800c203050301c1d481000301c607544496200488080d00f007038020f07a90a80c2c0e9140c0201c045644444102c44480c46200003007010300d01038550480504020745514140800d500052003100004501d900c01e940c021444180c031440030b800c04900d007540c1c030300481c1000c901000010503200341400b5a04c0020740c0c0c80710031840f1301600c03800807650703030520f02c0b03400d0700040f1b51420301c5020841a40100404090040c404990f00803d03105004010804c044000c0410113000186a01c0b550031010a20003841041310401c2040b00c543c5407050356 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 382297994 1250 382296744 382296749
    0x507181406040b0f03011104080f6c0c151e0406050a060b0a08010501030b01050f18090106020f060408091c080c010f0b030a02010f030f020d15120c 65
    0x350345075480511282c440e04d464541021005000744204445140309448544c0300c6e0082455500a0740007001c985500000c01c0b400310750b1502d9141c8515620391908103003001c0c0440408a40341000018546280d0540140035001a040c0d401800100001c56044844c0e00031140015000c40040c400e1b03540c2944089036558424503e004401035035614038440072032520880036030003803050700780b4203110600a003944018490035030340c00200442030710390300a40381e41c0c000d007090b40d40011450b400600c46548250410594020107041440c1080508184d0060f1608000d003006800e4800c00c511040c02d00e040100d050040100307001901e0164a0a1446031701c50304002d00c05404154002503140f01c5454681c8080c404855011350003c0c21601807600120a0717001d109944450340c02c1c030000c01012007240c42489040d40c001801400744502c0b580c01540d0f05464071402205259540c03500318042440d900080454810801c0d0002d039100c04040041d1108903c2d0704000520124005004e0003d5900c8006006 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 382299244 1250 382297994 382297999
    0x103060e190f110d1104120615030f1103010b090603030706020f090a0f03200d20060a09060816020c19050a0b03180c0f040b01050909040507181406 65
    0xa29680d0301c249a0280c28000c141ca0310b00362822409860701035841e07000c0d001464102a0601826111040c501194000d500800c06004c4030309802000240803a8800001415200000000b00340da0352110300014220b94402da400f4401c1300c41002c814a002e124000a100040728484030500f00301c00803039500d024040380240380640c00a0210320302031000058414a004c0205025011030f01c1d205000010b903081c0c401110704071114003d84003282c044903841c511a03c03000d85a20500f0f003450b00c4094100a10359040e512201c0403000d84030182e00d400c0014210f0b10120749684075030b1882e1090090820000610200e030b01d4800031803074040c50740c3c0817459001c5501c0484070000e40e03005010305529614515440341e030b4070012000b00064201b800d03001540c070420490850400500350391083c951070740400c0d040182d002e0790294040d44145020b51024403503a106241990403c40218082610b452080d03800361110f9010010410290001242c080e5944594201c144801c00c001c100d0303002c0c0f40c03030040c0010b031 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 382300494 1250 382299244 382299271
    0x10302071b030c081005090309060d0b0d050102031b03060d0b041704030501201306120608010501030f0b07050a0c030509060f270a0e0121050706110106050103060e 72
    0xc00c0c070940c0c90140800150390003040c66850b80c0d0f407801e403201814511a100c114050000c40100c15900c0b071046511030076018001d1843d040004081002c142d100e0001c1c5011560345400c1d80e202c6481d4000544a054452000141c0d207040007510754010105610710700c01d180c001002040f0440d203c1558a5507615440b00499096480380d01c0c0201c24815a0301c002040800302040000922505402201c180d00e88110b610407003417402c91a904071b1b4400c0c03414858058a1842e01084841d214400c0410300e04a42d00000480b076483e4814142035402c2a402a2401c0321061080f1040c0912580059008106410700c03e2820000d84005451007240c0e11014040c0100494407040c940c07201812103001da0707200d401c815580c4141c0840c92080c1c00c4c4810561030394026204c00319900e402e0007001442500e20000b0810b416a1820400c800707020104542449030b011203103140c40000b00d04000f000d000d41a16203510880700245101c0500b1119150710150405042880c104803040004182c0b40c0c00044642c83c0c0f1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 382301744 1250 382300494 382300507
    0x2090601020c1504030c0b0909040b060114070503070203010f05010e070c0848031c02280e03070f0603050a09050717060f060303030c070f0203010c030204050f0a03050606010302 78
    0x140c2c207028204255580040c201815100c0c009031040042007528455805040c010362686104065070180d82d0603180c1245a400c003107004a0114001d155114805240090741800315020001c401e410200b0110785d42e07403003c12200c04501c1d080c000c8000066040d10104459894204054406c1d50060040414031940c05a002c003070181c841c084414040d81c0070310812000c18808086205c0c80e0141a01c030789464400322481010081c1429407011031001600214204500b24010448070751980d00d041c80840d6080141c10f002a0b25000829a120341c01440d4261703c0f1403920014007100700c80300781c040c403039000f500d030901c11074543e003c411090340c0701c03031800080580d00c08000000400c03003040c2c080c013244100e250000f89440480d0001d140c42c0070050030385030b00d5181c140540300303000030a803161f69140d007003400018820a9804040d2000702e0085080006021564001c2030841d10f07800000000241c0025040c030050620704c011200468080c0c0341c001810b481c42e1601034031364101508940c100341d00041c02 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 382302994 1250 382301744 382301747
    0x615090d06061d01151409011409031b12150c0706140a0b0114030f0103030c052505041d0703060b040905190203010b090c0a0f11010c020109110a030f02090601 70
    0x102c8060070500d10a204000b024001451240e0750034401c14600c0a003084001c610035110301c801e030721441b000411250070b02c250440150f450140402c121510484140403440e0740e03681c104010303005100c00d844041414503090061269070410a851031200d0351003c20f18419441c1192401544460051482034681c1000e01c0c280024144004603132080201200a00c03e4265559110820100b002d0703d07160519003070070241002034001196048400440c200041002c6801103000c205502d04c100c00b43c442403041c4d010380348001070103110080780c541c56554007400b0509261141d0f00c18600b5a415403001c12501004a40e42e9481501004124541f907aa40c40c1c21501d40790405254582c0c42800d0b10740c04070881002a04114100d00c09174802d6003483c182504a0421a4229009941d410411454a42020400e803008004940c90404003c0034900e6180d28403c05c0c40781c4060390566074008240302d0785d28100b1801952a42443c684101c084403001c00c00140d4a8a41c0b80c03131b20342d065643c01e103580d031103000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 382304244 1250 382302994 382303001
    0x906040c0e06150a020106050a1703031b071524140f0a050a0b0306040b0604050a09050c040510050712051c110d020301170d080f0612012703080615090d06 68
    0x2090352403c602040c1c130340e03910b601034105000703499068400402255541c1d82d91031295880c8082000f0030340080001c241071028810b100c05c10903c0307079030703890749230201e079030303506079480c00017041e4180410b035240341020f80d194072154510280901041104c582c070b4280740e000400b0143c040345040c41a02040410b071500d8076007003001c0303000741001051051415507450050300c4c1c60b481100c00e140315501d0101c00e2022450074030255010703a00c3c0070f800ca40c0d100d803c3c02f0307501c00281005061241d10340740070300001600f551200443d8151100641da42c9454000c289003542c03860300311000d01d0050100901c000c0340b0b00c10703090250003180c81200c1c0c00400c2544032196503800500c1030710b100d02106400080081418488402d494a81072074003000c44602c810003a10499606006407a090545c0e5a003401043c4146010158020a90301e8440001103400707040b0000541021005641c10801481000100c141904801d49950216094440d489840200400400c05220300b00a071031040342910458028840700780d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 382305494 1250 382304244 382304269
    0x7062c01020c031f18050703080a03090609080c06090606220603082803020a0c0b0603101e0c0903050d030207081615050a0c080103260d050f0906040c0e06 68
    0x101075070134842140c000007400c110030612040348181002d000840380301c1007030900c040c1c2c107030050080d01d02c250440c0e8031240c0c2d6510101d520070405442e201900e0100e0701904c41e0515180c0b240b94059590b100311904c041c28040014502d481c280c100300b08000c031585230103025040c00c1209000409101c207840101000a113815040580300b40c4010405807140d21652203165034060313081c5130180d100c002c1d00008a042c0d200751046031300014094151400081c424240e2320342c00c21801400d88070103580004035041195105030a0820784511880743c003141c00b002d072040c240c884905251004070f02c1d00319180c403582c03800140f105008255000901c0d10511801030700390350401070010003521240c0c3c2641403191a61040d00382610300b1030b1920012801013032180c410342114901f0f40e21007500d203a1954642400092001d03002c12020303205e004164030f4840026000308146290540000f40c28200241d000b0309010f00204000c2c0603034007030717410702020490503001182200c01c4c4101205a958174500442c41ea8220344 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 382306744 1250 382305494 382305499
    0x4021606050a020f0d0c1e05090609060f120414010213030b0703060e10030210031802011206080d11100b150901091203080a05070216030f060b061b07062c01020c 71
    0x3080c03080410a4a40055410411b281e42e40c0c0003407106408001c09205103800d800003c240108007100b864103105c0301501d40401c0080171141007015120445c1e51070b074003280b20b800c042c000e00300410081000d681c81c107121f2480941f0085050071004420418120342d41e001c003400302200b080014540e280310ba0810006003401c1951031403a818001d920f9401407040d400100d110300006207002007140d10a22903000c130a10340509560304210180c005550640c29882020040c540781d11011410000401c449000158140d0b03501c0040c81d0140c032154200760306641e0254101c0e04003c1c4004040e0741d014150420b83e201e041805903500031342d00c0161568406d560001d420440c1d446018001e06800050f030602c40d19500d503080c0230b542d807a07640481c0c90b004c8030035000e0011082000188003003001c806888007043d12900c1c0004440d0032620004001d078000550b0440180d254440c54541c02c3c1e010700c9514000c0034a0b0405650710f81d081e40c00c20004d4503140000360203042c840c08010201e42e108125a90030030f40c01 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 382307994 1250 382306744 382306747
    0x30506061308062e050603040204061a0d110a170c0d1b11010506010203030c07050f060112030906050a050301150c060c23072102031318060504021606050a020f 70
    0x480318402d071204002c613140184c503000f8112262860106185005030ba50030501c1500b06503082a08010494202030401d03070700b003a610000400e400020420258005c2d841301860340d200c5615607408010f4600f0a103407800c10403414080b40001a07045850300c50081d0220400500316999162501c030107024405070f05140d83d080118002400ba05000c80742c00350401c40d81e8018001d202d01c032040d130030385106a6441e40141c1c01000041c80c4140044064040c0c28859001d03186440c1e554003140e0302e05103081e000b03545880c06074900d00c1d08050300801c5d800700411840c00c01c40e0401c2000000540709000500c12a2214100b160700b000901384103480440301e03d83d025200300100036425400803c140682d07680600c4c0c151b2911402d0101140020075219078950101e00e03080d1704144400b038130300f020041c0703401c001c1540300c01d00071450b0058188440c0c801800d051807402410100c072244003400c0c0c0f1155031006000e20304c10449a401c00031100c8048441d5a00003a01240c00e0320703844250340007485000f9600510250 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 382309244 1250 382307994 382307999
    0xc050a030e010e030a020f040e101109010f0f080402150c060a0609050a0204050607060c021c0f090b0a0c0609020f0a08030d0b030111040608042f031218010305060613 73
    0x4001c4107100c12480203980c0c0202c00100b002c00e06545088803d03000c1c0d803045000c94084814509a0044403041100700c046c3c848104078013400704c0583d10180895910403001064071002940d0268070b0008005007481c2a64144144d910080c181072400390002e4003030b0700380150783c084005d00b01044540c6145a041100c0c59403030300941d04001001d050007050303441400c04001c1a1458494002d03039065400090419142c48140e40c1c0e81c00c010300d5a600d6503015801a4003180c403030941c640d2030100c0d041c5541d031220700c41d41200150081140d500340d0444440e001090000303400032070707014079130600380c070b038010000142a0030034000958022600410180d001000c01c40110b07000d02d010000d049854904001030000e004180c007014282c43c21a4031080780c0300410700c010094079110310703001c90300f140c00f490613424840000b000d09000e840c1e00360641000186600000c40c0d03282001c10141c0000098400054140111420207020000102030602d04054840000c51060f0307070f640c1e0490340403642c18582ca185141c0d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 382310494 1250 382309244 382309247
    0x406022506142e030b0408070c06031a04020d0e010501060207081006050f130e010c050a02060609010e190605030a060c02070e09060103140c090f101205060a0b010c050a03 75
    0xe80084115451810005070b1209101e251189030700403201074401d0b004000b140d1400700358540440c5036048803a5014400000400c0d1140c401c00d00980c00380d5000707a40c0d03021a080c0000c1140720380e408901010718007c1691510401041c1200920808590141e42c4115403000e080140c0501c4054035030552800000044490f0001880c0707084440d01c070265828981c1d440800011a4502e00c9000e80044400020300024079080320703003045415601d000001d019045521042c2100e910140b01b002007000049e81851440d010000540e1000044a13514622340c10881000c10074000684101e0041c040b00340d0481400c440d54014401402000d41110040c0d45079003050406400a00c480070054007401c100400c1c0c5141c2d0030f403030750310800000c402419264078603a41c02e6a249401c050a05d40c0e8010720703c1c0400e95590f6a06014020380e0400503241c0b1a0514800f0740e0805001507001d0710a095044901c48000b9a0100d00d0b02d07801064800e00142d01d440d9140180c070821061319004041d03000d400020f40805 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 382311744 1250 382310494 382310557
    0xc060206060a080309090c0901090e0f100e070c0b1008100f14090703031409040e01291c0f020a0305010f0b01030603110405062101020d2a08040602 65
    0x1000121048003900d0f0352400155224864406403d03001054800000c003009541001000050f6061503c4200700d40e0300d02c214503640700140c4052940f04802c2c403c0c031040481392108880503200c110074021060401d060040e00a0a201d80c0042002c081c4400240d82402c0b010305003801040103505480f10440101089030013052102c000d0306003985000c0501804178080011a8421000300c030003080114116281510141d950071217810340408100202000d94589024800301c0c20107550020a80ba01a03401484e0040c54813020300c02490180703003041c50079a031040648a107104240c801019100003a00380400c00e54500361029400c13080035a400020480150310044513504001d40030030000d0b40c40d40046055418078800a000904840849503a92809070700c440d42200004110007000f0000046d020702041c600303c0c180c070450750b0100d04003020550ba8095001d081c0d660000c615103402032541c00401043d40304607107100308441080000c08000c010b0f4110350307103591102c051546d40c40070328201c042136 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 382312994 1250 382311744 382311751
    0x130203010b0a06210c17190c11010605010e0d0f02030304080f0601090b03030307080106120f0e030d0b0d080403030c030507050712150e0c19030b090105041b060f0507020402070c060206 81
    0x1000e0824041320501035126422090109660b40e09840301c8005500c0310700f110143c0142d804000b90070000140340458801d081060030030f40c50300d2480c4c10781103155501b1203e440c0c0c0014107000124a2003c9555200500e0104540d40400820201c0000f800400d2440c0141c0d00702c04590721075004c801400c1440018041d040f10b210700414440715002d03c0c2407580341d0005a9400e00881c110b1401440490300460110384032907803c0c940050b103081482041d50680d00307003030307102d18058100043c54519140f20703020309680c0010030b903800c280d07114140c0d8a01d240380c4524840a000c10a412052504051081c801c50310415001400c0303c200300d84a807140003102c00010001c0769038600c20a0360101c0074005000704204052184094090080ca040500002d00d041c505462800307210f43e10048002581400c40c103000c2c80001c000040d0610703041c0307054050341c03940035241d01d0719007200d100c1002420351101c1000070310609480c20303075120505840460044e0048000082c91078503d0200464220343c0003840911 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 382314244 1250 382312994 382313027
    0x30e0303040f0507120809010f0201090f140d030e12030601090b03010e0106030513030815010c0803100f0503070e0103060902040f0f09020108060607110d020604030503030c0702040f0c0206130203010b0a06 90
    0x140c4030307645e07580c12059010301c80000740a08000c1c44600350541c02100034941012060001050701d44040ea11140464684c002c01c403001c84861000560301ea03010018000704001030b003000c01c605040700c02003c1d950501b17010b48010140c800000200b030303070348146160001410302c40b048a440396102e840500c89610b0034011000000d1170725000840e07c2d0340442036000d4943c0c040c2c0750428242c503510000343c150300c00c5110a6041c01080d1224400107000712008504c1410b001c0a00302c419410492401c0007014503a0080748240d02c08141030141002c1c0c044414112507200d000052205850310100700549107801d11808964078103c6004050100c541010311401d10036030744c00140e9039030704080094600403440d02415031903101003041c041e81004000f0380b01c520b0008214508269403071b034070f82e40781d17510449450069450100703400e800c5080c00d0241c00d032420f45991041c004181c3c2084025038904005004003005828104654103648007980004507000020b045c2d608000d4a42001418098056641c40c5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 382315494 1250 382314244 382314253
    0x90f060215060402030f13171305030111190e011214070f140706091e0f05060106080103170702010e060c0717010b06030708041b0311010f03111603030e0303040f05 72
    0x2c0b640d240c1842100e10031641c0c52190a015214100209046402007070102c6242ca0288006075003600690085c00144000b446e400c1002400e003003e00d401d440440e814540090005e02c4010041140c00985c0c01030f84c91a45802203103800c42c1801214000c03003400518505071701d0501d482150b2192070000d0f80c8282003545a041861715510001c8800011440604071500d406002d02c000280b00c5401c08107015000360710041030010343c000c407180142245e071012071b940b1034041c040380e0801c80284055801407180e401d101049600d1a102e5901450485001c141040400110401103a0042d5411200014007800da035480785822001d0580d202c11501540c45402d52170102880300700d105021307030040354102418442c250b0f140c07500d041d21684000303030040300c11428540940340d00d21580d1503000000c501076060010f00040380800505891381c111481340c01c050130000e07400e080c659204125412801e031014502040410790608800810b6644204983c90000109010612154a03900c51000d4001c074250b4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 382316744 1250 382315494 382315501
    0x20403030f0801080706030e071e08060c0c1e030c0a0b01060207081614011101050a020a110a1211030c01060f060e18010504020f0403060c081501140301030210090f060215 75
    0x1560b50790030034072405000b40c0c00311100f405040d1082d00061007202ea041c0850b1038160700d030804c031008080312035a500d042449050003040340c403100700441c603041101c101e526454100d00354a8070fa204c0517144241c3c40c288800900d4400042c00070030482e80c2e200720440560b01d0860b0946081140181d00f0b200303030401841810000305010030301151612028040c151601440b41c41c05d40d5000c00200818a498180804100301030b94424080c0910382c45a10070310700050f0b0350126418090300140e118082e01e02980d219040f9280050416070141401400d40d00b020b400c06c00190000780d00c4c612421583d80641c4d403d282c00081d6000845005030141c60f000c1d15880c0000d5140300500480707001c8442c03040a01c0c80d00c4c0c001003125041c540c2c0105160811070079103502d403e40702c0d1586070a0350710030014003001510080030032100106611a200a010003445c00501c1204090b0300c40d5a603001c18000030f48200c00f0700b803060030346e280207000790070041c6005036400f59511750742c00000e51120000c59030500c0308800b91000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 382317994 1250 382316744 382316747
    0x50705040b121b07260901020601090c09080f010203010f170c1513060806030c030f150402030a0f0f110906010c021203130b0a1215090903030603150e0f0705090415090f06020403030f 80
    0x1b03a600900040e4018243c40e8a400042c0c0090039840d000c110034016503c8001c101001c0c28400c00c0d540a480303400242e940e51422900760031000b140e5010254902c0102001e0300440801303c1d02c0c00010008445588014a614560b07003103a03c100c0d00c00e0091421005030014201f500301c0805442010101c3c182c07424094560309154940c054030f0300590300341d042520455401d41c1a000701c036803c1750000e03048484405855442c00e1030540304800540e0039403810000c100c108201c11480d8504540151804001ca04282c8006000d092010000030300c103180b030002d104103c66080040e1100381650940050031690f0b6031a0001c1982d10011846000409801c0440810b488a02a9071811101c0d000b0320394400d49046450001002804011000c054841e0800400701d1034401c0310019011079154005051080302888500d00a40300b036240c0c0c0c2e590450741041003142c0e1b03850034079648141c00280410003820381c444010020038460070010081b490051042c002e09c03185a0250003528440e44170114442c582d000e0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 382319244 1250 382317994 382317997
    0x120203060f04030503040308181204050405150102030f0d0207121e09120305030604020c070807150e030606011809020a08041203051005060c030f0c030c01050705040b121b0726 77
    0x5014004c2035082004c140028410b9401c284e002a03009007103800d44560322500e034203004042d1955440f20002040c140040d20b890701c112030b0001d00075a03503444411500b80000c3e499001d4400b6a8454020119050010030026012260f04a80c4040003441480c00d00340060f1901d4101c1d00d070300400510b104404c2600c40c4c0200a08825201c03400c02230b2200381056601119154030007014650499000e001c5200360180030003028001d88050000b51901a0031b00c00c03c1a01112080c0c080e20030042400e40d400c0a98801041250f04000203203802c02c103904c0c813005000b03000ca4269000100040c80055410f0086600001c00e5000d1440f5604c10034014001e020100e090311801d4540d404208034100b400c002c50720b8001c0007494108000f40680741040c50b461103031050754001c01e005240c40c2e0030001d00500525028070408d5031200707403824040c4c100f6042030450302e03940c096100c443d101c00c0c4006021031050481102000d109241ca0005e959540b0304ea4a489101d00c00c46000345654810b4030f13044190071001c080c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 382320494 1250 382319244 382319251
    0xa0b060d0c051311030411010e01021612030912030224090606040507020c0406120c080d021e010f0609091704150806040b0a0b030709090b0a05040f15120203060f 71
    0x6980c00700e001d05010070464070601411070480fa4540c1c440a070941c8140020146104a0207102d00b254200010070000d0702300e02010401030b04641006684000d5a11540008016290f00386119510340c9188d20b030a58400146421500e20f2810b480210401c00d035001880462445458101800b50151032411540d001e0040e80c1d086026001000000d800e8203199000aa00c00e10034411221102e22200c045400c0300d10540100996540940c2c40605011500c1c01d080020030032500140780640030058000e443d085458039071110001c400302000480c40d400d4011140b501d0b07020800300500d07503440844000420810b00c040300e0800034603540380d600d40b04c050165000c4411000d9003034003c1190940403603110b40001c101d01e50003559000d9000480c1c130746030358607c041d00d0380e114056540e0500d540080d0607495a648040303901400c0c05803980b49074565a1000d41240d000b56800709d18034000500d550007400c44042c07414685aa014000034882006147c003080140c0283d054440791740b07885c000241151800c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 382321744 1250 382320494 382320503
    0x316031b0804110d020604060509030c03070509060607030903060c090920250f0803060307090902060706020a02010b0310020d0c0203031003080a09150801230d12090302120a0b060d 79
    0xd000203808104800a0682d003008024030013580701c2600c1d80013550b0340d0880e80000c4002500032800030024181040310b022444411401840350303900c0c007800500a10802400341d800b500380072030520101805446404040c41d48144180580c12010030028054040c41c414105258200b0781c50000b00e50b25120f528840756090000304e86080c17007030003039500942c0346190400b0076008645131510202d2040141d1500f0180324500d1550340e0b0070007104040c41c02e4095002a00780d82d00d0400c2c203900680d02d000c00c82c0d81450780010056140c0314452400c0e8014a07000b15200c1d01b6001e2000c60901d03010140d4001d02103c10748400402451a144408994900003101c0c0d0410710b1100380c1013800031850b01c00c09800240210f00d80b103207000b500c4038030964040750a5030214021a0645005108030072440342c0c04a070900c68244144407101074000020041e000403000900318203090b101e179840c0c8a104409030000b940e0003a0800d48101002d9021640c6e0700904d01060780c0300120070002c55803503e00a900700407c113400c07 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 382322994 1250 382321744 382321757
    0xf150c0e150c0f0a110306010b09011d04050906011503060b0f0c1204030b1b0a080402210a03020303090705010207050102211201030b06031c090620030316031b 70
    0x104061119100c5140704511003014240184140041c0030009007030070403007041c09441508124a080120300040d480954841d8200030018040a0700000c1940c841407002d1801840c909010820110105005407480e41c2050611013085894880058482c2c1210000b400b88490b04050280c2201210068090301c000300740200000e003070107502e01024200c2da500c40c406031009142c1c401d011020381d0388168000c840032200074080107020442c9c0420000d501040400c1c061400b141c1e10300c0208141c138001c0000740b080f02c000d0f9504061985031790180c15034000e10b80840f40c416038182806076503500304031101241d520071000040b07115440810760401306c500c10b07001440803040404c40b107003480d150345800c442141c4c1c4c140061380385114100103a50080d402004080b43c1410080c0915040c44100340b0024481c820703c0307920386c040300d900484403c1110104d2a02844640051000601d14900061440c01d14840801030109400c05420130840801d04c1d41ca0030040c0360360b04100b401024910021002c04140f0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 382324244 1250 382322994 382323017
    0x140301081f0c0e19080105070c05010606020106030c0501210608010b030f070501080c18030625181703120c0306011d0109030b06060c0d032003040c0312020f06040f150c 74
    0x200400f491041d01c610609071352019449103801d500311307801180d20400217030700c038009c074000c1c400300380700d0340010b08040d20084c0012401d6803181260342c07240e407103040d0420400d500034003080e40e8020031480520030b1010050000580d0341c0e0b5454080d00c64080d52500c2401103400d25005c1c040005020400c13900182c442440701c0e45e40c058a503c1c00e40046040800e205c18042c4a00c22543d0103100342d5201c0e6421090b02500201d01ca0178560902c4c00190b008030601c4885800c40f0748500d02c502e08442196090350b180010740004074545070a6000f0440c1c00010300e256075040c0724020901c40041c41c4160320a070703204946100024007915003c0d0480c1c0200303011a11051040c03010a00102e0600da0040014014515000410101502e0b00103060080b00009641d2074290005940083e451401261990841030560510b500c50204100040c4001021f040103100d002c080c9034000e010004010346080141e444a00c0c0605000c00c11080f054402c60341d850500703a000c20200b11030700c55001940529590080b1409 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 382325494 1250 382324244 382324249
    0x906050414150d120203120a0e1b04151403010c020d0806040b01110f1606020703230a0c12030201050604020703200705060c15090a0b0a0c140301081f0c0e 68
    0x40d50b0032020390f0000641625074000c030303080700f41891581c0c941c1e43c001c540c2c529408000c005c01702805440413164078106100c03000303844c0c400a21060030030042030074041d082410600003802003203169524801e80d903044100160114505007505200310065009100081c06606c0890701d0340082040a000f00d0b5a51010441909096000d0301c000702040c1440624600d50804a03450642c203000544080e42c054010505d1f0300c1c5600102d84001e00c5a030000b0b0106c141580d0740c1542c01032204411606104205811540d40c3e54200080016550803d4010004ca030702c940d00504090003442080d400340d820000130852034181882210641d03a0560b48a5040a505c41d0422801c08103d0401301c01e144215440480d890b950300380241651310052008000000d003511204e00a0030006142c0001a0020103040340896110305102d90702101c409400140d6182451007565549007800c2920004880840041440100080d462924082d82400381d100211000b401800b40c8070071004040c00a11b41222110340d030b0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 382326744 1250 382325494 382325521
    0x40801112a01020904180312180212012004170706080606090a1e0e060d03051e04180b010201051f1401030e060403090303170c0306010f1115010906050414 68
    0x40702003900162500b0341036800103042c1c030041c8030120900e40250020404054111556070740b111100c0c003040c0401082d407510760480a8440301d000c3d018418046040c00c800e0020b500c42d41d000410003a0160720740f5200c2182040540060040c500c245c0526044521501000a0654203e507100d23985c0f01e0b09680c8800030320141390004d44840f500480c031500c010480d0415402c140552400b01802e9150b490b1905909103290200078007264080c00c0982508004280d2082c2122510300103a41c4444c0b15051060b4194400d200340c4d4003414440040c1820b0b0815041a60092880c00d0026070080c0019144c2c02c01c00303c05031101c0600c4402c0c40070b030031204008002d10180c443c41174440c1414002401c24a0807620307802e10004550440000e203031190281304150b08010781c1400b281a02e150b45041c1d01d01001205c41c2407001608a6040c0002c00318200c07030380e44c4159420000702d074070700c070545080032903204100f8500b80080c01801002e9007001c00119140c2031501c50360008061344104024642c60b04542c14078031 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 382327994 1250 382326744 382326817
    0x601030c12110d0f090809040510080a0305130e06100809190503120702031306030b0a080d02071a160213150e010e13052d1204080111 59
    0x348078121140c00307400300c01c070300c10b00e0201c05000000c66900e082480509040f0f0304e0305550022058507000000012801000c140d840041d4181c80004454a540082c075400b816140c0c0141c0d4148146109241003651100c0908404a1200300981c4403039200c4401e401d0340c003c200c40954010a1074051204894400c0106035000402501603c48070030000d45001600d0000040945141e03200044104945030748403406e5a01c802c4501c059400c00010701c2441c610031045100b850201501c0e038103242c40c43d9448800e00300080114004031085944542000303501d96400380b0a824a02c03049a50401c40320010000b25204c40692440902030000564208410481c0d00145410020b6843c1d84124900c0d42c4030300d560014140841d001c1561b503161000c402d03030300000249a260380205105000300042c0f0005400000c0743d642201a00d41002c240a40b03590058202440301c043c0c2c880e90b16140c20700382c5031400410645072402c0080c0020740280c0300c405841c3c070407441d00c046100d01c52021017140c0c04a25114001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 382329244 1250 382327994 382327997
    0x60a0506060922020406020a1b0b0d090201020316061401060503060d08030a200706060614030109090215031617070207050d080903031306170702060a0b0d140a0c0603020f030601030c 80
    0x103030090708605078200c5e00071790405000341c0d0000e1101e0043c07010003601c180720141e100143d1840c80d0704010551603a0f00910601440107501d50a1200c116030080c419504503805400741d001d12500c0720b04240000d4035031010b803840507016a2001240c40c5200341c049070301c80e40000d8421320508549682d40c034080c5d4402441070641c641c7e1550b9425480860000c80501c2d4500707981100d0316007009082c401d040340d10301d130b004106214100f1034400120141000752811181030340c0000034001d0f01c0e4008960822008000050b0401000042100c588010304100151402c0c3d956445c0e00b4007840d50302d82102e40d0045d1800805648004020060b51409403c081c181c68400d4255504040c6a00b01092440c0c1042c2402e08222030760847c280300709070f400580c0300b011402402080c0683d050901c1c01946a00014105089041d00c0b1090b904c031945915012044007540b00030020806031007960115100d81b1071030021a10345000045c000b94540c030034003d40720301b0140c0103002c91454032803000650042c880c4510705e40 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 382330494 1250 382329244 382329289
    0x1a0c010b0a060804030f08042003030d050f0a060b07021f020f01060e2203080a15120b012c22140a02010228080c01060e041103060a05060609 62
    0x80e41511119103820081c042034403a01da942c2050f1070042e03c03540700030303126074204042c002c100008140b0703483c6d03101000e010003802915400300c080003090440c400c040b80581424100004d204000c0040091140b0411201c282040982e4036030011560610681c0c00c0a5445541c044002036040203c004204481060340100c90071500e0b02c1c40c4103401e650490b0300c00d1a00240400410503a04c140e055810100c1e01ea21403200a1800c0c1c1da9400381c001e42c006003000041d107540c0c00300324440d01c0c400c02c80b0401909912100c5107503540c00d45018043c1580901030800c2041c213440c0c0c08420801070707801a20310010300d00754451855803010107503440070303c4120b01c0300382c5043c3e00002040440d00303030302d01500c0f40b40001019144031107542c000a89018202400c2842c018006000240521540c3e5241e114442c0e000c0c3c2000c1e41c3d110b244d08858050400c0750420703000c07440400148000c001c8204541020318000780d0070390750710765550344e810000c0768000c440f4a500244108501082d52604181034000c14a4000415 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 382331744 1250 382330494 382330511
    0xd0201050d1a090f060108010b070f110f060f0c0712020a03060f1d15060307180e030903010e070f080c01050d15030c081e0c060a12091212151a0c01 65
    0x203d0a01c0191400080da05000c0103000495034824640350260605030300c803503d494204e54502411444030130018080200f01c8091413465690180c3c1c500c20b0100c020141520303003003811400c40c00f540c4031005600040c464804001503080c01011b040410b00d400400301000c440c82c5854000c06081d5011551820355a1405103003e42c480d80c11848111841c14001020310303c954032101344084c000500300758802c2e80903503800c021080f0800c01520307140003850000300304240980f038280e107140543c24440340d00d035080c42801420043c0028458007242c0c00c0720840d064250341e441c001030702c420000403580d000030000c2040c45500056504911030400c10081506820344d600d48a001c40d14500703410104840e0030000e919042c80403071906501050382040b014141c50381e03c82c000a04c1510031041313010107001002d60400c0820340030303501207010a9081042907100c924110801403210b01c400e801d0010340c0b4502550351400c20b03c50306012081d6010403032220381040303108a40000580011303200f82001d42d02c0b410f28 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 382332994 1250 382331744 382331749
    0xb0a020418020301050906011106060f12032206030903020d08070c02031506041a280b0c0c122a0607060f020901030c02160608071101090507050f0d0201050d1a 70
    0x1030715101c04461801a01da5040c9000c001003440003804090405ca41340c004000028404190703203420036812180c2900c54800080401c00071421950341c08180d02002c00c0421001c1001c408840c44202c900d104034284940b200b10517005c5955004020300140d1100803101d0405000c2c81070b40f03400c071b0f0403030a101d00226510b500191408035103410701c20b403203d0140c080c0301c0380d030829000c1c13001050303640c3e4200d1900d402c0c10b40200d20007805018120055108221a94600680f1003010390090104044120741e6200ca0501c4140e0b500084005180035000d0000c081c8031980000c151041403041200030b11068425269090024900401c00c042d03019130200855000a03109108103100882030714405070f200c2c08a031001408030784a010210095401c2003070249955200006c1c0c01050b05c03058203240c601d03501d07907180440f00140a0800c1d0490b540c6072144034070500c00d001841c0d401f15542110f002c420720b0303056410f01c00c0300d016034803009003c030300c0070700498480441d00c0d041604506440d03010448000010f100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 382334244 1250 382332994 382333019
    0x12030609091506050a0b180414040501090b0705040e0a0e010e010e01050a150b03070503070203160f1203020a0504170a0209040812071d040213030803090f060a09030207030b0a0204 79
    0x108691521241c4400103281442d801800028002221a039101d2890302000b10080d1003030f941130f880002814406e611a0765900d5000c2c5844e074006c2d41d03c3c0ca5035864286000c9008208501c3e05980b50400d0b080010000d520441c11a02564041684d005e4941c0b100c240c4540542002280d0704815500c40c003110b500c40d030307003485102c5141142c40000b00e41800d00341d5414007290800d11807035000c3c0d0306005007840310090702421203400041d58640700343d490b5250802203007180100d490590500c051289100d041c4002811428400c3d409001100114951440d041e01244a010001004160144000c00203e00d040301c0743c030341484800c0240d41c460f4030341b540000c5a510048070100d400c0310022600c210740c040c01d0401c4603440562420070400701c0f178104140c139260f0752050010070312583e000284404807024440081004580c00f0583e6078070782c18641c6145403205009420010140701d110b0001c0c2051401d8000c0c000c200e40c0607005003200f1070840d00e88046c039039001880040020b400b0007000030903102940 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 382335494 1250 382334244 382334261
    0x9030c050111040509060d080a14070b04110907080402030601060c02030115120c1502070e040807051b01110a0b01090509070f1503050105010e09150f210607020a0506010312030609 79
    0x50312030f41d44604190820000c29005800507010316030ba0405100040c00400c100c5415846a00b0300c417003a00d903400d8006505201d25040108007110700030902c8100b1220101480380e010b411070b007180c500ea60b010400ca503040d83c1210043c0d455800075004100c00340c020850407145070700140011451828280a4080010059000303484010b800c040710340500041000b400f014064a0401541900c0c451200035a11a05406100b43c0e9a511002090030405000101c418031a4460165181d00c0e048120360443c02c0b03c0b00e190030340428080040c0d41d80650380402c80003a41e030392203d0301e03040356401d110141006000c000c140d59002d21821101040c2c01e602c0c10784080c010551006402c0b41c1c9240441c0050580b401a40480d041c4540407143d00b80503076881c4039280e4007480002c500c4d80c070048045d002403000441c0081464111008001004043c5080c0c1100e20310314402d20200c4000740c0724000104d079100c20250700540641c01080040c800104418610500e1912914001c1011500c400d8031408960002 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 382336744 1250 382335494 382335521
    0x40b19020f120106090b0705030a050310090e0601030b06030109020607080a02010b121606170712110a0306080d05090102030307051305150c070801020c10150e04080c1002031909030c0501 82
    0x1800400000e513021740303088050102000b480f400c101031a03442656031f008000615040c820081300041380240c1e0000410001c0401410a00134146131034000c9813514020301066682c03159010006182d400c050056046059000e050107150400c40d44034201c603904803003501c41c219501c03030310192079580d81d062030b041d400520745000d0410840310070142d4030556490340c81401070144c000840284100c00c2220030f82d01000f507003043c030701c1c000704a20b4940003052a9202c40c1c8864101060511509605500c0396080d10302590807101011044001943c0a006003020380340107038401c2002a034118891009030181a20400003100c507280c42e840010214410072086030141000800c0d00d50b07002c8405c211440c01001ca14001b1480c2241d420725151300c402c03d19480011840e00c03580c40400f10302402c411040103040c0015120507505040c034241d481540074242d07102d40c5116031000407102029a1080707900454524044640301600d20003014050061190103409003d204480300d03010410030f019000101195 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 382337994 1250 382336744 382336777
    0x9052409031f0e0604031403071e09030302010b030a0f15111b01150f121502030403020c1e180a0207140715090b0403080f0706090303060501080a05040b19020f 70
    0x550b036440d0b00b1a01020b075000300c0d56225030140804260001a105d48070051000030701d60380c1c2d8444805035545504200344410110142c003c00050503448031441081c0d038480c3d070080c02458001010143e440b21038540140c1050000701000c0001050604c1e610408a641500400c00007000a001f600c5d903000040341230845000d8520780d040c280f00030300c2170305264a009504040c10509121647e403016010780294590b11610314001070a11911032070700407010949040543d581e02d0241b400035220030400095078002c03881a941f900300007202100340612400c010780030030303a500b10f604041d018025001c2c00400c80c159080140301e0100d15016904080c0405a00040410518101c6031052100710118a0001c01c030004600f441491160011542280e4101000a0300e0300b02e403880c04540b511840c840141083d02d0007400d0700070940c040d0843ca0407204240c13140c81e40c47d9104408002a01c0c800c860060a1203026400908146070019800c10025140314005051501c03151506100303030300071185641c44042 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 382339244 1250 382337994 382338043
    0x120212100b130e1e010f06030c030317310503070c0509060321340506060d050d0c03030f090c0807091413020105130b190905240903 58
    0xb03054004000781403408008103c010f180b441019181d41e4001844400c1344810500802500000d4004200c002406681008aaa0760b858140700345a00703488203e001c100c1e54041c042d5040341d00c21a680c400c80d440c40d40f002c2e0b0501d803518003844030100d101c0b104860b240000c0c2c08101051041000d09103040c450040110b10f10b0070300007005074074040140024440c0d88000d100009401d009002901040c81580390951500101440000b11081204004507140c1d881540400c401c3c140510305d403045030041e015682c41d502c40c602880f202200311706014003d5881803480200e80c51240407541c0c131041c0640380004442005401c01d4055809101068461201c80c9005020003003041c40b0307110040178584001c00c40b011303002280316484400104036a00c600d4142242406590007581282c10149500d5080c400302d80d1101c00c044020f402001d00c48500f00300e825100703044030f0300840020381501d5005101075200200c00403c072040c00c80c3c0d41c500c0300498600f40415056034a080019130420640880384150302d00b03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 382340494 1250 382339244 382339249
    0x60e01030b0406180f06120b070914090433020406020601090b0f120a020603040b0108010c0c02131815140a060b03060f0f10030b010e0316120212100b 66
    0x360103070a01d910480c6402d034100301107010704c0200441d0f000000004520341d051944500c00a0403203034007002000d420104528108490984da5521444658072145031560311050301505a040300c82c00d050300301c005074010074046040b00004000d079046c0610911002d1416000a41a001401100c0000c3c2c41d0003080601c030594050045c10b015011100081002807000c3c80011008408211807500410702110070b00d02013802840100d0459401801e410b980b41454a0b0641425009100c0c80c0345552800703050300e00181c86403091500040d0000c00180d03110126200c407100501c07456114075081c0c524442614005149c9120b690040c5180310300002da070540740070000d05601d00061491010502d0100c0a104021645003500d412403000d94400c0141840301021804000c400091240d000c51144180c482072275140e000b05140301402e031707102228500501e080c1a51002050820101001c07100001d1040c01144c4040d803403141d0009201420307444d5000395490401c802030541b10356043c0c440c19405c1e12030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 382341744 1250 382340494 382340501
    0x302030c0f12030109020f0c031612030506010e01050309010905060c030403030518210f070c03020103240302040905120403060501091503150b06040801140a110703020a170d0501060e0103 82
    0x410004000d000b840c103020a2041540c4814001c44150a5001c200c0042044c0b1420550340764080c92001c0360f50340c050340c1d03040b245c0107015407004888048003000700044903442030050754090103040c3c4440942425007070064815400c002c00d8220a50359038801000841c0c41080307002c0c06200b103010300a0303507400e02c1c0c14000d003a600020b00c000021400390b4215200c0b00e50020b400940402e219094800ca02c4000702c1221681c41195000d1801d504041088001e01207030041000c210fa2003600c0410140031000c980c2c2c45404500c1140b0407407003079060781c20005410b1540155003918426000e84409003d4500d004034650041d800c265030042d590700042c03103040401e00c171303500d0720208510346000b00c18516520f0184031401007082da0a4651520801d202c141c541c1e01c191006000c07271070000d0001070490074003034540c100e04540c08218035041c8031a555917000300c00c04035000e0039016805002d0141c056115a129010070400d51950600708000410502c1c200303100b0b1078040c0403159101a4480c4800b000102035 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 382342994 1250 382341744 382341763
    0x30d05040b011202010512100e0106031d01061d0a0e06070c0b0601020705130e0c041a011413060f021513150501081b061c0603031d15090613030302030c 67
    0x1506100303d00c0d0000d41c0c1c00a090340c0021a00103030300003960761640c0d442108040d13164400341342da42801001164040d05070f04280f40802000d42000b444520076100705003666440d01c2105a5202c07808c1c0c885d4041042040d00e0780e130004181002042c603038005007041c2d02d003070400c031050800100d90490341010089807400b1160450424402000e40b541014001400040b500e850040020b503225010030030b0210a014502c0c01d0f84008100300215a9500c100c0247c0700081d8403801e000542210742841c0d20601c03101980c00c81c0302024100400541403640c2900c41040c0c0b42c03406410351040308080c0c03002e0b84001d203040d4414041145044401d54440c41e0454450051451000440381010014401041c000400ca02d1100d000c1034842c081c005018081030781c6110344400d0b6000c07403d000320400c0c2090000d801c0a000c0f40e03c6942c3e464a1070b0300c84080515910445c11070303154068500700d01d0007044143c42014012040d0010700040c0340a409411102014031507510880158201049001c1084000e0107401003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 382344244 1250 382342994 382343009
    0x305060702010524010e0a03080a17011202090903040f09020406031d100c180e07020c10080a0209120a0b09100207020901031704080f0705040f060e0601080414030d05040b01 76
    0x890410308665400440348003000c00c0031384110102240035a1081251181942001e899140c40d541c5a0414903059404414080003013401c1904d000c070384a6040065034103c815400003541c5452a5900308809140003030509041c0d031009002c0402ca104032407074284002c0c001c00b8001a0388a26020016040d61030b00002c81c40f000032505180044480b0110f540c08002c3d00b042e80008a0314040c90090310348540c4e5440317206e64041850b4010030001c200c04800c0c1d018801d00e400329a503400d49103041006005101e183c1000003079040700843c0c008110358000e003001c20300090100d5000580410b01c18508101c443e030a403501014001880520002402003d0203418541d0065152490540104d0b54421040c88000e000e0b0308461120f240d00100b003010781e00074022040030798041e8022116030a0380d40703482d402400d100743d25201c002d6102c81c03414400c500c212007441074850b0782a44e401c00156100ca50040040e124110346a600c1030401c0d10920007010401e401c0c1e2000904c40c01d05041541490a05800c2003e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 382345494 1250 382344244 382344251
    0x40503270a090209060d0519020c01020705060f06100305060406121a010501030e1b12011409060a0c0e04020918100306060b2107170c1c1a010f030b060f04030506070201 74
    0x7802da143c10303089810000c21b102000c1400d40710002d18031540002c2202e00b49040380f0201c2c0313024110006400510100c0d009008446440d12001d03000801624103440349544407800c24940c107400c034000e400c0550300183c010000a802a5258984a42d4000a12044a00341800030728002c0100303404102030701410782840c0820980300711142c00382d81c600e52442411802040c2d250f050510380d0b5035004050145020342d00034410f216100c9000c600c40350098071035802c18020907000031001049441091552607055455080c0001c920003480f009500503461076401410b241039200501080210007400780482306500400c50b451400d00f00304030343d0390785c010303007400c440070003480e001580c2d0220006440c17402c03a80c010009440703101090700c121100360545074072603064000f0070102d0014140079045880005004460042101c40c00c2804c8480e08401e881e0710b1903000201180760351141d00655000c42c0c01d03040000d40c0170b00e0312002410a0308030109000111070001814030030000140080c5400045900090 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 382346744 1250 382345494 382345507
    0x40309080f0c06040b07060902040608010b0307090b01021009030c060e0d090504021914160309031103010e0a080d27060c020303010303050706020706020d02030a1b0e030303040b040503270a0902 85
    0x89143c1304a2149901c07a071070220304282406110f601441e126540100204903030b035545c0d88018060424004070510a025825000601015034082c40c02003e80507070240c00fa10081c8141400100ba2195094040140e941c00302d40020303c0350b2142c484030314154001030040710000e1000601d007032a1500705502407401485010240619801c01c501e040306642013203035030281d0307144100101c5d00404520356202100041c40c14149030b00510a0b1040d20700400c1400b1080c9015402e00d8203843e802a94814254801c2d41500d020680081c003a1a11200e98800403039090740540740c01095074640ca030030554108038861180208800c900c54001c80040b24005141150b2440d10301903d45d00610030007030b00032500007030b0001c10403034241d044178940418240115201d040c168007010080031031203402c20303d0404440202540c02d00a03c0340480c0000c0090003149540e42c1c1380d8440d900b411028004940c0c903c400d220305445036070101d120061828038040402081c040c2c030810004102681d500003210030788100b040 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 382347994 1250 382346744 382346749
    0x2150403020108150301021e03040b06041b0e0621090c0307060f11030702090a021215060f0d15240306050105031311030102030a0603020f0f090f0915040309080f0c 72
    0x12603520560b13050184a0001680300820302900c1854140121010344107007010003082070340b01460045016611001c5d0b95510801032104448031860703074800010b48198500702481c413919445000c580098a00d5083c0007050005440c1c0c0e03c000c00c4203020034083c82c010007a40003020080904100012001840e07200c0c61f0880281c00c14203404400b4080060481c0c41d410045401c00449408540c003401f400c86900c0c08550002c001c1d04640795094404130340d1400308000b05111540d8640c4914001c0160b0700e080003c45448580c2c0d4400124600107a84803801074040c99103000070000181905002051030055803098081c0300c10b20140500e050500e400307030511051741c6c09000e613a4880010b0407048000c510b00d00709402d02d81070700100d55074190300000030409403807d560000e100b120f2003178500e1085981070408114038888a000150b4012825100054030600031105442d001503051094454850514403003a00d0004229000e0303000c5811810108500c04042001210045001c0013405001100100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 382349244 1250 382347994 382348007
    0x10f0b04090f0b1b030435090d020a180b120f060f0a020712120609050408030705030606043f02030c0118050a0320190506030c16060504021504030201 66
    0x4028220a00340fa00140040400031480011040ca1802498032072038140b4001c0042040400c80e9007141d9040c00c0004040b10310141c620f21508822030083d410007070b010b003e0100d105012070082c0da001140180c00600d04406412100718003400400c00b05210002009014810000c1d104c61411540491440c0317580c82804030b11300b900700c000c5465582440c4c4032288620040d015100b00500700f61840b82e01c407240300b030700500c4082c2e50000862090090b03981ea0b0382c40c0011034030115400340c400e4100308002011f0310b110743c00559001c140180400e0500345c44a020f007120804404903401e20710b404921025960400f04544242d07090b03464500c40381c4d000c2a501003511004400402410b00a1080d02c4144a401e041ea0700406800060540126a566030420341684a90b030b400c03202c03042c0c0c40711400380c0c003d0a017080701e15045011407804581e907d00e0b042c10712007070341e0009040101404d001c0c49558609001590716080c1c142c0240c801041d1402d081c010449070007120a82c5441c030700300401c41040144d07004103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 382350494 1250 382349244 382349273
    0xc2001020c0d170f06060702040e25031112010e060106030b04050a11070b0c16030e12010501050312070c09020f03090601080303060127030206030903030a11040b19030b12010f0b0409 80
    0x84c030313030a550340b150004101c443c0112480250322a09041402160400002d203065070f04410040440640d00b084d40780742c0c190303a418000504446031194401c5000d04105982c00c50409615000181c050244048941460300a805c4000003d4961032004c0c914505401182e030001da17201070400201a00101d40c2090388140c0500900440c41d210001d011131905005071a41c4020644904540c102d10b858000c2c1511101503a10703120f0b1b08d100942c07a252400501c2a00c1c140c41c0003038006e02c840c50802040008903000500e0484007a0882c0c240480e181d0402c2c005000000302084800b503c1e42000062030b420f10b40c0580004031958410b0082110581c7e00c4402d024007100c080b21010740107641e80c84104110011a000079402410010920803140000001584100002503041002c0b00303a000419100f8880d61042d018508424424489100c0c2c80300c224400b01c140301c1c28001404d03d40107004c80d9004840f103852144036551a00c51941003081c41c01a0308141104590802c0030901580d508042c0c200100e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 382351744 1250 382350494 382350511
    0x10e09070309140601080a020102061302010e060304060f1d0d030c081f080105040f030f0206060a230d08310b0a170a0501170a0c090c2001020c0d17 65
    0x8420701402d00c040c2c980d811404000c3d007010386115685078411560741e1061208102d0051003441e0000c0d403500e00c80c2020764030070b40d0305940d1900c0d146003c104006898001070000d4407021b03a00d00e65414150500d01c200c903403698401c5280039281c42c00c140121b003085003903004c480a142c24280060881e43d800411164051410002c9078400740c00d0080e8140031156641007211107610b090248420301c0b104214444540f80709980700068801001c20403030b02c8013420798100e9001500b00b0b0060054200c220b034002c00c0054113241e0080700200c550700084d1103844580703040d0341072361001804080da50000206062240d0420185c68031400443c00c0484800f0391310312540442070030205521138650b1181c0c120940d01840c11a0401d040d0030b040d59150000c00003807190b415461031807003180c040090046841030395243c0044200d0f121510300f809010241c240384050004118018603607404071113612404242c4181c0240c00161100c03585403d003850140110225030a0000710008000c13200c0c1c9080c46264800c416 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 382352994 1250 382351744 382351751
    0x13080d080903070b180c1833010e0d0605070c0c090209150711030a080904051b0703030905010b03070e0a050a052404061802090123070b04020316150806010e090703 72
    0x4a407001410000e607400c3d110b071f0002c200310301740c2d165134210110a8065107090040740003001030080700a526285003680314408003201d0040e1001076000c2c07540c0000d08480600f8900342c3c0f0302190394110450b10101c500e44081400361085609202110003044042c011141e011840c003080400042c1d20105a20302c5000b00c1c03000007a5800c00c00131103055451217101c0140460303030616400d191400302074000d8520303140a0b500d070034000313075120801401c919914880c101507941f42441d2038800301c002d064101801d1301e6640d00c908402c0101d031000c014040040c0342c2e0300e55413101420880407000c140c903806082c004c0e4003803d260a1000c1c1003014039051110030a51107021200110318000308014020540c001c414100c403241c1c1c141c0703494640d5001082c0e10f1909071380b04076030444c034a030155031404009072420500030010b00c40c640c00503208480d00c5070494002000c407619503265900744812142076400c01541099100e0107980199005200c80d0b4020000742408018000001d0125201400041c000c8040549 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 382354244 1250 382352994 382353031
    0x270415140a0306020a1d01050f040905100807080c09090106050a181107080a030b030604030e0f0a120c05120606090f130f0507180e1504050313080d080903070b 70
    0x8498422000866000e04190b403120105c2e130000d01580d0649040c00c3e900c40011a0100a07984100c0884112140940c175990910b41000d05810082c2001400455a180c850a000c119450104007020080102c1001001000a844180201110040d00141480e0304000090040795180ca02c104142c0d000c5504e4401c80d418640842d0000d4203003490445030700c0400103000401c0c4202000107000100680e103003484045d2248052681d584000c540140024911039001042494082c0c40c021080000510141e5440d45400304601017000e010000c540e4821154403c000c42c5c102094954160640003002e0485403409201190f9580c0c0020403881220060100262504100510403003420b9000307001c1203003441071032500300ea448081d03010752242c1105580400d2600042170194402251010740a0b20000408021404e080c200c043c20498076400b081c03240b07654681d80480aa4000d200c0d02c2c00411380748500c084003a04c04c00340030740000d03100c1d0010040c034000b00d600d400320103412a8120440d04080f01 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 382355494 1250 382354244 382354249
    0x4050d03090e04050703200f01030f090c090e0f0601140f0d080a1d0a08031b071806060e010503090c090903091002010b1e01080c160827041514 63
    0x300150001e214441215003808140400003038171074103a910030452040300808403142c100a0000c01a90743e03500012140c880481075100340c00c080030030a03072110080f901000c20b41e01c032000c0c4d0f8204d030020548540d441c1c00d6040300c80c800308000210145501d01400036035061040f0900c440440001d02401380b40ea1a4200c0ca95803503002ca0105002c0c0c108035a2034490b60000d100510000c0085001070b2801105a603140f400d00d4400c0c2c290040754000c400452501390b007040211000c10b064007801c5851f00440700d0001b5810346a984040440c01d0040300090142e0528a02601410190071258100b100600c00c001200303100060202c840001100c00c18416a5424080b51951240d1100140c01c02980c41e020300040b5015005900c5034034046400003400c00c03000c0c0002800e03204000f0724600165126003c500307407025844c002c107800284401500b401030f07071585803840594082e8240c0d2031090b400081c0c084940c1d10000307140c255500e040380c00344031021400d0000f01c0707011035070f0140d402c00b000320485402c100c0d0b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 382356744 1250 382355494 382355507
    0x150a0303021509070f0e0a05010603110706110c1e0f0312450105010e1312031808120a2921152a0309011e0518011104050d03 55
    0x8081e10f00b1503080301740c0c4580245032422415100d12a45030305040000c40c001e8003e01410540504106403d42091195114000986203030140801d01100c2046400c2c0001028840d0100f04405a042908a0f44440340840d11304071000c1030516654200b4001503e10030341d02e90300d19030000c044038220b01c00807250090382509000710b140c40d12401800d000d01c042d080014002030701051000d0708000c1105a0340c0c1d440c1e030540e00c40c00f20303021902004200038180c00035101c2265019130781607610300058081d041880e081180c801fa00300039140c907100424030000072410100996844048068184428a43d400c41601450040207942c0200c10314107140d61040d8840c144000d090900c4c020907403c4411a01442c1d640301c100c00d059845081c3c07903003400079071a64030030600d004d8414107100041b204420031b440186001e800c00381c402c52243d52074a40440501c0c03000c000e0780240855107200083d02d810000140c07540410484010240ca0f4184aa0301914082c04001e80d0b045030030513144500c5003071003403600300c426 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 382357994 1250 382356744 382356749
    0xa030209120105071d010c210c082128110904020d021b030c19031704031106010501030608060f0a09050717120322050115060503150a030302150907 65
    0xe50701e070004214149501428100fa101340c2c0517103c00d040e1820000444000104400c060038514540d03020511204201512136402041031074520980111130b07031101030540c0404903070300400d01c06846941c01c460702417100c181c2010710203000e412042504d4203c520070b1020480101d200aa030b420310010030083c000100c42145600610031551002e0560700300c00290820000684841400005800d03210000070445e46203010f039800800e5090000f0b600c4a1001180d01030880400c14200030300d4a4041210303590a0156219442c0d41091a504550551504005910a03030401d41001010010040d000c2207854100d060071001e80003a0340d9001d5214050001c011000704280300d40c40300042c4480e0511145500c9140f860141c844c0c2c669011001d0000740402e9407681144078101090800058000c0e8949103500d20820021402c0300742180341c0b48542455500240c080b0b180001040f00d41144005a040401d01c06c0350004200b0342151802562038844126001c64074001002245400000300b060b01c00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 382359244 1250 382357994 382358029
    0xf010e070c0f050705040c110705040603031b02180406020706241809050a03021f05010e1302040f021b0606120616020309040609091a0403020c011202040510050304050d0908030a030209 81
    0x21034001f01c8000307001104104003502a07006040c00400c00380303800e00032002120f405640d0040314550b002403100d041080090100d0f4084090040c54480080750f0201c60f100714003c2d0030068465984d400c1c11000e854903590391745c0e804c04501d5031030890490301aa000c001c0d901c0f012000941140840c0b9400001c0c40100c20181945c85016691410554002603010041c00c102440300ca803c006090400d040e98828050580042c01203800510156030040c000f00400c1c2c001040800c0c5501d00a04440c1242d0001008440c4031240006180a204040110070f400600546550003104003e03160552140300103400942d1401203090924100741c801c0003910300d0718000510811a4503130791032036080103140c80241190a0b422078201014001034015015120300d030150054068080d440c3c004403800162102c501a03070303d80c01d10002c02e49450342099007040340c2c001e8441607924203090500c0c5140542e1000721804100398510f05020740c0e1408800d072540c00e4883d09000d85c8844441001a0796030103011309888 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 382360494 1250 382359244 382359251
    0x305060c0307090906030503180f0d0602040f0b03061f0c050105191a0a060318060509010207020f270402183d0e18070e0f010e070c0f05070504 63
    0x10100d412100194000c0000d6151906040d035a2440001940e48510016080c1d0700144600394a44154440110b00c6010081841c510564071000040c0528a842d0082c3d071001c1d4081001c0c0141c120003c1418068070607240c04070b040d494190002100615081e900380d802407410261601102d000e102c00000d400d511070002e120501d4601501c000c0c050030000741980c014100700c1003106081000021201c48a8090030410000b400e0102c142d000c4c28960f144c003003010080c003403041d0104210344205409920914005a6201c00e01d004110180581e40a600d2254030307682441032150a41c04889401d00b41201c0d8144071a81d0f5900000b001029910300340e42000340844200600804ca40c2008100c203030820303078031804000100e1400c103086c0480c408545100c80c0d811000307000150080c000b03170307600c0118185541c04040c0d15180d0182442d9440c0e01100c100b03804070301030114000d010f490807405454815002d0340d4500d002e042c02854422144405403400682c81403010a0180034861100501400381c01070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 382361744 1250 382360494 382360501
    0x12161e0506100f0e150604091107050c18040b041e030305041505010b0f09040908041503060b13030f05070f080d140903120a0306030203100b03010b01090510030213030506 75
    0x80d845070022a403141e00c1c11141c400c0070804140302c040600540704282200502c0b643d5a00c041d98801d00c0140000d07a1010041c0300000e0916268012502104411004d65468805602c0c00a10701000d05903540d10401d42c41010341022824022980c2d03000d90010180d2589403280d007402c03640307555176028100c005989650814141500354004030b01503441001000008180d007500d0300101c420a0092070f4a82344100305084a12120724050602c5c03020041c40000c102c060b540d00c51155a200d03038040c0003a240145115803445825200381002410072036801480c20100d5215000c1c1c41c14540001085420704900300300508c101000060f0240200b0329200042c1c1d07840e0108590390300b440b01c00e81c071300145000a0004d45c800320242514400c43d0b0140042200d94000d02441d44a60803d0f10180d04240e56810b0020250340d0411a01301110214080054a00e55441c249400c0d510440111030601141d0281001103446c1c2c0b0003022040e070301c0d030301d40141c9407501c0712550b2654840c079a1000d8905e00c00c402c01e0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 382362994 1250 382361744 382361753
    0x4080115362909070f020c042004030b1006030e070323010f0518070509060d02150310060311070b060108090c0a14091305100c1b050a05060912161e 65
    0x100b070640344003211090381c1c3e561040b000b20340d85699040352000580202020840d030f030800c0e40000d0211140c42c2c2000c081050100314100d0640c00c9035009480e0018203000f802094003002202d40003410251605121590002103080d42e100c045200c02031911226100f50018000100744084403c644040280f00750b013034144088014041c2983c882a05842e40144020701070340024605044034409886c405486d0b8401c010000007002d0701c801a0307049604101c0784210620418011031003002c2e16690280c842d41408070080498400848034a603c178020009040803c0c10010015031011007460100c443d551415501030600103406840754000b02c204c60080307480d04901000d494944030a8a0f4000c0d943e9a18034616082c0c0301ca00f501034401e400000300c581191019401140c5400e43c1402c2c20742d154118541c0e4a42a141031003404c1d199501f10140c4c1204019050191f660000520401814107030718101c5069128480c124520f400b800c68030442c03000b004001180c0c0c54081003600292030340100541803 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 382364244 1250 382362994 382363061
    0x1d21060901110c0616140403050a05060f090c040f110c061504060501050301062f0313140109050d110301022109030f090609030f030408011536 63
    0x118500d0075400c00482151452580c1e00340e0b128008490000c0c605501c80041c5141241d4401e43c101c2c0401c1002d01e03402420b1703400b88008000940c41440140007440075070a0080c108540580003590340135900c401d100ca8441c0002c3c20200d413100481c0c0005990242400501c0282031508241c4403061000c100c510709083e0101c1c103d13104a03070031390f0f4600070004a041000100d54040c0900c6000c0380e41400184951072050082400640800600c01c1c11881c0b8100160440741240302d08034040d17840001c40d18084d03078400814800500f80d10300644441e01078a4006094000b250140d01e01603980c440789070042c064510407900c50020050001c40d03036000d00c40d03200d001c2c05031805800212010804041241c0040000440e8495070750503640d6428a80880c0810400c0da0000c05040d03030500c6042c00030070065800340b00a00c0108a25800098202941211074100c205c80b5400030100300311124030405181d1200f144034000c50071440c4e080e2000e02440108074010441480200300880d840d00324098103080b0980c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 382365494 1250 382364244 382364251
    0xb09071e1e12110c0601210f060c030b0d03140f0706050c04170604050c0d0807061d0c01030b0a0e0403020f01110a0306151e0c060e06040b161d2106 65
    0x3403d121507a801502503119100c0e8852201181e03000c50010010405251000305400b80c0301c4034109804560b50311046404820350b14141c070303030390b07921b14805010b142c041c407a1010351301083e030f0f405c4403840030340c0c5014004185c00f0b080c40c8821000002e5a40e0029011411500a1030f807003a0200f1090400b440040b10030781050041c0b102d400c1000341c0d074101da4480043c2042c4110b41c490014504c0070444000c0c4a0306201d200f00489070b90701d0600c036503000140180030751507400c890406241c505c0100c0031034a80c5052407051101e8181850600d919200d81c50b60b840d84425240084c0c2e607101e10303868174503040389800f00109401000354a032071080785007222110300610a840c29039405001d4a5107607001c44540c0029500b81c64081a01020785c2014140104000c0714003076045e0601c040030310180d0301c0d0300c802d88501c4802d00001d13070008410441001300f035002d665003040d0220440c407030016490700054040e84059030481d0403084021500d544c66500c0100450022654103003400e54000c0c10201d0035503074003055 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 382366744 1250 382365494 382365527
    0xe0f010e07081f0b0a03021003050624030402060a092711040803090f0402160b0615030702101a0d03030c02010e0610030f021519030b09071e1e 63
    0x54400050b84180050004032003641850034401281c006984900100960070486411039034491300040941c0c0e400d1040850141942ca010030580f41a60030890035601080c0416000340c01102e100354075600e22401e0320f504c981c2c190f8426070340e6600b035542540c5811069102411810300c40389a80200c3d80c001d084000d2241c040001480030f04c01c20201d20000e03016501601400341d205000160300c0b031070090402d803500c0202410051400c0c0b0480070031406c114031071400b07a0350480071f40140403490602d0480e00c1d4002c854462902e0840c180300078001d4031521408807568509481d0000b680120484a404113200000140f100c1500b885038a0041d024044502243c8055403801f140c44460310004624a846010041400f0b880b16040d0343d100604001d4035142644c104c900c4a12084141100da001401c481400781c0307201032502802e800003025030704105c1040d030151f60000d0a0102503904040104002580800070803000d200c4038004035510880b050702004c1c00200380d5000b07040d03641c004521480f2076042 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 382367994 1250 382366744 382366753
    0x20703050a1b1e060e061f080304060906053a0f050103020105030c0a020f0102040f030b0a060506071124131409010603050c190503070e09060d060c030e0f010e 70
    0x40e1095407995802d414098800310b03c055001040081006111815034862940000c91403072610101e4504002212050b0303111401d200c1c504c0c81091900c0c2000b00401c1103c00452816091100003014080d59202d0401403150100d000742808000308024040782c9140010104010902050622800118404090301914000c2c82c2c0200d0f8415004042c1030b40d8040e1200ca20b55210040c400203260310000c031100850003034807101c00b28810700f070008000410030481580845070841c10a84921000500800c1205151100400542c4c5400341a01d81694101c1c08040e000d507101d8004c150f000340344129003141c0072500c5600903084240e50300900f03a1720358041c001c6001c031502c542e81061812008045998480d81c40da00421109200781c01c2039506c104145021400c0042038030707480c4101c1d076916a4040200b9000301c204848698442080f0b65801c10413580c095250401ca00801c0c0c1407201c0a10140c04261140c3d1300c8907101d0301070341001c3c038040d800100b10381e400509a00143d000300744500c01c07810f65019 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 382369244 1250 382367994 382368017
    0xc05030a021f0203131425030212060106020a0219050d0c08011b14030702010905070e070f0c030c20060d060e06040e030316120507050a094104020703050a 68
    0x101c610a4070311038418012160714080d41500d96503070441c0d00c20200c220703d124000901e6140d0501d050f47c403003641da1012203050128114410031060b00004c1c0407078503407948403000421640e40d0020b0420340b0690103450030851134032641110705016070150800c0e5000321941344d000040001c0c18042d0821108a40002c110300e001007400440510a01040c03480002e810261040c01071690200440d041402400001078480c2c15540e4a800c0c60680d9200c0c408a000300303030070404104e0b0003460400d00d00b80f00745001454035049640c0030706042800040940208bd01e481410303284042d1a070481e00b4480c0050050740c403001d0f00c015045c090301c4c0a00075050304905040c08187c4504082c0104205070007080c014500310b50f503c828900300c01d02c1c4103400600f0000c40e602c0d48030040d44644952030240103070340c0d5030b00e039661522140603005507460350000d4850502c00c5000303840107807000703180c0c0c501e5044201d0b406042a000b01c20f11808101210b00183c0c454400100030742055080001040b071994182c131244c82150 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 382370494 1250 382369244 382369303
    0x10210021b07090b030c0418020904030512070801120308100509010f0503151e0903041e0e06030706050f0c0c030f07060f050702090601080406180c05130213050405070c05030a02 78
    0x1300303000e03c0a505680810320300d004501c3c29401c1040c039450b5040701041341d03451540024901030000d42d000d40c04104001400f40800c00130310026980f00d515802d1412181d45498403c01441e020000c0203020401c1d1440030a8507030244129281c0108002012040036507140e500480ca80c1040348a52407003840b4000e504000141220716451140c118408492002d05032900b0030180514001c08a2880703010411000c120081c5401e0441006208d170448200b030281003002c00c8000c0300000e407a15109502822081040a41c014102c807042e124403820142c8614003940014508071503459001c1d41030050b0403020450200024066088480d59600d403449104070003000e965a02c950203000c2d40250b003900000300b455014a03405a0441d110341400101000f92811021720b00f074000108a0b00050760840c10070652905211405664110f01030443c582844041c00c200640003038800c180c02241c9410025841d00d006850503079074a50008240c940d12060703184002e46440c490301e1030072040f04942403406c1c900d4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 382371744 1250 382370494 382370501
    0x9060e13030918270b0406150b040306020a0e060c121303080c0a02010801080f1c05070c080601051903120c29011a0c1506010210021b0709 61
    0x1104490190412600c0d0356106004149111205a007482088030002030702c940d291403001ca24800801c1c001801040340c2c85038200d6032500c0d054054005880040800201d00074030416600035502c44030016401118081c2500504280d62016600d400045400014883c00da001040b40c03521503960b140c50a032169007082801d00030506200c0056010100c1d000c000c1000800500440e481500c0307000d05107559540703098455000040707485403600549803031021960416051350140031ba0030041c0c280f007188148180c0e0303903042c9400303450000030748602082007945c028003c4450594000100356205501e415202d5075648007845054015400c403681410032030500c05011040d02da109110100030030b0110000c41c2e0340081c20320191501c0955401d12021a00078042000c56001d44d000307426182c0d89840c040b086407503812080f07003000c04410809040380320008a60302e46081882c0c035018406849203030040789014041d02d2805885803000075030380d42003100280b151220002c00e004407148107072114400000d6 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 382372994 1250 382371744 382371749
    0x518190c09110d020703090902071a0a06180504110904030507110609010c0b0907090c09080c0a380307080f091506041e090605011806080a060504020f030a050d090906 73
    0x410303401e0010080300b90f40c035002030803103a009140c03a0884c0c9888154403401c0b644110300480300914200048207212401c00c0da4540e0100c00408100001c5161001ca8803084440172120840c0c10768501c0001c04004241c0d121250310600904031321303002d181030700c2d01038600d07800305a064411030743c201100120351030314404803100b40c101a0b44203610841d0350350315a01100c0303001d00b021400d8043c0304c4010803c0c451a205d201e800d5034090f6213056019207842101c50400e110429070300e0091403d10410300003c171419102c50107411440c0e28001407000742101d040210a140300c00d102900d84000180011903a0081c0010300038191003402841c180c440c6d00450b0303556840049804000b1343c046001442500c1d0a601c1a6500051180c040b4a00317035025000d001220441c140460b001e5568400605c0201c1642460104024403810b04020a5040c40c04c042c0d40c616071000010811911040010219241c50210680b841000ba080781c104612518190703496540d40300a40d4000740d180c040005201d007036401090304 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 382374100 1106 382372994 382373021
    0xf0d1410110403020303040e0c04030b0a060501140909040b07050c2a0319020411040302030105071d040b0d0b040201170a0c140705060a0518190c09 65
    0x100e40c803510866150388410b10040c001610004112015544003266540d10b50b90b50f40c000d600c4500c03a6810003402441c00d54207000204455400c1501a90801d8031800c1105080760030303806c254000c6408060f072000c1204040b5000c6a14920b10343d802058a190440c50694558030661510a84a45049050f44400302414103e60703c0690181c011100b01c0141c10900f0202d5203610302d81c00c000001078400d640d51080e07400002082401c403001554041c3c0203211a140504024041c0c442c004004140180b800102d01c01c9841c0a216440b07015078014242035101d8000e41700c4460b0b01c40010002ca0502880f003010030b204825120322184503102c000e1700465807680100000b05032801442c040d8040c09000d000c404000359001c985aa8066665140000e0b541d540c8000e08003003080c0c950501c46103002e00d480240d0400c0a100040c10854014500b441d00c031a0384101d8072040321113003580001e = true := by decide +kernel

theorem cover : BRFrame.Cov 382194244 382374100 := by
  have h0 := BRFrame.cov_init 382194244
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 382194244 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 382194244 ≤ n) (h2 : n < 382374100) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
