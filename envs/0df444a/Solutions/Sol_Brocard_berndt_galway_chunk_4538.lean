-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4538
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:56:22.864948+00:00
-- url     : https://prove2.me/submissions/23ffbebc-66bc-46da-88e4-4844872e73d1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 816007194 ≤ n < 816187050 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 816008444 1250 816007194 816007201
    0x1020325060903020c0102070603020414040504050f03120f091f024b030108030403030807030e011a04050702071a09040b04020f040302100503010608160e0910091116030305 76
    0x1403000c0014401908600c0512500d2014140650340b1050001e0590062140c6400000c40d14460320a441c103407000040c00e848100c0c08d200c104009440040c000f0f40b918051805001c038010400c10050840080401030720100e0310b0310040c0900b4004004005180d9a000103003103090031510000250641000260010307150502040c0144180782107031210b03907d450080c1034401c0040b1003120045212140e010061011a040c280141000e000c01c0c400c044103644180003d0000901a429260703000140d4640010803800d51204203094a032007003044440c0070001c20004105050502445e17910054074001849a68070303200942d00014202260380f0707032000d804a6800103968864101c607000300002801035440d8020016401d915506c1840308074400c1da032a0440c80c8855001d241070b40c1c1203801640f2980002d40d05d10150005d0454502d43c1d03c0100320241c130a000c050741d1a40521402003503081d52031441c190400300c01e10119010404154072030502440b07200305c0340080e1103003441625818503005c11580c4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 816009694 1250 816008444 816008497
    0x7081803091e03071e03020103110c0601030803270715180b0d06120b040f08042409171f060512030a09060503010b0315060d0c05030412020705010203 66
    0x81d03524841d404124481184044100420b01190300320045041d98850b0f80d4910040d6154a10450248202d40100308104051360107680646050f07161030007080c0c9002c10b0f9002650030400260400ca88540c0040180000b19034024904a5180001c1102e200070b40b2652240c40d640700910304c521300400e641058440c5056105103800000c9011004c00741e00c1d815100e0082c44072a8110710344107001e00c0c3c42c00720002203075600321150164580d00705004640c603482e141c071441102405010161412345041000252102d1040402e25240300d4030300d50840c075101c0c1002c0007040c0c481294064105080001d0106451610110f00e0201802e0b1a2008140350389400090402509844d84015400380800c403001c404100e0210040ca0030722100d6450703445081d224101030791540401e00403000446801c1c000200000c0d8038550700c078210000144030f0782c2448010407244041e5100200e5000010b1404000e02c000c0002c03805c440c156190081c005000300c141000c1c0001d64900030601c0d05402075610300b40441d1003c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 816010944 1250 816009694 816009697
    0x30a0f020d08270f0709051506120a0f1401030b04020a080304050a0513061d091216030e010216170f0601050d080d060b0a090e0a060609060302070206160f030f050307081803 76
    0x44444c0251071120f90354040800003008102c42c4a4010458854020038618203401100c1e5005440201c00e0682c0d1150342c20389004180c1c14420a0020707690320a015482101c2d000c0c1c0d41d000314030800c912451490b052041c0401c41840d0351043e102940280020b005540d076003015402629800d64000d001a000300082030080c0ca171540c0098108450302b01140404a01040c0252241c2006070440e01816a61060511a0300c1803440088000a00804d0701c000039104500003103012405104485e002d10b9516494158050305610802e886d006c00408843c0550050141c10b001384041d4000e01455031404010480c1c2e21a151001484c4840c001071000c0c0c0c01003107500c00f802134001101c0b09038980408a102410586850207003040188a2500103001c0030000d0241c001502d02c541e0340c0750522403902c40164040d40046a00701d82c03141c02807007140d4020b500c4d2500000260302441954500604070304000d005210403ea03110200002042081901508204080c4c0c01c0240303074040c4554400751000c01801c6 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 816012194 1250 816010944 816010963
    0xe0a0803011512021810170711011d100b0405010b09010c05120c030a030b0409020d06020f09091003030801300204020c01020c0609070b0720030c03030a0f020d0827 72
    0x81910100320311070a10890503281c80503d405540001e02000091025100610146614100054810b0009862511880003189d41d0042c1a0000c10080068801d24040012140460a06502c900c503941c8003941c881c000c050b0b01c0401902c08211550522003404c07801d00c265003480c0d051000c0c504900c020070001704a863350100fa480000c5485115104059840e5800880b540d40000d0500d80c1c0044180381910a042c070050b8028906c0600110598480001c0e4220300e010a512900510205905844000d0040e216280c1403030806080c60448c6405845040d040e00150000c548040c4080c2c00c0da0400c00b92004e0710440501403550401d10752000a007e4410780403a107255500200b03080140c0000060000d004100e40c0c01039850007a20741000c240b4600440d4400740c004801132489100555442d00303241c3e2030001c09000e4920360240b040204c1d00e180d00070050880021942c220064134540d05211240960240c0c0c50320421900b82405c0070030700e075030758860f01c8030105c20040240c80b98601c00b0000d1084 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 816013444 1250 816012194 816012227
    0x81b0f03070e06040f11070b3303070609060f030222230102012007061d0a1e1106090103090c08010c021221190207060c030e0a08030115 60
    0x4a00e0310b402e00e0107203485042e03841e03a00503400e00d10b00c00151101d80c0106451448078040441c20881d841d01ca0010100700501543c0000c00c0d400e66120700e00c05442130090200e40d842010f82c203280e003104140341ca0200103501500800c112000184002a400221200340c11064075000d600c9192094a140380b2144550440807036543c45034000801c4c1c04100710007103d00903640c4d4018509107000005a099848860b0001004941d52058075900301d02c49001e01400d81c05000002003104941c03003022581c042100200d1031550011060707034100050a60040300c8c3c091111440380300c1e405190b4803045201400c0344403910940010844001c2a44281d11180d0419001249098160303070b550207039402040300d00320810040c012849140189415001212200302088141c1c1800003241d8004200c0e065019100524400c20010160784020f95400640401c0d8010000001c041d001e5120140842c0ca1b101300008403a0413048613200804e1181042c3c0c1d044800501d66000d50395503c0381c080b03602550a40d080b04 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 816014694 1250 816013444 816013453
    0x5030a030f0908101b090b0d0e0c090708040c1a070201051b010603080a02070f03021503040203030f07031e080910020a0309020d06091e0f030e150c0a02010810081b0f03 74
    0x20000f101940040e40c1703282000320740100c90301c07040c0d00850f6480c00d14002e881ca001420001309896800c55031180c0c0c00842510241d4110705041c80016107805030948203900000d082d00c05000502c42e881090b40b00810000c030325001d0030110b40100741000e02074108007a040c002e000c10940c501c0003c044404000c00c06071402080440d45915140803540c00c09080f000040c40b8084000c500035114405000903241c0080c0002220104610b204000d0b0340000c208980500061003a914104001005001a984aa250311021b40f16208261080846822810041020f881c081c800c01002c00f26030741d0703005e138411400981e132043c51500a50107051604002904030340408003400900c0300f26448640c0e01c9105101118400064807268059001801c401502100b20b002e481d2000a0082c00d1300010b001d4058041c103480c1d0010442c6100c80d400c5020104101d80021844a046603803058201d54880c0c228100c10401a0518583c0e030b0b940c032700e500405022402400da240d94140d940f03401c41c003a07100b0020105e4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 816015944 1250 816014694 816014713
    0x501081f120f12020a150e07050f06091816030c080a0f0b0a030507030b07021c2105040b250f1407050d020f06060103020f071217070f1805030a030f0908 67
    0x1c1d95040041001c6d24115040501d010b641011801055a20081c80340100005800c000402104030400d181c05a8420300c00c000c2c5602e580c0714a0040c0b40c06031903220301a00f5a15003044102281140171170000c04052a181107643d115401040c0030340c01520b40440002c103102903008900052410303c1403a544100e440600004000c0c1c002406016644280c815001544500702c01307030795a00000c0c0080790452506012001d4051203104400d8400c48240e4a1501d8050282c804204855050350f003603600d0341d0500204200c02140e8030040074403440c4560f04010401507032340300405c51404c1c802c880082003030384559010001e1a103002e5401150304402036030748031081795602a607039403c02030009500d40201e40018105601900c00d4503400c60320005003a241905517900d44017602c03210001e0710706120b040300b9400a0815480d201d02e10070252900c481042c0000c02d94050807121406000c082c2d0300042e070030140607079200402c1700c02e074080d40b504019020480c94141a1540c0c074240d088031010344070f40b0400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 816017194 1250 816015944 816015947
    0x608030f0c01061707050121050412020f0a08040909060906050a020a180b0a03020901111b030c0d0203070b1605010203040606030b060910060f0311030406060501081f120f12 76
    0xc00c103a1101d100200700c8a913407919007401d4a01c0c010341031089608803440410a81d4003401107600c2c030b03859440c5804000c0281c500b0510403288156020784034601d4401e0310820103a0100101d80880e22100b0040c0751142030f0350396404062003503002c1d04c1ca1591300e4204a00c100112500300704000c55001c0410300c4a4902420f55000071342040041000107200b404c030480c804404007074004d06031030b42c0781e4200345002d0028009402941c04400303c04d040003d6000d070b1518044d010700648000700051100b20600344100d44c105468100b00c4164240300383e404000d04001a5000680729049a04070150a5154449103480b08014560500003a04035400042040b007041a10391040c8140e0344280300004481d200d80040c024000c0301202d60300d1a0845d0044240000d9000700141040703101240780c04100c14200300d408000d140c10544084a5a0fa19a01c041c003ca603000b8500c0790340680c0000c100028070f450246800e480040740e01c11007034210f0f0740c04010000c0c04100348142090ba81c000300c3d402003518a10701e0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 816018444 1250 816017194 816017197
    0x3140a0b041a010b03040b060d0f0b1303090f1212020c1809060f040f0b0603031e031602160e0c090a0b0a0e12070b0c0f011b091401080403120608030f 66
    0x50b81242640300701c00032680c1140e440940e8003c40d0424580c000c903543d00003e07c0309100405100350b070504850a00765000a0010f4003151080402c280d68402c011031501d8064451180c0741c00030b011081c010300003401240d28030f2169000842d00642c80304241016031105a04000e9400a26908440130300e103182540071070b507140140a15400b000302d80030350b99100388800010106503402014000d01901c03030000f00d14080c9005410500040c00e40c0e02d0959250034000c0300421300404502143c102108001d05500780c405041c585c008640041c10013100444424101c0d91054041c50301307503041e41c070045044100f440003907540c0711001426594400c4c5c2c803400034611039040803030410005009008044114108041c0c404c100208403c014644c1505201c4e0940103904200441003003442180b1307040345010000d000b8060340c040402c44c005040d50354140c000746440c10302c0d0004007281000800320318559911005003940103405207407000c2c070b000c60302c0c42d40c90107811150b00c00b030044e1001140303901e0b01490010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 816019694 1250 816018444 816018473
    0x50108070608070905010804020d02031203071206050a0e0103120e03150103110a051522030f1205070302030d0e031209060a0e120901030b0607170d1a030703140a0b04 73
    0x2154640d0b95995080100c80c40d8589000b491300080103c000b02d00181801445030030010b01c0113007640c2d40a00800000c40c080c0c0c200700ca09000154003041901603400083c0f0510014000c280c0d100301c0d5280c202109040b44403010310008040200e00c480c1a51503520130000504a46402820350309400070064404a08000071301080d1542009024590001d03c0c004803a9002c030350002d4811004400c0e0a1844007184d040504241421141c4040301c4a881c0404207201010798070601034603c1105450500c003101c0180325030908144002004003001080d0000151010105209030101d101e00e400d02e046420740c0140320000c1d6004000e0014001845400302e020351180304074440400051480f10070b860703130754400e0980f42448460208503d122a501c00d420010403440041d0145140010700c1c0d848018074120740300c0202c0060030200350300c140340c0c09500600c2031103d02104034035103c1c0354401c0065220807007440000e000304040708049044030414089203c1c4203400000c201c40304d15007410401e10688195 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 816020944 1250 816019694 816019697
    0xe0d050a050d0e1f030209030703020a1203030c050f091e040c1706040902010c08030c2a0d03020403030e091803161a070c030302030a0615031a0103060b1215040501080706 75
    0x100c00404a0b428181c1144c0d8000382001c001d0402e244404a041c3c0095000310140b9425005103540400035845080d20b040040c4000111501502c805040003800c8400c0c08400e5010000c04011101c07907015443c003070380d80b1010100d1340b541c0c004004058a101c40354103664040d400904264240705690b42004a0304540328a40390240995a1014104011115030200c005e001c9480c200021000c15102d4014590141050300500d14002081100e60074210f08a01c0c00402c150000c0491210714809110166100c1c0644c2410350400e82143d80c060000404000411b020f0300c40380c1c1c00a1746038003000181e50495101c42050740c8d50b842126440100281d040c880c25941703100f090302a2400e030000211050f1140310705940700f111001c9250b03403c81c0650f10151505800584070040490701803080b480c035000c2240c054400203400d4405a410060b41460031114606041c50480304000001c2e5400c01ca0761090301c4c095241c0d031103642e0f03500b41340c40c0307480d10240e007540051404001061010780041e03801c05507080c070f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 816022194 1250 816020944 816020957
    0x90607080606040b07060f0f1d07062609010b0a090603110603071b1a010609090506030d0f03021b0109080325090302040b18040b100b030402030d0e0d050a050d 70
    0xc803010301000f4400c5200c0d562484108002880c0411180c2c1e1080212601041c000310f0014030703844820003910540403022214046844100520007c20016003008150604060403c50401d00c00c0390141d401640540f643c16181c0300c00200a041c007944000300c1060024102041d03a5182d81ca00e200406407804100e41070740700d1314510300e2186051001c1d684107410a9480c803285000d01c819042c0c02034440d85080700c107034500c480c843e40b80c1030100703c000f40603000660358589002c5c0350045c02c10580310050711444c001d4011246100c1001c1d070080308100c010065040c0540c0d203580400c40405960702510300c01240b0752811000a04100703c0800460054031a440020b20034180041d001020201c0c405401e80451045602040117092036007040e200f01400030032120859461010b0f00c0c15a8034111800ca8071502d8071010403018a50350000440070303000007034a1504518103030740030940d0b541506180c03405220311110004242d5a600c80c40c024060750043c04c0e030740c05001501d8401e540e00c80d94021840415070 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 816023444 1250 816022194 816022201
    0x10b06070b060f060f120f010b0702010207051e0a150e010801270905060a090c08070b03010e150d050307053c010e0f030909130305040315090b09060708 67
    0x1412019505001d810401a0000740c642d04108840c0d5507800003a160004c0040c48904080c2a0000203070043d69210700d22030103e8584181c8080c0301040c140c009005180052080380302507680040c0c58000d03130324103458204a02000c880c04c08000702101c121954005c0d0195800304042442524100034130607503481c0d103042c4201010045d5240c002c240240200454031590240c40d840d407801e10a40c4122501d100042c694440e9110030341450801c844980703c903510703110418100041002800024200b0314090036015040c12211001c511040c400c140342403c006c408503101d0041d041881c458038100070021128000b1a1038281d480e80c000c00d07400d0ba1140111940c102405000c0d48a0b42c4500d101410740410030104070103408209040c0c110742007940c1d96101005805504e0400500d03000800420084d0340b40c0c0480d804010403924000d00d0310f070ac03101d83c00c0301b81c50001e41c1190a90302682c2e4080802008540c840c03012000130f1041c0007000c5c0203800e600c01446450390000c14014041c072403d607034a000954 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 816024694 1250 816023444 816023449
    0xc020a0b0403020d030509010c02060309060702121306050304080910090918080301230907090e151c110a0e0103052407050a1e0906021006050607030e0607020909010e010b 75
    0x81c5100c0603400855449164002902c5a8000c164010050415142000303440e00801c0050300121042c680f154072002c14000c24035010820f46983c1440c4514132480c03da4100d060300c0000300f40d0311802d001d00002002050400c0b05c00d00c20307a001514060655424403840e060010005c502070701c80c1c44803507480c04151403118071035000c0740d41d081384d00042428078513413808802d510540400d00001170f40722a42c1c0f03000c0355a80c1d103d0010a000d102155181503205050100c04006180c0140030225207002d0340301c01c0403040d1034040864507070300d2240b4280c543c40c4002d410302418111078045000c0c2e02c15800007002c5290156100c91074144c034003910483d44005c0c1515080034a2000204c0607031308081c52000000c900c0c6105100403c1c00342c400385400400780b40138104008440c0c11407411030011487c10360301805016410001003008003041c900910600e0b25000c003164180c480ea45001e8108503200b402090729407207070070884a0130355000e02106801e2410a510b0781c024901200d44d00303000d500f80740c801416072 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 816025944 1250 816024694 816024697
    0x1b080a020a050d02011e08011e03121b050d12060801150902090a0e09010c02210d09240f0c0e01050f030402030f0a080a0e0d1a060111010c0c020a0b 65
    0xa95018024404941c01c1070204840329030101c0b412810000d0a034055840740307100d80301007001841c140d00c895007036505040c951f00d50b560103031600d480e0000e03481c1d0042021800003030300001d100c000c60810300c0105400b400485a50240080003414072300c81e003a4484036141d40145c0301107501c00c1e003240c00c002c04c50f102c1890609131401044000c81c07848014000740300500541c0d005000c030b400020682504950b68591118401004031002c1c5126595500150130054040c0b0003907200b601c004031900494000f40ba02a9903138002d5040307000c400342da2144a0020080001650004602c128851240300300ca0f1411600203000341c0b0445c240310718102071101c109a40505000303114108140c45150500102008005240e000104180d0341342c03150501e40302040ba002c1c095440380318001d500f038907074a420303840015181400b11040b850052206400c0080868242141038110181d4440015996140e41004a400c0d40300200d40a241c0d500e40040404210b070407a411248251007601e802c503800e42d44002007001e5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 816027194 1250 816025944 816025963
    0x506010f1a1206010e040f140f16051309240806160e0409081b0f033402030f010e070b0a0e0d0503040905040b06041404030e041802030a1b08 62
    0x1d00e5424482c4001c0d00d0100e600142d40b111040c034003031880035030a03000581a91965a980c0c4145641d0300342e810240f0b450052900e41c803905c11300050f003283c02d2140d0b01e200300314006007000040000214005140306000100000203006003d0141305000075003d000c501b0300c144a0b051000d10300c100e03000190800c0d010413042c0c81051401c00f0144c0300800f86005640d00032140422940c816135540d5160005582c0320040d084c028501c0c400d080300c0c0481110080d28180e420050441d180e0700c1440405110400300c1340d050714a900307214011800d01e0401e0b116101e4905030b80c0700203506015548440710805415408514884280c8046804c010740c0c40620721500d100384c41c56400010444002e600303c5040c803582180005100340e085030700e03003547c441c541422540c0550303044504c040c00000f070200c14a0705028110192056803109a2542041e65010b0188103c0c8076806004989458901600b5000e5910356030865402405540924003245051150425400412070025149000210b400c40c00026445003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 816028444 1250 816027194 816027239
    0x121205040215090303040f0605190503040b04020d140a0302061005040b06031b0c0304080d030f0203101401020304090e1005160f0815040903021609090503031605070804030506010f 79
    0xd00328030500070b200c0e00d80c480c191107509032000f00b200041d0000c080390294001d07c01c60703450340e4840c40841c401c410590400f00c41c40041100600901012400040c01140c103c0d904540920202c90b1a01d08082030104104201c0d00034001c1415400038140c001c18168420003504500e103400390341391b40400c411103405645180d00902d06100089508504040c801071300d003412460242003966081100d072030755016401c005403035080310408074041c9030180280c0410201e400001d6085240464000c0a006120f10a48808000002c0e0429150740288111005412108014405000c1402030a50395030050030002d804989010000f82003007640703070106000c0d0b0351036a80395514003c100304101c507161f0014040062880c0320860f05103180e5182d10a01c0260751198001d0032252a64030b18207201c02130a98040e1850b10709062070760300016800f00440754009080c1440f82041c800d50502142c02c1d00800c10300800c1d101c00010702006000001840c141210140342d1151319003a255521140140c1c3c04030401d0740d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 816029694 1250 816028444 816028459
    0x30507060b010c0b0405030901140a020613022418010c050d08060109050d0f06051008030d181b030b06040b01050a0e030f100b150f040b03070e0301091212050402 71
    0x140012001d0304058141c0405152400980400b038403011a20401510100c62035400000c00314a5942c204855102c40306441d20418101560722002a45844d0004c200220700d11080045108540d10308001500e1001500720015072800c580030902c625a1107501001100190811030404070340c0302d4815480794587c1f000c00740244501e0401e080d40d09101c050311003414042010408119600c0f019548503819008504502c0c550a031030800c5011910f011702440c00c00840c1c0310082c00803040c00000c07100e020b00c480000040900f90740c0b24555842c0261080107150300400d0010407201069603150105a07070007021040e00a4590704104001c8440302400140410b0040c0100800e8078010885104000e80c0501a1480d4078003d80a107814801d500c07103291500b81d42c03a00036032003c1c1003003001200034054840f21a481c0041c40400140d85000398811121014400400910010704c101e000300c0c40440060024080a211403800d00040440403600100003140012001104000d6002c0c40e4015a009040c02c0b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 816030944 1250 816029694 816029707
    0x10e0c03121c05040b151005160c0806010609240c0b090c0d030201060603060e0123010212070b0403080f060d0210141b0f15060105030406062408090a0305 68
    0xc50868208150b248890000d01c02c032041c80701014010644074070b200d90114041445c00400c106101844421038600485451307495010701030701700045401d903110510610982c0d018528000648807100c0c0c00900b0113000b2003000190301500035071080c058424a0285007804490403500f5095200800003100004c0d02c0b650010000c01c2c000304250343c00c000c0c003005894000050382e002c941010b01030002100142e5407801c0400030281d051044602500411035051829490102504000151021200032401c4003854440107607000308100da1040030440032558450507941000c000c11072049509038041210b5000250342c0e206800c00c5e0318800c1500800e1150416602c0d000c0c00381c00c101c50001d40c410311440921203084030650b0409810303847c10341c429152340020b940a0030750600411700d40e41151548400b000c41e00400c000c1c070500d50320400038600607880e690396003004005042c10364030186d0b007d00ba180c20342880850304126001c0014682d02c98000c1604c9101d01c1d1a038401046a016002910a0001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 816032194 1250 816030944 816030973
    0x80a23031c180f0f0204050702011a060c070806040c03060b0a150f05090613050a1508070810032a08160e1e091b09101e03060c090305010e0c03 63
    0x250098001e4a102c03404110602c0d610340760000c0c80d07500f0640b60303035040d00002e5003145424040c4a5001c0050302c0203000421280c0f4000b072802041c1074009124003008503821612040402c44203000b09200c1044070f0b594201801d040f115100f00340002d5808500300f00075040c3d1401d03d81c9440d012034419158140c1410310f15641154030342c241d00702c50002c04c042040f42c0c003181d9a580c8054000d282c84121420f545603d04400c0001c1c03a501d0fa800b01c0a0070f4aa00700640625030869a4150b000b440350401480c243e50b5050305e6000c3c85840c1c0c0000b0191416410741200f100400856200c8060203400c03004846912016855681c40e11880a03e807400202882071051a41080c80c854000c0d008001c83c00001d40c036101c064220300c0c003c480d41c2d00a03512000840000481d03600504000141c01e48004510b41001d0311100300035405e9010310100c03854201801d180c825030700c81c5844021600240104808001004020500040c51105607015805c0101d201c0510601140507032240703200400074010910350a06 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 816033444 1250 816032194 816032201
    0x403090b0c0114070908060105040c14030a090203150105190305060c0a02030f0f121008070504051302041a0a0614160525030b0f0f04140106080a23031c 67
    0x41ca040655260f01c2400c00021110204500800c3c940c0c8441c03102c0d071309121159141a20590045101e81e04142132144002d422246d191445103401e4002d50307883d95001a140c02914030550001e4040c82411800a008030a02d20024160751045840c050742190301c24501251b0141e502000d0525001000403449001122004000022090040c0d905046070990038140c0340e0005840b01d0721540b80040d0b003840040350341c9030780b07a480340032111a28145420020030b1030383c900150090501072903403003020030300e190f000f0000540c0003640144103000c08404150141c00860307512208600031240c0344404200107010b400c400d19500d014081c80c0c0c2c20f104020091040d43c19042c4030640340c9000e40004684032042c00ba4050082c0b924003982c14201c5031030b624000c2203031100100700c0c0c000725401c8070905c00510b04000e680e46d003040d00240c2c0e02001101400c8420b0040c103559200040714814649068104020158980c1900001c42d411014100003404402d440b4814401e82c6402030621100f43c91140e0340715030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 816034694 1250 816033444 816033457
    0x50d0819201b1903081201030c0510122705280f0b040206130609050f04060501020312150a08060105031c021f140f04060c02010b012319050706140403090b 68
    0x60700000c60f690700d88680c0703441c0e4070034041029004c1c109001481440120f0800e200184801d031102030114003100001030440c0412000300503e540c0702c442180c00d1103100c004a00d400d604080e61020340400901d0219038076200c0c142800350440c02c807402c0305005089545a0843e1a401c0200d4000c0400d080e9a03070805000003c00803030340000700303009010036a10194440000303000107480e1004040e00304003c002c0c003082d036901c00600c582d05003007003800726903400300c2980c0c04881442602049611200f40222800c0d080e103c9442e0003920b5814009401880001c1d030b607040360b10170f9040e2070490810011110328584400120360140e40040b0070200c0c2801c003204281e5011f1418180040e200d02880d2108000f10415280184004140410b020030b00c842480f40c0d64200e81039000800489040c400040d0211014410700c000298854400c100c000c0070340002c459407038401c00064030a44901c0d54000c0c103070350401c00c0107840301481c1000001c0340d1942d150445000b0703901500d50180340c5250080e00c001590101 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 816035944 1250 816034694 816034729
    0x40204050d141e071406090a09021b011109091815090c0607110f122a090a061d01031518060c090501020d0201050c04050d0819201b 58
    0x4458541c3d20030b8000c0e9260303144007003a00240a007186440c019106840361035801c203110712802c0003210b0380c5590f2801c004080310410000540c031588000090054030213000e55200e05035003840148640410941c0081100300380880d1a140181c03503400740641c001800d414010402e501482c940409444521072150340540b44004441855100c070f0041080c03608544000c0f90050f20100310100103140100750031020301019103c0303a660b580b81003421a43d403501119410300b21310b06209800c0713608038070305160850a60080e2020b071107400c100e039501c0000c1829114600c4516803901041d4121070212462034101c079001288003025118030245c0c0030003441c02c020a400010004604c1c007002030380b1409a00c0c0030001d43d0302c0e8041058130740800a03081446c0141d0f6142164508420000e010803c1005d840aa900c01e4400c808460740c5480c090202d840780c000400000190b8400c0762011503440b500342001c2000c04c0001d042d43c00b8641c9001940eaa02084001e0b40c0801044000405818003400c0a05142141d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 816037194 1250 816035944 816035953
    0x2040504021c23060708011e050301090b070311040305060f060f030a050c0f03150112080c060a090c15081503010216030201090209060f063c18040204050d14 69
    0x20405210a603480b078050444403a5850340302034040541c40a8a010402c02040291405160500e4000c2c44444140076808080003010a414403218602003594054400a0000c01103107840b070a00799036103030085600d0000030b410310500c00c3e01d41d586403064604881e401300041450343c48009410712400350052038039410001101d6405269907040050321417050003500603000c0d407a9401306004094070744169417070107917010307100c08609100e40300c0190341180c1c0480300f44030484580c1e00d864403030b603c508a8192a58481c0006002c40c0911070341c40815071500c40c41c01a414140d64908895501040c00182c0012800b0740002407110010b10120314007a03030300180018901403906862443c0508400000d41c010f03990340c1d60400440c1401c22a182c2c0040741160900030008440d0000380d124820001d80c03056403a94002c3c000000c401c03480c0c080465002c00c1c24200d84403201d03500301c5110364003c0d8080000300da400d0301d5002402c0c10144216026103501400b810402c152a40f24204c02501d55609000203204 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 816038444 1250 816037194 816037219
    0x409050c280b2d0c060703020306030318060d09030f0905030a0305030604020d060906080c01170405070512100603030c05060f01062015010e0105130203010503032a0f1e01090206070204050402 84
    0x70461003001c15901c0d014590307407a40004c521035850a07030018881814544100180440f035640001540d02d4501e0380b41031b8400701e544100208403076000e550b00f0a0305603414414004101034200c59407000315503d607912590703410780d14400c066690071140e02c00380124004002081d501d00b03050b0001e15000c008100041141c2c0e5848410740b00310f80480d0311424a64001d10810385056034405841c1007000d0b14820b400e8034600f4030ba280e10b626008a80f02c0c540c0718007203001c030304007012805000655a002c0840c4082009a940303050141500340307200c204407098000d010003d001c040e41a000e050682d00e803681d400f0032090003e07036180c408848414000c01148900005c2111001898080e0350281c0004501482c41d545020144040b02c0d1070800c00c40c0c12140144014049510000243c9248118101c2210842800500381d41041c03101c80315501d055000700744038080f0351000010050030f501c4140800008440c1100401030885a000c40020341c080f100b00910805443e00e03800503a040383c0020050a9140c4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 816039694 1250 816038444 816038497
    0x102270d050706050a030b011418011704030f0f0c05060403120204081b10020d050a0503220f03180e130602090d120206010f030b0a0c020c0409050c280b 67
    0x44680e02c20f0000540008020f030b03005925002c0c071441d0300d2082c00c045540304920f03514001c50703000703403c0e0006036201c05902180240e80324a140d008070395010b984260341810903007402414010141003200205200b00702c02000313140704400c8410295001000703040e254035030796802c441203071402a41031040b0341c00388030104803d1b105104803c4000580180d201404a1302010720843c0010480200e01755040440104e81e800d0f0088100e60b00000f0a00e0039640d00c5e5a0b1070310078074a048800781b425031a100e0000d0741c82c00704130001c10314032011802a201c0240100c148282ca4040c20034600949800c1400800420182900b44107440300542c803444000d0b0501c0d040f4000302e42c00e9a080b040070346900301c1c4540000032854051040350b02502282c4881c051580c00c54940d1841d40202070502c41d506603960340d100d01c1051003400090700b1007200038801d2191180f5800c100d980d9900350000c1600c502e0319100c10240003417090300c02070700e184045424a440d1380c0c605440d40c0f0741c40d0014485c0c1100e80d5140e800f1070003141e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 816040944 1250 816039694 816039703
    0x90403080414011d0d05210703020403060f09110f0f060705010207052e05070c03210618111824040b04060e010309080d09050a0812180102270d05 64
    0x2000d502103405040862803001d1381c0b805064074841340c14044200811407541d010341c24040c10052011481400d6511180c508400a110383e40c0003503c114a4000c4a400d074202c0b5421941d5024013a01d10090841d0341007040200d0140380f441d0003079100c0290314400d405410500b010740701ca1805000010305000e1941c580c0d40c140707032002180055910812600c2005c45d0089540b04000c410590f9041103e403405031070103031101d03440c2d150240a01980d0800e03d0a040070310594a00010560042400720942c1c51108982c002e11550980070700714180303400c81031005000c809035a690101d105012044080c0003080c80500851620b0548040a0b4440992010b04421005000a00c82607074095552481c0520007403030810b81c22141410075041842c4100407881181c1034130524a590301d800503020003140340907880e01d151018010682080071810320b0b480d641c5210304501c100700f003040c424642ca5802044900f01d02c0381c1c40c00e2030089614070200710604103c8040450120001070700c145280805a01d030a0300d0b0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 816042194 1250 816040944 816040961
    0x2415090f08070510020304120b131a01050301180203072d03080a0e01030c080a020a091a0702092a09011b06050406230412031808040812040509040308041401 69
    0x1c50348441410001c2c0d09081d003030010003248910146d4149400c3c00c0c1c0b070502200340090098600000a0017041c2800d1070075031152541030340301410084101100e200b10500c1d4001348a600d100b5417800002d05401803000e0050001140d000307004c0c0000500b80b081c202841d84c2e042d0044840703a24100d070a50800c071010120403028600610382591140c07907024004080b030400c000400e04050038402448021600040700c10b070440000103000d43c41c0c4e92010411a002006a407104840700d1008450140d1000074000a0482034001c0e5508055541c0d41400030a07015000e5800c1e085d2206040f00c1a045010741d000036006d50ba00501d0407029002340c1d1281403144d142500c00640d00259180240400c00083d0321500c5041c0b5490250414501100c0e031200c00c10b4100208003800f1403d90740340000c0014440e9015214889840b54040492100340c10b0000302c44d0002d0040d00308030711803206440d1041403040160750840e00020701c0d520241d604c6a60840c0c99030805003084500210704d4a0b602100c2c00300780200d000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 816043444 1250 816042194 816042209
    0xd0e0d050a080f0913180b040206220e0f06010f050d0603020d060509100e100b0f060301030c150804020604090209040f110d1d0703200910092415090f 66
    0x1201c10401040141054104404041c01ca10b40b0021546d007006620031122683c0c1c0000324803083c0c2d5643e0010481c00d10884111005035034441c002c84050081030350f08002070b40c2e0b80301c0b210b60740b50750760404189496400760340442c04079154051801680d0300c9100100144840306201203170301656580410080d0f0040c0c14110384030740d2268100b2900400c10000051415829030b018040c05910350852030302d8000e00c0007600c050a4464208180e6512030050100c06803002070450f594070f40e0740381000002c0442c180940264585035815540e0801d114412031401590002c00c1035140c54500039050000b503101142c61908552560034852940040b4400c0984106000380055612080e0761032a070b04031106a003c003000c0030320050101050403400a0201b0030b69a00210a680d01494100c114824581511600b58010700c010100807441101982c41c108a55254070280a0555184925031030307a000c40a01101c00c070b089036010404803800c2c60b0308020341c08483c1446200e440d11f485c980003000802c1d410182 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 816044694 1250 816043444 816043447
    0x20c07081225050f070e07030e0d050405130e101b080106080c031f140102070617010509071106090c090603030306031f0e0a050616050708031303170a06170d0e0d050a080f 75
    0x41c1f06a0117000703207180740400300c0203009040c403031940107001c03801203004190007510003090f010300d4005241d100d04108031440c400c444440e41c02c682d482024125a079092010080e6072140010118080d03200b042c1a0340440c0c80d420400d5030342401e01200ca400c0200540744010111703480c028030394000d0502c0009801c0100382080e03141002c1d000a031800400303038401020031190031051030041c0a48958181546c20407120003455803500700f1300311002080c01e0155012800303002c050088072680054042d0900341d09603040686039441408041e200d0000711001605900300740c100080c3d0303100030650256a415a03550004a018010000d5882e160301c4134011607142e80944113008060700c07089421781a03030449280c140c0c42d0140315038170b080720b40c08003a203141e846c03000d8081c00360105030080c40040712180000583c0380c018038000b24082c010701454424101c420120701c1200002e1007020540d2044200607407101011001108180200c02c0700f18442a030300d0b4001d1000290000f82c00100504900c0005e050700e9 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 816045944 1250 816044694 816044701
    0x50f061b0c1914060d0e16030605010509011230020303040519051b030c0d06050703050604020a020a02091b030f0115211e020c07081225050f070e 64
    0x441109080100c000311801c000604000754140f045840404060030b54580b510b030304a1409010282c002d980401940c0c0c021166650030202410720408100d03406001c0c18085a43d9600074440d400b4002e0080b110310701c0c07882c0c15010110317122003464084203041240351801d00e8160240c030f0100b0b00180650034010703000001031205101080040604c821500c0035080600d218964520780e8400074a0200700e40400d03001c20004541d942440703441065540640101c0b41100c075444e052000b40300403610940031920708008501141000d200fa5285900c04e40c0041c11081103d80810818440003000d40040780d141d074110130b410900c5000614021b03040001100081d50500b12590000320102d0000d0040200e8031100224071130407909582110703484010006000d1081089104140d102c82e803280325107500004811104000005115044a0100c030544001da14580c1c1c10189038820745682c0485881450710b9001009030364444050014480c078203c07100d215085c6904e03820410182d03c182c016140a2080 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 816047194 1250 816045944 816045949
    0x1080f060d0203330105100203070308150607060c08130c090f020c160305071703030c030a091407050f09100512190f150203190b120a0503030a180b01050f061b0c 71
    0x13041c0504011503c085c030034494440003e41c0ea00a83c20041d00f0881c40d000400c82c6010902d00703190313080d013015028507903c141c00c1c100303200602244099400080c07008000988070600103102d800c145a80700809a0026140610410203007843c2c07418000035503403c10940071010350401203075107001d44130310071403240920354240b0604100c2a5030115564102c3c620702c8049007c00402100d40c00184058082d0b00c82c0c54840d04e80c4010130500e0f100400d01c82c0640384244085c107000920300b0407510200c983c0c0000148400600c019510300f51074020482c9203d5100344094542200200c0c00900c00408071105907003424414025200101800e442c1642c1c1d4000301c10500c20b88000180790182400d80a51950504440700c20080c500010300712402c0d80c1d5000322524590360110034500304075040b41203815403007450900c251a0390007541c1c024885403a0100640343c100349641c0520f462500940050896031034502417082c540300c194500707a8080d2040100c1c0000c410000c1800d8100e1200341c00904021040009 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 816048444 1250 816047194 816047293
    0x10204140a060f0807080a0b1012050c0c0a0b070c24060e0402060706111306030f1d10020f0d0c0536010513030b2401080f060d0203 58
    0x10800c070f011608030351a401030101604101640b4000d01c0d5030765007040d000010241f90310f405074400042c02006c268203500c04000c4003204903001d0200959202c0c0038003170201d4810760000440d242c00c03522440011942a40400d60320000b5824007607034526641d0340e00342c00c051249007410321001041c0403940524009100721009011012020b100506160f0000b984601030010010045500d0b400c980d00004240001c3d694010165020548003035214036000e0040d180d03211008650034900003241000f12b0040301c0b20001c5115801c0501003031889332018102940c41140c9003c141401000a95125110340c400c1400100c00343c0e5034151505243c3d84c0b5854200300c11090040070341c22000500d0010100c0481c03c81d001002400c1082d900e06c1c01c0c0c50707504070100c0f1302c0d480506080040030400180022611040910f901000010810b0560700c00040d651404159250201e11044500040c81410102c41c0360381654002021994980302c000641030000300c2040800d080c0c0c016055401105020015 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 816049694 1250 816048444 816048449
    0x405102c0f07090905090f061302040e06010e0c0f13090c1b12030b010c020409032a0c0b0c031b07090f06031a0613050916080607080403050904020c010204140a 70
    0xc0441e19050140000b0051001e038000c0c560110399601c0801e90080c41000340c000c403051b6000640717000b0b2500c0024030b4004481c01c0e00c244d002d54141040391207608408110a03050302e107032110860003910348511003213141e04140381c101c10b49001002104544110245402c0c001d0012080100740c40340180e0000381800e1071210f5071035440c413403d11010009500c180c1d075501495281d01d0001540c06860004035103041d204400a034000c0d1610a00a0915503c52101002044144010200300c450010181d841000071031000d880e13100c5c00b0600f8400c103000c10000f40b20405485049a051146881c0412149044414109050307401904108200c2240e406100d0007040b00e2101007214901d5621070310703c00d803c045840c686414001d0001146552800e40496008084220030420341c038010f9540c42d80d0b441d40c034916205501c4a2840021410f00020340e20b8401c00e00390b5a00115600c0b240e0701030740d1941000031002c3d030250702840303241ca480c1000d2018000070446210340c0c4800c504803070244906c200464 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 816050944 1250 816049694 816049711
    0x10c0b13140c100315032102060c0703020a0b1506030703150503150c030406090f0503040515190c0c0b0a0804021c020303030114030c06121015020c0405102c 69
    0x50801c10307000ea640041c1584a0b000760304001c5000c5c50441d0840100b607440760002002044030944c043c0080c0030803401412001410b80881d0095210b5103144080c41c01080341c001d0042c0e000f0319600002903103c0c18416040854003d0701070a108500c00081c0c3c2a0304100e9950f40002e0b950078400601c100f98035001c0d0001e0030254040e0a051003401c4820040c800020409109010000301150801c00d1503031203901c4240c1c2201c110402403101b854004d4a80d8442c0c40360921501c1440a40303241305115038100c41203200c030303d240340d52a080040c4040c1e51041a5001c19140c0030041100081c2425840004040044480d541d0b0b01c81490b242c8100302c1e00d1045802c002d90014028418013005840010032641982d83c240b0320303600141781480000c0d103882e00c140b07802e5400541c04210142d40c10740201c0810b0050524043c0c0170324168841c0301d2544480c004a06c008d0042c0d00c072540b40c0b942820580d002981200200743e10410305502c540c44000c0301c0d1040c01c4802d10110400039002070005031507003100c1d00a8030f00c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 816052194 1250 816050944 816050953
    0x9090f03080609060607030e031e060109050105010306140d050f0714011803050d05131805180a021f05090a06050408070b0f0f0c160b0c0106080a0f0b06010c0b1314 72
    0x81404100031b40038800c40141881701165160125a800308101e0402c084117034044000e490308019031a894400a208040c0c000f0300340000450f0640c0a030107080b0030341d60105074401c05250142c08101e170261070000107440601409003038160031003080c001f50000d003501000005408600c00001409401044c80c0b0700c030341e0701c0420340600c0010030109a03000000081d02c0e00d2500c0307510420051002901d103900c1013441660709101143c0c40c0c0c0345034100c4c80c031903181c0c18812101c5003260b110302625802198002948003404881400c528425140801540d00203490720341c0c1407005650100e00030b0301c0305801910204030041410000003c0410401c03000d0302d40d144e42e441c03c1c110511a0240076000d1011440c40d201004110800c4020040003881880015034000e0010b59560701c01d82001c9500c030300300c500e000b9401d00902258048002406c00c2503070b030b400781d1000142c41d00c6480d071259194001e0314690401000341060000b0514110100340114100461180b1184080c81c002070000099043c01106401 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 816053444 1250 816052194 816052201
    0x4020702030c040e0f0307030201060905090309010801030209190f02030a111602060304060e01180c05030a11041107020a0b12060f1c0c0f17061f17010609090f03080609 74
    0x9011944202d40c0c0300907207020844a09126110b41040e08184030a1458400800c2d04014544e054020604803151076404000a861340751380d250b1070380308080f85240841c45010041006051040c100c0707911110721070750115076807404c902c0700c0190b800311106414415004001e04c1145409842048440f901d01840305183c100c0030044024400c007418800f81c425400440001c0902556401076400486a80300800c94501c8100724038034800b003006019217000e0746c0e06030089030f079050009210701280c0e0001c2c0b9280c1c0c20814201080007610082d070079406511001e00403000140c441e07006200140c0f91540315107884081c140d0f86030400d040c00a083d2441030100703415844094403150081665400c5c0311089074110540c0e41480031035140075500445001681c00800105142d880060345074100d03070038080c6e981e99100c0d601d07003131460001e4440301d00e1150488541008292244860005c22003000030001c115980e031090080100e4075840016565101d061000000301076203c061507912500c1103962210320304 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 816054694 1250 816053444 816053449
    0x3050408011505090a0509010b0607050a0312052e0b0f0304110d0c050d05011407020a05011508190c03080f0903010e01140703090303090803040c0303020d050a0c1e1a01050f04020702 80
    0x7040640f031860111b5a60340400d411040a4004804101025209966030101440c1190782c541c012601640040c01542c1c61038202d1905008150003190100c0303080580203038001c44000c0074070003042c0c000031900c0310b00300c000782c600455030282124103400901291245043e0074403008040d00030152901c10802034040d8400260401510820b966056841c0340c00c0b0380c41440c0190061682306480740740c5800c03000400c11450b5000a00b9103c0750320980091008103142e91806446210a009072403180e0022101512001f81d15200302d580c00740200004070700e01750b0f81e8540040503801b91001520443d030010f9502c0c16401c0c24020f280c2d4000030309c00208025000c12258209820300503101c2010944c03509203c0023030500c0398205030380036900801042d6890400b4600102294050704c0124058000d0521101030180900184c5401c022a525143c0c6031000590300c0f01d084035a100d80c540d8400c006049040046020506140c9191800014510065043c4002c00c00c104d10558002442103004001420058 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 816055944 1250 816054694 816054709
    0x1e090908030103060c0c1403090310060f03020919050c070614060f0f0607150209091e0601080415020c010906060b0a44061903020315150d03050408011505 68
    0x144d0f0403810000e45008111000c84682030700302005081860040800101d010003c0000c1c103003400308401b2100085859480202940c003188519110346a08074810130250402e02106a40100c8584881c81802400c0d90504225202681c00c040b02d0309001c240c0408200b0a0b10502d4808020032002456625205000509c89058040ea044c012504002440c1725a181d0724151a045944105480f00c0d500c940c2d6040b100941080003468810b05801d008500700160320003c45403069099001051a03079203440042d86c05090103032048074405008040f504e03c41c2c01501c0603012003400d0f5000400d0341d441504001084d02c0044d0082090702c00b040240c0c0c400150003c92000d42440c2d841c10229601ca051003030002c400228007a81d402c0e10003e04d90000c0940c035880c000500c45e04040f1124100340d41c580c2901c1120744c5d16400000e4246c1e20407040320b40c40f10290b240d03842c0c1c843c41c0a0316a504030700c98400810300ea03980703000d070403804694003040c2444840b0003800b8000c06440c0694100d51040c3c1b8000004401 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 816057194 1250 816055944 816055949
    0x1031b030f06080d03090b10060f080c04050a0b090a060e0f010e060c06070c0c12021509030106080f0a03020f1b0909280302060f091b03161e0909080301 67
    0x24540d07181088800c9980c650400070040c0f00070025149201d002001c09409440740003012151000040002561a56084144800e48031295525058621020410b03100640e000d40b8011129406000000703841d6154034601020f008410b078bc036625a1121420b0055241894001405020a103e412003007078981655940071a0000d00e080740d504224100403030100d114240d1072480e40c0c0a14020042040d0300b010707070740d800b030780c0f060b07810100321940d0310114a084640c90800950041c0302203440c80d881d0180c803010b0086803500400000d2403a0f40c0707400203490414116080e1555422081103c0103068050007400d0b600c14070340700540010206c0802c121040c20b420121503215203140408103141c0241000b256100d0f022441a40c40b46421004c0c4250444801e103200301c0c0188107844c002448090714605550150b034220340102550f1480010490403900c07803082c900d41522078a0300f894100c09004e030000006090b014060b200148030038038080c81901d500d400039004a410147c00c500000d0030502203030704 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 816058444 1250 816057194 816057197
    0x6031510030243140d0207081908030408071b080606100903170a02030d0c0203120705130e07020c030105190608031201062f160f0b03040f05030c030c0a050c01031b 72
    0x16201814a800e840b0400b86003440701e1a481140c05c0d400d0388540009400041c1c0303c440c801c5942888450300004104400020001d000c91020b00c040b400082115018021503446061021540590342510710401c100543c045241a80401c06110150030100f85002c031400c0740c3c0c0391102c549400c1d6200c403001d045001801c4c0903a10000030b240380c0e10f01c1c800c0c026119001803800d024130071300c921090003e64035040b1311208081c05e0138240115081034010021502500881c03841c42d41c0e6580382512244012000824080c15030080f01c50307045482e94288103091181c4d088601c04a0441809030161049a5407074002e50f00329403003080203000054078040c980381118024604441c1b007601ca0003400c000181450b0400059910031009401d0405d030100e000e142520b24484d40380c1003071f0303a510290f20414216100302c2020b403c0c200b02040100d0081c04042480c1e42c001c504580c07805a5074045c00740340d0340c401c1030701d18465000072018104102c4184014000e0000c00d1800340503403480c92000c1c0e0203180a4005940 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 816059694 1250 816058444 816058567
    0xb03030f03101d01050a090c0804021002070b0409091103070602060c07170703050309010f020906040b0c330a0b210a0b091e070f05060315100302 64
    0x1601d00d400d030002c0c00c01800320750405041411400c4000244041d0a000e40391040300c00704c2c00410303083c2041c8185404980706584202c0c2549694080c42441040c0349118400c40c0103480b8081030405a80c0b00400052021a500080b40002402c200b403c80c2450545203100790042c8808000c0300e9030000d0201d8004940448040c6c2e070b02039620f0008402484054000ca0b610f00104884080c50b4110000e10b104014060007801304c414160780c950101d101c2e103141c0660184c01480207107d044600b9010300004100329003190034028035049443d100000b054804059030100c000c591040e4401c010800c0c1c2c000908074400d1080b114180c0c0001c0110b250038454044036014100304c2c0c001e03070808002c14207051303820030140034160402e84507282d111241c0c0042c445184241c24031083c001c3d040000c2420850b47c0080d81d0360000ea0800c020408641e00203045a4a0100ca031249262580c0c1e8080129042c84410344005a0322302180c00303a00321780b0280038820300c02081d8a83d070440b400b402c21085501c100c007441e10b210 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 816060944 1250 816059694 816059701
    0x71d0c070b091f270302071e0e011e0806060a03080702010e1005041a120f0c0d02190e040516080a09051506010908070803040501080c09031504150b03030f03 69
    0x10ba152040c1d603070840030f001d0000d20a00103103001c3c940c45020042000c1010159040c880041000e041d890740701c001380144d00555040100803590050425400008856640150f5560201d907108000a07040400304400300300c03101040d0803901c0011001410007101410040c50310b00009440714400c0d00c00070f80f608800181c0c1d00b045a0dc0381e040031100510051984000740d40100d00103100d46c005001c2c018010740c0f255000403640481a06541031089600303d41852652508130342d81c4401c101130164803034040b0500590b0314a0302c60f8000b0b026245030085180d0945e4103659001490101203c822a000310703e0175051003111104d200c82454819603900b4020400c0d1280c1d0303440c0000700400d050107405409a001024610100513298600940099031280861a01c036050551075241a21604803147e104010800c095401a60b0700e5600c0344076002c805040805420100341007003590354018080e21441c0082000b00500381a40140ba015402030421025a110011a58034030030150710740f00c0020040000f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 816062194 1250 816060944 816060961
    0xb040e0d1e020606130e0105040c05040e2830020c01030507121109220b041e4101140a050f0a08030c070608060316120311010608071d0c070b 62
    0x1c06102e038000000c01c2310f8541800c2610180e44907002d901d100d1400c3c61a4082c85402c0068000d80c41c0c032981400c0c04140b040380980c0180c940c402601218800f0408421002041d8040e02c0301024030888601c070b0310b103c9c42502e002400c1c607648102c2c0c13906043c544000d0103000c1d50b005c0007c035000c0c1410385000898480240000d12030f0b00518040e10340c020350300b03003000304008080caa030010403141d150320074400014968100401c0da03800c5820700800e28010700f040d62030301505410444450305103180c0d001c087e00345215414105500140000708080341d001114040b409034100160040c4084107603901c844c02098009013644640d4031034a486140b18084a00d00396894031014001040c0f00800c59548000486455841e1000c910641000c540030000007171140c1000304502c01c2c440824110943d20710b0900c3d0518a003401d20500c10b0302044540325590412907424850b4101802070380c00185211440c1c01660268035807503091084281c16004d00380813843d14020f00751441a82d00540401d17903a51012030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 816063444 1250 816062194 816062201
    0x7090e07081512011e090f02190302130b031c050a18081e1b10051b010c02250e06010806030a05010f0605010306090e06070809010b040e0d1e02060613 66
    0x116550f0040c3e094401c0b41000f20150700c54400b0222454181240004a4000c20100d0301d14400250441112581c1d5500510b080703240c1040c005940d44000c87d01d0340d20785d00405c03804e100068888800c43c1e9100d1907817a451500304441040c102a59810482c50381c001c42c00104503010309624030081c0122800e45d031a1100a904000c405410755000b29100b07188403510702100c02000b8a031088003806580c0d030720018040c04051321280180050040f41400081c44e10869065000401c044001100305610341c5d00c0301028000e01c415047d0b658002e00e007215813518813030031034900403945411903038181c1410800410040c10311640582d090a10884176030b640808241480f84950001300b03954a0305040300c000506d5a8400070039141c00307036010400d454a40e8002c000716001c6810202040d0b03c00000101c419228607142580300e040b2000104c0c46010400104083e640b0b1800580600e4104000c03021b641544400801450b04d509a52100e0454100401944030440a8a41030258040c0d00018000072200e40 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 816064694 1250 816063444 816063481
    0x506030118061a01050f18041404050a0b060316030f02030304050a03080d060609140904060e012f120c2b0e010e1209042a050703030507090e0708 64
    0x22850303003501010301d000340007008803c0041160701207800403003030f0719440340d41995003045800c00001e1400000846105448450010640c0c1c880d0329030396141d1000c0e49145036540a1131190303005242014142c9401030705040020126802a405400c460410540c8d0929007000c40b074224401081000b581d0000c6411171050b608000e8200e4500c2400000304400d1000070441074502c07031401c1202c4ea4840008039461200c0740704005441c172801500b07140c4c0e46801c40b08260002e211302c01c002024100e05000c90300b0b56441d11408034440041802c1014001001c5001507410b21715030b00114075200714500c0210740c0c000b0117441000c10328004100305020444206221144100c0c024144a162030540411000f610f24080400041c3d400e00c00000c40a40000581000c5100c0e8000d48604085d600414800208118442807403200c03c202402c21201c4420071a951358009180d607544d40d85c42460802034103448024150f5410803002b090200130380f450604000d50001003a1511511584807d500c0015810030340b03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 816065944 1250 816064694 816064721
    0x18020f03011d0d0906020601060909020315040c0e01020c060c030f16050a1101020c03120a120b06030a020403021e0609010e010c0b10080d0806130c142106041e05060301 74
    0x1c6050302c02c091000240700d80f44540356035528000d6911100120f858013001c0c0b03d9a004221781c89001e0185000e01c0d00071710b03801211290002c500c00b41d62000a001e482c200c1004001240005035488015641030212100d4804103650091825102c3c40081d13980744203100001140c10400300d45c00d00c800c0700120303420b2109a0403101705d60105146041c110540c00000c1c03112400740c4101d9134030040600700031504401c4407e0140310749040154103a001d84100d40030030350a080299032105040b50980d00c0c440614000c106a0800688507400c500c1400b400c0b0f4001000c0140000c1134090400d03842d40e6035030850700700e01e02c2807804034405980407006a402e191540c000815048411003001107070310070907040104480d441c01c200c0d0010420208113642d0b001c415590283c00c03000c02d90101444c8030907500200b8101c1114640002d1980029120142d160071100c20340c00200406140080c0c3e80300c4c030b01030207504404100e4007086051f4444102c0c4a0110010031810103090306d42c400102d00da070f4294000041c3c084003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 816067194 1250 816065944 816065981
    0x70203070c0b13090903170c09192105030301030219030f05060403021e0705100215010603091505091f06122f01121509020a020c040c0318020f0301 65
    0x48901e10700c03503500460f04181c10126400c80000d1100258010005050740640759a4100045110701c25440304004064401c4402c2c1000200c283c2c0c2c443c800c05d902c4505060a459007401d0800301c100500c1c010196210381c0012680317a5200100320080200d82c11203604540c11250702800780910940d040c104e0f80040c011041c010050410301c10049001d40c441c92103a402e0f1601190a030b151802d02500340015649941e100c000f051115042c02c1030795102d019120b00403100b907440ca514403e46480003d0700900d001135119a401010840b06d030940341045c000d281401d200318038015141e40d65940002062514014100540741039201c41940140040c04109020310481810780c00c011154540c0034000000c64004801000e02102451a136010000d90503540d900500221030310b90780103006207070405c00b200e00d858940054440e1903840180a200761b0b5401a000f003400000130441240c103a032084100785814074004901c98040e204441c1c20496040321960b406100712808603004000c0e6050a034080c485 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 816068444 1250 816067194 816067199
    0x80c030901021204120305071703070903050c010302040b032710060f090e030a0807110d0c0303050f0603100911090124020d082d0f07140f04030803070203070c 70
    0x40110080480300020703000c0f50000003a04004108a2040303200351002000d01030281c0000a2140300200b12045c040c441d42d11180c0354015102d45558820740b036002c0420016030b01002041070a004903aa800000d003402c50400340342020020441c8001445101558009a010350310b0071410030241241d43c81c80b4044a904c0500c42c0d09200003403815006510317550380d0722000000c492925000300c07a080a4610b001c2d608143c4107050a907044400601640c00740440f901e151410340c0c604101d17007550300b007850f50b0702c40c41d00089090107422610045d0001c01141c0200c0300f0000380761000035521401502084002503010710a081c181000031810002e26405420080000f881c55100149200c21a2007540701c0c1c008400d9241c01617a4402150003094041200800000c00c1000c03403001c42100d07109516100c55540d1800407005541c0c000841d00c8290b0101c4240034400140d034400898450585152111460076242e116041140d004a2000904205000001400c5075200380141c981d01c55011412503521034 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 816069694 1250 816068444 816068467
    0xd02193e120306011d030d18170606131a15120a0204050a0506120a1802060c0a0c0f0302030a0b0405030909040f0308060103110d1a031002030a05100510031808 70
    0x20700c142c403400e0001756001c1c0c19410000e10711901800e01203004009040c503824000040d80c4074420503d010a8501c084440010f102180a01030800303d056100685202d251030001c222024003100c91084a0500e0064460f20051680a2644008008441c11151f0f0240c614582c03641e40b140603140a95441e00070280940c1210350b07006881501c000300c41c20446203480c1c00520010340104041142084607400118809000c00da1050603c03051064842004138001e402145050b44910f1000c81503910510249051040b0ba0684a02a00d488101c14240c0e40c6581c0000b0342c0c80742030312400703010446044003040400804000302d546203040940709050038a02414491a03400f9501401c3d80402c04690010b03102d580301307103e84e8a41041c0c4016031800c002c4910340c10802040b8407500c40c402090514000340b10b03550100403481d50104200805641d83c46c225100304199100500107038040204420203100c203507214401c0040420f80c0c1c0c680080c08106e080d0407141101c40c585405022108001558441c4c0c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 816070944 1250 816069694 816069697
    0xa030501091a04080f1309060303081803040609050f0609100f030f0524130216060b040b030d11011b0809060609040c14060d020d02193e12 61
    0x40380a02a03030010541c140b912802d4040d0120b40042803404100600440d8a8411001e0310314100b0b8003001050064a44003010105e0300e482c1c006401041594042003004800c071120b01c500c4071242c0f400b40d42018500300001c2c0c001081801a207210340601d0b1840c2216807600019519515002003503191032011b41c21000d440c16015910010000741441071154000a0b10b000c2c0c0c03409094240b40c0c41d10388080c04c1c0c00c5061454412681c265010904080041300045240050819640482e0382d03030300c4801441c50000c088484680d46c86020300e0900080d810315035404507050180c0d1415051107180c182d00c18400341c1c014141d066860006281c00400c0007201036000344110310a0907400d0448055803610030810400d0a0221002843c5504000c0141f01003200b510311400c10b100d019002c1804d0012212001c0309a03007103554405450790b804280e42e14201003e1406c2c0400e819107003009003904035402c1c0d01000580440807600443c0c2d001d0181d2041c080c44009413403048070004407c1e5901010154041c0e64103 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 816072194 1250 816070944 816070961
    0x3150b12101b020316020f041d07090b0d02060f0c0f0a1104051e0103082101140108160c0210051c140c130e06030304051203040815150114090a030501 66
    0x20300390b044040d12982d00000403145038884940482c0b60a8030181e0030044d00c02c265201c0340f5086600c614500c0801075191290b41c0b0f51126800142c001c0d40d0510b4480d508403003021540f54410f00f080d00309100581c0300c86086031000c6402c00d40103981d03203010040ca01d00c0d004c01e0346d1241e0300501c102101071061000417008c01c1090103086405000c2a10b404940403844140c0200b000e105400000042000514042c02001e403980b1008014400c211501034010a000e42640480d10758002444c0307421317a41da8400013040c0c0c00130420361000b030a903881080042c201039000400070300459040503054003044c0100e041c2ca8050040c840440c208503505450f140c041c10803042111081c0782a400814444150141500c48003043d01c03210803401c0303203820b224a0100c80c020300050b8150008000100d400c1e140c0b29500c83d07090800718000c4d50b54501d0700d19031070301e4425015110f10800304402c060007218000756110f442041405d280080015540b07003044143c13803140240a940c07004804030300008220041d08890b54 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 816073444 1250 816072194 816072221
    0x90c0e100b030103030e090a290111070806160201020a0504060f033b03040602100f23042006041512050910062c1008012309010603150b1210 62
    0x16111f610aa80a46d91070272141c40c054110001c0304a5000c46000300c0d0f81001d90149000620700b80740c4214941029810340216007982c000104009072040181306000808074103100031454180140b1000b0540d000c0c5024001c2004040007000480303510a400503500801c0d10041c030b08210082e880e48207a84032031311200308100d04091101855180010083ea002c9803c00e4018080702c0245d690420014600d0151804903030369101074000b0101848a6602c40c90940007110310b5042c02c3c24106403948030044140001c514200c80302000b107580705c400945048a42004d220314204030705031402c0e6803e400031455004000c3c6041d00b00980c0840019040016061109041240b99140d0807418144044a01148985500308010b885800448280c0f07030360107181401e150b8019902c4411301429180d600404039995900c0c500078084108990341e400d9003011001000700036840ca150303100004c96940c01a502d411755a200041c0e2626220079500010b80070019040c1c0303d0781104140b0f1702000b4103100c0f1440c0b4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 816074694 1250 816073444 816073459
    0x1509030302150403080606070609050613031d010e010804050f0f01020414010305010f0e100e0c0403020130020306060d0204080d02070506161205120a1d01090c0e100b030103030e 78
    0xb0001030701006080e000725019601d0210071350390308003802100d50100008541881d622480074020401c1441114068090340000880d00c400504000b07040510304481d18045c1200460b80c0300080c0e800c02100301100c142801c0813242eaa5860078081d061158581d0540a40c0c0141d42c1200300c1704d6030650040c02035404514260804910420044085030710900078040c3c880c51401c0b00303125001980ba41281e200c00548000e003440742d1241040d041825040d034810842c10400704061045680220980c0c890024000c0030699410207162280e0464480b0803040d085a640000401c0c500d4840100300c0e40c51341c100380f106654a0b595807422683d00c46400010f2001402054400b2441e8904003040b1542e405009200801c154019160345001c8000f002e0500c080c07000c02c024908582c425052064418135038410f0000340c0b100d141c41d00c80041c00364a128900305074500450000040e4060410310191800c141d20703448a543d940010760f84009407030304000114980400000209644031402200701c2c042a44c035207 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 816075944 1250 816074694 816074713
    0x105070204142413020d02130609080709051303081512060405070e0112120e040501030f1406070f11160e01080d0c082218060303112d03041509030302 66
    0x1c844180e001484250f112251001300245140e140e0064040440740c81c20042c41c0c4452800030408481c1c240e03121001052605200300b190000510107040100031310141448140f40008441301ca01d0810b400083c00e100c00400030070b1540c00c00561000401c98003034101c1c0c0c3d011190555459030f400e0210f50440700c4e03201d1240081410220040c081e0704030340024113010102505c03507079201752010a1440807400c2105004515240740c3c0e5500030613000358090411034905030007900b80700300001c88120f101c440f158485814040000e074003101800a032401490012080b0300d182c0e800310704050b0104a0f020144260742c0b0b0106032900040002e504a841d0301c2d045a000e00510301050f21401c3c2d032120b01401c180310a100400302c1809182d01300700d03031010302e5908041158440312500e141d8200000c0d000c4100d070f500c9806008040e0410b89143d030002c40e4200400c41303070540340d820181204c5c0540701b01c071243c2081c0880300201c1c50200180c4028050112071a0302a03551107200a01c07241c0e080c0b2050300148140e8850 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 816077194 1250 816075944 816075991
    0x10b0c06060d0503040302130e12070b0a060308160507030204111201080a05060f07181401020c040213030f140601031b1d0601050c0c0607050307030825030902010507020414 76
    0x1000b455400000713941064690340070041c200e400d16160151140d1a02c00d03104010b04140800021004952911a10b0ba42c4500300009442c0004000c0102e50385841c2c018400310701d4110039142c2648076041e081c600d6240303a241c1a030402c0b495030300081d002410078246002c00303290b0102410440042c6001e80c54036a980740071656640d106050054111340014003c1141d4058801d1210380c0b1100300c5c1846030300e0142ca40c0a1a04130034403980711304600d14100d1031001466a0500a45e0440c500c00c440035810300c0142e81c5006882c0410707101c01010b410800802404002d0358000c9001302c8903d03042600c00d50740c0d5a040810191810f42a29020f0a82e0b0702008916101a28400c1d81c040000d140e51b00001d82d00e0900540d0f055028075003400c102c0c424541115420b654100003010564810009145c982c0220300d0b01415000c1c01030300c19a400070b030030310303442c2401c0e41d2442e001d42600d1240d24011803200c0040c00161020b11900d04045d41080c10b1500504e07030210703130301d01c05802240706e400003804102c082c421 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 816078444 1250 816077194 816077209
    0x90937060929060d270c06050c12030912040e070e2d030c0d0602120702010e0604060b1f1d060423061b250b04062303010b0c0606 57
    0x1003440e0740c50b0708007024032a04001c0040c204c14600441c0000d03544415a50104081240a641c081c080351940466810011b8180200000f06000d04041c0d040c0000d29019607203a07000c3d484010b60381d000110000701010390402036518041e00c2c042020381e0307641d210f0081540c521011100d010208020b905410b29505044903050840700b054107048095400d0410070311902c034080701000da40340c441c15412803c02c0d03440a540c0b04015108407401640e5440c00d034407048405400034441015a4540741c00a8a40d80000c07546030752155105400050f440c4811001860484169107d90900741d06c8003c0d0106450b0032178180030000304195003680e60009440c0230407040b80720301d000318070001070344914101c80440d000c45082429840142441c5c20409824440c54040e100000802e0341c44d40244a0010f24410000c00c8840340031062500308106414140f0020240c4030f54410f4004100a400d035000000c40000d408441c2c5051400c40e543c0d69581d01d03115021543c1061181c0c2c4d0142c02240c001c203e01307113041d030b5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 816079694 1250 816078444 816078491
    0x20601050609040902120303160905030a03140c0102040906060314180715051606200705030f0306010e0a0602010c1d03070311060730050909370609 65
    0x91000d4034202e042030901c07000e4040d004080ba00804402e503558008507060024610132003215800401d449800304000b4076422a503881180030360849c0c0c41c0d66000c2603110310600082990303640103503500c603080c0724042d0091060350310a030b120500e403460214405078150405a042c0a10b11104802a11600742c5100c07012070112007000181e1000100f00b051400e1071000140403901414100e05010b14410040104142c18004031a4240c1e00e451806100d021039120340d90780c0c44c0d158102c90802c000c1d9620b00d540c1780720b900c0302e940d4964000705c00514287c0c810b038101100014068818590607507140d0b406406840b600c0d8482d0082020340c0e01d800d1f000500e407440d648202c0350050040820701e00e0f40e1610710054402d041216007008042101e000410094851046240f2040d4403d0010310300c5c0f0020300034054029400ca00402208201c142c1c01d59884003980750708048040300000f2248104104038001c0030198120404854813103a4040b03140216500110459500d8441800340880001c00c0e1010001200b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 816080944 1250 816079694 816079699
    0x1c06050403030507260603071a07030f1d19081e061e040b060a03020a0303020303161e08090f010606020f0706030507050d0b04020f0408100b1203040504090602040e04050a0b060102060105 82
    0xb00c0701c44c0c1040f0181141d9a000200501915840c0351203180031800c044881460040041002a24800f003507842104118174614370320700061262030b081c044118036640e44041900c00d5180424103500ba060300422800206100c40071141786016003074500071250f428803015031a602034480040c3d4401546005640c031510b4410031040c599a445e07135907038014000900196041511001c0100050310b1700c640a0300a14080d03002540c481c40e10b00b64008507012815400303010851600b4450440100100c41c3d0001d50295091000e101d5a03015a02e92400c0448108554503601b4501c0005229030045942000014180b06032510a9201e04080e81aa0425284100015820484500041e20076805501164001032016180180041007c989034009070017009664000d50088400322040703201e10540c2103000ea0301c10796151503070322859480380100e10610740101e40320102841000b4440d4102c4018003c0310074190843d04060400c540d0380c0a110208843e00c0d80c50901281c01c0313600001c7c0c0075040300c500 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 816082194 1250 816080944 816080987
    0x11404050c031516080c04320d1a06131a01020f03070b070c0f060c17060a150309020d021c2a05010c02130609020c100203040f0602091c06050403030507 67
    0x10300c0000c943c417010040140c13500502c284000301d800d9008180b11415644001c4660844000c4160140000300c80c5200040c86200e07800304c2480050987d2110030504581120100f20ba40d4035140440c8101038120b510910041c500341c660500311045404500c1030031400e030300b00e510403136518030341940d28410356801803ca03080320000038480502c1990b803200c90a1141080c4190315007142d580c40183c4116140c500082900485840380c0b601c0c5920030280e110008654041d0518078100941c7c1c4805080100d041c2011348610100d01507489245a07940c0003a4040c043c0c615001d5050401c0844651240045034001c5040301604412559100b500301d07548280280028000d02d01001035031580c94101e401c0742c001002e68401448101d040c4121001031601c0b81d00540c1e140380840903d41070807405d09860340d0592042c01413102181418280044480d0b10003801a541c404240006060001100c1e110001000517400d031010170030503400240c05036100740c5051004d6247c0807803c8d560b03221901d0169a12204 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 816083444 1250 816082194 816082231
    0x3020f04020d1517062e0b030f0a0b01020d0806010e04060503061e060109081b1215040510141506040513020d20030403200a030302090f10120905011404050c0315 71
    0xc801c0344041d80360104903142041140d1f603180c00c1c078864108a402c2409145004100314108015008071002d0392000d10141c002030300c00040c09000d0700409031841f81003084013910607485841c0e5900c50009820001d007103030200d1900341120440c0c20610500e0544412501e000325155501400501c0151003040c80034000794908000700398900464000c4080d400b28182c40000c1d400c0c407041c00382441103202ea40f94035010740380600b03003203181000b8890001805858000e1408158000d483c50344d410003035000e801e80c0140f403000d000401078025500900d0f8850001c05441420a03200d5004012070340e0402c105000080201310003152281000c0c4010480020170000180060321494080b4046820000d9400340001c4501d0340a14040034498202c0200350300052071b03c580e1030000c801d40e070391000031241410020320b9020010401c00e120740d113080180303444074051410080203402c83c000c800246c0d0b4200a03a440c0c41d0600e582d8685030943d4050180c082c3c01c1c98003070141c003442c03181c512602da40030300441344a1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 816084694 1250 816083444 816083491
    0x905031608090901091a01090f091805011103040b10060f08060307081609060b030106021e0a050303040812070201050105090c0703020111040303051e0405030703020f04020d151706 79
    0x1003a04000300d8401c00200400b208940e83e0044a0b4080d00003400b0001c1c9038541c01000581900b001c00259040c090b41c641e01300102a6241401c0003983c031030180200305200240011f5614401900b8028055400c00b990022a0340103c00a0b5104500491741c0b10074548a084024404943d10700482002450210900799010b008410b07868000d00080c0465200c291366101050a061441c00003500701c00840000f080880c80c1170050340054541011128699403611394082c0d07494020607a03c440710004c0b40042040c0d1003081c0801071200d0307008001d80c0e989180070b01d800d0401e54010f40841808000401c04101458814440c0d00d0585102030b200301c189480d24a400c04407900000b504070700f103648404007142c81001040141008504c2921825118505828100b49140310210030b01e008040900c410007131560009096000c072501a655400380100300c2010070040c1c41105441c00c585400e04250b85032088104d401c0000311016203c80f22401440240ca560b225a0269010000300c80302d0981c030302c0d600 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 816085944 1250 816084694 816084727
    0x1401030b060d0f050606040e0f1b06040308032a1303030503100801020c01050603070e0f1303030f15062606040c260a1b024318090503 59
    0x324006010740a02c911035900d030384414a42c0f0b00c0840d000d0f0031036011700c071450426000341100001c00d400038018410305030300029591402000079039080c1c00700c11180034041e100c1e90121000355400080c100e07580e15100c8003555100032030351144e9200e1001c01814030251002c2c401500d201070403402108840d0361850314103c2d0b075034002900f84111140050300c001140341d824801400c06141003000407400e0b141c020201410103440d680309001d401240d004201842503032081066101150b2089412020020f040807801454003d403032054a500c0c0ca640f20ba0b01e2a43c0c140c001c411100b0395580c1d800040960301091410208110106c00c2d01d9640391f0124150b490550400c4550904900e402000d01c0d40c4489003a52542b000e00d140a40b00c2526130500070800340b54040c40341c14840e20550301c0344504032840025602c00ca070038551903101e240002c10507802c6a03090941c51410354a29240300803040b010001d00900d003000c0c8283d0040341d460340703181e900212150243c0400303d41c000010318108803200105c0e4500 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 816087194 1250 816085944 816085951
    0x117041a06010509060a0c06180203120f2b1a03100b1219290408070606080708030c070e010602150a0b091005011704110f01021c05120106031401030b 66
    0x41c08418499401030381c8408001d0006c0c14215524441400071500b00001250714940d5280211400f10504c0409a200045c085e0301c00c8103011655603680080c2840d801280c00743c8080407280d01400d02880301ca0810308589040c4203030b070304441001104e0303007461110000b034010540385425400a072554100140c0340d0703000034818000605140f806241050481e070070080c1145113141008070f2400c0b00e50503c41160580311442403490454090018003403055450004024401050000c000407001e04000141d0004030040004004590a0948a074607940c1c5a80202103155201d01c2011400034490518561740d138120b50b02c68014106800c0380c1c0050340c10000d0f0081151110540300e403091b00785c0391200a461446040d80030082c007602342c200390005211000745490f80940c00761600502c0041400e89000c0340b488013003180c0e90540e00150f540103030b0030152044516a80145510b41e17410307106030440001c10355144103a11003483e503038036100181c048401406840008240050040c00000c8070042030940 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 816088444 1250 816087194 816087197
    0x806010e0d060c020d140c0303010308071109010611011503080409110c03070f0c0603090312150e090f01050105120d1817070e3301031d0a020117041a0601 68
    0x307104180c80d032606940d012084100140d1203c13080c1c03130500d540400d100c1041c82003e078000d4908095403401c1546d81c001170101800700d4400140c084100500415203402c3c0c00b0700504921030710342c1d4400e8050003600d44e01964000e2542800050b001c07041c2200d20031400e40394000d084074101802e15541784000c001094100c2d80040080003c0401030508001401c00c0a20031400300042c02c1d80d500c0c05d452201c005a02c03100525040119840000b60004d007030a407003850402e000190fa401c0710404051100c03040e80300400c0030021a09002c012580400d416488001802c024855079aa680034403503120303102a041020368010328800440c00b8801c2c1400c06941c0e03041034140041c00d88900165403140c1d4422b40240c801d51015000f001403c20002c0c0c01079000141d486d203042d03040343c410401c0040c60070b8020800215003049069910302d038060780c0301e040c80c0080881816402d101d204021680c1d040c284a00741d01040940041500c1d000020141d1486664019030715407094100301d03144500e012000c0d21090 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 816089694 1250 816088444 816088459
    0x518060406021303020a1202040f0506130b0a0b0703030b0915060f091f3216020a0b0c0304082b1b02031002040e0a020f190c0203010f0507110d0806010e 67
    0xb40c1d541b5132001e0003402c00c02a80c4a5022503d20400c01250b5080350180007031030030003041000c0c41c0c0d1404180341100309091800f14840740c8134400500000015000380b003102d4008030705642815403550200b03914080c140d9180c0125100c1c410780e42c044141011030240d2020b8204140402c8490850140624100207440302802020f00a5407011103401c0703100b003000295500c0703c030340d03e5200d1150507a102c200300c94042d0101e40035100d94a00c0c4521072040500001c082c1d4008603003c5496840c052001049240c074030396160200145480e03140e500900c180c141c07030b101d103418281e80702040c2000070107850710082003440d2102c48020141c3d00103451042d0080d903a1300008204000d600d0030304c4500301001e004400165030740d040903400d052040300a40701500c4a4410321420001c1c0d20b000c01203a41d0401405080007a4040401080f1040e0405030300094041d400d1828640d0480b9136500214020b803002d45a01407800c410100d0240c1daa81182d400d040064002c2c80800c0382035000702540101c1080241480 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 816090944 1250 816089694 816089699
    0x50306011125081c1b060c0e031614062104030201060303020708030a0e04050a1407021c1b030513032f09040f0204020901050c1501030c0e040c090c0516050c0405180604060213 77
    0x101118207e280c0c41c004662051540314151030300f03001480700c9103184000051b8041c2803525070308090484034405801100c0000e80c1d01c1d2107030b9a440c81910800c850f80d42081152420346002406000f1510045025201d17504012a034802c010082e00c0c450320341c0b503031130f01c41c076500c00c50402000c0c1c2400307081c01d140d03260b5905e1020003000384030500a01c5081260014008844d01240e10103150140305521001c1240480300d1501c850001031000d46540c1d014542141c4400034451204440d1600b0342c0020035942d14030713102c903064550101c520320007035000001c54400c03150228244a40e050f0b049030020110312404031013000529150f8082d20380c03d2010303d801418208250880b40c501482c138040c0350054203103d001001040300d10b0303402601520b81071101d65028242603466819212940c0290a4180d0700e5610a00d0028071440c00e5955108034200302c1c0507807581c54101192150345400003d40a241840c0001d4160851a28098205070701d0b072005100c039542c0e5490ba44029003280900e4028411281ca00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 816092194 1250 816090944 816090953
    0xb0304150e0a0606150f050702041d06010e16081306050408090a080106080c06070c03062a0f020d1b0305030c0f0c07090f060e040201050306011125081c1b 68
    0x10401c41880b5110001c1ca5074184030f0300801d031445d440c501c039040107080262200307034541c070906503941203905a40100781da1816081e04209802480340c01c3d8032500c10708000282031301883d41c103d07004480305290407a901c4036065040315103031011115088108400665a40011407540c00103511a0040c002103080443c01000504001c8240d803140f40b0a03034440c00144a02e02d8188039010b10700c1822200e1900d409915070b201116500d20384000340c0f0295441ca15081e0104903c5908800c030b40e031507901003440c607001102c040c002e0301c003d01c801e400503c0b902d500f400e0903c3c000d00d220f260102e882c84030500096001e070b80840e0254401404e00750702c1d100500041c07041c0704460f0040c03d200303481800540741050400da580700c2101c1e083e9041003229030902008016804080b0302c002d411940a01c3c01d0b070b0342d9980e0240103880003059000c154030188503008000c0d020010f4400d00342c000c2404407190202031941c03030103000d54130046200c4020400340c03a0002d100441d4029030140300094400a1020034003401c5464 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 816093444 1250 816092194 816092203
    0xd050703080415110c060c1e0c01060b0f0711010e090c0a0306050d24090b0103060b01020a02190f051504060804380606070c05041e050c040302090f010b0304150e 71
    0x11000d0034078003080031802e118051041c5076018810a0b101810301a030010348111403882c1c080d510030303c0140003c1c03427a241b201c01e4100e00050207404a20f00c0d03556440ca840c1130341d60b92200c40c042e0b032000001c00c0007210319032160000f89000350b00100300c00065180c1c00b8050358a9408501e898081c16030f114000160750715003019140c0294014154103062028162910701d48290003680d0b0111545814910350020321040f102c036040da5040500098410b42d03070350061f46411540b00c4c0103076000850b8807010501e00d203079000e0b0800f5108070640200e2950342d00c0303040c1310521042c03400c4031124110500003400780c039100b1580140d1090040c1100b050044460744a41c02030b032405003211042044419080701075a4048a0098201800fa11f00c2403410302c164880c3c601400380c5010303c522498845050381800e0082404071002d1050a0b0010031403410030a104011652003440200d006206030070005080c4c4030030405484c121100034807140d207143e955a0f905081403554a40050505a542044415001d400c10 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 816094694 1250 816093444 816093461
    0x170702090c090a1205011b0c0c150323090106090e030702040b011e092105100519060803040e10030b041104110d020d1b0e01030b030a0209070c12020d050703080415 72
    0x2603180303040300b600203011060103441000d04c000c2381e100c4000544014104001c0316421241d030201c42d5030810044004e171180540000204444c003101c208841107104190f400350250400804c0b005950f044283c041c0c545c02460151150014840d40740075040c0f40d004010384c10070501d020040903110000031040c80b1070103441c2000041241c042400400307107204010004202a100302003c0c4180341c3d40341c40da18290899449412621034001c1803d00c055443d18984a000c150740a000b0a6158000550703260464441c0303540c00d4071a05e022944107441c0c10968804d40303030000720100207942c5070b894140d80401c4040300b140d003040d512000814013080c801c010b040d407084a000702503940c2d0300345286602555034020f0780060905110012010003a042089249401030a007004a0300340d80c1e10b030020707040c800e42040c040c0d041080481080700107580040c000c10f2491007000203203031100710303a43d04a27511040014032a000c40c0c3c1c2003020b0000710b0302510100f0382c8188142c800409640460a1010998001c1c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 816095944 1250 816094694 816094703
    0xc030f03040c080309090711070302100c15052214010f050619150e0402040f0306050609180309121006030b06031b060a05161a04170702090c090a12 65
    0x100c284010045101809801004207000960810301c262000603006940500390a080c070204142d880c518020601c142c4004607001008a180644074100192150410040c21074159407090300c10402c7c06058070405000300e10024604003a8114600303403012070700702c244066900c81114426102120400d000d0421203019858010400d401c0c40814440411040b0f04458180c05182c001809044954610841011060310381560300c04488000328000380310f03e4000004240c10013a01100b800600e80003c0e0096000b0f5403000d0142d55580c00c0c40c0c070340c10490f00165446400404c14050b003841c08022885501180c078050b0f40d9504d4240000c8401c1fa00c0e0340d40300b202c100e8101e00400c50140390070301c0440950020403043d84d80300403840d4001603d9101d90704c2580203000340030500d0a25030340c080442c8074440da031001d8803110703000e0b11014054442504813011101d203164a1540504e540c2c0b84429540c5a1398040e014840781c0e11540c68403d0700fa00010005c0307401030658240002c0c580f856011041c20f03140074 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 816097194 1250 816095944 816095947
    0x111090d1505010906030b0703050f0610120906021b070b0405010309060204081e010506240a03231b090d030804080c010606030203090f07030201050a0305040c050a0b0c07150c060902060c030f 84
    0x4c1d03181c01c1f081c4d468020214424140703000200120802d14126403030b80301c042107400751020000302005840e400511700c819610309180c0880c5804011096004005200d00d28031144c003000c8030089415500c041c01e0282c280c040d0802c0c0001c004030350003604088640da22a002c0076060035100e8840503d800d0034400104054041c8540b204e900380030a100d031a401c00b0050302c50010b4100c544480e001c906081c8404010004030010b0b040c0302c014800e034401c0d5074250020840f8102c11204040d403030f203070700c005640da0060601000e110600752000c00003200c0c00c420300036000c0904403500d51800d407440d000050080c0d94080b020003201410210078031400001c0d0050303890058503801e180101c00c1c130300030500c09403134019446040e01340003607030b081003d89100e1012454082201d0350fa5141c5649042e01780d9001c1ca4200c4011070003c90008500e00180070380326070490444045c65641c00c42d12103100801c2c8445004100c10201d03801c08600b03190813201c4241c2c0058546480d00c141001000c2c9142e0029002c0c3c21301280 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 816098444 1250 816097194 816097199
    0x703020712020a02041d0a0308090a0233030103120e010207032406050906030606090a02040f0e0105030f010b100c060902101106090a031d010e0d050d030b030111090d1505010906 78
    0x5080c8034500e480410604030101b00d030003106a280e50384510240107418041040001489204100700400310170764082c0606062003880061040c80740052001481d0b1840401074028070200240242e9040b20b03001080c0c005522050b041c19140500d5041502c0d0460080400100200c0c0054041c020784003c41c1e00300c0d810103141c00c6100c0007207411a40080e4462690017041c004603503000201d294010000b20b0f0994000e4551880100083c844c0b580002d1090f000c0e8400019109100d01c01c0c01c2c102c40e015010395408001c04e6080c58200c54030040d1030b070b500c00241c135412024144a444940105440b550340000c1e0065280c0008560451003000c500c00038034070130b00b070b40400b17541441000d4015540c480280604020303070b50301610b40c001108560000031031400094855a105070740001001c07001070140e2802004c1e5080450711940c6400014000c01d04101d0004402c0c14141b02e500612521380200c40d0400e101d200804c4020004805c06843c03040380d42400c2d0220840307500c0b80d14020929980c002420a2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 816099694 1250 816098444 816098449
    0x120c0703171e010b180d4103120a090209190f1104061b03020712020f12061f0503030d02031b04060c0314040303121e09060501030b090d02150703020712020a02 70
    0x12800c00c2020b0042031400c58400020b40c8001c0c087c2c484150604680f1900d0032840c9880e00d07841040038554180e00502d00c075036021010040001c02e14070100100c010351668494107c04203540e1410002034029135900300080c92805641c005010200c40407402090803a0105060804d40d04006004010b0101c0040d0800896402800c1c0e40403030f40c00380c02500c41e202800d86000e034849555118400a002c0700d0f26600c01195180351400c485428010700b10300360207004805865680c002228241006181040010041100088c5890480c1c80003002549410f485005500194102078200000010b5614034007062039070324005007000d0321720366460001c02221400c005044450501d190720410004000a0020a901c81520340078160540030208401c2ea842003500384000c0908240900c0501d06084101007085980004c0d04032402600344034520b4513054122500d603601901c8041c09a4403010a03a1301d1003080e81c0c00c059200c0c00c42d0a005040c10184d841d108085403da842c1840160842d252003802c51 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 816100944 1250 816099694 816099727
    0x6010e01140c16081513020102070b0c0105070e06041503110424021626070504180c08060f04151107210809191b0308120c0703171e010b 60
    0x10151342000300302c0716002282011910002600310306841e40c041c488181564020007911000308107100a0030b03075492a40403014008c003c15101c1c1000202081d940c1034441c41d10000703031801d44444c007043d903484210740007058008206612182c20100e90a01002904501c1c210b01500044038884c1c04a16002d4030050003411b1403003020100700d042600c020f080c8084842d9006040810f01207404007140001504074940c0380c0720071035001c0c5030f0080c01c00d20518081c00302c28421041c1184608160104d8070b4039140b1094691804032544410000004005408500d4000c1400300340c20710702c43c001400c9010000c0c800060391125030159245410207025200745070a16080ca03400080c145082e54041c20860a038075126038042101c1040702e00000e42c3c150a0002240944034031503039000d06205107603038078500b21074550420b050843e02403984800142042248508949d215545503680507280c071580011714140704409400f04907906056084401c03a100003e0105000e0580c1001e01c0783c80300c480b5a247ea085 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 816102194 1250 816100944 816100949
    0x6050106020d18052205010b041505041404240b0901200705130e100b030c090c0d091713140607030909020c0f0a03050a0f030207050606010e01140c16 66
    0x20443c000e0140007007241416500015034108680c04901a00488210110314205180404005151000009401002c1ca00920455003100241c224140c0d4150382610a80518441c40040c1d14140000699a2a05134841c05011040350140da818440170005002e02c042035402c08090300c400020041150f40c3c0003050502d0a5442040e031141d08000c100e141a190381a80c40303518020609055103044054460b0402c00b16a0807020443d02c1c003030013000c07400e4007030a9a164a0b502a0060780480c81d501e00b012100940700e10603030384880307250000d90b000303d00003007103030700030945022103d241c0440c440c0e51201c005060402c0000d42e00c80c003050910007030400c1001c1d00140b41c0c4c403420003081141c0010b50800c81d0101120a860b070010b8031502e00c8400a4200108a040d03031009008001d104404c06402c940986104011a0344500c602c1e41124425000ca1041d074030003800300d500040002d2209e43c440c0328400000b0006240100310200103a400100d0b54100440b125441c1c0c100c0e8503401c00428186049900 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 816103444 1250 816102194 816102197
    0x130c110a1740051c2d0b0402280303050f0712030209130614060d0902060403260307050403120e041817070305031b040e0c04050301150b030a1509050406050106020d 72
    0x131103000f8100801c64080c498200520365040e41c0f413503010440c00c0c1088068042d800704907070842400c41e840c100e664a01c0803581244510302421807500504c0415071043e5040c90086820000c007030560310705660ba50004148400d25003810488900021050041c2da405203900391400340c0c8480141e000c110340c840c250900701c030781d091408804000d05000508000f80c401c0c401c1d03422a5482c82c01040791005061442c40c003a400035000240042040420030184003064220564001000c5d50722906003401d110590389000040c030180001e0011400480104161103414241465011490008501611010f06160046940b10415401403007060710041c80c0c214144c1d55000c2c6082125a8007410b01d00024090b500b54501b03407442d00c40f00c4c14000089070b016009034003000846140c8460100b40c1c5a1090182030b02a5007404400400310880400e00001d5598980d005802c6031744030350300c21000740312000585684000c10600010421403070310603c0d0180340261404920b66051450180c0703405050f0a2110 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 816104694 1250 816103444 816103459
    0xf02180f0d120c02060903120306010906020703030c03050f0c060a02130e0408030112083f0402030616050706090f030e1813030e130c110a174005 64
    0x30001a07284010610440c000d041883c0c00f28064000f140d107030f004426010781c061048030405a0301500c0c5a024601c160801d81e030b012004c6441c0d000407038072906103100007004145040c0c51000001d00550160a4550885000c10300784402070900300d00e040c00030390b552440654006524103da000306520600508000c180088103800d280d0b440a007103220500c2195694860800d003030782042509030860300301a1541e0030000c104c0101d45101c001c0c080100d4415081c01c908842d000c45070321144d0507014419500140074006681c2c03070754100b01480e03070f02d62030480c2040010000380000541c01d00c5240a101e019403900e4240288a280141c000c400242d912445003482401040b0344240001481ea030046101c0c10324000ca44c0b1034901501c00325545041c1e9540070051048404601d011680000d80b422015034a144080b001260460303200d410110002c0c00c0155126006541000c41000800c0a00071503044100d420072085042400d01e00d100d1142c84001100d818006009100c680c6460080c2c5021036071003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 816105944 1250 816104694 816104719
    0x25110901080106121b0f030b15010e0f0906040b13090512030c0a030c1808010c170c1803070506120f240405070c0606060903050f060402090711010f02180f 68
    0x400e8040344800200050340103207000c0b10054002d800e010007415482c01c0c6d40c5009490346400d16542e0411202030000c0d00002030040511341c410300014540d070b48094001100d08941c0c0c0c09000a54100400503500140c90b100712001c01d44540407410300c009442c5000149100c19807921a0030084038608090680070f0510034401c15108002c103c94810000c2c0c140001c400c024000c0a54104107130509058840ca40841e00040303816040d00300030000038043c0d49200c004c500c480590580d43c442075a202442900034007c040c1c0b900340003000000c0c4914000d04840c4442e070b43c0c00000350036a014071000c54041d980d83c4203000a038940300c503400340c02c128402c009668140c0c84450f400c401c03000301c10740307140b2481d210004289058012580400d82e0303600000b0910540fa2200c4024000c0f9901d84000c40d4988510960090740300780226500d4022a401040c418003030b142c1c0070003100c1600d00b24001c5034565507038034541c140511183c8010002d0701f8160001c25a014080020016159100120240200031072401c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 816107194 1250 816105944 816105959
    0x91a0306090d0507060f0911030606040510050618030d0905190303020d03020a050c0111130b030402150c12070c170d08071b05190204200304030525110901080106 71
    0x201d040b42d068039000d915030840741002805007103110f40c507000f0646482c00c0d14003400b50402c80410441402d81c1110741c0d07520b614007808111441201d030440c0c440c030546424001850101c0060079507030b8901070384000449240780000d0404c0210004c0501088150104104606200f20a4411810100c0c50040154a9510040d40350030002c03040c0000c00d80d0020701c441982e40a2000d07100c3d81d00b0400000c0001c045441e110681d164420209004446140d210001e40340d41d080049034451035028044035150256141400070607005003e500310030b40075000000c640c40a000025044d450701808845180900e40300c071111100740d81218550082c0c10a0326130545803034104001316044842071030101c80e100c941c0500401c0181d4421001407050085c400d08641010b4455031585260380203c40420070b542c2c20080302c5040c6002140411440751041c00000c1c0420b0242000d80798501d46081740400c4a000020f0150b00b900e5909001c5581110810f04001c26040c0070303501c00d015113103583c020488070b801d2402 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 816108444 1250 816107194 816107203
    0x11409090717070f08180a0206030c160602090103050c03091b03120c03040e09070f090c17090d11011503110301060e0c04061107060f0e030115091a030609 68
    0x50a02030080003012a4920703104a5000224a8840351041000d003005000200300c2558201810b000034000e2010452172030f0303120003019140707601000814544140d54240880ca800c004d1469103000010b0215468100c0c43c4514100d100b4480d110060303031414440005400c0b248094154008a407007441040f400320000503211034900381d076444a80c58207259a00081c036000c043d8400d089904004a2064000d1600001800564040d10000310444e510b00c100c84d07a8513035080c46504031031a041101048511032950180181c4e400919080108071303803200421107072280a4641024a51100c1403040320658003200302544810020f009100c900319040000b078040c602400054010300c0e20301d200500f240c0c2c0c254441002800c2e40c6195101c6403030700c0040000300e07401c94070918010940300c15485514070780c0402c0d14410b40d00380c1d8540031100d5640a100702e5080c00c8090415800d5135a82884500c1d15065814042c010198510080ba1500d98145044ac8e240710501030340d40079500500c1400042c0e1008603 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 816109694 1250 816108444 816108457
    0x21506040e010605100f020f032125170a05040b193317031c180503031f0b040e10030609050a0b090d02060c0906040e240114 55
    0x45001c140d544965140c14014640c13980820340c0000082000c603419500300c20b40b4040100380d034003603610100303c000400d5201d20800030310241d81f10419009194400c43c402c034094100766100607104400340041c0c2c01c407254595210781c04000c030741c0c01c440c3c01d25490b0340250600d81c424251507042c0850704103a2f89030380d455031018182d4601d142604414100d8450140c0c0710205400d11520b0212141c1d038900e44030303040307481c840303445c0b01c04101c0f001404244180175001c4030b030860602d070700218600a4203161011089000740e40c001c4030f59031581d0951041ca14010f42070f042d9140540041d42e40e07400c0030091004a4050f4030345821ba6191004c0003000181d41c0c1e103050320704940182c285900d0300c0d600c2c0400b070b01c00c42140e900020102c1c1c0c80c00001d1000c3c0203000410081c410b200321a00c00e415160711084030f988040c0c2d104c5580040e44058006440d05d0080d4000d400d00107005820141081e454040c850840b90085a00504000089003c110100b000a422035203c2c1e41c00c0c01d044240201d0700915480b03910468 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 816110944 1250 816109694 816109699
    0x6050d052a0a020c091905130c2303030a03060f050307030519061b11012a0e12011d100203010510050702060706180501050105030601180e0c04060b04080d021506 71
    0x490480c480d03600900000c60460002030896111b0b1802094212040c02140314001c450392070302000400303940c0c2c0504040b8141da00300404680f03440c40e0003040300c1e60807282001c4440075403110034240090346040000d4a2a40c440303440104046040c0b20200441e01070991105200354001c41003080458000b080e6480c48080b00c80b1003017a084820308008010f00440d443d12404080b07006804010503510441907400380d00f4090091050340000c0740c0e0700d24002040142400c102e4058110307401e113540601103c146c5108040c06200c80d0800c60b120503400c40703107014101000321003001111b410300c40d001c3c825054030344007210f4110700319410003010802050a03d071084081c404006991b40a5503119000d4911039640000103000f0300c50380f8502c0100014203400c04407041d600300f00001c1040d00d404154a4144c480809041c2d080741c010300038140c0a4101c2082c01c40050007a80c160300d0042d205e81c0510340141070580046030752140380c940404d00e0401070500d4030007103400400e1403140c080f1268040a400c19401c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 816112194 1250 816110944 816110947
    0x60203060d02120304140103050f0105041e0221010e01030305030c180618090a0516030906020d0501080604050609120901030903031b0306091107050a02060a170106050d052a 76
    0x4940100d6080041c116000e940700b50032009210040000000820030b0780e001204003c1103880314001035082e5041540d40419981d0990014441e40c00c0c66404040c40c0b00c1c131801001c84842c0072019007022a84281c00c0515811503040d06002507681803a40c0c54010199074005150f0742d03146840080480c00f029040310301000b40003801601052000c94100c056090007000c0d90fa0710520151901061058658014090104440002c0d15110a840303058461445e8002180f940e0712488002c400601d1000c8003181d030301e40d080c4842416882c41d0301c101d0340070b00390f901c5c02071019061504142c0e142c50700c01001107016a1240f051048000400c40a82d22025001e080114411203c0d16055019103120024148414a07004142c101036505401550803507150800c1044208000e00c10036a1078071030200e010b401503011a12030700040c00c00200900030440c4500d00040101c2302c1480c0440004404e9005100081c00400c1a1000d09a98464240c0040c4440050100503215560f528840e0b056100300780c058000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 816113444 1250 816112194 816112201
    0x61b08120c070b0a021e0909071206182703090501050f0c0102130302010f0905031b03030714150a140f04061b02030d0606020102040302010504270c030b0910060507060203 75
    0x510010340d5080c507482400411249003000e0301300b000390030150741070006543c0c90022a01c861a41002c486141c2c1c0c000d041306100d507954102c16100c1138014a00c0d090001c1d6125030000e00b40c0b079407402c441030440420402103140103d407078030725a0840462103030322542100a1404000a60031030100c004460007030901941721000b8214500540c0500e040d01c007080d500004001d009035244034a200141ca100341c94801048440410850b6210020f0240710b4240d0300c0404450300c016122200020f40d16002400ca81c40c050300307a5103c0c40074841c5511005555484002c160101000203c41280c2c00000101c04114000e041580034034a0b00c0c0c091b040781d88245648000c981442a580c2213459880001101100202031a08000f0741c1c0390701900b1448151413502c140070880904c103000f04e40450703070141d40300c83c02c05092842c10461142ea40c0c07901c5544c004a0664901075103003500a45078104102d403400150450b0000902109441c0144100d111015003201848a203400c001941c02d000d1308088c00680340d54 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 816114694 1250 816113444 816113461
    0xe04030e010e06071b1e0b090616030c031707080a050709030b070f2007062109210c03021b0301150b0342031603080301061b0812 57
    0x400715a90309411003c006141c8050143c200e10100540d1803007540a40f41c143d44d01d40201d42c049045400900051960000b0403015401401030011420000d2640d0303e001204451203084403070300d62048000c50f0042c04400301317041d0481031502c5064554043e102040ca000708005002c001c000303180711111607070303800030503241ca1007a84620043d40c2d002450742d2a50030240c901030250b000700182078000134220300071071100304403030f40c0f11442916440004002a5040290036203c0c0032450100406c41100f5120214003404980030704488180100421809404a01d1008290300c040310303000824001400204c80029a001a60081c40c440040c2103140000780c1800180c0505100142c40d90611403600c404142d8608910046005049461554914100d0030341080c541d05036803050145201e101183c4004540300007401810040380080580700035008041d003080341702d03443d6001074900b2100400140482d94002100b40d940c02c01030cc4a840f0004403966501c0344c281305001d9040100c410f0034000c0782015 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 816115944 1250 816114694 816114707
    0xb04030e04050405011e09050604120c0525051f080a0605030601080d08090a0b07051e0705303705071704030f03031104210506100e04030e01 62
    0x8000041042c8954101810003074007030034594030340040b40911b030026010104510710071080050390201c05440d055450b901c0c0e01a10740950106d00c024015940302180c00214203010340e511104284000b1485c000750710290100907900741d0012801142800044100c81c003041d4044842d606451034600c1c01030b501e030708908002c0d001c554042601442040f0010811607404100700980904683c2c1c2e40803259070301000107a82e29100040900700e4141080070a040d03900c600001c001800d01200082c00021100000011a50100400b981c841d000300708914501e103c203280c1544941c403134030700d00003240080200441852096032804200442c084024480c40252401e95002c1131740041c584540d00b0410240c040c21030746c4201811914030680402001050036000141c1d810f586d08002801d84203c5180e42c1a80100368200d014048001d051100085d011031314141c202100303000b25101a0220842d207081440c0680280a420101032183c50038010101d091085544c003580514190419881001c01a0f580 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 816117194 1250 816115944 816115967
    0x20705040c081503160f1d070c030e0a05090f04050105070207180f152414030601110a050d180906121506180204050f0d0309090b210d021006030f0b0403 67
    0x181708600340c0020310044252200c000c4880014580c50440141c040c800c1c3c0c3c1d0300702114290007040c64012000086440394402040031000913004100740b545602c0001c02580d8101c40340e08403c1d0212080200f041428012140c120702c1c0d50000300108ad04140f20f018103e00f000840c42402a0b4402c203100038000b654002403e13005034280c40400c0c60303854410030b07140200c075854a5000240740c41000881c07244104070a0036810380122030942162990001183c8030203500401d44510321908019a011400c03e101e001d503481c0365500c40212540ea81c242da180d0015069001c500c0e800d01d02541040b03000d032880400c11181d0380c4143c4130701c1d1004a01300640028040d40e040302a11045090b1000110000d0303500501c00d64000721840110b02c00c07010100489070281902c01000581005020451a0210f4000d110035003001002205001e0403c1d0002080802440080c4215400000350300301058060010f0b82203192141d005003c52404e42c0c80c1c07070ac602c5c0340024000b8407000102c000a030605101c0e8081821 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 816118444 1250 816117194 816117223
    0x70b0901020301080d08060d060207050109061b030c080903040e040804080601260a020a0b09040605130203010603110703090e0601030f020706051506090310180203030d0c020705040c081503 83
    0x64100946514000d40090144a1052051401c001c0d011030055040920883c1c00a0110352040f442d50341b0070019402240088683c0d43d2240480c80010350140034051140950348442180049144801030035241d40c90b1821080c031140105000d1940404003c8405a500100c6255100e4032140340100061141c5c0e4030400d0f0394000c1d640045040e60446940840d074009044040344000500d10803180c4440d09000d000758041a0b08200700070b40403812020301000c030402040001c00c0341c0d07aa00811100601c1420400039243c0c0080184100e41e0944941e40780c80030604110b9003409516070f009080130403940210402404e9000019400368841d0300080a500100403055440c1c01c41c6103850006000261038410030340c00103106204050902e002034980700300b40100100b41e03100c2c00c0c040f075000419042e41440104600c0000380005038408000a00d243c010b040c90000e15038410400090400c0c049401c4544501d04002c5031420387c03039010f01001e41006c061440540c80310751280c0007031715203204d2000c1c010 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 816119694 1250 816118444 816118463
    0x30b0c0c0d05120109020c061f05041406030d020f032d04030602071103060903090607060b22110928080708100b0a080a170d050a02041401080103020108180307 70
    0x74032254008058001144034445018603a42c9880700c000036809040d203aa02e2a50011000030408100320504d448403003098084403400d6a291800700b404e0b0342d00c4c203004500d031000c0e03c1c090103c00e040404c01440140e4040c40508085038040100075100d108502c0c0900c24800408a4200c40302a41d0f6107200409412a04480e0365079601d1801c10003a40101c2020b0b2447c00c0030203102c100d1801c0104546100e000d009024629040780c20b0308102c61a0402142034811982c0c0394010301c0f07562100c01482c169000c00a0352a2801500b001d01101070381c25803002d220300b8000038401d907a22500ca914100f401780506102442380401c050310009807040c845c4c1e000c0000c0384a00400001c1c40000032405416500640c2003d0212120705002e11420082c41c0c410340c84a80d018441d8400031500d004641168030300340384160b40c50700c840901d2030780507070b1429962013150f01c0c2d00040402400346c41905560041d030081c07d01d10460340c5550000b81458900414108414080040c2c25031554800d1083303500440d44180d02e007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 816120944 1250 816119694 816119713
    0x705060f13091409010c080117100905160803120a0b0303190e010e0102060105061b1c0203030610030e07030b090f0a060606172406071406040219030309030b0c0c 71
    0x5006821140840c100410901010035080c50040c091202145491f499109580c3d1a110104606120310340104216020740594502c1c65405401241035407402070008060b403054084881c6015601c592146100358010040e06001100000d900c3c0d9101c0d144c030b44001a1056598040303400c61040c107980c165950b100d80c40c08a10980c000d90b640d40140c17020ba9a00000c15003c0b40160382e640002c1c0113541c1e22003810320804000c01c0d404011072101c0754109040d1200e200c503103c41000ca140b07444054101581010040183d5801c040d0120010320405240910074041001445a00c50890303010242684908800041a50302c00300a11894610054111003203035810f03007800c40041c8218000c590000300c242c1d61074000c0c000b040d114140076070f45280c1c901032b0982500c3e135503008000e526282c0b80d4000e5424010240400d038040d0451a030b5021030360240440745010b204104080d200703148034450300c4599000500201381d11002804c1940d500980c4200c0c1910355004102140c0203213400c04906124651a1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 816122194 1250 816120944 816120959
    0xf140f1302030a090519080d1d06040506010603050c03011d04030203041206020c011b0f0305040c05060301060806010f1e05070c09020712031a0d021915020703020a0b03090705060f13 80
    0x213000a140660241c0340900300c50000b20070549102e01d009040c1035414000c082400322590310a1703c8490076141c03450000d0800011007400d080e4102c509031000e8002000400c103a1f60507000c1c0340e50014036544007502e550704100b4280c59101d840606411182c1191001908050081007106c0c080e00e9859180c09011905280c207034080d51201a082030395500f4016505664001c000b0192503000131130315140075002e00404110300070600103000f40d8003250742003c009015103c0709d0046020340503940e42d040180ca005400545001c0202c04800c0400030542c4600000000010016440c1940c40c50455038604560401840020040e00001f9072580f002030b42070104204141062000700082d142409258040c4c004485400e850140264101690290b21001840e103060905402200f4060940c0d8854482c005028180c40c4210700d5000750b448514184150f00e010a000320051a01e92002032651810001c1103880d07601d107120742c07801a007002c6031603660b122914040e103000c0714440483c1800566100c00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 816123444 1250 816122194 816122201
    0x515070c0812070501061409040f03031103161b0b011401090807080627030d050705070c290408030405061c0e070311060304021e060405041b090f140f1302030a 70
    0x10031181340d803070040c0009103100e007040070640c0c41000412085190b507558540c1520b24003c0b501c01c5080642d16070000c1d0b41860004060350040006a007040f80101d60404042c040001d4000801c540b04200121000020398005180d815104544907524000a40d0001603892103e543c014006134007418001150003200000c80038480d014420030041000c01058140404402c0d07120400429001044001e0b0300d507003990031558021025282241c903000543d1035406040340660040001e03144a0490f0381640b100c00c0c040000c02c0c070b8035440401c2c07400f8589041039540344100c2c8922400b4079401720306a0186031307041000c0c002690540380144840c1e100700f81c64680746e0741180000ca41d40c540d201c40c0070815081c09010340388210b6016100c01d50b54201181f03484401d0228031140c82d0302880c00c200c0442e984d2a18040c030b20b41030a0080406c02c10107207118016001d07047c2900801d06185072140c08110800784644d81c05000031090700c035010715080c24000701d400b00311010b0030845a14000014401c02010551 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 816124694 1250 816123444 816123457
    0x130e060c0a09060c05072102120606010908030a08220503120105010813150510050a0323010b0120210304030f0f090501050d060e040305030711070515070c0812 70
    0x29205210a603c9040036141400c12020140c025401410f041c8510160071288019851051883e50440011580002e8102c41001440349a603000502407000c0c6503003066400014051103400342d814580c032000002c00018004100d42c84200d519082c04900b105041d1664403295008004d80703544050114000d078000720300384600c60000d00410001515803c03170001c0f00208940c0000400301c07007030100d01c14902400c4058104421031020000000b442d64481c0351742c0000758880d4405144003044940c0c5600c0c1032461681318a03050f410304811034a00ea034070110908052019840c0e420b1032941d805a1503203089d022101490702407c0d000740403038031780708a180070390700c92803191391840c0035450504011a000400e191034030f4081080444180541d40c000d0340034001810100c200007031100e40d22520b101c06a00243c406a001c928004188044290301110344020010400c004195091030200484c02c040c1800c900d841ca4032001040131001c000054818100900030034003141c20300106041c1a00442d0700c0324 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 816125944 1250 816124694 816124697
    0xe0a12081501080103151d10060914071209020405071e021c0e01020f010f0b130e1209030c03161d0906270307111003050411130e060c0a 60
    0x1000046000d200724840001e882010f80d101c2c50180d1945ea0b61203807000c0d080b42e2850100b034460460074804140d841858030440d0200004100c0d400c0c290180307000322109a00300056003400c10340500c903126101c403010358100e609031801441088082090b400103151445000b5130084c1058144107115502918001401d0080c0c0944054107509600580e503800a08050310301c0c410b110509840068000c12401c00c80f8070040c010750342c1d0b501c9410300c95030840700020200e168060340e03507460711500d050172140410740c1141040104401d0030307400b400301e075980d14a01e01d440462000040d2140c072a02c0a204180c0c5082016044401381400c2101d000c4480d41503010340d145605c030034001000c40c0001150854059803144000d842c4070b4030b450744030b07491390301610030f120010591100241c280500200002c001c0c241c000c01c4440c020210321404c2120400c42e1070900000c050034001800045a02040f070100d80040840c0c1c06400c030840c96949038081c3c400f40e01c04070601d02410302003000621a074002041c112280c1e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 816127194 1250 816125944 816125957
    0x6020301080d1e020601150c060e01020d11070c0504111204050715030903090b03040f120c060b0a211401090501051f060203040612060b030c0c060c2106040e0a12 71
    0x410001c903043c92054180d010050b0700c803900401004000940340b4030b9408252030102c90320070043e103071a002ea80e0700540020f020781d8001219215082c0611840b2001203910241c103203008610b8a40c102e120410b4010341e8841c42d0360b18202d20784424008201e900c50a80c0741c1c0300e803565140c1070a0480c3c43c1c241910600303201c0000b0000314120b45121f8031418182c00e5042e100d035081c142c1002207407219608010001c80312141500884004614031510700b00d10340d07046583e420448182c0d45032200944841441241c024041120284002c0310000340c0c40310454240410314010000381e081c5410a000c80025241d400e500c4e04452805000381034000d144074003c0d42c0241096000200c0b52865204264441d400041c0c00c2440300303210841c42020750302c80c14000e1003804600700791200214405544162050310800c2030025041103c040103200c01640a19a421042c0c24184036400d12172000744088032a841d4107081c0c00000fa0a640e90b0f5012180c402498803c4601c8003401e40303030400c0b4149410350034002082e407 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 816128444 1250 816127194 816127217
    0x1a0103050705090a0608180a0b070216030b0c0315040c050a03060e0621010207050d09031505090303070315030b0106090e1b12090c12010219021912020a06020301080d 73
    0x140c4200d0712200d0004c4c000d401414940a0308850011b030141c11a4045201400d10500d00e003410040214141e018240002003424a44400703450050705480645020580100c00c001140e2190f0500b036112040b15030282c2d480d070300d00c2c0542e507040000f080350304d5006180010841c0c80ca64000050711900e0900e072010041c0c0f40e100c0c0c2c00c80319840350499441d90321283c119510710031000440b07a054145c1800d0f01c00035091041c180d8410307042c540800031410000300201d40400c14001031102404417194180d40400c2141407e096858491000030320a20070302d80c5900c82500e000c120202250029078108034202c2c3e207541c403031000400301403003031107019030410051001c205800e41d03499038444031005c403640c014a07011181e41082d00041c0002c02400c101d010706d9a00c030107139440b03481c00350310848003860005942d05207404c10a0400c00d0340140300011075200382e244800042421030501d00f6603800080700c24015040c600c00700e1400c2c5003000010000e6001200028001c0c200040d200d805803000d4a41d01d81984 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 816129694 1250 816128444 816128447
    0x92410050406080606010c02011103040b0d0506040e0703030e0111060a05100e09030921010c0c0c091406090a0e03190212030601120b04020c1902040e0c031b01020106091a01030507 79
    0x20214000c8444a1308501e01080103503008040c108081b51041c14510440c50400302c0142c250b4000307502c41a001940000d45500954191040030b0340a1001c58040100003010800b5903640d12203070000506208000b01389683d030341c0c09050700c1d0307148000000071181d00d458000303c00000740c04155641102403a170b024000c50422071f990071561059214100079414a91040200a0000041512000b202c0120312240c1c1016200307000741c1d41c0d2204cd58a561045144c2443c0081c09015940e1100307105524040000c014590000b010a400000803115249540c80d241c410b20000c0200c0d040801c6580300015218130007000021817440c6202d4030b6001c0e507800d48015000c00c000b078402159001d00080c1240c029121080d85036100540105003c0c10050400d072005000303c0c07812500f0090300b01100d144c810a10218501401140d4103c00400301510486603030802082e9503180380c0b03110944502e0210004403559100354460401820780380030900408841d0000043c09080c88200c3c41d001a0901d0000f54006 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 816130944 1250 816129694 816129701
    0x30b070912020922030228050d08281406030607090504050a0b0901030b09060705030606090d050723120102091804030c0206071212060302011d1305100f060c15050924100504 76
    0x43e040710203000200388550044a8030301c4020300ca04500002082d03560bd01711345003d00e0701412400000001142200002c26003404640140000c5c4641d022a0411500b90741c4103031500200c0c1c0090301c021449841e40b003020405803544420240c0c0280d003c00001051044030394129004644100c25104140c40340300c0c0c11510b0b807004641c45500400104210821810321151500c4000d0045054400c40340d100d4260b4007506440c1c203515980071a00c4540050742d45020a645601094414000c40c42c0c890b0002c0401d03401c0e0400000802c0092801c0001028140109460202076500601150b620b9100c0d25040c00029080016100001d409480205140046200e184181c82d0140c54282e41084c2c02c04031142d400741088001030304141c0c1d0a11203a0010500c1c025180103955291091140a04042741c080744c5880c60b50203181003104003c2e8210106421050380581540301c80c8000c076a958a01101070301c0e1407030b808125150710802c0c580c0003104038904400075024a509403a20a000f80c0c0d14400c01058 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 816132194 1250 816130944 816131023
    0x302130504032f071e0f05030d0e060f0309010f06080d140d020f0301080109171326031201030201022e0b0d0c0f030b0709120209220302 60
    0x2158110b8041c503001a0161903000c101c1a6814002420f0040c103448141030078613981c84446100d1400c180132203e000c020f61a140039052000b0400006494400081d0759180c030322126038180540210004483e0715894103c0710b071b00204840b02c075682c2c04e151804074000c201198100300141e20b400c90214944101041107280f100c450303036032142c0701d0100c2c00c1c4c4254541d2005004100d0b540c0e0030005500c0522040780510300038948440000381407403c0d41805914000f001002c42c500d02d10800000d013401001564480907a05141d060f480b00f138000c003580f403586c0d039031003a0144036a100105840ca60080c1000e003003416a8400e070f00350740408408140843d210410300c80d170807030040116242c040d02da40c11540603541c1c9900041201d03000340b40e6a00c80400c40545c54005100002000b4400d206002c103142c401d581014a40c03402262161a020640e5001440740c04000d04ca80078141c045040c000c80361000e0050320f0f814010094031030400b840c0195890380184100003103048441041003100d01034114105a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 816133444 1250 816132194 816132197
    0x130603051c0513030b01030506010902031303050d151202100e03030f0706060512030d0606020a2114030c0903010f0905060f04030504091e200d0209040e030c07030213050403 76
    0x148592800c1d100421a1060103035204100b01801081608408042d4038002103005035000711255046003043c0381080301c141c0000401c18010030a00c00e02418890a04000a816203091a11681d80d089444040c01103251501c1c1400c1d1242008a400c1d070258501603100c2d403089803152200001d0b0320003954850040c0700d00396810740092210424816102c001003482030312a410001e03a070b0380c8034400035180c140c2e008505c0c0c8050744045040340c1001414403503a000741c9864002456a11000e69401003d0720140381249090740900b091b08031b03c24040e00220280404d1000707142e489181c03003881c0006640010360203d10940c24a0408803c02c002441031410072500b11002e0400c45d951000000e440140140c01241040810000001c100f2040c1c4282c40b4407500e00207a030000f04180810310810340b10140444241764a9480c220100866100308070359000d2211203005d42c07540c0024001030f00070a036099000e0602c0c007000030000c10754007000c80c0d00802c1d203200b01c48036010f0031020500307007003280d004660050 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 816134694 1250 816133444 816133453
    0x16050307060309050c15070c080c03030d021b010608010e0c04060b0f131a0d0b0f0d060b040207140303100e0c0f0306040e0d031d15060d0602040b0304030e13060305 72
    0x100780c4260000c8020398010341c00c54800c2c0000030701103410b4440c900c40d842c60810020540c030381000507102c8000c0c014a0100c00078a00f110501c2c000a449200312007420307042c940e001401168260b0703115120140e41202c1002048840c1d07071108054041c0403441c008040d140504010000d00d494030b442480240c8440c00c0905083c0008900228059440a60301c0c10920421100006410008944151341c2050a02003d0748500003102400203650030420040d225000b00e920040050300c0e800401d0b140203030800b10105420782a030021400903c43c104002d0850941c8a42d41007008400000450045c1c02051000308241d6030b8803200710400d4001d4400c028056400c00c691420244407070055034010380300810005644e0844080c0e40d00c0c100d107407401080401d0b10b6128852004480c0d02031300a0040c1c415015009880c030251051480c03034002411217100f0682045100180300b030300c1c2c1c10b40d00070304a000ca03401e6403030070b0608001d0701d6515000300440c810502e81140030840c034114000e480031240d0200042 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 816135944 1250 816134694 816134699
    0xc03050f150a0c02030f070614160e09041416150207081504110913110306070f030e03131811040605030c0d150b04171c050307050c010f0e16050307 65
    0xb103000c1c0140309142011403000b03000040464600030300420702075104d410001420300d25048803459003200181001008003a0ba8155019141c2290000040f00c0341100e07464016a40c903d814000b003a0744841c0202c09105046007030043c90341441e140416543c01c00f01ca5014524414006c81e580d5103a405120801e4002c01040309014404003074040c0c0083c03041e094404050442004030fa081c1c401115248540f00001d407041042c031824581210040405a001e003c503464495005415903122003000c1081590350081c2040301c0c1402d10943c2c03c1c0b207a4140c445141c0641d203450f04800f510010355200fa080340f4160300010000c865200300d4080380c2180c0c0380c45040d599400300076443e54000e40c000c400056240c82c1c4400c1151014210030b000340400070039264860f81004483c81c1140100a0011700302e41c000f6154003c8102c485680303a01c503031100d180c6907035a135443c030100b2a054043c49a49076200e60a0501580e4005a01c5e08001410040301d030885276580300902c101c0c400080d80d4400c42e40c2541203c44107 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 816137194 1250 816135944 816135961
    0x30e10020a1b0504050c0406030c08070522080f03031b0705060a020c0f100204150309020f04020a020a0b070314060d0c06030b0102030f18090606070803010506090d0204090c03050f15 80
    0x2100d052402040b00810203680c8602242c1030b07410803522428032900c0003d092040075094451354100221504d8030340a207142000c009000d520404d4442c8650440e0010208032400c02040380601030b120213810743d2503c0801c3c010841c0d036508169940940d0403015500d641d0710b070311080f0549e80e2183c1c01c10028841600c0c1d03050040c0080d07000c44007844c01e42c05102031095480d4002c00030b4070b031402103407580103907681d140810341c80d420642085150304250401180c0320159680314000c07455a4821a0016512203800c101a80341c80203144c0001c00e8001310340c0400c60400c2d0164031000501c030346903032140a81c0d03031352004200c0000300c0c0307000050031427040f1402403041a202c0c0d44240c0140e441801280c1c0b4155012001c143c281d0080503c0165001040261000508001c85510340200055650b2400d11045640b1075010b400305008441c000c241c00315070802d081d6181c911240c04d20350040c10801c031a02e10342c184114500c415000c03e90f89440b542100e08800c4030005000e150202d403a40c82c860194035407005 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 816138444 1250 816137194 816137213
    0x62301080c090d0f050a030c0311010209010212030919060209040c14030a0507050c0703082d12040c15030506041a0f01080408040308030708090d021606200d020109030e10020a 77
    0x10180d80f102c0d00c540c14500010170400c0001c24140c003036110400a140f091030000e0000160580081140c1d0050100e1022a42c00240740358958900c0075805807203aa400c00b0305494a841020808140c0d0464050003041c025035a005003201d01c01910b050210308800441640c1c0c0500290b6201c584d550100300045420182c0d0b82f042e600140b8074580340d40707000403403480305180ca200c6403c2900c5001c8e000880d178400785402e8107039064848414280500c0c403000c1c46000c1c9018054111085098017007040010104071310902c100c07004d010041b00403101420b1041c4014010720084414500451604a45001c40020b00421800f150400ac00300108000f03c40c00450b4464000341c41220b80c15414000840000c44000c007a51003504655161409417070040c0840e850044480f030900d081d5000760b041c50712030001c601b2400d41550720170b0408100c0507050b9904140841c3c070862010b00c5900400c40e81d0150700758103400a0344c1d06800b9544104484101d00100903c00400d510840050381c0201803810028807282d8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 816139694 1250 816138444 816138469
    0x22060c11060304050c0613090506090603060708090a0515160e061b030d1a0a120c05120f0105040b100527130f030903060e162106062301080c09 63
    0x2416a00d501c3c6103080070500c50340084141642c0780307607d910309010341c170503501c1403d51001e82122189900d0030b090f004203807500406401c24041224070400031301c081004003d2000c2c100c1c2d100049514030401020b81c519a964251000340c1582c02c040300d0070880c1485119495080365000340303003070300c0c0c814807006040f011300020114030b150340014404501894000c1c820700110000c030310b0104a0454000741000950a030541041c50058207501c40303032000c618022864400d80e074043e1031280c1010301c038051a51505840c1c203e0610a582070a00300404c0100c481c00942c000c0009440030199030f91a082005a400101003a01800070080c0000c181000c510240083c1c11120004445802d402103407a0148d0314000d00c0b00c1a40072034440c510030010081603100f4548106a1500542228108400d5495204d01030348035001d642c19520b918081030403e0301d0240c0004d25400001000000d9440c0240f101c40307002412080d66100f400090580c043d4091500300748a0ba05000ae21482c0c07030b00c030408005503c110705 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 816140944 1250 816139694 816139703
    0x9141008060d14010c080108031c0c050405030f0f120405011407060902180403080609010e041103010f06140f01021903030e0a021519031b11030f22060c11060304 71
    0x11000030b022500040400820004480c000b00d400c0800c9072000d4a44001a032010f8040c0e80100708030903030518840700c40d0441c0c0110000c04038043d0460780040740c3c035000300d0b0419541405060b00302d0181c00400110325100c0c2c8815800d6521460318900c0354a11801140300b405d0114490b40034125000c901c50004244940c4035810000700c465564000c072b500c84445a04141c0040310040038401455006411a5480f00d000c4030412060343c14040407020078032010740001d081107003903030020700a50303003e4020105074410000100903040d65640510308080310048220b026020542c1c52a00c40d500c040782c28425038498200f040220401680c00300c004010441c10703050540039800c1042d005075104104400e41c0e045080030243c0b240d907500c8109041c04140c0d2590700a25140c10f034040b11901e544101162190b00509001c035100d0140040982103104003c2007180c1031000241040f242c1c05054a03a02c1756200b0902140b9259483e06030a80740c020300e0106c0034284072007501741000c951602c01d0040d644140325 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 816142194 1250 816140944 816140959
    0x30c041d07050a360905150a0501030f020d0203151302120706050319021903020307031a100e01030912050705070608370c030e1908161416060914100806 67
    0x20404c01c50304041030488164100c0c0101031149a800e400940c0c10801d03482e410441d40d490742d910100c0801d140c101c024060b142c5e0705d00c101c095540600c003158039020260069034440c54550512888030f84900e03c200d2190000f12400c6000d480e000840d0402d48110740c4583d46543c40c0e400ca00da8442052000050820380c00308140c00340444085003c05a421180d140540c89040c244000380903240794187d0041c41c2c17803107003450700e80c6940e40c00d0040c0d0b080d5409003010b614001c0611300480c041d188051018081781e00b600c0742c0000c0144c0c0007005000a501410035200d0903a1980310031540103000f940c1500180605018108522241042c0a14014000040200c401841400302400c0d103500080203000b003980e61001c440f000301c0c203003c1204042803845018030700000316030340c107050390086540e040c000d038030815043d40400552100c100000340c0003404581c08100c0c9078000160560050080c0300010380403010016039048018403040c02100010f0075581d040400b0f020440f59003000615060b4001035 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 816143444 1250 816142194 816142289
    0x40f17040b18040605010318080a050906070c030314040608010315090b07110f0f0a0602090d0803180118080a0c030504050a08010207050d05041d06030c041d07050a 72
    0x2000006042201d8054000b4020188540401c000c6480315030101d07040c0346c20315a128290f54078a03a20000f409a00c01c150316201c200c0000304407868022010001c2c2c000c2070006250090080c001165021284aa03403850801440d42c944210140694410700020070b05100050000a0b0030382c5000f40002600400051058402d0700d0340c00382000300355107220121707521140b03030340c403d0394144126800703001c120340102504080c2c0751009645404442c80502150f90100b5a60203554980d502240095000f81e81c80d070300d9003801e034850f00c4258085818a0425881d0111380f200b03845054880455054000e5080303410301301c1d1001c05650040780184120104807040101040c0c030b99a0090400241641800041c0c0b80c0303039a80f800d41d00d801d2541d1102424401d06010030005502071014802c2140103050f2040f40580320000880d1500c03425592240c0d210f401d1100d0070403101301a0500445d44034120b41124104e40e6510240664454213000710101c0d29180700521103ca100100d281d4500d4000d41810403201a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 816144694 1250 816143444 816143459
    0x60406030f06090e1b031006090b031e030f0d0f0c26060a090c09050307121b080c120a080403030e1c0201020c0d02150c0105041a01050f040c03140108010507020f0303040f1704 77
    0x20708c2038002c0706609075185c0501503a410200075141801c848103600200d00c105850807940c0e24081d0024400035003c0010b143c102481050f0080007100c5140c0b0703400d01221680300800f90070144201c00c031410074120328000c003aa003541c0700700050207003c000d0890895a800e1142e00000340015406480c01c3c08185080004d0341d40b01001450004c10201e41d20710000285850b080c0c13600e83ca555072508002d560503c00703214034a030108010003484000c481d02c01440403085c04440c20700200d03081c05044204040350020030701d41c10580121543c44102c80c0b100d80c2804080803503400b2452110301030300503403010b0008540e5050280c42c0000c86400103100ca4035610791118407461701e41c08040014903d945030b20511041240e141414948003050301d03000361980d07040c80c01240d201d411114405100b05c1d02e03100e160003451300030340c031908081c1e22002021845686070340e46140070b40020b80b011001442a207241c5444004080306486c011540034011002c08a51502c2d4104640720f1550410030001003080300103a0725 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 816145944 1250 816144694 816144701
    0x9040228020f01060e06121204090606030b030115030201050c100f021b070305030f031909060902030709110315120d0207030302060112020303030420060406030f06090e1b0310 77
    0x51000d020030480c040d94484000b03007031000b01c4958440340d80c1014800c0c00307081c40d01c015003681b295043d50603001c00180b100641c0d14000d020b01082405010009020881414580094040d5072254405000700803a260505088400a010b00d1404080b07149081c00103620400081c64916900c808440000b880241980115a1034020482080703600084d03220b103289240341481845600e102c00f81ca0702c18a1901c07000c1d12489a03100319840d5035400070000f6101c59032039102e041301002802e01002040300c80d140210081800ca1002c1e446441070b1000020001c005002d072154070250480c5082c11a1a07505d02845613010890b412a401010617490313081d080e800300000c4817840c0b41030f4020f0085914600b801723403c00074180c2000c05002c03041000e040140c0c500000301c0e40c0050b8888100042240240c03081c011050611110316484900050700041c000c1e4507400c00030000c14102e00400107990748004800403502c01c00d03030090716508030b0a81306407000d0342000070419000025060700c05c582d0b807031000ea030100c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 816147194 1250 816145944 816145987
    0x9010c021906021605040204030503030103030807020a0f0311070e091b031023090c010f1805030d120b030a03020a15110310170111042309090106051f0c020105090402 73
    0x40c1c0c04084000348404004c45240d006100c15502180b406080d80c4403940c59100c1400091b0a014003080400d5146d03108010025030b1076001401c6a17940d691a1030018480380c500d00e00c1490f180b2413a44080b80c500700c02502c442c000c4150342e00270409824403828956111780c0c181c983d0303941030083c07404040e82e2202c107000e00c1d01c80c14291a504440440321000016982c03001428850142e1704c032216450080e6002030350303451210320a051204817400450050701007020b03545c100796054042c214005d1101a0820720b03031002030f441600c080c80840c44078018141c1c2c1d40c500c01e40160060b80400c00e01404244001320390388526840705008505c2001341c030341e29500340d4016200c4800400804400704404891f100100300c600300010000e200408e201100d04005000b01c0c06284800c07107a6100c902d6070381c00d11034280c10321040080c2103581c0c01e02e80908164024465807080341e02031100307404540c0d502c122100c10644400344a0311075080d1144e1580045426401409900750410382c03c0021070200716103115890321 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 816148444 1250 816147194 816147197
    0xc0806060a0e0f06060304080c0f01020a12090804031b090203010b13060c020901030231090327062a2a0e130203151e06011409010c021906 61
    0x8150038800103104100c16164800994002502c0a00c042e142415460750340049003154030b03030340340d4886c1c0c140442e0a11401100206910030700c4450000140c064000e0718004140f80c039084000390822145c44169000a50b004215403c100018000210804008519004024412032119403034010b00004c0360f0003138100e03000c00310002c2031090500300e4a041c0c03200600f5661503c0c103810982507001c20544070701808024401d085036099170030605280143c5a20600707540d10310102c8030303440e290321400800211405030300050001624000d4031a107031020b0f1440d403401c0451016014940001210560701000c050345c00002c1089600c150004144088546035009201007100604a009050450500440e421814082d104003c00a101c41150080e030300c04000c0741400000401440028205102000d015900c004103034188018013003500d003902081880301868840303036100c0d500151800c0510403a00c0a0404080292029079403184082d800c083d40301412801103003014841f55220902d46420040 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 816149694 1250 816148444 816148453
    0xe0d0b01090c17040f080d15051c2a0321080109050c0915040f0f030605060301050609041115032a040e0601080c070501050103081902070602071202030a0c08 69
    0x649252240b52110112814180302c54081104a42e5100000400161412403002200000c5c010642c0c2100c0400e00f001000b082000f5070b180a000c2500034601815014580520a0485014802e1101c20743e80350400c40342107102064404000080307035117404c1c86a942c650b465000000500076150740d81012501d80da1b09039640c8024500501c2c221059100780c4031170742018141724811240b07508440340c0303610945011203000e1400500030554030695108400c812442000091110364802c3c40c00152442088144110385400b030425003603035004e0b6170140d440450440071030b0014000c180400100710001d0011842031461409024240d0411a402001052034551149c28030700d85c0c1e001400c01c16080c420050602c0e09100d11341141c407000421b500d040c4241c14000c1407040d290304065500d142e501030000d00c40307907860f4584076502e42c0003038184c9044000300386008220741d03001003070580986c0c0c0250f0040120500d00314120300036960500c000c0c1d815028010171030340850a41d00c03004001d815010000c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 816150944 1250 816149694 816149699
    0x1205070b0f2b050c091f1e031b03140a0507170405010b12100c090b0a051308034603020a0c080d06051c0b0a0213090212010e0901020405060d0c0e0d0b01 67
    0x2c403c00300006c000c04007550f651210550f9402ca500404030032192141e0400344c00041c642034009004100b80000c001000c1400d200700e80b40c0c50341022448105c150000540c54036a21520020303a03206440c00c5010641c145801c407400001c0044c1e4582c000d018000104101d0301078400310f491400c08818216003030308054a41c83d0052054011800141e40c2c80c80d01d942c1240c90a0982d1200d4065900035501304240051541c4910313003001110750152426034207413582c0e9009444030b0303114407100c0b80509040070021140030b40104a8101803004010308101c15044107544124110000c5d40240015414440038846900108680002401d1895041900000d15078100420000c2d1940c501081a0710780410944c0b41000038000c64016802024030304c000358449041d2281c00d800000b90b40c0200c1515440842c03000b04942800351814121080440ca0b1813458036050500d80c01c0c3d10481c0a256040002000a001c040b00550701c550f113645054682090303a0100701e03000445c2d440712144159041e54010006 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 816152194 1250 816150944 816150949
    0x3021611100e01020312100b03130507060305040206091201021e0301210f030f0e090c03070e0604050a050d060b030102030c070629100201151205070b0f2b050c09 71
    0x124090781c1514184004141032000000b9560f114a080303407280c00034601c01003000e150310000008058202c40041e9516803a043c0101d2002c00300341c11041d5500d120703482002468500030f2180343c3c080d5030050f10040c5000010014080c0152941c45914941d40d0f081003101256403809102c0d00d100044814619503d5241c05001c3c2c503150320700b0004094000c000034070300d80000c07514040d5014503039050600a0303008502460035190031002c003810507007116020f010001521070840c0114400c00d1030f51600e0f40c40b111004140207607801180a229003025840c0014420341c9440c90441000911852011491801f5000442d003640c00030356905561020125900040103828080c024800810414460710700720012082d0030b00146820040c2e0254009248150807240301f0740041c00800304905854680543d070710031502000b212904103481500a46001083c1c100740c410868080d40000704c1c1050174034103603004514203104412041071074038194119105842c2168020903100d6000141d100d51a160700405 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 816153444 1250 816152194 816152209
    0x2070b0d021209070b1215091005030f0601050a140402090d060b03061f06030203041514060307060302191b060e062508070822052b0c1203021611 64
    0x903e806402c1010240710000c10041564904410280f6446498903080000d5005241d070408407904070a043e002c2005a1603600d8642044a809404441c4001a06e841e2691100c4080c003406900000745d00040101d0320b19409020190b090017800149040700100000d92a280c102c1e00444030707151510088501c51a041c461554403c07a042200405045d10307a42a002007003c5005a006265003c004141803045000d072642003440c0d501020400c801d5502d0400c40507020481d00d880c424403031380101140043c42402070b0740f9401c0d516001c0f8a04a000e181050360308062840020701072488401c0d0074400700d1000e000703052441e00d024000d40501e040c05481929000189001e1050580c0680c0b03040445503400880c1c942d22100501c0d204049880c1c1c81d10303c041c840c0e1004a0110702414900b0b041080c01b401150821200c1d24144014403105060020015121803a400c000c01285050124402041010140c8000010755240043c5070038901d0041c401c0301c1d49149415541890031716254455810f002c0d5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 816154694 1250 816153444 816153451
    0x12060a0c020601240309060203040b10050607080d0e0a0503040b0307021b010219150f0204080c010e1005092b0c09020408071809142b12050702070b0d0212 68
    0x1019051541c145845450950801c109071681c0100c070134041c001c1d86110303a00408442c0c3d48075806541d40d090900704680c0400b0107807950b40000301c240340002554903009080b00c0c24254003884660824601c3c50115004108220209525010b0107540d100010020b0005002030008030008940301e0801342030080c549a001000746440761851103a4a040781c2e00090765042d40000803c5040207040a031800036a440090004440309505100f42c0c0f208025880e00603105542d00c41003190403803070a40d0700454600030340a02c26030704070300110181105984120001c003000c040241c10760794034200058940b03503d0a0070b0703500c042c23043c6440c4103080e0070415140054001400802000d6003014203240d03400d6200c1c0428071944010180004050150074400e4100d0200b845d00668050700d0b0f003107107043c40c64460301000d001c40c003038051540c0d542070301a41c0c1c0000803400102a036201b85428035000c01c0c035401400e0152000080d44142c0f04001307000900e032070040600c02e10080003d42ca620000e1840342c8007103000b8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 816155944 1250 816154694 816154697
    0xc0409020f1237110d140a0b0f010c050307080d0519051005010e120102030c040f1508040f110a03031808030f070210050f03070503150103051b0c0c12060a0c 69
    0x807410680200944040f010768a042601c1d03402c0e4094141d1052002020103400045107414041240a500c20040c3d0001029025140502d0225550000d55004550028606603401407003003000002e04d5120700b004551140c0f040088a14080c020b480340401508a848500d12035a01d4004014860a0320102050302c0d2640c90400c0c800d6003070400c6090003190040c01114104841c10070411030a41d00c00c0b10901c041c44451008654034280540045490b6202d40120080c055804000058440580000d0004c6085603924010301e526286d641c460003001c1c28800780c40790300c00d80582c180e15550f55410007004520175111504108140b045d400c504c5c91055001d8080c03a0814070642c403406100d1001c50780310320750403604c2c0c01e104921010706894a002d0005010210740c404820010000d0b0080c00030b50103000b20303481e407111800d8280011425501e04884024080c019000c3c0e4010980071130020b000440520b0081d5020100108086401d042600d200400700c0d0f8401024480c0341170152252082c0b82040d0b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 816157194 1250 816155944 816155971
    0x40b0906010c06150e010e10120507090b01050c300405030601030b0c1b061f060e22090b060f270403021612021002061506030c0409020f12 61
    0x3a800182c0b0030020007802812483d15140c410b01c00c0d9444400da4400780244414082465031a00d155510900d4119007148100480707401c0840c4209034412450034203607001c0c000b480424200700348000905581540c5a06001c0280600c400c560780600001941018522400b5000d07080b054102d10020300c3c00d4140b1188060400040c400c644011414a064a0b000070750f140d819101e06110000d2841442c9448200c60300c0080000c1a407100410504d025a81d030450814600740103540002d000b9030340c2d22400c00070407008501c003951410b140103140420001c600e046d004480800c06458165400030310700b103440704c146404100f120310342010001c0c0d4040701981c41c0d085030f2104c01580c01e0701c0c810900c4480c54031150b810000b4105482000044440b071800b025204149a40e40750003108400380b410101e02c02c451811310f40c1038440c80010301e07500c13170301140071112101841441403100551003d8803101d41d0440c104800f080d9000c0368002000e100041d10380450380d96140045c9020341c804c0107022141e0030404c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 816158444 1250 816157194 816157201
    0x1226100f05060d020c12070b090d090e06040b0a0305030309150a02040806060d2105120f060303041208070f030809060906060f040b040e0a210207230303070c0e0105040b09 75
    0x102c2000703403100030b400118010381e01c203c0c070054945041c0000d241a4008140050800e0030801c00c1d044c0c0d240100d200b00c00302e80d98062507100c25286041c01d80502c2d031005c024800020b5041c5000d42001001d1040500443c14154590300d500d419607204030764648103035001480c4040740c51200e41c00168006400c0700114282401c190110b5102e8902400301071080e5103c4003800706001c50a035503001c0d00800100030058a022205c4040d0550304001c61103c189424080001c000280161b4854410034000b405186400d08080301014041c220701d00580e00d80005025480002d1109100d044100b070080d01c0d03400a42c50003181039031900200034001b03c5d01d03800c58001c1c0552a2504841301d400000121404a01c448400e0003140041005014000440c0304012814080c000001202c440045604140e0142603103540b105903603a2210340300c1c046600003100c0390400082142015031000000003802d80e841e01d8000d44418841d140c0c02d410801c100c003100c0004004074a42440355401203002502c106043d4070307 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 816159694 1250 816158444 816158449
    0x1140d020f0103200703030f0b030109050a0201051c0203010b070c121502090d080a11010f150b1810020c1003180b0a06050d050a02090903070506041226100f05 70
    0x28200007114141a22074242c1800e544510355140300f0032080e510340940350151401d008019052000d181e0b5007803460003903135025904040c0608a07038143c01000500915840e42e0044402c1d5220450303504040e00710b141d24140015031400218000e010208902e071f120360803030900400506c1d4a61040b40c08400300046100000c0109180c481414120000143c83d03200180c04901c102e0342c21700d8000d190801c0015020b0320503810482c510401c424a1000b00701d90b18a900c801c00440c2d80400700720240d400070080403c501324140c00100b00d040c4800c440f075940c10031000c020a40c0d4117032031507000000d0307080f00e01145102d081504014078641041d140910844041140c01c0d1741500d10424041d244200c0c0c0d50010700d01e07800f150440c0004003406012002c60000c241003c507103403601c00c44102c1c8101142800300b13280078400000d6a11541e0000701404e85070b220303651a01401441c0040d14803c3c86901c0e4550380f18110000c00c030074803501102c60600c10318030b00750b401c02e0300b0402960003101c00703421841018000364 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 816160944 1250 816159694 816159709
    0xc1202010c171b0403060903110c0102071e260d1409010c0302010e1b0a080d17150310020304050c04110f0702040204030f05010b01020609030c03030a09030e090702010501140d02 78
    0x40c202d1142d200d101e9281c40c20441c180c030b030640120030701c007400c0041c0000401841c1c0e44002c1006029540da400074010318644191a4a4629401801603024203020300980820041d0004e80340c80385503074202904d60b2910360305000c5032160380e1b440a150044d0a101c111b04820300140f001c0744524940f41110000da14914003050244040715410040c030204290201030013540b0840000758908219600c140c850b8128910240608000038005c4c0070801d4006040d00d00082d6488010220361a240b503400d1300c03c40c0702c003401d400040c10304502c4040c2d14404c0099071000c0c05214410341000c038002d80d403840e090138080e1800c40c07000f007080d000d14074003170121040254500503140c5800b540040640c1d10552070000401900841c3c0000e407900c3e02c50320203141000b00552041c04e980c4400c1e000d4406554030001d450f5181c0c010100d000c0416002000020341130700c15907020104082c4242019425010250046004101d04490b0078000d03071356036030060240111000d141014248101c3d0402c2042c2d41960114261 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 816162194 1250 816160944 816160967
    0x100c1806021203040f0b090105092e1806020711040c0c170f0d060b0a080f102106020a0c030201320903220e060d02220209040204060c1202010c 63
    0xc1290203c0442c0c01c000d90030340c1c241003050b0840c0701c4002c3c0d4280030300000c2c000c3c101071b18178000e0341c410201017524007a40d1220340c0d0054042d00300c4240907410300c0700000c0080c050342d0401c1000942b00c5c2c8155070009403240302902c61030340203402480414126a05020450303a15140038804e00001d503819a0004d03041269a10410b440300280a485600030300700c10140f40200c110221045051503804035441c103034200600326801d01aa2003a031107440d050f507042c1034458141d40e141c00d8000404001e204503404604000141c0000440200781508551101c0e012a0003100d014000a020f250500301416824010f0000300300c03c010708494600d491100c800003422880301d8807185d1803c01000182080001c3c03081d90390708981468131020b4414201d4000c15a405540549a10407002d040400d072241010054559921350151642d112103400304c00c210071120b4400c0c402640580c003041110000e84441c0040c00c01015152034005180c441c6140924101e41c1c1309a0741c004580c5040c4204010640c0502c0e03000c0b4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 816163444 1250 816162194 816162223
    0x703022526030c240703111b070302090103080d060f081f150e01080d0207060f050904151409180a0308040f0b07320a1d03100c180602 59
    0x80c00d00780122035a0450040303d1049a80e401103041c2d00000b141c850b00410200d01c400d0f584940b1954440d003094040340e1761102401c01c40b440c02c1c0000e00c811300445000101c140c140c0d40072030710360554a03400500566800d8004564484d804920b502c01c0e09a9030049001519070704500c200060304000d05903650f18210056003e540700e00c011002c103075a007142e11805040c0f003040d00d6184c0680c0c4a030003000300e5040070312440b04035224500d050310082c0d1000c00d51505132416a40c1e04030090b400306808803820381255514690081d078031a905950f6001e030800d442c00411100740d81003d081c0558040100541c00203005050320b40108034001c21900001c60000c21003a0700d824000100c1d115818100058204030f1001403048120701e041c0071440d138024100002420110a20360741c140c8040105121246030001d510f401000e0500c0030801c1c150060f201d01511100001441070300d025600c000a1406412191800700d0300c0d0741d1814002d42591203d030265061000c1c0500d60102440c0040c003e64407450043c4001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 816164694 1250 816163444 816163499
    0x50d18050d050d180503090901170706030911131e02030402060d0504052503020909031e0903032802070f0f0509040303090602220f0e011a04050607030225 68
    0x40481c4150350141130740350034086982102c00290301e000c1c0c1c1d0b030758031648129100702500000044c1e0780249140742c440746084030300074020661501800360054150040d04a6514550b00162190f640780c00d2122150b800d010040410308401901c079080c3c2e030500002440380801c0c0104100800b50315000120f4440c807012400000e4603a43d1824150704010044400317101d000da40051a9080c1d034032400c0f030401980d000b101c0800c600c0e03c40c0a0115540e106110071080c1c0001c51615085070703150b85401504200300082d00356842c1111a2030880c036080d0081c4140d17405c4191a910384500107504004c03500141541d002c00800080c1040c0c280505d400c1c051045074450454200010308043c400d4201450442c1e100c41c080d03448000461915404001520000090144040e0002000380341d0044840440c0e84407440b1640303507400d00481241301c0303041c2b0040c00340c0b85204110005030f544411009010b45806a40030b00720011021700c0c005521490782000491010f03109a00f841140342d0000c036042003000325000003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 816165944 1250 816164694 816164707
    0x1d01020304181404030e040605060a0c060b1c1b0605030403021f090804121101050906161e05031314060f090a05040c111e0706080a1b050d18050d05 65
    0x1080948800c250803c2d600f0000c03c148010075410102c6007420340000c91301400301036140c1c02841101d000c0d80f4640f0000504d880407200105a241c0d00100c03405201510080b15101e040b401501c48041204c42209c1c440c480500109024000050020203000242f40039455030030207880081d540e80c0c101807060001d08500c0034241422106030701c50130080750310400301a00c1c0c40d9131b102c1a0641403211201034403280d50302c840300b803050740c801c3c02203520420340285940d007008100c001a588100d181c2808962004660030714034102036101c02100d00542c8280000c541e1000c020702407080103003d5500110388082c00381d0359402c0684d01c00e82920400401101c100c0e454411103030014034080c119a1015811030304d06075140090782d900540300c035180500c11048520301034480705080c030070000740302c40004250000381003448010320a55205410004081011443d01c00d0098070244000380e0081c4000031500c000303040c2107407032140e000340052106124155941c40c003403034860f152603050f03420b0480104100015003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 816167194 1250 816165944 816165989
    0x90c1518040f1a0d0b18030903161502060c0a120216050f0c0a0e01090c210507080f04030e040b0109080105090703020a0506031003060c1b030f1d01020304 68
    0x541600000c020802d01c0b5101d000740c0704000802000c007040c84a101c11020b80031071810204400007581d030340205604c0160744e480000402c50322013808103038058007040042da9200d079401c00880402c1d8111300001c400091400e07090560380c1e9841a008001d5410440810071080c0320f010541d50640d00364141049213001752241440244900c034104040c005110589070140040003c024404540701000c58a0031004102040400e064521a428030141850018003402d4030503040404a40322509041e083d00013031100034564120801c540d0781110340e5036020452610780c8000c00c035410400c8151a01303000c4c00d050b10024012048006550300560701c0300e095184503441142e0403001041d003200204000d00b011000c113510b0340054401079201da40e8000c00882d0502d040e2044030f0182c2407081c0d103900d0103841e5558040250451841e003400384005058510780b00d03800e8844803001980702e46d484007030080b25003030060480306000a400e00c0c203c02c060640107990340c0010071541070700c0da01c403001d4511b20600d049 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 816168444 1250 816167194 816167227
    0x30f03031906080a0303240302131802121614180c0408071e050301020a0504030f2d02040c050316320d06140d110d020306090307050105090c15 63
    0xc00003e22a040c1e032130050540c960300982c041c00440211620010000e058440661218040603620140b04242c0407070b51102c90744183e28034280742041190600301d03074001550000c1c4521840820341c114159040c2c103103c002280d2006400417540340c1c40c07036188501c041920348550035a210540080740300441c2502c03203100280d0307004104803c1120480ca8880c3c0014081001140c107840d443ca43c0007602040030f20b03044c02a19502d034115614241840d186840f01070b02201c0f01b40781969810801d400050304150415151b00a000203031052004149aa205210403506a0302c0e0400c100300043c82808823445e56001185c1600c0058541082801c0300e084107070303820100307040a00d101c02c0d00181d000d0f20052101c0c0098995421214000c0007070503640e825800307214078402903055208142d030381c03001c002819000c00103c5070700e00905601c00040d6144c4c00700f803810b203064907070f015954400700e0440c2c100b00c000d005240d440008100a0120a01d4500100f003008404100b4a841c41ca004100f05170440c05a80 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 816169694 1250 816168444 816168449
    0x20a0903080a02010b030f0a0506070f0e03030412050d08011a0a0e0603010f0612020309190501150609140402120403030519050c030105040e0d0905010509060418060f05030f03031906 80
    0x505190342d5280c9079102038000e000000c0b50500034011602010b00c074140200e19081c050b600540503210310f5442400c11141302040c1000c1d0028419a802c1c0700d07900c0d40b401c0021300042e24205102e9100384c00e460074580d00c0d200102d00e40c0400c00c014000180108035113030204000384205003501035140c10301600207a901011400385c00760042408400021248540d2112800311a002d07120310f07510080b10072640c17050340b200702d408010382d900000c040c0301c414401059406116000d6030000504070490788128605080ca035010781c000410ba114244501035008001018a00c0211011490407514060384401c0210081c005000d15a440d130008550060002501c0c0c14240060030401051071320038143c0160fa0028080e090080d071900c0345c010125540050b0181240c40183c603203e00c21880c0400440f41075125801c800d410401c11300001a4000307140060741c401c40f0706480042a074508140040e0311001050f40803622940c404900041082c1c4040212038110145803040700704110a4003860001d000140d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 816170944 1250 816169694 816169703
    0x21b040209040f06091b09031709030f011d07060806040b180703050901110307020a0f0c090e0c10050405010503011e032009070306151809090c140402030f0a020a0903 73
    0x4983e44a11040c0d001909580b4a50004c210f04803542c40140e8200c0c041071052004102080703428000b00f41010f500b0150b006004090602d0308418002103030503e0515411140c06a4440700e0049460002414140c1e40b0500f002c000d00055203440401031451001801c80c07401036075100d85800c1c25803110789000c010702114030400280340c00e180303800800809084421102ca5440d008943e400c2c458032100304d034002c1700564002d007044c501e60345403060300a0945204a0700c04010a6001842240d140110030400d191800581035494201003886403040303451f416032080210411040c0420f0381c01200740c0e41520700c070360080403001d440080007101c01d41c5290406401e0080008100000c00803079a10140f20b0b00065a81001e1034440030015016100580500c070322034000040d400c10309034406c0b2205204d108841840030700c407070b50301c0502108a801c8404151050040e451081c0000e0240c80c2a101c1003400a60382185140303400b114030301c45000054110850a900010034003802d91140001c80043e40e0032 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 816172194 1250 816170944 816170951
    0x1701020d0e0304080d08010509010612090b100f0b2506020702151b15070507210c0506010b1305040c03020c1608071712031021110d03021b04020904 65
    0x10544280e0342e9402ca4402d0982d54490300964180041c410603601c1d0481d60044d1440306142d00f0702d24241c690f4502c10842945d510741c0c1e140c1c00c0c00458280700b01039010301d0b04446101c0e8441d082401580652945803c803854642c0c0070040500f421080080c004d1485c03101d94a0064480b20520307146001c0d105455010f90300c440c0b049400701d0a4900c907070060110a034034580011035a54101402602c40d425205500001d2900c0000a15400d005000805000b4880d81402c0880f0302c1005e03a030402070f800800c095000410064404c2c04000081154902400f0111001030606200c41030307104002e90380f40a09402a9152151400183d0003501a40c08400d40a03099070728003a08894446044c2213940704500c028401d0580022341d90800140325401c070100710300030b0100803800256155030b0f1352000d003c1c02d90005820030001407070740b00d09c804900c10b04074032030b20450448043d08003118001c048140c414880d010040da482c0c0000c0c0c0018040f111840d00700c0684603402d0070701001400a0264030099900b01e4103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 816173444 1250 816172194 816172211
    0x307030807061b0e010212031b0d050106020f150601121b0c150b031b120613031e0e010c0501180f0b01090209180a06090e010902010305010e0c041701020d 68
    0x110740211156504081d4a03030b2062181c2da4084501e105aa034104d800758208580340c00f9408054001954015219805260b0000c1030600c1d0b0101c607031101d420112031030359610051000c50350602030510340d6030304000200291410029150590708014060324103224004618010441b019000804182c40915107071103c070411410180c109641110111070512030700040d0002d11407a4860701f422400091b004150700c8040e60840007070405000b0007194000c446c0c1c11205001807040003160303c200091164090200321500d0040c061044016080c07120381e41c2141d010407200e0b48002c0c090441503003403030030a048003040d040ca140100103c840c5050751000300c030181028002c040c004914103511401035550660b036180d40300b02c00c0340240b10040e54844000210003086101c1d90300d015800c000304103800101c290303541201310f040347c9030f840200700503944500704282950f826204103401001d008074519000c2c5007480441145104a0084084040040b04040382c500425810381c1c090002c0134004020141 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 816174694 1250 816173444 816173453
    0x40506060306060306012709050d0c03030b03030a050d02070c050a0803041d071b032106091802011218080a0915020c0a05090a3908160c020307030807 66
    0x1401120464001d00c40c150103d001401e0000706607048501070703640740030314a002c01c4011400b08a814002c24600d0b445468000c042002400780c5442664280c4610348070740c407141b0b0041c0a07100c411858500c260014001c83d034401c4e402400315024002c001600581d140580d241510310724400c0d800450300607800b0039012642c100d000000700241d0740c0b6080c10540011042021034503408048aa20f000034200d814a0076180740d4600c1e12810051081c240300450f20f481e503c104030400c41d440703120702c03d5649074002005018200d01c541e8400303821110350382060b40c0c0c558002a000f090045180f08250350348244200c5040c00190001aa6650ac00421543c501c44018028a207000d00d000c0c0c0312005c02c484105604003400051420107030440a0940c05000303141c81c0400c044a00001c05080c4403540360410704980d030120024105615148021740c403410440b00d1004049003a038440e03110f041c00003003018070042001c400c1015007121038520b0f02500c21843d0f403020905203815540020b201c040089010b00412 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 816175944 1250 816174694 816174703
    0x9080c33250519030c050f030d1b0206061e1c02030f0703050d0507080904180b01060f120209010512040b0f0f1311031903030603170306061b01140405 66
    0x40c5031045040010454059902001d400202004003194020800704140d94040c0483d541614000e0401101d07007012034a510f400c000f131001800c1240c1d0000681c0b4807810b00d642c400e4030514810203071030902e02c0d000602d01940c2c4100241c02c103031151b10301c40d101202d12000c14960080403100035100c0c00d5000d5928210751942c02d40d00c042240300b030045e0942c00141e03040004a0404481e0040001e000c0038004075000d507115403100000703440c01c1c5070401024125072070702d010340036040440e03c00031107520399182800c280c0ca94042c0c002000f002001c01448019662002c0c450358120500c010069a409550006039440e2199660042c4a07a003410100820301180c402070390710402c00302e107030003d1681c0d400316044c00b003080480d5600d401038400200040426550502444084801350488001c89900c1f88000101480e00004800103500d40409100300080020b80594018010400500f142020f000207441c40c000c00c0300d0020a80d04202d1100300c0c0320825045014086074a184540e04ea05041c180703941c99 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 816177194 1250 816175944 816175957
    0x518060d09110a050d20130c080406050f07021b04020d06180609050c03070c050c03100c02010b0a050303040b160f0f03020d2d0909060602030909010609080c33 70
    0x10074455000003224244609581c0741e180d4002000d000380b800001d42c48602c1c60320446c10b150000306905029414001c0c52142c0781410105850700b1210386041e180110540344000c04400c4000a400c0600c10324580000b9500304203115035950b90f41000c0c040000c00d00038002d00000903605414010f0000f0780070740110b4856922880000b0500409031507420800903540c1c140d40e03001010104000140807203114601390250144100c05441c0c5003145d0b41e000030714143c25030020300a869640e04c10000310030b40904c500100b0f0386055035003c2141c0d01d00400603490f0b00a81c0300700d41181c04001014102508440801d04840c0c0c4d22102817081000b46080c541c00880009004a01520443e008101500d008003102e401d03074048001e070a0004580c2c001c640302d1041c0c3c040100018811000004500a601801004060401903008540b550024010007407003403010391085050000891050045c0c11010401c3c001d101010384103060820382c00c00300c2c80d20021000701c80b001c0602c068071b02c44540d0200c0c80001d102 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 816178444 1250 816177194 816177199
    0xd0204090617030301030c0605030a0e100c090509090727020307020304051512011403030d09080d1407050f0f0702030d090e2214010b0d240603030518060d0911 70
    0x241030550f07540e200c20301000d4124201c81c0f82c100403940c4a50020741e0700000003030f4007003002541d60200619050441044003202510b5054103c2c1160740314039818001c2a048480160604100000715184c014900440b241c9051130b11401e1030003483d2030310141c05800c000404554a18000100135142c0d00140071321441010b08400e40c80c80c0c0c03a529801d82c0c1105003a03141c00075040c4d20307140c03202085d43c1d40c818a00360180018845009241402c0c800c10390030031700442755595141040200f41080715449600d8244408c07852042c40207455001c000da40001d0321100e001980c8400e06044050305010f5000025030612404403400503030b50740100740f24102d8a100361040403e4030380c642094410b0048601a0b502141150029804074070407584180b900280c1c000000350a030a442e01140d40a50300d00320680e000c000307604240340c01055011808503000c5e4210010882641150b070000e0003440342890866041f26903280003038099031f42c00c04031035249121043c20014038109140c03000318003425122485c07 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 816179694 1250 816178444 816178469
    0x60c030306090b060d0e0c06040b03040b070504080a031d15070c0504062d05040504140601061704030c170310080c030d0c080d060e0a09120f090612020d02040906 71
    0x1440b0403240a8200b0102000b00384905244c92407001600500c1c040c0c4403078209110340c070b00b04055a01d4032002000500013261031070399a4640fa04005444c00780c083d00704000c0110401007080041c4d404a00c9144007a07051421150390a400c54150106000f04210755510242d800da620a101018000928400d40b05200310aa1140cac0e58040104803803552091500c01b290110800c40b20f480800c58403001c44511700701c603d401d107071548040f50071124112000c03503d000f070030300c0d01c840303185420400d69004164600e003001a241100d0083c0b10b01080c0548014248503140001c0c0003042a03011405200984214200d5180d00d045502c01c60842400d20078007003640940f038078440003410080b03034041e541296610307020b8046250b583c0b04403260f40020307038201e101b680d02c4c180800c0001c680c00040e03010340788484012034804d03461b090034011a42d0005100342400310081c2861400b03604210108211202c9043c0f00c030a188005100303a02904c51a03102d003605500c000b401141c4014294001403e9510968910 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 816180944 1250 816179694 816179699
    0x4060f030b0301110f210a060501020f2b0c0219050a05011412060d050106030b1009050610050306040908041211060c120d021c09030e0303041d0a02090307060c030306 73
    0x10301325416030480701c00c00001081906504580503004101207a4140c0c0718403080ca40b030030301a142440043c2c8041d48816102c200c1000381c0c3da810400c03d076542010f44060b2a048245150291541c0d074500c016500c51240941c04c04002401095901c0c84c03250080d1502d280c00c80c9001030700c3c0c07801c40e0b940510b501c07443c3c0503403010525520811040546200110307071103145c1028106500100b51004140d980c1c032800c1800070800003002809050001c5128450510352414080c290425888040e0803041200380341c40200720316a561081c07041c000c0401c50070525034a0f2248800300e005484020f402600e00300300081d0024040128001a001ba2030240d9040207004d00321104010051251540c00700035580308020f60041407000100510a8121341000180303811007150001304c0b003004080c000350310140d4410144051540200714000310600480113540b510f0308000b13060611000710320005903240408000078040c003109604541c14204014200c80780d450355128020071140401c4000c4001a0400c02c00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 816182194 1250 816180944 816180949
    0x121008010c0e090f04050f0d0f020c010c03021507020102040f17070501020a0201080a0c020307020d0312061e14060903030708180604210f06050106030906110f0304030c0501020d0204060f030b 84
    0x10400a1000b419100c03d0b0321400000749540c01c0141003074505025141c0b8080300a03a04125400904a007610360403a11a5890000fa0800c40750020060500c42c01c0440c0f0380c0041c5d4081810f564810b07003010000d00c00c1d1a80d540890090207550444641c8500b540d6022520076549034142e100c081d0b003803046400741500c9000481c1c540505480090100380f203030380864200c905682200080c2d02c941c0c41181d0901201d41c00180703c0a034078500503008540e052403a0a4207445900a5802a000b00710700d000d0030303d0307442801843d02c00b6180705281d0000600030f42c1c017101c0d0340c44030110703541c40300300408a0f500c07036440c2e0078410240c0d0711822602d008050041c2404ad40c41c140f420030b5030221f445043c1d0490320781802d0100700e00c03c806040b40488030310b50800400000540300d0b11400d4040c02d4682d50000f2508407a00d0210115100c6070000400b4810038000c2220a5810100302d0b64031a40c10300c0c01894220079450b1003806801000060400980007040105007240e104908510303031805690f0521440200209 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 816183444 1250 816182194 816182207
    0x30203100b0a180b091006030e06090d120f0e1f05010b030c22081c05030c18030a0602070b070e0402070b0103030516020d141e030403030c02010302121008010c 70
    0x4065801c55001401044151403000440d0300000c18190f000c14540d5001c4000307120041c0c22107400c418042c550100380301c01039061058401900e407950007407025062030f0f5811542c032004a810403040107419007000c40040c405410010601d5a0540d00b88609100f185200d51907250380c0c0c54082c0b1024002d40c48100c5c1219a028440c101d404410031281b55803119103200c1e070750754060884010561011068108603060032211140108000000382020301305001010b000c616030442c4250030000c052091108078141c06007101d00f02c80629265210140074140070a060040341d10300036010300c2c40419050f05010b03441d070040303103e00d400e96a45508042e0050411049001b054000b0f40000c00110060001034090401040412090000060750784041e500182d10750a00c0207003110307540814208c2981c106030402101c031440c400c0f600400240003008699980c1d81c002d610000d8200406180520b0941e406a4101c03044000c0000d41d6020915254540300c1c800c42c000c1c4a81c070000d61034035031984e250604c80c20 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 816184694 1250 816183444 816183461
    0x140708040f0312060b0d0501050310020c03120601110a050c0a1a0910110a0f021009080d0c06090804060509030d0302030702030a0c1109130c08010b0609102703020310 73
    0x2907403124404056182128404030100d00355030321542d140700103e003250a15002e0014203000380001b042940c140000d141c2071010701010900054010b003e000c100ca5008001d68025a05042410a031035a034000107c4484401d0113070303002140111110801403050100d0003180d00002940d50b05181565543d0302c038082581130b100701000e00ca0600034440d442c5001c0040003401c0900e484d0484007003c900d41620b007400035140c0200c80026000c5001c40450411505000260506050441519180030000c50301c2c1c00f4014107000420000d0805e113000c01200d50f2143e00101e8103c1c43d0103444c0c60311030501038510fa0148100e1740c0b10784521001e50070308500c80e000702c0b031040ca00345d4007079420903084c02406d0b520307074890803801c507051915664107040544600000a109210280170f030135060781142001c0c0c074002c180f6040400c1a0f41002c940c0c030001e841c1e00b000c45210381c40c1580c0d40031021900c224101c58071003010b0034050080d1f500404081d072811107070081205482c002c03015103501d0100581103004131007075403 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 816185944 1250 816184694 816184703
    0x80c1e0d08150109031e1209030209010b0304080715020d090c0e0a1505060d020903010c0e01170906040308180d09050103060b090a03030e0a0807031a1608040b1e040614070804 77
    0x820090002805125002c1c032621800400103800e0781c101d640340c801f0740120b2454400014802c09003002949040703200c00b4010101a02a240b45080a4a41d0110f46c810003001608401e0365405030080000c4603411103210814a12040111907003914010369010464230604010310441800f081051145215480d445800b1610420329140780c07100340130003904030041d02404507138240aa0151510280150891103600b9035588203110740301000504a4090718400608000c00c941c00c0018490300003450a400c84c2c0c05003008000d039942d1802641c10500111409a000d004030190300b010140c00044142c203a603001d0b2014001307141c6480f00c2c1c403020300403000070980c0b21071141c01c200082400f0740000682745001174100401c2c66124403449180541c9503000301c5100382007400c9016900c030641545600700340711661541c8108903080d00100849000341c000b920100c865030225078400005c42901d288440c030328030010420300d41418102d0007840c016004c643c010142c0400100b000e44950902403245500 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 816187050 1106 816185944 816185957
    0x70c150212070c0b0f190207091a010e1323041506030305031504020405040e060a0605030609151005061614031303080c1e0d081501 58
    0x207000e0211103200041c005803001880880c00e00088407107403100079032204850100e8424a100c3c1c03401c0b1b903071420041c0d0302d0307403078140d8012820300c0071207004510403c02144982e02c1c01f4102c18060b01064000f40704500d404440e0300e000d42e40e00b400c180945c080060b41070000454001e080e28907010041508038407008100400c07040703810454003500380b9482404980e10b07580d40a042804090502500c50381d0b82038002e6010740740e60f41a200106801401071080340200c1e05000c0d2212010703500580524181704000c00d541c14001a80b40c05422110010078486548040301e00784540f01611110081d200c804c0001103564410000d40701040c0100302c008844442417400c0b403e1041203c5d0840c55940040c00031005107035100040c7e4007200d41000d040759072040203040aa0a0226400a0004849280c0d203946100100001c1e0800e0380e170710329120284540c550700080110450400591400030f120b = true := by decide +kernel

theorem cover : BRFrame.Cov 816007194 816187050 := by
  have h0 := BRFrame.cov_init 816007194
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816007194 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 816007194 ≤ n) (h2 : n < 816187050) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
