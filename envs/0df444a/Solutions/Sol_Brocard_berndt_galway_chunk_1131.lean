-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1131
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:22:35.775986+00:00
-- url     : https://prove2.me/submissions/a6880190-08be-4e4f-8e21-2d704e53277f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 203237410 ≤ n < 203417266 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 203238660 1250 203237410 203237443
    0x705011404030806030a080f1b0307050a031701050a090209030f100b030d08040203070618031704030215032514190f0c030f030b010c0206131a040605070609080903 72
    0x1c01050603406448036801240c11406081e0480c0349440d040e4060203407804c3c00412250009055142800381e0050303000002d690800d40c2d0300d504241c20120b031140200d02003540030800c40c40400203914164060a41a260000c1604002c4d40c14255040000c0d000000782d40d03018803d8000109000c4010000c05900180062020952203c40024103045ca02c041900000307014050f4103000052b036001c80c1342000d41c2c03864517110a000070148201b825842d000e40c0050240c40f10900c20200e10a4801c0040068a00a03940d6441300c0070f80b04000605171108549650f4001c214103010911840c80b1401400004414a0001d000c00d501840700012544512881c0540300560b0726002400f0b90450705d07a2000d002c0c03905007a1207818468401070326441002390282e04040e554514036400d40c1c01941000b14064000d0311540d2a000c81061280402c0f509002c0d00c000d102c1c22800250605001100b2078041d110a5a6024203003078080e0790700300c05005854012180c0c06d105111803402e5840030041d40600c45490314 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 203239910 1250 203238660 203238701
    0x16050c0105191b1b0c030b0405030a0306061115060613080703060b04140a0c0528020c040c1409360703050112030e0109030503030a06091802090708090102070501 71
    0x51140101c0741c00c4840d82d40034640d000d0000903000c3d0130001401d6003084100300110745440c1c0f460011203001d00c54100804580500b4140400d008000020b8110301d541d40d00c0802c181070b102c0d0b40c2910080010601d240403503000391918081110045500c03030b00007001600084c10a0404181e640700440c90f508009020b80c030462040042c05010b000300c88200d001610b04119003042d030020001c1c0f1007001080010080d8694030b0324140c8070702c184110b5801102c55400e29080c0c0040030a40000c00800141c0180184540010400c1ca490188100800309800d0b488034025400c4840c000b04454014603801580034800d00c0b2803405000c1c0c9050602e50600804000c7c014042d521a1030200c03c00000d0003100405203040018010404900e01142c0c00070b0301402c120241ea00c0c00710040b01c0c40c590541000f41a80800300070b00c00950825004141580c4486d5400d1001c0102180c01429405c02c0d40d1010358000003400110700800c0c010b801e5180c02c00c1c400400580703480e9540d150349081d01d020600e070394a0104c40c407 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 203241160 1250 203239910 203239951
    0xf0e0105060402130522150806090708030d110c070e0118020418020306030c13051504110f030c04080a08030117010504050604030813060921090b0316050c0105 70
    0x284109a07004404640c1103041c4141d4856001c503d162a015180c000e1880b4510030640c000008003c800030000c0100601a48041841d00c5a00c101d280c031400829209000c00308102d24400b04488050318141001182003070110000ca03c0986100050301059070000c210014048400f031103000c014007252140c0405952400c4c11100c91005010943c0748124410300040c052181601c00003a54001e49600243e00c0307803604c400190620000c030725060b50000800032041c10004040e0485440780c0003083e07429514031110428407050799000c0e4040e17107845c042041107504501000010396040202c100f413850401c0d4661480c1c0b0301d8030388440405c2e550b028011004024203004000b04402e40c0030b25800a010608041d52529514a00508001c050010034400030b101080e440442c1c0c2101c0360401c0003170240742054181000c900d02c60700c010345259824a10910000b50007a4000f0040b6407189081c0307855641e0703400c0c0c401152800f860ba02c500708801040b021004003c24000e01d030144201a082a030b0030041c5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 203242410 1250 203241160 203241163
    0x803030f071e02030703080411060c070302010e01030b0d021002160b09090a020903031c0e030d1e09050a030c210806010e030d050a140405040203040f031b0f240f0e 72
    0x141040c42c1c0c80e0305010300040d00c55a0302000381d651240d170500f000780361a191803601e2007449015245494000300042007a00c10203030001a1030f8100c9000ba25000c0780c08100d00011419503c1d00c07a00d09810181620300300006090048002032040818415198080881c1d141c0c00c014800d540d100c10844c105c00304e4a0700c82c916140842d143c001c4484072085140c03041c0e207004aa02c1e8015840821510039400381c40c04021100c5d600801020701040d01074950300c240d101c0b0520b0003840c840c09512032040d104401c5245510441c802d50007440c2d001b1008050b00b0702c0b140d6044900c00302c0350604950202580407400643e02c20f02c1a403200701c04658a0754881031522600041800c9001c081c0d00e40300340d101441c00c041c0140c0150440d1a07071701051500c8070a5040085003c030080c8140d52100e0b411a20002c1003009001c070034800c01e1070301e910907900c800080300c400c207040c80004200d64020f40448900c1c410000000c403940d2100390000c0d90380b1141c152601d40c04d4000301c01c0300c1144449980194690a202d042c4610 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 203243660 1250 203242410 203242427
    0xa0203041d010f0306021c0e030a09090b06030609090a0602030106110d03110f07020105070b090105100b030705040e0a1503052103090a060b03070f09020d060506070302060606090a0803030f07 84
    0x1200402107000d40c58040b8040070040c0c14070018003001e600040e038203000640b51074001c0780108051418003400100902030b55482e4449804000003900014000c80e1b145501d01403a00340200080c102c50031500c5040400c0045c0f40e000d0300c151001d10803002d1040005810740040d40c02003110b91036912444000c10059410010340d80110707000c040c9000c4010005029040603038201c071003100000c607180c040502c010303542481551000360100c5590b2080010f041c03815000244186d0311882f0b600c62182e034651441c071042c0029120300b00401c3c81400140045051080b01c070340c1c40103a0740d03404105803003100c42100d0240001c0e08281c2d019017141c0100690b043c1c0101d00314010000400245245250114520b07807a00036440c4020a00d58032030400080c245c0c3c041195034094081d40d0156038034955680701000003540702d040000d43c10340c00c080000074585800e00c04e1750201609500a00740d039985038010400641e0114030183d070712140032480856840d40800c041c41c85aa541640b2000c98140500f02515528 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 203244910 1250 203243660 203243699
    0x209061914090106080708071b0b0f06030c0d1703130609050d021603170a111614040b0f040b0a090204060507020f1020101118030d050f0c0708030a020304 68
    0x2102c014002c4a0382d12001a07603000c2800e19100270303004410041c90241c0a07042d03001034000c151917001c0c03180d19000c0740b45190144008030300310750b0401d40602c00d0080000358a40c001c1c10702d0200d44040d000080404005640c007400c681001d14100100e0342d113040403140010425101e0ba8450704000e50302c2c0360100100182181c2c011910001c0d10310f155a1414002500700f8004401c5c140070804020446c0500f0307400035190800d505560140c96100b0f00c44180600f54070450401e00b104800340c080030305280c41040c3c9200400b50000090f0a041c5042c48083d241900566400440707481000a07a524144040c1020340b41681d2203523650301550041202d0340280e030310703014815106444031301102a00305540f0600e40c0d00040b003940c4010b0044040c00e007000b030382008051100d81030200100004100070008c100140c2012814ae5036010b91505059842c038202c19038001050040000c0d6041d20420b102420f003604600301111899034071840100c5c150340244400b040964030215040c0a452145401c1c0d0718541c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 203246160 1250 203244910 203244917
    0xa05060f370f1214010c080727150915030c030b0306010f0e040f06050412020105150a14030f070f081902010804030f02210a020c010212070209061914090106 69
    0x294180032400c070300d0720b07a10310901035800c034815841c00402c54600d0384240a00e00d01d00c000c21000000307030005000f183c030841f404c00000706088107002c150f03a040000e405083e510740d0064030303e5608041c942203031a4012104942840090319000824940b004540328032900e1565002c0303041c40c048000036054030ba240c2c214902c2034112800600141c2e040814a0045500c40c107084030710780d21141000076981c0c481c400d0203041da81c1040f003000144a004400e000200144e68000c221070303510a15a481d801d00704205280d802484036600304442800c1c012000e100150040650304000e0729004218900301343c40d4031290b490840d108041140c01400d21500308580c00108015115142a13030008041032801400203042c040081e5081e00c1042c0308100586001c01c041d1100c4a41c1107900140b000d030341e0800c509840041c810090140e949501c08a009407024a40120032818000307290300300004c10304004c0201c0e8100c052180c8030100d9100f1003100c40c00501c592041c042e0704015070001d00c1003880050b0444c7d02032 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 203247410 1250 203246160 203246269
    0x61e060903020603060d020d060603031d121203060102120301080c0406060809072306070308061c031403041a0711010c0f080a0e070519050a060806090a05060f 70
    0x581c5800701240e41c412070886d04604920720301c2c0300080c00301002810103071416103000d0000c010190403024a9100c020a20390540c05003691404128201710312540b12101900a07031070004be60041a006175420030360500640d00e20310b14504c0700c07040355002603100300d041358070080800a9a00b0144501009012107141c0020300e031600035551595180c0034441c29101d075200e14003c4400c012210144500724074024010f940d60211307400c00038540390040c0c5020b480b400411344096140b03002c85a130312003034613130540f10340f0030310900b1203100d6406800c0184241d4261a21040c1c01505610303001445118450b03540703440002c01c0212602600b19405441c000f01441170f9415840e20454108400941c003007808040842c035806045503840c14446d89510040e04222805690780010905640c0310040e202c0c15541d5134a91550740c0340072030700e1b46c5051f55510f420650090114410b140581c104c117900c200c01414584840201001040c3d10038501040c42d500030114602e40b00766000352102c3c02c000544403100c030034034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 203248660 1250 203247410 203247413
    0xc020111130e0105010c1a04030e12031803060105010f0309020409060612050f06130213060b0406201207021e09040804030308060d1e052814031602010e01020a06061e060903 76
    0xc03c00402e41314080c07803507c040f00103810503115118a031144e480c054005107001d09400003140d9650800da0062107100d0701141c2c038002074100059102d040b40e00581d903242d0304004041d0160014019004240c0c0c100d510303079619101040b594040d0500800d08607940080301c003c241851414a41c5156956070315030000814400344050000103d419142c04840d07206815014000b5000101003d0740189a00b220108000600a400c0b18807446960010340700041100041000d007501c690303940d4552281d804060081c4405428900d0020414000c0000321008a40d0804005100320200303c0d002c8a400100040600030507910010454001c070042d1f03a09001b0baa240d0360b45103c1d11032102111a44003034001540030a110041206810300401424400d0b110003803100c4112107128400030580750000070841030f0030140800421070340040f540100e44c0125400325801103c508024074041811442141c2000c00400c100d8411b4400030480301d0501ea140e0040814095404106036100c0b5043c040701c183d0400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 203249910 1250 203248660 203248673
    0xf12090d0206092101050a180512130e190605030d020d0809030904050411030f120711040b03190b0c0a02210f0a0c05120f0a030c020111130e0105010c 66
    0x600303941111125150003c81e80410103002c5551400f0490801040301003680400641c4218059102902c05200080c0c85104a10f05000110303001880d82d448100081039a001020107001c031231021400f0711800607500c0d00c251030306280544d4900000c070129024140c90005611075140240b2042d4040e0100602240c000b944480b904c42e0054280001c0030005a41140180b04482003524018000c002600346400e0000b44510060681c901174440c02200c458284000102114841d840303d00480c03a008051b40c400039240b408407805500640c5443c51240700740e0b0184085240304110441d031007400e007814107000200c810060000c0781640e07010400d5481c02540032545961f40c0102105030325014000e5801016640700c1e126020b000030102090604010354407006902100340510120350504da042448101c141c450032051110dd041d040184a558a020f50003440c0c3c0041c0d41c0c000000c9403010707482c442c506540b206901010b41000314406118040c2e05011690241c0750038a0505a98150390b034440 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 203251160 1250 203249910 203249929
    0x100b040908071103030d06120209100513181e11010e010c030c02030c060301080607030c05040501050702010c030909060b0705011109030322050301020a0e0f120d0c0c030c03050f1209 80
    0x707415100328010380d0326035440800866446540050040000700c0d40c1e00141d8123a40c12492003240301c0c035149008030f400c1681c5600c9600548000400500030304155440d524010250b198003801100d4140c00c7c2c440c007040f82100741c3c601c0409071050901a0400c2444d00c05800e8620031252810320002038041c20700c50340d100c4492800e060b03041c00c080c00503440e6800001d24191000c8040d0703078401c0c1c0000010a038040e003c40d5050069119071428020344000ca50207076034034002e501403035000600c00c0c403444000d50f215a1174100c02e5402403c0c00da020f0b030340762201c00007034502682080c00840303c0041e1800070013000344a804410a2441011410503842c0e000094591084443c401c2100c03019450401c502d2806101364402031600074021540d6000c1840040c08103414411038078400c0c80c5e405c0060b041803d0401d40110811410380150580c00d150f02030a1b5583e185180c425201000784180200000f2045402280914081c00c000c008071485a40d49502c2d0104044001c089031000384490308858032600b246 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 203252410 1250 203251160 203251163
    0x1c09080d2a03050f0903030403080f1201060201050103020310111603050a1d090411030f010f0b01080c07150c030e12030108070506070506060402030613230702070315050604110309100b04090807 85
    0x64545c0e80080c00002072450240ba08041c142c0303030000801c1000b164600000308014415141140410381e40c441c416401c071442444040e4150700403000d89440d071402a48014600b814491210f81807160003040603c0a05204404030003103070340001d07194184c54001680300840c1e02c810711038241032880c40c0d003c2000c40101801c01450b901440c2d84486135598144041c0c141c841200c0001c022603040c2d1000400901000012180801c069201242451280004541e03e0035002001e034191105050b01c40c400908003e48020704241e40c43d4402c0103501c07404d20002c0d0400e40c80007030491301da5042c030b4072890810426030703c902e104140401803c1c000031030108807139a1180d4120384c0107842c0e9852902150101d1507503c6201242803070900c60070b103a40c0d480c01d40e40c002c60346c0d2a80800c038542e80f55001a40d42d140c460102900200c020f010a000562081d00651350042010304003103140c1c0ca00c42d21580080e0000d0b43c0103280d81c4c0011841104100c0d040c803a485903401c08a5060020b00c00580302c0c501940b040c03040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 203253660 1250 203252410 203252437
    0x14040f090906060e070e040501060c03080f070e0d08180301020c0a0f2301051e072304050d050304091a06090418021c060b0a081c09080d2a0305 63
    0x1458428445250301c07039002003005000c2c040d0149842c0c5c100914044111222a03c180e18090020400c80c1c42210185503443e072640f64000d00d81c603076007004030204000400d60b4081011480d88188140c94201003000d08138400c80c480ca4881c4050548041c581d044000400c0c00380c4e20500200043c20f5000400c41c440e41e4000c401461000030f141010b0460f90010a0003034500c0001003903d00ca608030542c40980b1810303014188001c1c0c01d00161002c0c0054400755816000103200300c080700b80c000011001041041c6001000a01e01550b030408904c150894031800d441a03000401d041014049501802c1001408425451400c1c060840010040c1c002c02d600140240c0e5603000d50003128002c3d00520300c01640040100203014800ca50700ba55038034404030300301c40e101e0401d58114118100440c080058906c8400034122a008121101c1948003a8001d202d04112900d5400030740c9a50501c2480054070003590b80d0141c042160911042d0b05650240e4a0740380d07104142c40c000030950080645100207070164 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 203254910 1250 203253660 203253671
    0x2030d030b1c0f080f0409050711010e0718020d020d0507080103050f060106021f0e010e2d0c010503070c0803090606010807080f010b0c101b092102040203180d020d14040f09 76
    0x1e82100300d029a410280c03000d45081c080c27010240d044031036092403d103135400030b20200055070380c89030f10b4544074030890802c41c030070440e2502c0103002c0d0380182c00b1640259000500381803008101030140c40b400e0700d1704004550000014070070312a050204000c844400e80c000e2803203500d49a8020340e40c503403541d0302c4807200a407140c82202c0c0311803680100d000c40440500911809000050303803501c401c6503030003100035102d41c030700e03600710310000341501ca10341d114403001071700c400840c10005444c0c641c0010040c034200422450341c00c00248000010750f000b80000030081115241c01c0001412034140509201c1c20311017a03004210610030030384d407801d05484403100310030b03160000d19054501c0e01c007a071420030980700e080620300201200e5100390402c03821a15600c680c1000d07036411284c0f0648490000101840c24200066409810303e41c00841e0040c00c0d01002ca81600d400f85001420302440d00f208800581004510385006940502100340d03010a141110780350603c2e10000303020000d0b580c032a600380c840d21a07 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 203256160 1250 203254910 203254927
    0x30e040b12010f050718030209040203011104090203010509010504181b05030d0305060307120b070c1104061d31080d06060f030e0102031b130302030d030b1c0f08 71
    0x98100c4405080d01070304400e98012032250700c9000e001c106543c0d103045458880003c60030740c40b038401121807401404401d1105400c580a100c16144000c1c4143e80540d200c41d00b021500d01a54001e1005219800e001600d80d4100420400c8091040e0300441c4600d00704001c0761030300d00000c0c1c49800410340c01100c1d0202500d00f0003022541d002070707900c4207901d4058203110008140e01a00082d115000840548050303948458618007002c0b4100800f40492407958001902c0c03e000303142100c0c103240160240208444840001001c1e41e410f0b0700004041a00208018106400c1110745074103c20f00700d540c181c5c0303c80d0701c1d6210588012540c0c428216506140d1b0a4428080760000311842d80b080000c00307200745a2111406010f0750b00d100e40354030006e8035026402ca41000188296070042c11104d80425188259000d50410b0340c1024603400d0b0380d4101500e00000607179040009000c00100c0391800b0803002c8100041009840240040194004031551404002144502903400e030ba940500c0c6e42d504d5501c1c4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 203257410 1250 203256160 203256169
    0x10b0711040603021f0903120509030f120a0f030b1e0f010e100c150e07030218070519050c0f01060f0b040302060a18230a09140601030b030109080708040509010611030304030e 77
    0x11f41c0c0003400004815071440320f0f0a601100620045105034110f610800341c1e451419030351031940c01d1010b241d181c1880f00c15030951284c21501c4400c41135140c08200b40f020130001413050119440d818280c814640100616801c018140c01007450313007403c1107515501c2071008030359003e035070014120410080030148c0080010031000c02542c22400b54081042e400141c0300a0f45e80c850501080c1d10420307990a504e48407810110039548109443d58946003402c0b0443e41c4813800600c0b269100003448418850008200700030820302030060600130002c201180f4144c020780f4801003542000c6001d800412040c00503868800171140045000c2c0b40031506032948591107074a82e2015003002c104030942d20009410b40340c08421b0030b0002c08080700d650100e80c5c0d54070603103402c0b1001c000752104035219080008802c0d40c0a98017080b040300c1c0140001c2141e55140e607400682d40e000301d2045645001c04501400305082207040507016003a00d05020050b0036a04c1c4405903a804004e0004042080c0d46415020603201c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 203258660 1250 203257410 203257427
    0x20f1213030b090601171c081b19140901140327060403020c0d23030c030a020a05010c03050103030c0f0204020403020a4e05070509010b0711040603021f 67
    0x200503440001500f440382499888220a12442c1c010010f09045d000401c400810004c0a4240b03202d110000c0032460ba5007642c180c20018001f0100c00c0c103c1d8500302c00d83c4082e900070054001c00c48042c100c00c19248030041c0824504285001d01640c080c4200300f882d0340c01c1580c607103920083c080795035100c5d80d801c030942c0000b015840d0340c510680e4030180d1b02440b461001401e40e004510036001c1e161900d1019091107140803000001a1003070b900c002c1d41125002c0d4a002c894106144038040d02e241400162525185a003c800b034000103a0243d40f180701482007c1c40744400405052030140895403440d2001048007911000142402020f145a882150740c0d03941194000d56000d40490f080315903880ca50071000010038548211a0049146010031b000d642809400c1c21180141100e01d55800c0403140e00710842c1650111001e101d02c14002c00c2035500c400c1c9050003040d41d00180f030b565440c40d01d00303040c100404d40c03c09170103a4100482440140d171a40008843c0c001103840f00c4110040c2e10300e08030f84010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 203259910 1250 203258660 203258663
    0x120901150b07060506180f04141b030c09040c05011d03010f02030a0e010b01050d0b01021509030406090816050f03010b0d060218030a020607060b011404081c020f121303 74
    0x86403540011822581805050342c280622010042a1344004c1072100d00c0c140e45010005083e9080001920040340500c40341c7c1003406250708201c811412095285491200840c4a80c4a0069901403000b441d01300300c965600d100c2969241c80c0b0341010358130103030070b02628015941440000d1444007801100348010a44815005000340001c41c00c00020310000d500c1030340d200c000141014908001c0320700500840b4000c1c0c0060351141d10f403038079107001c40000300754400750207045001c0c02070f01c8400303003089100c0140109202c1b409035a55518000b0050300007041a400740b2155004015401d04d01010701040a0440e2410b603400241450102c0019004150754101d195200f04c40c0c4d00c40006101e050f80c060030382051800c45444503840c3c41000c143da102c0540740005d40c00a001c000c2c0d10001340003a00108034004040c1000c500030308246010030030940154000c105540c1c441611844428000320001090700024000b600002401c0c1001079202c0c840300f45024400b100024044404018400b5401c0055 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 203261160 1250 203259910 203259941
    0x30403030e1f080601080112020a1e0812090103240e040f1a07110a02091f0518060901060311090d05120a03090b0105030303010f03060906060909050d03150b120901 72
    0x25540c580c030150601c0f030309540290000d580040081000c00502104400c51034009018039240c500c0c3c40d17102508444101c0c0c0d50500070180040000d03100f01c0800c4400b1803064042c22068841c035001c40014216502000100990007954541c504443c0010403400166a4110b0780c111066841d414024080f012145005280c1101100e02c000d0780300500f0000c5009102c0c603070702d128040f01c480c0030803036860341c041c03802a6002c120710002c62908200d045d04242011905400911036a076140001080d507403885005034050f02c040020010f16142c507400341030140056050412031706400d800450100e0080ca0307140b5010f40145890300040c0701082110034513001d40c0701c000035540d07802d5102c010050170980d642101e00120010010542c1d01d004001e49041c1e40014482c00c107510700c1c1da00c840b0003403c16542d060700d2031540c544000c20b01c1501070280090890181c0c00520901203080f4004080b140e110490013000103580c0001d02c0303503070020340480354040800d012030083c50f00c40c00c4580f80104803c9a80300b009 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 203262410 1250 203261160 203261209
    0xb0f0a0e060f060d2301060504050105031306181b0303050703081021050709060602061f031b05030d020a020f040209040b030604060905150c040306091e0507090e010e030403030e 78
    0x1100404c0e08111542114a1131031742c800360618105401d480c0c020b014071408214140710038026540300300d015541c020740e413800620b4421142d8486c41c3c2100c0101c4044501540702000d150217220301d169424103101640b00300f00070070924589000705940105440203040165920210304040e0600da50381c0d025003040401e58040c01818010304807a0111610b080f1040c0c0100303400042c148210784101d030308a4080ba0090301041d540c01c07000951441d090b071140036422403510001310102d518100c07000c10002c1e5003003019038403034140400c0510780040549a07200710f50002c2c07013007401130b2964485001240d01c1070b0303809600c0341e941c0e0300000c0c003a007031000e405505031040104101c107001150b0403024800d40901c050b900c43d55080015081c409004442c8440d240c413007080200b00248084e030003115013600602c03c91080d10420380c000240c1400552090f951a80318180070b0054111900c41d403000d5500b01002040084041000c0302d40b02c2c011448094148021000000100d448403118031082182c090b41d901c14 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 203263660 1250 203262410 203262427
    0x3020105090904062a02012315010c0503030c0702041406010f110a0b090c010e12060f07050d020304060b090702070f03080903071205060f1e0411060c0307080d0b0f0a0e060f06 77
    0x1d44642c11151707400541c02c1038042032501c3c452980d803c1950700f0128034003c6541c0e50385201760341f0440f00b896490402500821042c0411410310286005200602c1199902d03e224010002a241110003121140d406181440410380e00100501c01c0c106a509014600c481001d0b00b82c1d040c102100b00140509507280200071001801081c191100403007600d84e220060070000a12600d021600d48003201070b4041d20102d07009400c0c0c40607440e8020404d290051800c40758007441c0e02a80c00c260760131079956444401d910054501b141e400b40c3e00144620041c04444c3c036041c891101c2c100188400703458000c001440c44e9450f00c1c14803100000d0242c0008041d100c1e042490300550f01c3d041160184490030307204010802d05c400070810200d10141c008120300c05034580341c076010303805481404441d501c07803000c10440400c800148050940c0b06d01411000f40c6845001e42c0050940c1c000d400c040e8410a95007000f4512980c58186881c1594012104100382d40d80300404030340c021a2960b443c980c0280042100070 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 203264910 1250 203263660 203263721
    0x319030e0a030e1206010608070e0d0c080c01030606050c101e140a111e0a0201090203070f0f050306060319061509062c130f0803010b0406180302010509090406 70
    0x3c8482d80192680c04981d80754503076031a22490207003e0100055000b9010403030280c07142d0250901a40c0040c440c1039101e64642e11800b1220340c650000c0130b40d801c048154110b80d81c040c03044100402c07040c100310345040201056240c5074020b24107800170b826034403043d080a40c000106a2450b880000328100b01c90450300d42e90f8445000212440c50007d410200d800c032090a03400c0503101006840d010742e03c408801d403014200e640d080a041c00c011503580719500805070341c0820400000300318001c041060142041d6607251510a10780105001360b21120074464561000600c1c0702c110f1521030280e9186625510700310b00901000340c10700b4150200c060700402e5181e2a948540111500407105045c0b030003145a2502e48620021985694586244001070301c600120000421840c89840c6441c0e150707500b03558940b02908281c100b00c0710407401080600c156034100e280518074000b112042c450b11031a5038002000c51040982d0503000304c44200200b4108003568015150a09020101104805142c1d0702107 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 203266160 1250 203264910 203264927
    0xc0109080a091e060c0305031801092001030905030d110417071701050f06040e031c0b03060106020a05120a050f0a0f0905040608060c0c0f0d030e0c060c0319030e0a03 73
    0x301c44809005001240f00501c1003003821115a0749682400c1086514140d445400081002c600410120f029842541c403c0c8100003e0b14400d405900d50503801900150950354100100b50501d46454240c001013040002501c01410002c08085807141000603e200540103991144400045085000004c160040307805800d03030701d40003170107c1c24440c00c0116a090f5501540c844000c0000030307002c203e0718142508061800b0240d2002c0742d103041c03201c1a135801c3d03020303110450b00c8105503591603040e030a1a00340012401029584028582154a0f4840d562180102c80c18107051145c00140303000843d018109940c20620781c0700e025910303518501c402520542d815140700e0001131090102143c185040c1c0f040005950b1071710028042651058600700c2ca540c81200d00c06454401c80010102e051001c003d00300e0b00200564002c24803402c4002c3d5186405000800d15201d80c0d024010807010715400400d40d252001110307004403d207810050b0070b4000704000c25000755075008600c007030418590030034046c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 203267410 1250 203266160 203266169
    0x106020f06070806100c170d020c0606040207240b0d14060a020408100b0315090a03030c050a05070609020a090203010f0f050f01021504060b130c0e0a050f060c0109080a09 75
    0x2070301d507141d40300310088440441c21a4050340c86540d041e4101031342032080e40e01e540a00d100f060707602108452403112003e46c0c0c00c50403d4010498001482e04090101445100d401c05400d9400f90b04004107a40d4880104000140d01c20f030710341c0b82171500104074100e904640c901c0c40001c0c10f01d0300800d01c0781c00c154420904001c5001010300c03520380850503801051080b24100c5440358007030070241c2c40511404000d04940d0580c207606100b0121540422080519842e004040e42c078010880414a0720b4080e06544c070340c5007603a0510106000450546401108071241c503a848540080c82514501c000340c05031281c0d40049069920210002c5010422400c1034019980b06070004840ca554560402c06a024080251030040c0c0000c104200c1c5070007502c0c04980c10511440c004101c6c2040500450884000c03910701000d041e8469141f808002d40060001240e4042510345403c01c1c0d0034040400c55004a0f626001c0c0603000004d06c0340e1105000794828080c0503488a040740d17881604001c018a83c0c1518041d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 203268660 1250 203267410 203267413
    0x80901021c09051902010e010f0306080106060e120a080403020919050c1e03090318150c0102070c0905040b0f0c120f101203080a050705070f050714061303110a0e0106020f 75
    0x440c1113590b44c12044620480c1c2d8169038102e072004914004480511044581c3d03010b00d511104003080e401c1081c06400d000d045540d8410b040048090100851117901d8602c1c1d4007070781c000b0101ea102060101c0100d03001e1342d8041c3c1d480841d0361590f0318055079000310b150042c541140b4140c01d01121040f448010000201d0388002d0210350300d003118001c41248030644da1a80c00c2e81c01040001c24640c011011a80131810041c000040180070b80d014008507808402402826540041c1400400ca031418100014010120703040015240aa4411203a03402c0a0283c109084102000440d0480d0b01c07c1103825504c01d04a01009034104400408005801626509441060010007040c6450f000703a41680054250351400500c0d200d0601c990002c00e000b0b4400810464200190004a644c612403d80124410340040c08050724045030640101e4244822030301c00c0e0350403c01104a1b6030b600d00c170f8009494200943d4080b50500c02c1c00034160001c19841078a011a0601c000964642c0124883c00042c24010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 203269910 1250 203268660 203268673
    0x170c01140627040b07020a0c06050a1e200c0402040b03040212010c08070305040f0605040506060f030d02101505120607020d02010209102001050a020405011205070906080901021c0905 80
    0x18800003403480b2603060303140100051001401203240e00e040d4580081450041d00c220b00f195454881140040b0703003066010403400109002c0040d48007210408800c50070707492421080c504100202020380c203154000700c46515100c005030110082c08408071508004000315920b41d51050a8403454201700d03000e034030441c22962000c00001043c015403c0ba6011543c44050f03995030000150010100a07000b51450542d440c000c00c00034074541704442c06140100c00400c0a45400c10030401d032101c4050302d1a000b07400200b5907140303003900015105c86100d48544082425810355005504c02201940425884100030045801c00540480c645016000355400d44d070500c841548242e00307034425201c0007a000201500d8101d1150701c1b0707152411947d10b10890100700c81101c00101800c1d50400c0d03d10074003850340020100303e29a003141a0b002d12294125081c0018640200003405090040c4100c80c244030190000034840d440030760403070300c4c2120030140c1d2880c542ca0403809a0014404c03500101c03128800c08 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 203271160 1250 203269910 203269939
    0xa0b0609010b0405060a0e03010507030509011d100b0303070515070f050909010e09100507030c09061e11120c070501030e0c030703021c02041e15080a170c011406 71
    0x103058181c162540703002e449182c5880c1000b404246e40c040c1c0c001e0000c02c01c105850001e640c0d020f00a440c0222101d980200701070502a118900315112001070714003040404020f50070f081c0000c1507181903440490f100050710414040468150f10903128000c1c07050040454910594200013440c07402003203540d440071801542e09005617528401c60075055406205640100550205010380d998000e1000003514400c19500c000201a00d00581c0c9a801103034030b40903007a0106500000c401c00800451800b40d522044c00300100c0b030a41c281a141c4c0e4200520040d006001c98004c10265a25682003000c1a540b00da00e40041900d83d500c5004d650700207414500310701d40006e4002202d407100c8000502518080b0304d19400c0248055040c000241c120703001c1813806000d07941c3c40c854000501c403195580e0714124038910003e400c451810243c0581306c00d00c0e01080c820707014006800c0100c02c2c0c1c485140d280b90b0994051401c50b0b4007400c010b030505036013003000c03922061440f1411207003c1c5c50244c0e22007000e0b0860 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 203272410 1250 203271160 203271169
    0x1220070b0615040b130e091c0e010c30050d0606030902060315210a150203100e1308040603020a0212031513060b190905030601050906091905090a0b06 66
    0x340e000c030000e08052006001848090005202800700000705c0000242d803241d039440203d0084442540c1ea0304840e80d040b85c1d14600c808000c151075403601d0f01c04001841c00c0000b800703c500110b0b016110031854400711400b4488612080e01119003024080d02260b24010001c01c10f61007007800110290602c203000400318020300034072405a0340100401d085a44140900b15048002e0100c503910116040021600481c000010001c10950001500320740409092403104a00054002d4833814410000c204c00c02c10038400306020388030400011403807621040300070445130840c11409802d14000050004442c0d03050780c018984d44045400341c0d00403643c544010b8485000881e11104e2280d128420050350345400c5100019580030710b580011103580302c1d0401041c68000109800c0e0301e0000130051020a41c011b910b40303008101c210002c008641c14500441d40c080c4010303103983d00540525000c10003446c40c1d02c600503800f03011100c00300014501000344075a64040304000b070302d500c6080ca010800714140b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 203273660 1250 203272410 203272429
    0x15071b0609030312052a0a1812080a0c150501050f030d0801090e010f0603060b120604030504051e030d050301150504050307051233070309121220070b06 67
    0x1c154541c00d00e09410a800c1c1405405e0040c400c00c002c5000d141950440c80c078900c0c102c004e41480002c6984c6800c81200043c081c070030507158041c0030304103560302040034040d1524000b00060780040c0c0c0e030341c840350251000ea403451003412004096040300040c91442c5001c1e0707442241201c00407a0242074070341490007071507114071203518220001000c0300014008000b80d034100d0349101e9940c3c0c00004401501e2131044040320311941080310b2035510350740180c00f149040c02148494807038030b1010b0221400c250303501410340d1166105442c006c10700340809150b00c58001e940400302000140a50f00b8042d02410002e02a5000740110110401c0c0e13094218641032048060b0343c00d030f41c000340003090798034141010002d24a10300340b12020548140b201102400c420788a0b0300c11006449121144038441c500c441081e280300c02081101094908890200440c911800c112101e40c1d00d0306007031404000300c030040c0c3c014000c4060880258164803c0315460041504020a5140e000d481903040544904080140022 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 203274910 1250 203273660 203273663
    0x4030b1009051e07050c0601080d0e03150112020a03080d09060c0c0507030213060b1605010b18060108150301090809180c03011a12250f090306020915071b060903 71
    0x40011a20111003c1c0c03030800035412280b5424281d041c45200341400749401400d03044410303240c2041c007a20b10301a41091041c0c0900c0350444c0500141c140e40d6411705581c40c01403140b012a1803896421006548070007000c640070f1500403032041d50301d0f8080d2900b80041e042d0048119600b91800d00e060346a07520600f064514540d1100141c48100e19540130400990319054482c160107980307881c0014000f020710010060385003200000950798070039007040d508454180386000d02454000004012030700c202d19041d0350201003400c00da825900c6115210a8418010038241c4d0107600e0000d902c018010100060100f81c3d00490320001000002c4010110390807060b5800031281200f4001440030750745626521006a0002d0718250500c2c00b00041101038a4054843c0121540c540c07001c3c07191041841e2a8801c034165504001c108128040c800401c0307021544800391a80d50301007070f0302100b66142403004c0b0f2a9007070480d049132958483c0c14a0345200e54004158404c0c0001c2000000e0218020b904140c1201d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 203276160 1250 203274910 203274931
    0x303062d04020d020f030112030206010608070806040e010b060301090207060f02090a0b0a020102070f0311010f0509031c060509010e0f16020a0b150a030501021909030c060c0c090204030b100905 85
    0x11203940a000180d00100700e01c2c0381094091003241084d0b030001c0c018500a00520591005200384e6043c040d040c9401a000f901c200100c80d810007104603000884a608150140c0300007448401800e86c05004180e90a00203500c020004000a44800341c0d0b009803500900070603041000c00400350152040f4841c00150603080319510758200003900c0d650018114100003400050329009040d0381e406804412400300300c02060704002820a4040c0900c0750407444450061300b0000f03414164200c0e5906d00825000f003152038126a420a5100c010360400c90041001800803d802d50b16400321440e58441101d052011080f0300c0006002e5510070b44401c2c042e411150003400da800c16585402c5d10034031009000c2c02c142c250307520055010361a0100c04c00000c600138800141c850420352000700c3d030004a000850100140290180f003c41d144280950481d02e0034248503142d0304407850060110b1b030b06075020303443e160f101003000028081d160b1045481003503c03a10f20b90000381c07902c0b80002100c40554591403207 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 203277410 1250 203276160 203276239
    0x60f2604032102040608190b012f030c03090117070909050c07051902091302012c030307051006051005090d03050c010c0201020903010b03030a050a05090409060608030306 75
    0x100b40541c0d080d07900308140340e2030500c1d0a4140203800080c1d0340302d5417120001685400c100720880c02050880d000004003001c051150030304400c0001c10f4000014242808500c03c402000c8004103002108101d004a5005880d160124103000e242c4a81101000c18081150186420340125010250a12078021911460b4009082448100082000504105155004214903404900100041c2468501d1444807c080c00460b1060105003000a0000c200d00c07040b03500c11600607a00110001c001e2002002c61001d08612024400c20b00704c840444540c040c040012075a0500801080d007211100c03c00205014456446d030a000c503c40c008a0007400141050140f07181754606038a2124019000e0729042e42810b503802e0030903007100d05074110100035030350004454141c1d050038051089a007130304801842c14080e240c04042c08a10440c400c0008101000440000541c2c50b0350082c030340d660300400b0030403038591a001819540d9000360340e40340c8940c00307400c4030421000003903811180b400303409076034845c4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 203278660 1250 203277410 203277413
    0x30108060712110403050303071409030a02060706020409050108100e1f0c09090f0f060b0f070b0709080d050304140a02031c02100f0b120c0a0e06010c0c060f2604 71
    0x494034145450400c2c016210b00411641c28500d0b0003a00246001c1d102541d034038240a500505003406142ea403a50010b420b010041d103d590105e5031207461501030700c0f21a565811460400001d100f5030700040d006610708400407505110010741d00403c2c403c030b03000411054108100b580e80c0c802a00200b0500c1d0741070861020141705031038000780c240140d1411310300c0c1501c0d02c800b02c01c81511041d0380c00b100e000b42d68182c182ca46011500411000304400b80165107401c00814100c0f520388600c140180c800c23510300e80424142481107000500808602c000e5880803001040010016030040c0d40039101c3c0c10108106446c1c40101042600c40a90300900800d10151906003c40050b8010440b15096004416450040c04494080c8181e00010328000040b800060400c0148500d906540e4454507406510704a8968540c10101f07415103141c02c1100c441a921140104c40c50030803540000c1994204c1074001508603001071341c0365002d10f110344401d00085165200507814518001c421840414040082030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 203279910 1250 203278660 203278667
    0x306070201021201030f1a011e1e0b0309030712030c09061701030201030c09170a0530090607020607030806040608030705060c0d0612111504050d0210031e1e020301080607 75
    0x2003403084901c00d0f0300e05228051030302c900c84264041ca1940c0c0d800403406041d03c49e00e050042c098011103101169000300302500c0c10459034240613200032403000101091146500300141d0b4071301503010003045245e50603200c008018100d0142c0301000314820140200e50980110b040c1000c100104088180c240c1c43c5800450180c5103c0c00c920b418400c8941000c540710305528079030710030f0400c1000180034042180c074025150044602c51a4000d030014080e04001c0b502c00d980000c0c4500042c0e1910f81c90342c10100008510303125142000350720000c0003c40d0030404d5085075840d44030b0b10b0200d80070400103646c0c0408645074420004008d0140c7c01c0300b8001038041190038040c00d596100940006902501d8040304002807001c10300580d0b20282001c2c03604220310f4003c02200010000141160400d49044042203000c81c6c0200001d1055006c0340d004044a8425030251100c000e20740c207814440c0c5009594140142040b01100840c424990b0400303444080c24001c41e03040700c10703100040005039512300c07089 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 203281160 1250 203279910 203279933
    0x504050c0a03270507180b091501031815060b09010203070201030504140a05060103050601140a0e0a09170c0c03160302010f0c020a030605010821091c051902030607020102120103 78
    0x40b15050780005a9a410007100c116545070369214100a0000b58101001e40040340301e40714020209506080e40c000c001d840c1d102311213401c2200048100310480c0d00d1303801a805060140c265044012800300b150b0309000d03c0280004059559030401c00c0640e8850740000d21510400d036006000d41c2c010400040154883d511207035219020b1904d125100c411030320384a0410b00985c030b085e20150720017001441841824003c6600400040f03503256680c05584c404255007051130f1007550040d40b0380340c0c000354400510b6004490f296502070f03140b000708101c0703150003500740d00720958402c801e2290400392842424002407c1c3c40c11403c2000078400c107443c0d5401100e284c40d07003541c00760400401c082d002006232034013109800518401e0501003070ba50304240c4c07000c0c9040509007502c1d001c0031141404003541074005084610490702901e06002e20103600c201030365000303421100208644074109400407241c1d08041d03c0c05810707100310281d8003680c981d0242242070f4010352002d101ca00c4c0e10308004000103407085000d07 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 203282410 1250 203281160 203281181
    0x220f050c0a11061b090d052e0b100507060e0105040503041a03011404050712090b04030f051e090301020c0f0303010f0b0309191401050f0103030801080f100509030717090108010504050c0a03 83
    0x1462a0200342c1d610039081c03444c4001c2c003c9000ca00d00071108c4000c2c1d41c01c412110205100035080260120305000584141b400b00c5501d014407600060080a001d00c6070401c0100b414030034028002030505203040d0f681c9a1161141c8056a580a500e106424019404580c125019072849400101101003004010080a441481070003582c2241c06a02c5085014500c3c1140c010100451246440e0402400d034811400d481020400104000610825594040c0e45068015200e09843e02c4484010a009114441e1035a034a8820074030b4084180340000010b50581d141c1102000000c2d540c2c16008072180002d581d03504450700f082c55100001b07607041880b04142d9019609804003c01001c6809084a000707654000072401d021005205040d0050321090040c02240000c0038111284080c040d01c40b50b03840d0f4980c0d1460b8403540450601101042943d0805402c100401c80a400400d10560705912060ba000d0102d09480c0c00015145000c1c0300b4a0300c10001d03001c0b014a0440310300400c4006140c5100c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 203283660 1250 203282410 203282419
    0x10020718020f0c06130b060406180905070f24020a050d030e030409050906070906020f0a0209130803010810050c04060c03050d24050306090c220f050c0a11061b09 71
    0x2c0c0f9000c1035410881c0b2070041c1049410710707070850a2410035007410700000342981d0142d42094410441e80005145c50074608114190000d105210b03403604508050b4158080702080c05a52030100750418410750165090114124103103129203842d10a986503248480b01500c1500a4101c4806c294029082001d0300e609a070141c1c2c0c40d00e501d440d1703200f08035a0241e401940316030010b4104111550010001009820349000400e4444484061141c0e10420214001d004280b2140440c00901c1100d501182c000d600481054a80d1f860700e12072666400c803201070081543c108000b00340030a07c0c403c2103034250b41b1140d84900c0800c0c0c031502c058545610400c01d800d50306aa880707130b030022584bd15815000c00a5074035107070980c56103407400301031034460090548061074016851580095841c4074803c800304040641c0c54508032500302050700100440f04050303401c4c900744001c000744500000010040910a603d61403000f80e81286000d50b21141181d8048001a500d0800905800140c010f407500410061 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 203284910 1250 203283660 203283667
    0x1050105071718090907050a18090b0906071d061e090d061b05040506070204051e09010b120f0601170a060e160e042006091e10020718020f 61
    0x100342280c0d64032000b0f812501c450700880112031440e01c0e00105400c041d00b0b0006048a0b401c00002440c140500d124100664514250301d100b1308001760401d50219800413140066494210712958031141c04803080030010b04848038034100f501091444400b1110701504650070b205500792000b0300e00315507040080e002e00050281d40500d55a51034072500c1c041c071442022030f144c0c605401001c40006001c40d250180b010500003072000da258501600c40c1c5a804484c007142d02d455203240d8903105081140300050300d40000707003080f09000781504000b0068900791405801070745012840380e2160707605100c450442d0072240041040040c10700204040c3d40448003610b007c6101c075a1280115600ca904000b8290058422417855480641d004c03401406500c404050604e4241d0700d002c00554602d0aa445001c0c101c0540405034070fa000c15180c0c4017070050000781107000300114440e10001c1000403903106446140c0380c1c1c03d05034030116403a021500741c00c041401f40c40e8a42c6401010f9001a4043c4e00d28a10a1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 203286160 1250 203284910 203284943
    0x9030a0c06060b0a180b0a0c0605061c080c0d14030f090304091a040c030e0a0f06140f060f040605031209150a09090e07032f0303030c0a0221030105010507 68
    0x62004100c6041c80d078171000b254107407455481480b10804d40c405003103103406210f455a0903030050048000f4503441740001031155241d000144811b210620030b000403140345a601010040d64000a240301d5100c1f0044030000c0819020840c0d166920088d00502c5c400d0510202e03207050f011000b03045d004020281a01e090a888030084001c0300c13400008003150140f03000654400b81440d01c180b100d4003000e45001e001d0000c2007401d035917a5441c8840004d00707148910081005000460780040782d030000405036000b4034100110303c0428207009840051080305020b80e110054541481040101c5801030098550701c04005154141c070340100b15082e4009401140c031000c40c024000c01040c401c10380c1d8841007041c0703040030180300441e401424100b080c0d50160308180081100c080c0d010141d80c00c040784588084031422020101e000c1048019a00740c44080f061003102d080120140541c5190740e400c40324800d01020303050426815084901399030031020001031043d944290000e1403414000c07802215040c40c003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 203287410 1250 203286160 203286179
    0x902090d140109170726190e1c03020115030b07110c040207060e19150f0e010606020601061805060708030702150702240f0109020a090306020d050604060e09030a0c0606 74
    0x400361500b8a51000144030030030011a1a6440d00d0054610341c41b8400c00d0008000c058107101300d05203004a108014440040340303100c1e080340c07a400ca40c0500045aa1582800d44a0a100341402e00320059400c0550640340d1080400c10803048a4000010304c2c100c0d00c440d80c054904201030201d0b51014064606140d04541300c40c001495036a02c41d8900007448001f162441d41001110b002c5803594030340c0d5410420100b90a8242c2c040d104c1c20005001850a6408082d040100454081840e02d542080b4001074034039008513106048800381e45070800e0340c50b00115800c510110501603071307a000d03106000c1d51022820303200c09564005d10038011129460202a500359461004a41080042e07110f9001c0d22000101c1c190b03080308020783c151800c801401d103500c0c0000b440e101401400e0780700b0b03408500441810b00c10400750000b950400400c540d14841d41c10344001800d01102c50070b000314100440090860080a105841007030400083c500703040801200f20349088100e00d055031029281d480c0130860400 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 203288660 1250 203287410 203287433
    0xb01091401032304020405090a08181807030b0f0117040803040c05030f2a010e0f0301060f0f140105030603030409050c0d06060c0606050907140c0f06041208010902090d140109 77
    0x144000f641c1c29031400b03104100549000030104c4640b500300ca0710742d6002403400c0c002c2d5480d00129002c4111007071840d2001c2056a28450100d5003407000190131311400a8040c0d00049142c203040d5070b2515548031003001035900702e030581c0758400200c032144002004600500065504180300e01040700c01c3e95950000686801e4814880c25150342084804c160a010b5801c0d03644070004200c507000e0801c0c0580c400107449107101900d00c0d4000c403042c0c0b814000a60342980910080c0c0407070382c07801407061780b0346858004210302d9000704010f402010312410155800f46040e2031080200030011860300b400c002c00d4801400300030f84180c0a5020500828207095207034006d20018007a030f80d072401403152a9041a206444280c0d100314003902d5000f0500190761b03441105000943c002440755a514580a11058600030000d210072090b030151400348020070a51a0413818000303450741d9414143d90322200080200d128050311503920401181342d00000518078080140100c000030700000c0c00c4078054032054100c10 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 203289910 1250 203288660 203288711
    0x130305070308220302090f04140706020d120501080c1005040b30090d0507050705040507020a0c08070605180609090a020301052b110d0804080a0309090b0109140103 72
    0x40b4007180794807801154601000d01d03601440c010303041981c61a000f10352061000703410043e600710a03070001001d001031007000092000308103044440d81a61440001e4680f40801d0030000020040403c8000b00c00c3c1601070079051703480344c1002c0c1c40310761002e2081007042c1480c0004071003408024400090030b0414203000e0f08481000002c00c10550303842455200c10a1340c088070002490350303884188a20102c0c00a409444101a410400c1c2d0380c40cc1c6041613071901c0345075404a6402800c0c03001300a800c2d50701040b100c110303a208030b2007000601c1d100c0b90b03403a4403519a400b0304000a0340500c128000384602840b07000c40444060040b910b0884503001023119142c0c02c640009620b60000010041414560301e011144004405a25044184a10342c1ca10131001004003400b1007094100c0c2c450a40d444400740e65030705e0b1b4850300507562513689404181c1c40d410250f1068005c6100b110002905044e00d0007800103042c03050792030306801c60805c1e0032481c01440700219a410541d039024948034480007040750503d4031 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 203291160 1250 203289910 203289923
    0xa110405091005100f0801021e0d0204080a0606030212060403020a0b06060d0e070303020c060f1e04051011010c110a02040e031b0a050c180a0209010e0d080711150f1303050703 77
    0x2c0d4142145c1c00c0c408845948000780d1a031040000e4035916803645e0098481c3d16a001c0e0203030f91135103a00394100c06800360350080882401580410020070050768409000c03240b081c0c642840200700680d83c0d503203960040318080c0c09600701c070260500007000341410f182c1c0210010542030038103964402400440d442d0440304200d0b0351018405109058040100b03008503031086034142d20707040f0310031402681406420000c0050394810b01401c04080f2850301940c025100c0a46200401213211a0041401e005401035440c254600310405c1c003032902c07840c940e1244008800060030081041d90902000b840307140710701440360005000200c1c0b40921038202503154000c020003080354007200d0402605040c000c2103002d220710000c2c801061444201c124441d40b0407031502d00140c50700c81d5403005842c40c0e501c2c04507090b031140711019164208060303400a8155a4001c0710ba80c902050000e052041090200981001e000703070034400c00c004199641c0c024000460814600d0003840c5d42c030b942d210303d000503941044812 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 203292410 1250 203291160 203291191
    0x130e041403031e040204090501140106080c07020901061b02120706090801020a02070314010207020d0b0a0e0a02010813031404031a2805060402130801020c010b01020a110405091005 79
    0x103008024a60040c90500903010714550f062090451102e440100580d030020f6141c07600143c150b503940c0c1d100a0700150064002d11a54502846c503a003826402d00030030000c0b600c5000401d40d12410b02c0c0a41c0c14641e4068201100c80c1d003440790960300344e0420ac101229088800c9941030050311131aa0985107901c890000b0a1007504002016040140540002a407a03105002408015a00007a81e0007180d42140384401c145804030352080c0684a65903002e504207503100101d0f02000800500750703100b03034119903040000c0e00c600c008894503880352802c040c2c000750700f000114408420301040519840d03c02d00b4410340034038400321588501e400c154030a642c824000030b084000c1d03000c0e041c0701c0c0b58806c4003100303129456a16070240d4111152200c0ca00814580d07030b000000c41544540d4100d4101c0014182501a540d031341704005401b03540724404003001542450501d007000d5000080440056074001c0d40440640100030501c002824020000586403040c208041c546d000c151254900601505465215 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 203293660 1250 203292410 203292413
    0x6030a0b041406150705060f04050313061806020a02010c0803060d0c09050901050f25050f0309070303020f121603140a050301051008040b0a0507021f050609061f0e0402130e04 77
    0x10701c59443d11211039564010080d680c006840402c41a61104001c9078408c00e80d151410910710b103001e401040c0c444071001d0f10005c0f131016000070079000c0c03440b403604070710603855143c1500300e80300c08503140024003040503c10003100041d040341c06940d0280d4050895440d0080035100c5031140c00c41c590080341555a984203200b01001c00f030141a03030103002c5641050040c10540c40503040640c10034000c60f049549031032216092849081126081c904003e80940c0ba424074030603540d110b02040c0300c12030261207000301040c3c401034041104a59901c1c4820000e00b8142100240300b08820040390032000c005202c1200d11460300450050700804011784e486a803070b5810001408101d0b13210104d140306024143c1c00b0080042c22485031b0350751084129201064649035000c00b6894400c3e07403106060031070700c6402c40c4505411a9400175114541c12a850100741d06d80500388804c04081c1155408143d54151300008500d01412499500040281c401441d1824543d000310034000340360441004091a00300303000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 203294910 1250 203293660 203293669
    0x230f061206120a0507060e041503050d120c0c02010c08041a13061715010207030b0106020d031b0c03051806120a0f0e0304090b03030f0304082701080606030a0b041406 73
    0x6181d805142c00034808000c854440c296681c01901c00c4900b0815072440c0c0180507151078112005240031803a60514494a0740b402d251100e0003004000001040b101801c0e030103506074001d4801c40602034440f03100d014442e0f0011518450285400d4851078420000040c07081034201c3e10900d0784480c201016210420300d00b0380000b1030f0450f801041004040b0b58100c05449010202a4110b403000710501881211500183c1c18041c0582c005032114400c00b00000d86680c001c6620b00c02a403595808100d03001c640c3d4030045481a02404000010315501180e4000900450060480005042c00b0310440c50845000403841c0c1e000c1051080000c186406000d180b0b2414010300200c01700104040c031120310552012030740c1340158450015038070b0b118a20624607813018000c80711107004030745401e44c0d20314050504100650241103d2704007018071841d0032400e110b03144000b5840c680144e4a554041e201c140030044c480c1c00207007601690035034960540c035403551b9910408000c0320380c004200403986400000c21 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 203296160 1250 203294910 203294929
    0x40806040c1409070516020301110c0c150403062c0a03120b1503070c170901020f0303130303021b031801030c0c020312071703040c03020a0609230f061206 68
    0x191410218841d80b02c60607942d2038902540304250389401c1d41c803142402800c40400803440000394040d4a4400710b6003000b180f000c001c2031084451401c60b01201c5d4400c0510040b09003014004540d10814001400018100e8010211203904a01042c0740c11076a210812114038804845500075030100b5004c10401d40c0080300d1592a58152800f040b0454280d4041824610329503c0d2100008000000030f0710180545e031505030494024118042c0d00b89001c08210055001e240118003511403406001000d20700001264421400c1c0f940305a01c0040e01e590a50213500541400140c00e0750150b07001c82650340810181c542d00702d55100d013085d081424030002d021a0600201d0004012081040d400540c50008107116401071000c200360380c40c6500d003040e601c1601002c581460315a0000140818001e070080030000f6030b4000ca0704080300300c1e80c46a055904065520400d0040c81ca030088501840031414003c4240700005070030320322226442000203883d03070321044003d8010b44005c000d20a0505101020 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 203297410 1250 203296160 203296169
    0x90f0204080d0f1e051603120c03150e0903180102150406050703050108030a0e010804020f0405010b070b01060309151509050115021903090510110d0e040c020106240302040b040806040c 81
    0x20120b200202184c0140030b4458550481d104041085081d42010700c01c0c14842d200ca10074580811540c82004c0004021b0462407403010b4201c4d00305040850565116520b06010b02c0100300214a003168055001c0a452005070f60070b41540510100702d842100d120242d03074426841a0000242c4bc0b8003140c0c05822644181c02040440d442800f68820480c0c0220440c49942001d0030800a00c0e1390350305c00a820901c0045000b074000b814800000b07041120180940381145c8200f5640131240c1c1c035244118101c0d0f0200c80007a01149603002200403c08990380100300444045481d05522611000b01c04250341c0207911110b40b5946030746417410196030600c50038108031108401010202070b40e450050100e1154000c1e28460911000b4605040c3d01030613030201c98000100c1079804124101001070a5501e801301030394011340c1480d650715800d503c1031144030282c40c0f6884c0ca12020701240012000420501c4140c82d040c180d00300b1001c00c20404440150004040c100d008140f02c2c0f40c2807038640403102d102d900 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 203298660 1250 203297410 203297447
    0xf01060909020705010b04091b080d0e0409050a0b0705180f0a090b1f050d050a02190302250b04051c0503010b0f0403080c07090506031501090f0204080d0f 68
    0x520055500c508428200c8803001d03800350b114606401c065004000ba8000954020700c0c2c5000c8a00300300d00b004900c1420205014040d800c9507030b032503200d5202c009125603040011048021031a641c9003d40c4041c0c0514028411643d41840544c1c8508400100342c0b116408100089942c0301800b006000c3c40305212000c0e204400d201440e1008074140b880039018404c0819210858541d00d80c941103030030640c1c20007007146486100b100d580d02402d40da0012540803c45814000000d000700c1c400e000b2644d00041003081c0100100e401c9004038020340008100360240b85201038051818240d41d4a126a21030207003951140c28146032509900d400740c4030126803400c0c1d507181c0064040c50f8001c400e482c11100c3c16100e207544e662855944801a12481d00002d00c085400b10720980c2c40d50001030b0703e070140c60700780c20100a81e0f182c40f8105690344101e4111503204003525001031180c12419040120b003201441d00250a040d1680045424800b00620010000302c50351102806c841d80144c0400c0031910400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 203299910 1250 203298660 203298691
    0x3020d150b01050403050c0f03010921030b010804080a110c06041e06080606030a1107080c03030601080a061202010c11060433090e040203070305030a02101406010203070b0907080105010306050609 86
    0x51b10b0545890141d90280d104aa4607406c1c0416070b1002c1d00f00c4115030b584248440020381e001d24041e0303460b1007a0300b9407000007071a0100883c0a540540034050140340c00c50941802d055900104a81c0403c9103241e89540c1e0044500b01d03445a00c40e54080d1016018141044952850044e0169808a500e0748100304200f0200c050010580b100011242c0013000c00740f0128060381c8204483c00c042c401c41c580108541c200080141159001101550140340244d0b0742c0c000030385911028405030381660050341541d209100d034120056005010207003045202d01901009080c3ca4030000d04580c01951021031498490002522807110103071880807001806020604501210000107000c00e40740d01030600980000f001182c2555030802c001c038011580329007265661035007048000c0d00c038a0b002880388043c5080c0044411000221801144103010681c015410480742c0c0d00c038280d401c2000344c40e0120310b004000020030704260a000b032a01a5000301e0300480e550810205103d000300c4020001004000180d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 203301160 1250 203299910 203299913
    0xa0b091308041e080a03030b011d092202030f0313120503030141010f03021e03040f050f0307110f0a03060203182d1f110403020d150b01050403 63
    0x181c1624261801880c112030f014102445107a40d092240e040400c4a11a403001c5c3d404056064102c000c8801c0283da404941c00c03100262401c040c0d00f8440c006902c000000b0002c5c00005014650140c03030340302c2d116502031311002c540200c0e00f0b2000c6090142c030250400202c2a400d00c01c81e44140c80200391003030b07040340f171300200d0740301c0686074041801048401e14007a42c104507011601c52070105040002e050f5981c000c000c440b5504404d030742ca0b42e24140403440008048032500d01074404d0342c2203c03194000f42540040340c0300d10401c80350310007441110718500700d509141c04904204608600100c0603401503a5540301801e128500d501c0028005228003038001e11a25a038942d039036800110b0354400400360f100e46a80c02c490f102d25803c0e09000300184250340c2540034440e14540307000c0c50005110036203440040b5000072203844012a00040c0c0c2003d03444040b51060300d02d15404800754000c00f03401941459245d50001d914036104a07410750701040107800508000c0d8642c464900d040d5803d0900030f103030904e103 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 203302410 1250 203301160 203301173
    0x30207080d0c08030703020702190810110405101b06060f210605040201031112040b16080103080d09080c060a0b010801080a0308060a050a06051b15010b18090a0b0913 73
    0x4140145083c8012011a4015000c1e8054038460384c0d004003120007045807003402c0351424180b84070707004c0070f84640d0000408120440c416800b400e0b82d03840b80300c1d1910f030600041c480140401c00c0541e04201c0070703102c14041440c054545c400c0b02c6105940102e0010701d0034140383c4140543e50002148440400e0b50890100a400c16035110f040e801440460329070381c0d81c0016001400d4803003a400001e4400600c29400203500c40703c00f03100d10710500c42000c82e80c51394408030013910018403054012480b0a0010b101003030300600540000c07481544003044a52181d600c140c07280d04a034400c80415031100d8240078207000075000f80307040c8070790078079080886600d0040a1692004502d01c05000d1045400200d411904c4101c201c001030324029010803207141e0b48090043c020381c844150103414042100703008480c4240494021461040152420180e07420038840c0b448a07444078251078141e43d4401903504140e140c200038548034101040700000d8903030b000020300c012031000410f2000f510341100074090002cac92 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 203303660 1250 203302410 203302427
    0xd050f181501060f03060506041502070e1501080a0e01150303110604030f05090a0e07090e01080106032003240618100918060207230d2a0c03050109030207080d 70
    0xf03080c50300d01c203442c1d14040198010000c40d0040364100b10300160105640e8501d0340040081c01c825806c84480c03030380e00d486d6611003004c00d40300c00d810035013140003903080c035807091007070381c0d00320491200003c0c00c244051092030842c1c2035503c03c0469942400740402c00d0541160001e40f4484400d405400740c3d1900340e07401001c1c5002000004217100d00841d61031001d40300c51241c00c016165516903c585400c00c40c0c8050300b42140e6105501500c40d20034004600d200040c000c210840394071021103202000864400c0b4109840100e002e07415201d240d40362031049142c9400640d490440e41c1080c0c00030b042580c02c0c010403104c41948045c0785003118041c030594011030803010040340c460a034005440c0111021000001c10f09240151106001240d4201400110b200d10f602c000071030819140c40c205425405038803100d8041c0a08042004001160320b400d441c4015100c2a43c21000c89001c11185951880211215900143d9044c0c1d0758101e103804050f0100300bc580644104c1001341800101045c00a00111 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 203304910 1250 203303660 203303669
    0x42c07080405101a0a03060609060b27062710021605151b0c030106062a06110d0e070f0503062d0705190e01050d0504080d050f181501 59
    0x1a0b50702507a804e0740d4030140f480440420001c0c081d201d21039503800c0c03210141a6500500c0791092810000082c0164088121a4a0202040504005210841250584030311200c81ca60486420410248a60b01d400c400410600202071289038201d533002c1845440c0341403c8000040d5800700c060400c203441e0700d10114040700c0003104c0c0818400100c14503400707180a0403c0101429415500000e03941e000800c020030164415070080141d40e642e124102c03500c149400d01c0d04c80342548048207480d000000c424030484c4c2070084001160713507490b5041000c0d080d400391341c1350326040350b0b5a08180925101130281d14014400340320555481810b0900090301d6442c0601141203043d1600510740150003026104544400040d0001d40c0038503007040b0140030342d801002c0e041e0400040084d03640c19140503020301c0ca06480e060b0f590713a0a00000d20178180051001410a070f42c5600103000c040051f400c2d074059588200240ca03201c17000b50a008048102d00d0340c244a01e01c255800c2100208094241c084503141102c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 203306160 1250 203304910 203304943
    0xe060306030717010b10090e0c030708130309080d0504060305090102030907170c103501090902010e03010204091409030306060d09141002040f050603010f05060f042c07080405 77
    0x10741180403018018001d990003e43c0001c1883c1d00140081d0300b10002c3d808940d050110105581c5ea00030326104907101c11640c4d034000c540e034480454037100301408403101c264407034200205481d8544480900e0711070380c0030301c40d00040d03400a07060160903414005d654001c001070000f07505505000541907161001c0d4040d00c568041213040200003180100881c010b05400a0040c8420101e0000c0081400c958101d00d4140803000301104003d08104c2c0b02d00c1010342130100d2040509900304100c02029004151080e0304104030818280d040d60740a00c000e10082c2031015001400c100c1c0d4031103494110b0030040031119240c0040c0108103094644500b158800c1c1d00780500080c02003170700d190402900e40600d070031210030b12501081003020b1200358020016645045014080d8981d21f078100b20f1184000d02407102c803842401020412401c115001d07200600c98000481e040a850f03041d582e01103031080d4481101c004120720820265032500381d005c0d0b04201ca9141c801c5241c0b600c0d03203400356115034681080510 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 203307410 1250 203306160 203306189
    0xb030a1217090a030f0f140d0f061202030d110303060f0d06050a09020f0d0f06231006030c08130b070203091c0b060904021509030c0a080d0e0603060307 67
    0x14803030340100c03821a50005410a580c180000b10035590458950101c4c041001707110000f5a0500900f40e0148000607540d0311445000c4201e6101c00540290741c40d490402d40364501000051814015003000d0000c5250141c0381940c1d900400d494902d07441450400d00003001460407540c20f02000300e0344d00080c280c650340b05004c81d5070301240c2444604240541660320301b8060001011664110104040c02101c072081c0c402241410000707824070b420b8004009a520010030400140a5004080c04003584c050070742c01c1c0c1403040502031442d0012036854040c410b00c0c800500c20300f909445a0a42e1031418a00340301140703010412801c851400c0b00307000e40212403800004001c0b6208104a81c01400d001c0d0004540482c01c100c1e194054602c2d01c0200d444140040000d9020f08001d001180301d00d0300200215941c24105030b01400365404081e0300c1c1e0301400b45011000581c2c5409000398020a0003d0040500032030905000341162803850f50103105450800078441b05590020341d0700240e4540b1000c5800 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 203308660 1250 203307410 203307443
    0x9070e01030305031f030b0c1b01020415030506130612060c02070b04031e1205040305100902012001060e010609090f0c021f0f110a08180304030f030c050f0c040606030b030a 76
    0xc2ca6130496000400e588880401c10a840613114049c101040c0f817040c64180343d44190164909130301881c010343c0c0c82c25030400319801031070344a9001250400d0b4094104c0c2801c510318101001034800542098000301d000030108400c0015611644c00b8102480c40038100071400c0c40e44030240780c407443c800603040ea03520348030348200c42c840d92511070442c640c05804d80000f01c0c5000406051504240b005035294004c2c0150700e50030418600407954015816500e880148000b1407903610400503410400550359aa06008590307207910b511030b11301a01171a05d80800f80f46c504a001f0b800da404c070414903c0c0c1c050a20702400c80d85900061f0024010240883c40e1303500c01c450310b42c00d00007002194074507101c0c94207007008440b5199140004124061b4155503204142d95201490748001d100052140f529a00c200f1040021035460510180035510a1514180003283c0c2d889440c6003900380c400b841e80c55044041d54030f0302450180309650003055603080038040c589201c0700094036a10380307100c080c1210075044420f41 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 203309910 1250 203308660 203308711
    0x304051207081b0f010e01020301051c0c0b04030302010b041802010806040e030904020d0204060f0206040f06020304031b110a05030c0102060412020c06070503030105040f02090906012703050609070e0103030503 92
    0x140102d11100e803c85a0503440710310507035603040100e0a85159441c0c480784251174401030088034180c80c2c0145c80f82d02e8a8020034105c001c002c0c5800d81c181c3d9a1104500007044201402c8010b100660007a40040364003800c603801c21003155545600c4066179a45603402c640141d8001801c113a00000032603000071b4517000065502e05610070101e015900510006182d2001c45055011380269070040d95110416030308094141e07a06c0340c0940b800760400c84518030103c0040e10b25002954071070300c6490491032900100c2c40300b1003296aa01403c540f00c911a4240f1103035414968a14002484210300034554000140b00103516001e000d0805099500300b01c0c90400c920b4000c025001200601405099950350b542c10083c1c4c480e0000c0c010f0a10640c289841190b04504070300035280d006c103004200705815203441c0019200103031a5403940ea03c2c04443d600841c0c42c480d4600d001c40003507001303602410a6103011000750382800215003080d948c0c2c80521005201217035010003540c0c0d00507016044502940c0c82144242c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 203311160 1250 203309910 203309917
    0x1512050105010c030c29040c1e1e030b010611010e070501050d051f0f1503050c090402071703100608060904050a0f030509040c0504060e03120315040f09140d05030405120708 76
    0xf02c0c0002e90350181003581c40e40c080446d510450240c89184441500c401400c441d050310251031100095415406010842c82da4803911594000700300140700c0c0f590f481c0e0f144589000244d2012010681d40c0e480007250340f02c04c1c001e09841d40c40c44406031034618140700020b0464000c880000b80c0e5560740c2d1000503034140360170008580e8912046d2181c00100d59403082044030248500510003203190342980d0401d000c0c041c0c0280f501450307102402c14144064030701840029040030005440440000c00100810b00c08240118050303071000001414480c00c3c1040504511000b400382030107900190f00b0000807a4001c9112140207a03c51140c140240c00e60504a460740228640264498603000c00f406015170007034000e000711842750301c80c1007a200b540310415413500c080c11655404860100000380704641035140381c16032400d00401c00900300d1407810030314044030000d090443e44816440e451103100c00e0200130340341c1c40c590789251080c5180341540e01c041d101d42408642428601c004102e190820002800b42c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 203312410 1250 203311160 203311193
    0x412020406030204240e0c09060309160807060f0e0d080715110702091807061112040e061801140105031e0a06030c170303060607020f0303041512050105010c030c 71
    0x80c00102d0314103404c04403100618400a5040c5c0f1103110000e20381d90407420991050003110069410205c01c0e000f40101580010f220b00b10501a1584810141194003d010050010b6400800c529410880041d21600c1200c1040c000c0c4030b040c03900341c020b030341d10300400c00381103a03100341000c0d228034051400d928141d10007044038110b0703410146000a4811800c0140c1a814001c880c0c0d101561240b040400800c02c0441e48100c0680003904281b1039a8041c6d54426143c1410078112071070302500401000a94001c0d070050b04041c8180b00502c2050300e00705440e00c018042e44010329940c0d51404001d9500c803002000001d0501201000048400403403090303002c054481d0b881d01e02c02038640809018000d01e528003003210320480300c450100b0a00c0f1904080105400040020351440c1c0300c1e0020071400f81c004d0319007240d0150702440800c5003910203101074802015185411548003402e650040c1503001c1803610411414508030040189aa110408046840d0903003403503103a214040c281101d4468589a4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 203313660 1250 203312410 203312419
    0x409060b03120d05010905060f09101e0f0603020306010f0c020a0f1205060906060a060c1b060503090708012a140a020a021e030d0f180b031909030504120204060302 72
    0x5042500d42c110300000e01d8003510910b410041e80e0307201d49074202220000e03a0601e80184e951034544129060040e0b8090b0080e0003614402c402c00e0340c504c5000f50300101d0a200c000b4041c1420010000c14010308403c002601040c1015811031900c1d600003400d05d120441140100420841e20006541301d0b945440080c000b1030010102142c2c540300f1006c510710103980c040703a841c8100f1001960440b4003040d10390043e940280120646442d040c0225a451220070059810041c4e010006c144410290b000000811144d21200d40324071b80012042e00344030304ea6210b13290383d03414901c28820740c130b0150000d02ca64221302c83c2d40d00ca04a40b44901142c02c4000c20310401c08202000840000072900040d040c2c0c100380c400c50390302d0403581806415070007054015488940650140211880c014055281e42c0c001c0d03e10b41c07501003642221544102e001042c5648211180040001072000e034480311440032140c080c0760b103c20b000c0740c0a165030040680c8217501c0b48200f00e5285600490031540d940d0000d034010360b0003c1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 203314910 1250 203313660 203313673
    0x919020304030302120f010609140a09050a0e0f12030406020307030e0a20151b15040b011a1e030603150f15100c0f0c15120c1b020409060b03 62
    0xc2d02074000d40c0080d0f15130155607041000254080300c216401816a041c694510812602e008500441c001100c400a5408108000c0214101d5828030980d88a0051401d010a05078005582d0034200710b42d40800d00c2c070b0350b0400300780c0544901d184412241c1040d800360005075030b80d450440c101c0040c258242c003c2c1c1d0724000c0c0d16810703081c4803030720206000000c00c040b90140d805800b1070411810404001e00110340070402d00c4080b045036070544100030745503286001d44103503d424002c00300c0c0c41c01c41101c08543c1000604014000e10401c00d040000610301c4001c3d071072501c03d1404107803017110074001800c12051800030010740c0c1c984080c0b007640441c03145243c0d441d0080c1403420030344003080412552030a00d2030005035412414941220881e8091072183c03070b03100300c0c0d40141e01c51f0390310b1200420043d10b13010112400025907075100c111754002d001c5d49640309802d40e011955810161101c00b407030401008120522220705a052503460281294102e50014a441180c0b030705030080e0045c0401e0075032600646 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 203316160 1250 203314910 203314913
    0x5010603030914010e06090d21030f0509030d05090c1005090f03010603020603041e0b04050604021009050a050909070b0a0c032309010503040203010603140a020a0f0b090919020304 79
    0x15048401524800e8030303070040c900d80b03c1040e001001d030b20382031150016000240a1070682804c0008003d48400600481d003010301d030352102010090402509050342340030304000035105501d4890344c00682425030042c011070401c00c801d940e80340070703840d51000d0031640e070000720741509010400f507900e011024090100400031100080c0c955004140020301502414003d046280340c18400d20341965801014142952a9616101010703031b100b040401081d0308403242c0c1008140c000c3c08407841a4030910051100b031615105000725903c041c0b058806000e17260006020540e500e0108070301340c54080e0380170009640c840c0c102070300d0501c40c3e42c896050018000341c030020b451303400021b84110138040e1712158800d07142106280c00c0d10420f03a0f05207003555004d204407920b561041d00213580060000f00080780c0725480303480e0303511324083c0c0d40c1c1d0520090384002c6022003141441d050b1200102000760030b0101c00307894214002c2c240d21600200503c038180700c4000030048641c4010b00a1380b6070785807800319201d1034207 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 203317410 1250 203316160 203316163
    0x20402131e0801060b0408030a0f050409090f03030f0603020609010f17011203091d0a050618010603050612010e1002030402060706050c03040312150b0901231206100c0b06010c0b0405 80
    0x101d01502c03156508155002c600e41c001641181c3c22070303020300c0c015403a210002e80202c5684184801000420a08100c0007d841da414060004841d010305d06071403043c440b6140c05012a048810904503090804000304050780d2000280c82c003100c02820003040c80a441442115100500704105c180101c03010004030341c1c840003910154400c0d11079203449000c030303407110821400102d4181e0216901028072000a100d403d03241c0120350024009007010803221424174807100408002d1300040c001035600c0c01049028a0040389030501c89812030000c2040c8003900300c00945a0040c102481321241d0004041421900c60301d0840d081160002c00806c01410818501d07019540140c9098000030600075030800340d059030b07218184c0340c501c0541d00700440e1850002c43c000c2d6604583c20300380c1840320303940c14101508807150410750400391100c003450ba24a400400d001c0c00800241c0f94500401c00181004040c0340c101c5503100000d900800e1031079003952100e0040760005007045c402480340700440280400c1060 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 203318660 1250 203317410 203317469
    0x306020301081c11062202040c03050702060c0a02060c0307090f140f010f0215191103040203070e0610030906090f030c050c01020d0c06050a06121b0803120402040213 73
    0x40e40100b409800e01c012204580320103e91000c01c0554100300c0110340d400404420311b0500e14039020050740303080400d4000404642685810fa408603407204100b085d0694107010440d480301d90081c2d0b040c20030401d880000d6452900805c03400384550000045a9181d01403510980103202039590160ba0f140c40e840103c64104c114403100c0c0c00385031425030f8000558000c0b0010305c000c090650003000300850704504a49660400f400e4616080d0800d030389001600b88030300441d0052419610030310fa890405106062418138258800030f42c030041e02007801011340ea40a280c2451184504e00402c00c030b034540c10076070020040c048000b804082051034410401d40c11550b0198007602807002d565100601400580e282c0740007120303803c0010042148400000c000f6407205420000c141000113035547c5481c9040f2403210078440940d11311000d10200700710030000400400140100201440c140342c8103107408524688041c0000348240e402240410400e00001c10103401443c1405265216200060303842a0680 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 203319910 1250 203318660 203318683
    0xe0a020c010c1d0a051003091a01060f180f0501080405032503030e070305030409092102060f070e030d110a0b1f0803070b180f06010801051005220c0207030602030108 73
    0xc02009400c1054549049180c0c201c1784050081c0003242076a40045000708107800048854103c4800041e000c0383d40141c074140a8001d40c2c80e600300e102a00c9002605d10f00f03001600e115000c8410780140414030030b26a40d0001c940c02820009002d86035403801c41e045000d5807000502d400c8250582c002040038030115130740c40790b001f07807401c11005103160301541e242c80b520b00028107030341d0040100304010000c81d446103001c2070081c520590b40e041e91000b40704020070f0250300e440041e81f000c014818482800710f011078000d14241000d082c14010580400d450751160007460084c040280d01e142540b00741032081110a6501c80c29416440c5028040c0004800000c100341348201d215003008035a1440000032285801d070481200d400a55030f081c9034001c500a002038404c080d010b664005826010104803441c041c010400001c03545192036640e00e40c0c18041c0364800340c0b103442c600c01d081c8159001d002d80f0791045d5180d060080340211040100380e2510446500040c02948000000540c01001017003c03035204 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 203321160 1250 203319910 203319947
    0x70c06110102130302012003030f0403030b01020604031d131b1404050d0813030807050109060b150d05041103070909050606040915020309070b0a050901110d05040e0a020c010c 77
    0x100c50810340d6800c034000c0a000031400d442001090000d5802260022040c15264643c49012200350b0f007000c1c21031b0010380d800148200c00006120425030113004074a000c060078402045e4900e02502d008004171148003001001d000d0400b208802612160000079502004440901c026250002c1407014050150ba407000001c28124032100421100c1d000c40c0c0c03c81e0b80080484000292540710080654440761010301d002c0012800000050301d0380018010f6103014400000d80d104e150b08040c000e9270309008943d8803d0113000b90444500d00541e0580d15003880e0120006007503940c0340b070942d41080c80040c3d5141d00d841482c400095510158210702500c5104106880194642000303020513107181000c0180a00e00c0340d803024150340d107194095070744144104120741800b55a0501c448282d031000d5600000101d0005101c0004e58100720401292800003004184c128440000104a80100d004401350803d581c40403802084c0240c0550704003903c80c8000b004441146040034100500d030700b258a900 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 203322410 1250 203321160 203321177
    0x10050403020a11090c0a0503090307061103041a0714030403030b040e101109011b05150103080c0606030a0503030604020702010306030206220605031005100c06060f06031404051e070902070c06 84
    0x10f01308844100e004c2c0300000441820621000001d07640303074200600c034000074402405007802140309409035030951030949550aa0302e0070142030069409264510214140701c00e00c00340608254044034a541d55545601410340320f80710352504901602d521103003035a02c0350030401186c0007a00082202010b80408200801000d40c5400710308502d0300489025601050311818030715a0002461400d5501620039000d950600510b40182150b06a027a0010760702d10401007050b0310844400c01c180c0d0782103502100207248188003641d81542d240b200810a42c09142c01084607030840e40241c00844c09180e009181c039403160710680180304801c4403040b0000c010341c55040700113901ca001d40d08803070188600c94004000141820140110300043d10350720360800140e0401c69011a20760701c602e0000d81424078054940b076240110003004d8403d10920b619500c925001071000107200004d61501c019190441d040408072403441c0f1900b084d810703030b006c054098000940c2108004a01c01c4100685020b521801d07031 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 203323660 1250 203322410 203322443
    0xa030f060f060c0302030f030c1b1618090512030604050f150420180103050702070b041a070b070206010e0c0c0a06050c04090c110d0509090a0b0310050403020a 70
    0x19244a44511048000846018030210b449441910310359070085c0110703441d1407080d01106940354001c1b2400f0070003010100d1100c11100c1c00070225290484c42c500107001c0210b8003031132007181c42247d104858400428900d130302000e1019412218a19412000b90b421000700701a0b00102da034004c0790518400c0345000001411102c1000c5c07118080c600e03419049040280c4c1c0804e020003000c1e10002c5140034017180c1d4070038409a82c000c008060340a06012882c0c2c000700e05000160039581c004d40040f0a5402050040c005c0d4990304080d1790880f440c2c0c10714290441d20729031441040303208081010b060300550804211000384c001404034120f03044084448416518042d0b0740d041d5016620261159030040c0343c040c03001c50704640003550003003800306c0118903065035030307003150100ca80c405052404034800003d00c00c2c0d1910207010440007904070303040c100c1c07504d02107034000351400500821101081d03507503400d295200e8800b0480b02ca10002d40030003c200700d04013800c010703603503984a040403600351004205410 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 203324910 1250 203323660 203323691
    0x20705100e03160f02010302070c151706010c150608070e01030b150105090f010905130e060105031c050c0102120a0603141204060e030307020d031106010603141506090d080a03 77
    0x7203021400401201012800d580d4880c4c0440d5520016410541c007800300101048203400b1103002811a0190784c0004120820068010701d13400c002c1c0321401100c1c6040011a90300002d0b0041151f0f44000c0c8240103c003148101d074018240303904203041c203105040020448441002c80d042c1030340c2c0117051601c0d0a5540c43c40d0103005491010646000070401c0c0020b900c0ca040c007640500e000c26050514500030b6032281c010540510301048074500c040d48450800002e42c0081c000b241c09080c0590242c06804034000704949138080c81c4c4c41500400800141c1061151420340c1659910100350344581c03c181000c101c070344003a0107035000035580d000b215544005144400117005402107015600d090420340307042c0081d17444000003040250940004c00100005950f05041e83d010540310b0b44408100c1c0e00d59031510303880d280050f00308800b414600214010204c000810096012182e14080d0841e8402100421540e00411240d29000a9280c04801c10800420090013140145540c208066170390f42c8000e0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 203326160 1250 203324910 203324917
    0x2041e06200705042304110f04050408090d080c01060b04050406050d11040b04020c0f030a0306061112030a0908070b070f030b130203130c030b040510050c0a03090312020705100e03 79
    0x440540d21a51003044942085c0d0440e07039807521090b80301500c201407101a10200201203038112450420207010303502d45e03c0c1044840c00c210301c0c15a0100705504c1c25580740800341c424150388a2207400c0c407403650010841910b084544003c0520024082c403940c8010740042c80d00035025491140b8101030020a042c1012100100203d420080168135440302806200081500c10540c58110b5000c0041a41854040041031003011551005503520440c908005003143d0142c0c0041c010403c0035004800c61900024070703c0b49500354456801e541e80c0700d01a10344010078182030001c1881d20041201d60a010105407083d03c1a402a10390307070b01100c92854102c0c219070381045400e6000e0140c804407941303150107070302030b5510403012040b901300305080d91644a20f08005a00c00c9400959a804200802c00c05011091910440200511403828007d914403c540200310410003090717030320320b404c0c41414416030b0090144040e0280840d07540030f65007400c3e0740f640c1c00ba5018500c0c031800c2000d02e042c410000801c5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 203327410 1250 203326160 203326217
    0x1504050d0503220602040f0609030b01090501081509150405010905120c070b07020f06031f0b070201050a1b060204290406080402010c030c0c06030212100302011d0402041e06 76
    0x14691101d00b5884503e0fa0a12100242c0e140c603030910000c1200380d10356a50001501d00e540340c40c4002483c1d4581380c8a1500c050308484181030500004004550000503224844400d04600018a994507800d0518140c2e40c0c03c595500492340320144014000c041d800a290903000d10b06071000c0d4404294408202d10680c2c0220110703502c0550100161101345003e40394540c4020208060ba040c45000a610342e001a10120030522000b079148907511081d000c1c5c8070051003212143d600380b42c000d40020b803050040603a080140100080144d041401c1a01c000e000d07554001011502ca540b50b041c01140000311140d02d0300d852403582a40849014610261000c841155403940032594503039004450300c0c45048800c03014003101d1007074100051072951801010b005d10360340050301c5c0e20314400503200d0700b4000303088014180300a44061000d42d90040000030599426034400740c8807050b4002041c0240b1442c0c3c407207203041000d0729007031210016036810201121042d80d5040a80304c024500c50080b400351108 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 203328660 1250 203327410 203327431
    0x402040c1706011d040219110724020f060906150901030206030a020f040314010203070e0409050d0e0f09150306061504120f05061504060f06170405010605031504050d0503 75
    0x15078643c8513440615440c440d150000c04030301103680115042c5d8111120310180543c01c03401a8550b03e07444100015402c04040040840c1031410f0040c0c1300705940740755440d00c480945040103048034001c12261114010030021140701d0b04d00718512070703100e90003540c480c0d40708606a030f01c0104034a07080e00520305880d001440145542c562100e810300030740c0134244560b41004144000000308040600000f0303640b00d02d80c00581d0f245405c0d00000c050f0321403044400d1089242c041e4440c04110001200980342006051000004d4a5100048c401340705506107070394414000300400443c020b90b15070350001d003901501241c1403515284100901c48064030002c041c1d03408144400c1000b000706403126401240120f40031903115200340c480728142403044640020140d85074a48280c64145441040b000304500c0e10246170180c00c1060080001c0341c5070480c9400903010802050a0002c20b5200c00020100201180d406440100604090400454080e5a6401400c0c00d108545000310100c81c0308030345191 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 203329910 1250 203328660 203328707
    0x801050f220504230604060615050702330c06010819030e0d020402121006180306021b0307030f0809030301050d03050a1806050706060801090519140d080402040c 71
    0x5a1450007448018020b1300d102007002000503610f1040362444c9010000700d00a02000d20b80b506224040e180264000100401144030038580c0d0396100c81511817640d4100d40c00d00c0101010b16440b014150708045904e441000040704030001007001d401420f81700c4010050f5441070317a0710450141c8039542d01544142c0800d14000395400a4426014044c0d1410020542c0c3c1c008141c940210b0100e0700001c1e562181200841c06000b0180e09a00e2000001c101c103182409038040d00601da0fa50340b54030762200501007600410088054100c2e0320b0090081001e80e4102d0707894041c02d060080241d03140d00404404550400041541500040100d90503200f0184c55040010110f540455055201d1000c6204000c65580d01e581480c0f14880c41c0310040c2256030703c10741c0346c2a03181403034801c440041e0b001c20381c02ea1405c69410001030010402c40702035194100e040c8a19805410090000c40025025440c0d0780034855100e0403840e041f02c0c61501541c003c0e0340410031622010300c1681c1400b80d02400c003200e4890003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 203331160 1250 203329910 203329969
    0x40b0d0b1005250f0f0204050f2a0403081809010603020c071502030d09030801140102030c06070e060f04060305040611120f0c090a03050304081203010f050d030c0f030801050f 77
    0x1e4090803002d101603055503c140200703031140340c01010940412569801320902c0390b070a500e0305004244c0c20208031403602207203080900c032070b40404201200030030080701d040c40c45410b01c503403080a65000307580044809070b13103140b14440c1100c85000c030f000640c03007100c00d0000440c40c140709100b0f456109030444001e14040e42003010b185c50390700c59000c0010444c0b008022040d915609402030030300b421b100c5e1701c92561a504200800c0b10205011840c00e04543c800c0c8203001480600049041d00082141031403000342c2c0c80e0902140b010303c41c0d56a181070300140010f00040f2190306030300c41c5209a00443e0304008440e40340303501c800244032310214140c20030340d200301013100a0007500641d6082202c10500500d081034580128162482d80e5009845641022030108011042400202649512003000516640c10085050010714403070003014020583c0741c50080c04c06019401c0d02d02c480d1340004030741c1c6001c411807400510180090081da4081c007801d01b000c1405c0d05061042c024070805002c080601101c80 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 203332410 1250 203331160 203331187
    0x30a1b0212030a0f1a030106150e09070c0f08040501080a0e030717090a030c030b0702010c091202010215011206060e0112141e240103080901180902040b0d0b1005 71
    0x151640c0c2c1c10541d0b44242d40c0b509500c62003540051004000d0b114403003d050006c25003105c02c80e030301011203031100c0703042d01501ca40d0003008174200b030300d084078814115100c005040300c00040a4000500b1011000810b00038404004007600480b0b40981e5807001998940035070340d050320005510020150b1086c003880c00080d1054081160400750104ca0300c0c00c00340550000317041c0b40d160b03620545403100305503024010300c061029455440365103030000b480b021400840c0244810010b00c10f550700c2c10140d600807811a803081c841c9000c144c440d54120142035840b442c180d0107a5038406c0013242d440749840b8001032028207500c42c581c104c1c1d04030b9145120801c0280c42e031607943c040c0e1505030707a003a001d01c0942c0032020200c810040f00c060034602c005c040ca2820010301c4041b2401d00385591103440003803001080012149003c84650007402c0c60444058030b00c1040345414805a40c0040c4081c5002081c042040b40b00a809098105003442060000c10316920a01c807003c00e000751401c001500802c08501034022 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 203333660 1250 203332410 203332417
    0x51c0507110102100f0605040b0402030411090a18060c0e041e020a1107030507050a08060606090f1903080d060603110f1c05190c11060402120c09010902030a1b0212 72
    0x141801502d13604105045400c081320642c5040c071303070125a00d0505010703900b02485034002015007500d0852450601b40c560300203038254030700e5030351051032004000b0754800d006422506000615813074101d00010a458820080d220854007100003402e040715105031803409015a18110290840750003640d0010042e85020b07602c100084024040c1d201c5808920100401c5408010f5003c2d1010f420300d50704000400c07110404551001200e0342c07040d41481011b6484000b200e240c080308861f00c6414013044070229484a103010132104600350403000000070700c000c00000b03003145001ca0000300125502d45406404a407444541c41c03a01d43c6040c040c142420380d0500080c0920b1030555150151440302003584c60035580b080f280d1845904105080d006608a54050b42c88503042c1c03410400b0307058040301c034030300d40d951001800a0311130b4a451500713a5640f4424804201140e4001d00101003070740e118080c2c02c01a40c0107450481c10070740f0b004035242052030000099000b1400c60383c013070301341d40b0b00301d0855036003982 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 203334910 1250 203333660 203333693
    0x3011d130308090309060f1308070812210a060501020d0203120c0307180603022203111e03011d07050a15030504051e010c02070506340609050a051c0507 67
    0x100c00c000001740341e52403070041e08100000301d01060782e401200f00440da03091a6580444007a81c0030920074415030300007189a880700c030750003503200b40c03104019141e007003003004080e56082d1100149020f001e04503100780c10840940b1002c1e021030307054509440d0b00b02ea691107441d00c0c590080c20520003190402e03050038025134014103149002281d02104147d2584082202d80c000d1b00801d600052076507803040c11801c0d214950344188030b44060503213076403110701c0301080f103a0100e4030030344401c0a80c00c810f0b2808014030a03e5800035008000d100705903809409e110741c0716000004544150400000c0c6884d00b10301c683d00ba21140300c84004c0d1007046410540144c04080d208448a0141e24006a42e084021070990044140302c000864102e139445406401d110454124a006047c10803c02034020201c00040c041d0400d0b402c98040c43c090700900035400c00061910060038603080441d01f5050082c002840341e03101e4003410a0300c0042d1000d1501e4a80006000d50340000708400b48042c1000c544115110010003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 203336160 1250 203334910 203334913
    0x30606161a131502040f0506030a142a07020321190906030e06010e062119020a080105040506040201030c170108070815040f0b0705160803011d13030809 67
    0x3000040c20342580d1403049030028401c0003000e00c80c02c180328034461503603401a0b200404628181c00c0c07400c008512156805800c0c0226030010103c1c1304400b0b903a00ca0b0302070380d03a440c0c03442c05507003003000b072240700c400e42d100c140946001c400d4805407800032201e084030882503000f4002e0135113482d0420403260003442410740c2c80e0102800e00c990718640800c40c208074036640b0117540d001d41c0715040c034001604480c03a0a01402d5141d2046e001485070600c80444140c000c0070840b0746003501ba00c0a1525106d4034000d140d00260380c010801101c00d01e6035805040401c40d8802c948006400d91603400407030898000f22400307081c650100d0040b9025501a620000420480e407524400c00000390700b40d8000c01d075080e440642c031944080300420141e04240b20301450400c18015048282c03c190300c410303080e540c0032207015114182030808145110b001e10110340701c1210021981d225100c85c3d0070111016042445842040b00c103032005e07850b00741005a4801d01c5010010407400c90b09216403000c03562850006c02c01c2906 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 203337410 1250 203336160 203336183
    0x9031501050f06270d050a060203062e0e03210309010e0a0b0604020711060703020a050706030b03070b13080d0201020c3c030405030a0807050d0f02030a03020c190302010b100503060616 81
    0x41601802200050f6012301800750362424840e0911031024488a80c1c00c8818050b0a5050805c411a071030a40c107003d000d2514402c00c0d0081c00003c2c0c10b0481e154140d040c13030050100d606011501c080080c40c4a074a03010000c000072049090815110054500014020801c1ca00016030382d01d0950f001e010230a008601000d82806e10b54041481030740070840c19030250b0310141d0b41d01c00700b080820109000d040e00e07181c14046603544101203540c9022501545a0503038011407001990925180350000070a240011125403644512000e4000d61100100e0401d07070040203250b207640307500064000c00c0580c0184514181601e8001c842a42900c0000c2d884c0b0ba1740020040040c00c0d035002c01925145038010b034880c666595207071822510f41902e04040b9404c0c013014201c80c42c407054000c4151010101541405039554038210242810040c02c140134855a54041540905056055200502510003503a15040a40314030600799090300040f107840364000400c1000d241e100b05070402400c0e400e0f2240080c0f118 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 203338660 1250 203337410 203337413
    0x1050405031b0a0b0a0b040e0c0303070609051908121b04060e18071d0301050601050703050d1b05030a050a0b10032004031a010b03090a0609050309031501050f06270d 73
    0xa2413001034400950030b5031940030a00321442c141c8101602100381d42c005085a10300e110109881e03000e542005403900c0d59480b5034001b80041403240038040130405034800311241c410718280c400c4c1c1d0030a04100c80349801c50340016030101204402810201068045d060810385441030843d12404d01c1a1a42d410480f840031a44804d0b00414180d809240d40340c0340c031314051254882c2c403079a200101d450540720303038100400d04c4142c3e40c110302290481d580501d0001c2d5503000f00002d042c094a45180c0003004903a420240003455a03024000e507001d203d01c44000d01a0b07441d55401c6106603180c2d6202c1c0c0394001410781d40105000e020780c1c804600f03400d00500c04034800c0d130f182c01c2c640c0c691341141d0f03c141c3d91180f4035001101d1078000100a075000d0045000eaa5003103042881e4006d50368143e0960042c2100c0c0e64151420911804005650000030000c0803560114605211203507010000c1c801c0030700815000c0c103406101e2901200f40c9101d2405840b91b040da01410380c070403a0800f40c0d10140603421441305030b9400f0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 203339910 1250 203338660 203338673
    0x2070e070504080c2e030219020c0a0608180703030c020a0608060906061317010902100801030c0504050703020906030717010f06122c01050601080601030204032001030b040c08090f01050405031b0a 86
    0x12550305e00d440040e15108068a12078100031186800011500070321840a00b0ba5100c1c5d5414041d51030341d01c0c0c101404c1c0da800c4c14402c044601510040b40910511200004241d8898111507005200b0783c0c90901841d42c0d07090940d030500302980c45035803250000c400211207042c0040500042415200191001561862403412110000b8039100099459580030005d50802d00c100c064209900e10b080c915640c51611002e0b1040424001c103885607898001141c4003a1103601a54185100180165078a04012102905a1100c0340744650110103020002031611050381081c0202c800a8468015011300c180500e401405a5000c1d211281e2100001c002e000c80c500449840d80c2015200003e40360401000140c0b011500418240c10103004110600004064413282c940780145000c20000a080c08801a0045d0141e50702541e0054507003101c01a20b0b50340800c0c082d01651001040d145044004c005007803d940c81181e020305558020402040001001846906ea416070034081c0d0700441c0c6aa41c3c0d40 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 203341160 1250 203339910 203339989
    0x11091009080609030a080406020702013605010206070e010e280e0a020307090302042f0405130218011404030b0f2d0c070309030605010602070e070504080c 68
    0x1000540e00c450501400300708224403070300048000c0080d0b0602841072070003010090010b00c001e00254000c5a54000c69024025003058500188806080c0403c500c140300c0c00d4030035224142120b42c4086400103840d50010071428001c952941e13916a80b88074044c01540d5a400503500d840d0444d4212a000400c01891091102c3d12200e550440003e9403501c0c21001480001a1100095510410900010719003000b5030008480c1c0c10b54011851101070700341146403814032190312184151014018031031404000080c02514021600f6200c800000d00303402080f40961402c83c01c5500c003103500da6046600030307040c46030104900562140360613141e50352a0300c071800aa480003607680c00c44040c451050900100341c0000740c91103040302002e645083c42c10201c03070740c09041d82c0a09400022038405243c4601480c2001d103130418410700c91540e448030025903406080c40781d030400d01130000100d80c9451040084030212107030f00d030007410010b404004000071400c0075200000c1c0503580c1c1440c00f061a90b1304011 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 203342410 1250 203341160 203341189
    0x82b021b07060908030301121401050403030b10050f0d0e0f030706062606010905090111070c03021c080306040c0c1a010e09070f12050c191406040501020a061109 71
    0x1018140104812141c40d140702604440c0502800000511100302c4c000107807070440d41c1c096070700d84240c003250920170100d0300324140c282210750804040109164254110306055881924290740240366400d044030a401501d690404000e800c01c2490011040340c4c00c40c0142c40c69182c19202040021903841e8a5940441c0003250001d449038400c001047c82a080c2041004800a8030400f80e1074005105480e0a414043d04003655135413004100e4001013588940800a91040d0241e92015a400e100709001394920049204a403290802d140c071884200c2d41c1811507a000380c0307581c1036446540400c009020340f00c840c20108a103150000010400c00c0728203103010303962230840500302e504000307180143c408000c10340881c41c0d12081d41000008251000e40085a01c83d400c4c00707500d0384080c9085420403180010f03695010f0b4a020a0400f0406030041c288200d6914490980b8000300c50000c2c8011406140324040c096041000c11201081e1144c0185e0a08010000000d140c991250005400107601441 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 203343660 1250 203342410 203342437
    0x1050d02181003170918090f03070303051602030f040605090d06060e0405150919021c080409200f0a030b0a0621091110090b19030f050103082b02 64
    0x2081484694030391303c42c66100903000689000f081c10003290611100040786d100c4104800001000740c1003c0c41401c600d03150794000d0700c1e40c404042c10b0040203802c094a001c00b0000302000040304283c00041281c84000580306030904140c9001019a4581c2104c02c0c1650030041003000040000c0080c880c0c2c10291004030580d08890405003002458000007084484041d90220184400f18100040c101c03500c0040c4142c2100382881880452201d002982c070301c181031140001103a0070007014030042c00c1a40c15110080042c0e100c2c1d10a09514403518030408000194104040445802840001c100034015820046a41140c0380007061a00c3e00307984c4a07400043c1162031410f034606061050101c480d240000034040c0ea8030302c0c0c443e603816032240c0e5826440b4107104c3d0f100a81e0702d4090850744c0b006000716001320707842c0d8070b0b20b10000d00c410365040c1c606d0307000078035003000060340180512500f07059940180c03d09080142d06e5a0580711102c0942c520b0301c2017029485104da000000d4002050100007085 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 203344910 1250 203343660 203343691
    0x210120603081209060f0a0c050c01020304030e090f04170c0102130312030f020c0312190504050c1002030a12020d020d02040f05010e1c0b0c120907051e030601050d0218 74
    0x6030b010350741080a001032107150025006e0161207500b41207034a4215001070740c00222082900c10a07501ca210300540e0000c4e5500200810041c10313000080d42c04c4061003a84d2186840d9035404403031410301801c84008100c0340c1c00c00d00c207003848803d00c3c0150000107034082c0014904105004400c12410042d4000c0b108018454246401c0b154103010f140c01c00c07949000290700f000c44403994a5100e0080d0f000710804d95400100040c541c1540c00072055200e028104104250b0515051660b111b400000d21103009041d005111000c96200004840103401da958410600c0424003118078040e50040b901203d5464081c80038200c101020f10090000b814482c0400d840d080c54880090514030482d55810310500c5000f4442c403d90303e0000790340000941c080c003010040da8808900301950b02400940308180180a4200005440d0001d184002d8031011a400074220011400942c131480a02d102560541c204100421103800c1002c0d005c584184010164484030300780300e004079504141159a4400380c000c04 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 203346160 1250 203344910 203344927
    0x5071b12110102130b07061d1006060806090708040309080d090509060402040e150103020d0603080d050a020408072c070804030e03030a05030408090307050a0902090405010807030f021012060308 85
    0x7101c52100a0784070003e50411003140000242d9421500c43c1e140c0600000894404000c0c617644521205621040340c0a00140c40c4000304e69500d4800d20380c0c0c240f00b071910202144050251242c6807003400014205000f55483d00002c60788010080c20071800d204414802254100c814002010503100c5941c61401007441c042c10444c2c405000340c200381c0141d00c100428400307810820788096000c2c842c46611a02c0903d5100102c0003486564071010100d071805101004001d1618020b11794841120028000d0741c6030407405904030b00c128400e020169020304030400000004c42e0841030701912a10707468a5880440030f906642c2d220803666600020f501108100800d5008140465103d409038029800c1c950b524402820704d11028102810306600030910324410364003007002e100506005400c0c04240c65440e007480c03010703401241e15248214144400171403603000000d113110440340c00800340c0b07100071855002e100c4039410540d040c00400980d09070380e03891140240580b40080d031088002550300d010b076 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 203347410 1250 203346160 203346167
    0xf10031e090218060303030c0f09040c08060315010b1903020f0c010b011403010605090618040908210606071209080105040b370c030209030624060a020a0605071b12 72
    0x140300380b42c280e0f0f254032003444056100001a02c0e0700480d40c00040380d440c94080140c0e034035805402c02c07290f402400d00c0c2c008940c10b030380500c1c01c9000307000940c101d0301e101141c24040201007100b4010b140c1d0f8500f0034089101ca00a51504040c0e4a0b0113604006162800c0b0710b0104503264042da10130081a91900080d8401e542c1c095001400042c00c00146802c40d4100400100140b01c3e4802ea140b00380d0010907045c0101203603200311000c040001b40200f00a44e0f05141c0085560011003000c40c08100488d0f02240c0c2049010040d80305402c0181290f25001c0307940c0d544501162042450340800403800008150074000748556802940520307081170251820103030901c0c036a80031900c810410b0454011000344c10f441c14060006a03480200302103070411484038200c0c002d00801300107d0307240c880c140c14420202d0184200104114103040c429030020b00d03990900003d44106400c003401688010003178004107030a40e01031904103419150614601e010450790214921074400143e80d5a000e450b54040510f42 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 203348660 1250 203347410 203347429
    0x19030506070516030f0516050106060f090e010504110c0d020c0f04142707120512040e0a090503040e04060b031005010501050406030e100903051305030703020f10031e0902 75
    0x20601d889850f00c02c409840322003820036640020180904455076140f4280207400341c2d0740c000100c0200401c0b6105034100039018040c03070300c10b101c08510a600096049445610043c09030b544502046200b6443c140502c4020440c143c0c88180f01d410501c02c2003401c140c20300c50328013280d0341c0c0c0d402401ca0030846005c0000b10382c649041d16200d140303080a00202c030680e494803070742e00c403021030b40381c46846508031081401c0b944200491180d40c05405070100d401000c040482d9a414010700c00c0b10014144122603a590f8810f80c010713072103108040c00014242c6030050300491242449403050740d08080d40c0740c8402e83d8402c0c0588040310341d07503203034003211a05040403c4113009644c9402800d21a82d458540007030008e118034041c132020140c503252403114080e0300b00018422550404010080803249040050003508005804004810048000180f07440d00086150036039030014650468400f40c203003005402403c000a800c140342d01c50b801c24041644d4010010050205040082441701e09841001140d84 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 203349910 1250 203348660 203348671
    0x2070605040b0c0705030336130506030109141608010501080c10020106080142050d0203190308040302100203160c030e040914010f020301080613021503100303090608060d08030709030219030506 85
    0x140088c1c010031075986140f19041c100000130b01c0003400740c6400c008280545000030001d02448220720342c111000c5c1c0005261061f12030980800881e25803500c0801d4280c501c284200d83c140c0d8403181849581d441d01c501a42d108080070f000010b041a51010340600f034600d040c681a1100c04207640171500703100f036441d50303032800500480410716409090b44194400703480350081c14050116140d00804640741008004c00090854281d084001e06a2a008009440803681113006000b401c000d4400400c80c0d0090700d0003014480015000031381c1116007150f000d000c45c6403d904114581258a416071624400d094249001c2d1500f11000301d401e01c1101c0c00d566840140d01c0c445441080100300035000840c3d450f80020740e01d00768010180b082d000040440506102c1c5503030400d07001091106000c0301001c100201da1181d140c4c211119520071382501e138540201e68098004486120240008900000440d8490460306040c84401c4e182c1c0c0114940c0e8003000c1310f01452421a583c24014400108403203903010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 203351160 1250 203349910 203349997
    0x6072109050d12080a060902070c0618060206010e10090510050406140f04050c0423010201291306180f05130c0b130506070f060b0102070605040b0c07050303 69
    0x5050381c0d03d24504074031200f6014108a0b6a40100703c04811a0304040700034880e0140a40d124070f0142056140c840c5140b0a500200f829822026080002c01c44214100c5503550040d0049a02e0b0034100200c014004202174001060075001080c000298400c0034010f180e2004061800c4d810201440102c0d0351a40240114840c9004000e00642d641007140030078010645002c07030356881d15409020180a070348c020604803500c2074007007400e071040101078a501d841c0983c001d21410090b042801e900b14402c400315103030300310000700c1d10040d0704050a65031001c2c03040071000a0350584c1c4400d80008000c80080241c4110b03141c6100380e01501e618041d19410280004104180349243e030340b113071010092881840760718840822455a4400f080801100400d400780441d1b40d24030144c6408224000449000c440d52403501a42d822603500c0003e0090039a805038442034035013424042e1210359078000c1e60b080e140c40c0c81070500c0490107403014001f401211044120b000410600b03012440135004024222034202d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 203352410 1250 203351160 203351179
    0x409080c0c21030d0207060f0501060503071706061b0f06070203130b0405030d0c0f02030307060603051006030b150f0d050d120216080313140d0e0d020306060108060607210905 77
    0x40440c0070045844c04c1200318001030395400f4501e4014068910f8507805d0010358540750000502d02e801800a41c030500040d41c0703202008106d8042e007441000c007034914a40100c41407061082d149101c4041c03000c0081030720101e0b04802040f500700351501c10102d81c41d4005030404102c142100c0494a40100540690259a0300707140c10034010a9481101046c108c080040d22040303003060001007500040280d8018040c3d90b6280901d082c0b0780003904161000710380d10311034807645e940510298402c40050300e42c0100c0140c195140e41c1e0007000000458642243c0c881d5000415240c1c40c3c1c0c0c2e420b08a080301c2c0c4030710302601301c418250b9009400c1e036010390310010032640100f0082050204c8400024850340c0d018004944035126804403040c0201c42c120010240d8075004002c8807291000200e0141e2816a607032030403124205c0c0024461114041c500094250b131003100460407071b40c0100d0075186d2102c0080c0010741400065210008071014007c1c100101c0c0698807021640180e100350500003038075007030f20990103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 203353660 1250 203352410 203352469
    0x80616122c0a0b06061e0406090f050d050c09100e1509180601060f09170106090501050d02060403020d080c0303070903020109051507060c030626150c0403030507020409080c0c 77
    0x4070f403200900b514840d582c0052281211030007006a04440d0210034a900c0e03c85488100c05001015240200c4001d070007056000291490104401840701d64018003070500791800005000d18048041e102d01d0140060010114468418540c580d00c0341c1c00e40c1c000215414500c10510130a2003014241c0302c40d10303d01c1c841c001104800041c1c200c2c1101c04901c0c02041105101b642106c400c0e4603034002d1004040100d400e0540403105401800968400341010803d50340ea8104002004d0440c20009411600074003080015107040745c614038140380941500c41c540311107503041d40d04650045904002203000c6110510955074032680d0342c0080d2500365001081030b100c02040c1c40b0700b8081e00c0402040f05441d038007100c0381a84290030200082400f40048540d5007109400060b83c00307217421200e0114805c440e08082414140a9410b0041090b80c0c01a840c043c04e5440c122400c0c1c0c84044240d0308681c45d07003651030015a20200a011810000025100c100708101c00c010822990b0a01460013182d10192483e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 203354910 1250 203353660 203353673
    0x19090804030b0a09060608060603011104230303040305010207031706040b06030a0b0409050d03020711062104030e06040b0301050102100b010e24030c090102070b04080616122c0a 78
    0x142501d401030b14450070b9039908240f140150019440042102c2d0409800080740f800c0003d64030300416040b0002d001d000f500e1340000c5400e00481c4079a405508601200c040881c07558602407240001c05400c0e07a02d4140c0f25262a802d90380104011000200030460745802c5501400c0051b8000f801102c060000703da40e000012000e000c01341c00c03040b0583d42c583c0118070381d58035984003000c0300e54032406458a41e910040041d0094003c1081030b0385007400c2d5003001115142001c1280c0002e441040c0410180500c6508101310b0f1600801c01c40c180024104080d0f0f00307645040150004055104d4580c0d5a0b60400c1c000a041001c0000300e0f48440b80bc1400d80c00320750380c1005a031494a80261200a0303880c044044450002da84c15488801100c400000c0c02001c205890080036002001e808664609584148441403482a80300f000030740d070002404640c03000c174002001c0b0805505452f040580c0700345c050580341102e80e034050000c441f851030480e0a070b51444002140503141b40e82ca010f001c0c6a0444d4075000c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 203356160 1250 203354910 203354917
    0x1e030313060c0c0602010516030e0102270f030a0218100e0115030b0d020f040b04020904020d020d0509030304260702030d020a0c09090b0a0c0201091a06010e0a03120305040203070510020303190908 86
    0xa231700b0b068850404080241c07003581960340312003050158041c082d1a02100d9004900070340c030b00728060f85201d004601c041c1130000c0c90000d2664082c0010401132407400a0b08400c035000307030240c0700c038080d641c000160030701520a626010b0240c142c6000350081c0b41e00d4010341103403020407284d0300603550000302d103002d0b80d5441c0401c2d5011f4825100401d20852443c0020024811a42c80581c410f1003c00c4515041803030358044c04000f044844c2c1004039450b034610300d554078041142e005141074400f0741038148040700e042c41580c4d40186040071608010b0641d0000f420044003501060040e07100d452404140400540c40c02c0042000070020444420303140c84050f175440004044c1c608a913100c6410b102d09910035401501c03103a130020701000351202c1c0310070030383c0e00a842074171182d000a107400c01903401850507200b45021131380c0c880e900c030700b04810184041d0003a0000410a0760305007d1810001040e480d40c0f9072040c258500c2d03902850b80c07031070210104490b0520402000421a240080b0440012008403c8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 203357410 1250 203356160 203356201
    0x7020604110f10050c1603080d0c09030212060a05061002030702010c0203030421030e0616021915031401080123040c081005010503060601020c1e030313060c0c06020105 74
    0x14800901d02100204248480c0c81c41d80e5500100c0d40700d0300596030303944403010b0919036900c18151401400c07110b507442c4c4045040d0002800340780081100110203034080c1e06c13044c0010325504010100303594940024480c0030400040d0313041138000c94204008403010303205480e0b003c00110752164403d4001c10000303503680213402c0300034140500c500b03500f07083d96810419180206410461001088404ca841d400e00444090045011554842c6500e5451410500740d03030b4440b81003241944185016000c114550154211a2540300300712040812824a80c41c04002c0300e48080e10017184041c5101e1a92442181c143d115101036407602e0b1555050400d4a904d04465911000d200f86c0740d40c032103043c10001d0307200c29072090105100b0001e01d050312001c1c5410050494604505840040d0780f03140059031150b8000006541c0a00c6000c0c1c9011100103000d000d005986001c0c1c01c4034200109083c42140000d216040b4a001c6000c1d080990200252040342c00041e0a481c8024003c42c10070072900d002285ca4100c0303 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 203358660 1250 203357410 203357423
    0x141f0509011a011809061203080c0307051c1b03020307020d020a020d080915070303150617010b0d0b0904050106030b07110705131416030608010212060607030c020d0305190807020604 80
    0x10304d01c0310380c000942d00034050060080104105a178681c40701c139180ba110b443c106c01040c20750300001d648a004000381c0c0e200d40c600707490b0039150001884140760341401c81e60745050010b80e40d5a00c66580044e03c2c007403850080c09900c0050b6681000440039190190a404e014210361101c204800117880d80e03080c2003d000c0d403101103161204031050001d045403000500d1501219404a420b5040c5175242d00314501c1d081440031003003c0f05880703150468201101c00000c1c10480e4084004022418246c0c00428540c40306030f4001807a08025000034000f0102920305650130381d1140024001c0c440c40c07a01180d041482c1d030034520026400c070002e294581d0650703c94941300e041440025403c0300050f420045841a8241203221285000842142c011445460100002c0d14102000c950030005200311203401000182d440340e80e81d01c4c20304200c0150710500045007084500c0c4211001611391650181c02107209480382d94a8a44005000011070072070340d501b808110001e020300600399004161550096003005 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 203359910 1250 203358660 203358677
    0xb010b04140d0c0506071b050f2d120c09070513030b0705040e190506040e070504020918162d0806030a0804171203010b0a0804141f0509011a01 63
    0x24040040d40c204d60100c1c1d042500064100c04008001070384c4a0403540c07654100c103c01da10b60741400304005180e00201e4001066618032001c4035080b1584c0c00550790854031800c0c8110420000c0340d8102e0b81007011a8007540044203520103840c0c402c0905900411500d030103030802041e115030342e1840140b880040c000441c400c1c00f05070028498011940a00700101e00040141000d01d0580d400c2c081ca058019607031864900801d803c1e04c0c05003e10324850300c00301d004101c114241010032000394400c0741c0207940042030130009440d075400208400e104040c8030039806141d020316440645005840510031281f4891400301b5080e030301e174801d4403406d218040c3c6084981503403034402003032401000d881d0180c50f0b20000720f8005a9027902c0003900b071904c83d080382a6200381e03080705a000d0250100703009a201c11803003401603281040c40360022650082c06042500302484034003128900b00b07d6003003082e81405072125806200b90429009031074210300c03248020088125501000e0200a82e80c1429604000080 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 203361160 1250 203359910 203359913
    0x6070b100905040b09010b190b09040b0d0501150e04080a030c03020d1406120a1101032003040812090c010e040c0504171006081501050f060c0a030c0b010b04140d 71
    0x103540100103445a11000c02803070415091030110450b0850708a81c20f5030801c1c1641405040050b06c01c9030300e000b011013064000e401e150b91201e654000080036078000d1b03641c020a481d1030392000b00700345000d8003d100002d24400c101071480e0148403243c000056032101c1e00c080c000041c0b01c1d07800319a484590340c640002e195802c404100d000e4407808014140c03a90401301120010b08030056118024001100c400450804a00b2000d4403031900e4030b40540101d02082c9480d426502030341141c4120304c04117510295000c4c00313a0044586130816503054039090000303d100c03d5a84031081783385800ca0800002042c81c0c82c180000204561030648140b0b0182d5110310040c0030f95401903080d2000b5180300b2014141186280320441d54440c0080002141c450804100003504032000c52210b509062900800c16182c0c00d000900034000440555103810410400414800603010311a002d1000d100c0d0b540c001d0400290300f0720042202e0107801c50403028004000412012079100c07a07980c0a0542036486040d9919076 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 203362410 1250 203361160 203361181
    0x3050f07060f1505030a030512090304050901030503030703111206040f0609140912070507060806010c080c0a02100f050d1a0604030b0915060109060528092306070b 72
    0x1400030050400e81401c80002020880e5085070060070244441d102c0901d9540c01015941d1080c0c15000c0d01082c001c00581d140d103510f480403140c2c03009001017100e2401d80c0d90004100c6010090b481a80c00350070100c04e101d819030b40750040003507501400d12070302d081100c4040000741c0c40f00041c103da48a60780d900440d03034100710323141c0140e0700074101040100302d91542c490103440154402c0b5200e04050040c800b80c512800e00160595030125046801440310034180b89050307804a00103880f050501c0800d440e100005040000142084030800000c0e100c1c0303850a10500c00010482100a8240301075150481800d5a11005030b41440421600106040aa85d00c22040079407035000d1850304000300003408001d114036040043d0090740700a08451f5450f54110382d14248070400c1c9c4250b4002807030a0300400c00030344039101801084503441000c000e0041300c02078003441084a01d0b19000841d50500c5c1c00c001c103a041014400e0400b41c003140260880303042c94001a0107100c0c980f001410450000e02081010b40b0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 203363660 1250 203362410 203362417
    0x40b070503191d220e100e07030c0b03040c0b0a0c0b04060912090819020a0305031204031b080307050f0d05010303080601020f030f0921030f0414220203060103271106130303050f 78
    0x60000b013000401f40f000052904d4280c240800d403a40c0ca5402c1c800200b000d44241141c2c80360f608000220019810081caa4801d40e2001100c48204105d01d519400403410404080e400f55200d00b400041480103490700c2d00120400c0a580814040d10038010450080c01041c1c1000800c2d20301020102c641040c80044d07000380151f00080c10601c00452004402d018110302c0c1c071300490294460391100801c08410112800000c407002f4510f01c1c0510100da03006e40114041e20034824040d207010b00b061582c00d04202110401d0740141d0004e41e941d010f10242d96014005805101a128080d5161910f10011404248601c1400c4c0c1d000304810308060500c84103071210f24034103a03091f10a0742da035103041650cd01041c2e0010f024503900c2081c00e6070707440c1c05443c3ca0f01c002080f40c800c1c20b00041e400c04918202100075000103001d1410301d5152046800f00c07004000c039115002c4014411801c800c42e0034180402d00e4241c0110413405024200b00084141e000c50b20100f0803282d0501e0f00554810221045a40a00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 203364910 1250 203363660 203363683
    0x70501030c051209030d050919080a03090204020a0c031b0b0c09010507050f06060406090e1005040606090903120c0e0112090302030f071a0604060b040b070503191d220e 74
    0x3c1910003440322210010000f03140c8014018014011030f00d5045000f40c840040c16100700319140039070000303000070f41000042c21140c1c00e14200060400c5040d004074050f40e00000c80000000d468031140300815030000c0c01c1e08032559800424109140440d550150313241005010791700e1030f05001c2202d4605a00c200100c81405a0005c10341d4030058003452001d60b01d079400d1b1a020b1103a418490701040d030710010b2040c2c1c1c0d01d0100944c020a015800310b03243c0c1d4018200508141d0f8400e03265000400da4041c0d0780100d5548034400e43c1c5104039451203802142c125210414643d040001d280700981203a07138810b69034814001100d10009043c0e1080c90b00f645140714204803c9000080401d8100510002200305c2d410789229582c0c1f1141a900c40c0100401c6502c680140c1c01090000c2c401030000f41c0d0340c1e030007600219104008a0340f5002102d41c071800700e0150f01598000140000880740e01500003040110380301c40301540c6401c0c2c88013000b090002140114041020055035a0081c88880c8078100282805072 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 203366160 1250 203364910 203364937
    0x1011030c0304030507030302071d0a09020103110a02070603060902120c0c0a0605011503141b0c0102070606030b0105310b1906051306080402130b180109150b0c070501030c05 76
    0x30b603a00d2601d1910b4100c1d510003038025004440002500c0b43d44190b10000005103142d1600465640b00340d04030040078141d205a0415a0f43d40300d00420254500007030600f601c5070b0300104400f52400ca0000c0a451141e041014454014400d001412413041b50281d0030005041d03d9980360707410f00d002c06140014550021340303001d08080001030001c0807100207030021401d940d07052085689055001d43c00001c142c44103401d850740088410203050340f02d000703040d0b103500c04000540380c080c3d6501e4210170340708580c00a0b11214910801041549804039045e4901d00c10340c0e07200601c0325684a003820607101c032031006100d4551190b0743d4440694628400c581c05c040c4281495006649411008025170000d960186c5007141d22400450294080e100952146a0091050304045000a401c1d4041c0100c42185900400300108510303041d02006940b5020380070a180020702c482100181001e4626990b0261490600c100300001c01484040b0348041a00c40a0902040c08051401d00b01e0700d0348500429030508 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 203367410 1250 203366160 203366167
    0x318100c1b03060506060c061b0715021305010813060b0d080a020a050601090e03032a160c090203040f1403160303090b0f1306050606090619021203061011030c03 71
    0x30407640c10300142602d014280c20092030307848809001702d0b445031074000d02d0943d01081c0020140710306420480c0c00e84070070fa89482e0405510b50b0f00c82410307440c400844c03881903070082080d08185000c5e8213070300010b12003407800e05810b051030101321404004886c070103402c2544489061000b920351840c1282c116034418010b41d0340da06014070013503c900c21400211410301641c0c00000e03607043c882c000c448088100300080d51a43e22954041c1081d039151a0042c81405500301c02400000648005400c10f15044040760b4030f03100d03441c070b4010780414a1b074105000076441071051101188907840342007440344d4400300c1c00b01d080c40e807001c44910314000e4400b142c290840140c003040030594950021100c1c41d100f45102c0707555480350200c0802c00703031044034146410700f2129143c802180c3c06411160704001c014190a2421404d040401d1240e03014000705546140c11815020401e0703410032440e804056000449400e50038182e00007250313110b803809088204840001c0d03500c680d034414411141075080d4141225134 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 203368660 1250 203367410 203367443
    0x30618020d050c03010b040905090106091401080f1501060c020409171804050f04021c050303070f1101060f18020909040f0c08010506010e12190501020301050f01020318100c 76
    0x41d50154441040c1c190400020450603510901501c0c1610808080241002c1c01c20030128000c00c00200704000c190340700e5800244010841c842c07504400e100400322400d640c10604401d2400300c0b294070f00c041c0e580c0164541098140310100700c41c190b40d01032030256103161242c0001005026045401f8258415690200708110300b0342c00100b900c40302240c1c06c10421111303041000103c8000300d070103852401c00440004e006240194602c0c0e480b80302d00640900c040c8154407864650742007100e0210100344568020745209809c05c008441544240e0024040d481c244044a01d0900741c6224140300d10010b00100030541c1e045030160340c0319100141149000380307050b04081c000316141040a56001c0e038200b40110321018107003e41032040c0310684400c1c11145128050080c1d503001114004424007030160740000c1450248280f000050281c1d00150b129410f0504101c014441121b61a0540d801040a400705416020712190314102c01c8509500140071480241c804101c1d0140042c10840103034074121 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 203369910 1250 203368660 203368709
    0x6050456090c04061d0406090f06020c033a02030702030d1b0e012a0311190302010c050c0601090506060405060f0d0518060a110c0703200114030a0c0306 67
    0x1002e1000c100c905114541da1145002c84203892807074103540d80103900c00001c0214000741c00c07040c0010300c5076140b28810442515600c0c126000410f03440081e4100013030f401d80c60940da210481d85049000e103008a5100005030490010382491100d802c0c0b913801100059409000b0310603500c11481030b0005100e141900558034080c92581d03500d00e40071802c0c0c0c0150a609510520020b980420303186030030303a4000308050100f03c03100907810f0110104209400c2c01d13558401c00340007507a0b4121076241d411182400c149406030a41c2c484507115030170040c0a0100d062003010004030365045038000c200c0029981c4908020403402c0c0f26a4000c00d410000002e9040d600e110303c00020508244411820016900c0c0d00b01c9410070700038800071000b42030b800b290108406549542c0512115030014070240e1030703c0507294500307007490f46a80c0140e606004102901039a0100c0c030b00a0f0144080074a07251821502c0c1c0912841d850102074012041543c0e1080715940041c06648134070040c10f00000301500c1844079000d41e8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 203371160 1250 203369910 203369923
    0x2030c070f050a090e101109100302070b0f161206030b2a0301120b07020c120c09061f0c0809090f071e050904020a03060e01030605045609 61
    0x902038441807400240c4c140d41032003094603001c000e00260401c0d81e80c07414804041e00e103a107403000c40302408002e810159520804c0d2080d1114440d1000360700e40384c2500781188404802002c4102c400100d0f420000c0d42821508d06e0000380d03945003420441d141e101e800c880d00800250b00010200c502803403d00080303641030841d03526030903050500d26000f04a2405480d40301c1c0828421204d4041a503603101d1700043c0700600a5520182ca8412108040d405000144900c4007010401e12a1b0304141043d02d0300d41051070259a0001d000d4034101882c0d42e0304012108031038104406d4030b041002c51903900301040281c604541303d41c2401032802101d4209404200c0c03803a030041c0e03854004203000459101200882207140140182e450b150941403990402c1440065805200f283c401c01d03a0390316010845407459400340340a940038020020782d5241c546040d40748c5c01502110700420141c0380703d5441d09589a120054900011005408066140303003030701e6109a0031141d0304400c0740c200071081103070380007002440 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 203372410 1250 203371160 203371169
    0x305010228050d02030916180f0204030f0204270507170609060f0a0609020c030a0807080f040f060e0109031805040603081603020c0303040807030314030f150102030c070f 75
    0x40c04040c4158601008a111034545002c100103114000c00c1da403040d805550710290380c1c0c080d64a81004c00c284008140d0301c0e0f8002c0b158441207100c088110b0350b460f01c50b14a9070700c1810011440c007825500d0300c0040e0112140c009100b151500b80c07401c4030030900060400896521804000131901c80c1c41c05980300d00c3c0501441030520b90403440c0290030000011301c2030146940300040e01d1182c1701e588880d02d400340028000d442140d2a02d00000e4001100d01c002e050240014014549411200c01d0081c0b1a0384043c20500400074550141b160440c42100643d0708142d000119900038507062408a01a1107034200b04031465182001031400d140c0c20591030b1112080b6091110211342e1110f0410046600c140800303440050140712030503440c101404407003001406801190051211400081e1640e4803540003800c040e040110700300109504403032002d2603031902140e0a419031074541c036000714403074005140a000aa48058444c1107034002e0040fa48206200c2050300d40c5907881d030790240e0942040d40f29 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 203373660 1250 203372410 203372437
    0x3070e09070504050d0609060e0f10060b0903070b0a020c04050a05090105010801051006110f0a08130902040b030a02131806140607120804060609020d05011e06050912030c030403050102 81
    0x800242c49801107030700751580100481c0124406444d04801803003002c03412210b090341c40608107071056042044032301c12403821000304800c421820040007910b2159002c2001600d0501400c0200e5030701083d20750a403840ba640c026141e24515104900c2c00030010312142d0030030b02d00414040c0700c030200d8009a01c02c44203403000380090b0342c1e03918886080b00d004603002c01800c8406c64080c00700c117110380d092840340d068003400c03503098400031100c150408050040c101c2e0140300c001000c04040c02d92406080c002c041602c811804c06150014108151000801c105141580002c01e03184c80a501030001028004041041c80e0603110402e914006003214080c0054840c0389801080c4186032802c102c6242c1903024a2101c589030b810f03001070361880d49c0640110740c070741e0721108041102d10352031024240710002a034002c180c6514141e14007029610303020b040c11091240e003209220b2107811004868a80d401603401c0300741c0315440d010640c1107000e403488010380780c000064000103000701500600030a030040403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 203374910 1250 203373660 203373679
    0x405011413211b050705060c070312090501120e0f010609060938030f1005180303042406230a05061903020306040b09070809010614030a0204020c030f03070e 69
    0x101c040048040300b41800040c80c5080294600f0305403c50201482e4454021100990f0316440001e2107074100b0720b100d120b80e600c41d4030200300380325440c10700080042d0141044a440c0d0304241c00280525003550026440a40329013007420040700400c416514102758030000c1045545485150002c0c14a6200b071002103414424007011000255445681007070821018140750580c0b01d4006d030710150b0080c1025030500480c0002d50354110f06118103640c8a1966400048502d040c50446604a2040103c201c00b40d00030310030403000400144214003060700c4142494060109820090003410345500424500001e254003420b000c448081d080c01500d40450b0307a080f08175260001d12140d80680c41561080e002c0b03940c40045418043d50003907410004c081c0010a4020108000c03d10f003a005507003074000100d81c4020801412000e1054801070f248001b41468042d448000081d9280d62016001e03101c2e50f400510400c016004004498140c1e041654243d16854801400b506444190b1441d40c082ca01c0e86 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 203376160 1250 203374910 203374943
    0x606070c32010f091415070b060102060a1109091009020a170601030b090103031b02061c270b0a1d06070e01020a080409091401020301090f15050f090405011413 70
    0x500c40301c3e881500ca82c2d54808490f03d00000804846803046115801c818101150f96550005100824002e80100107043e0b040c2003042c0020b20b885e000420751000c00781b520308841c0e101c1c01560200c5440043c100d52080d0716440e424a01c8103036248560103140f2862002414404c010b41004d034004070840f9004108031266a104019400d607900d0312383c060390068003038006000007402140210103191031713003142141925131640031072882d502c015441d5026100616010714414040c2c0140c1c050321200c1c07902c026401007540e10b03413079036445078410040c422085080010034a01850340550022200b542c2a030f08902e00c5d589103540c503608207940c005e0000b103003031031b42040c3c6500006180e0001584903a005180902d000780f0500101803501c8101c64200e000f0404c0c0024a40c2400514040c01c020b10f40040c02c11444124041200d0951107401e0201d52200d604205540c0c0e246c040007402e200a80c0c103d401d960f1903292840c01003c1c2c08000306132114102c42808441500960b0035200c280c130a00c1c01c1001856007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 203377410 1250 203376160 203376167
    0x605030c03060f0a0b0d0f0b0709180903050d180b090325080c010603030e27010303050a0504120c060807030203090a030e0a081506150a080606070c3201 67
    0x40414440e050b03401440400c1d110000c44400652208000c03078005425140f1400240310700c0381d6501d080d50f42c05009100c035803d12507040c0c5408c0e08480c081c00d00203040c5240a00344c807820f4034915642d01000d0360b81c094060505005100322041c0030940201002042412011707109000c00d010300c1511540500d0740050030342000002268007201400258010b00711141075820003041c540201250120814403480030284403d0151202552080e02c44500d03c400003024421500040e040303070341c0d600e140035010144582c070000306281529050728002d03988020b10300081c0d490740302d19401110f04050b00c1d195501032010031544242903580d6607466804c10b40b6200b40407000d030302066174406c40c150803c00b100c00010380696a11040c0083c007a2110440c00e07540e07230300a0304120b8882c62a010401ca81410403003145010094036114485a0300d01c3d034140499550010311795000140740502440002a40f5003d0081c0c100d891030085c81c901803007005581c8601e0700700010341008a4080069600e541c2180b115601 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 203378660 1250 203377410 203377423
    0x706060e100621110c060f0603010f02090d06090305090a03080d15030b070e0102010e01060608010f050907021e010f050405010b030601050a080a03081f031a0108060106120903091e09060503 83
    0x3c115040352040d0102c0f9500300020320210012041c80001003119400d0940c007402202c0c4282c40c00b001360b07002494510149801e43d400301405080c654810080720b035040d5242c0f18203040385ca4000000081d0301c0d010386030a81d1184030b0b40e000c6c1c2c1d40c02001420000200a2000028204001404d0040c8070052402e00c61000c0000107000003406002140000b44603180b0801500407010014400881d502600d88a003d08580716900b0660000300158018000300c914240b07443c000b064203441d0315034145440c110003902d0702d00c9030b40f1000b035980b0201130b0100080c04c2504804007803581c50401308494202032404500801512041b103011340501c0e00001042d00d00184440c0032104000c000d0005100c00d07580840d070480e402444041c0b1001c4a156882e8005205907130000507504c00d1994107015203540701d49126507803050344801120384c0300c100180203190340303c1e441a0840401c44000306107400f2604e41aa01340700180c004005080800354612151114120460212440c3c18401c008181e03d81e41490349032070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 203379910 1250 203378660 203378687
    0x8060403020c010315030201110c0603090c1f090608071101020a09030b0604060810021303050f030304260f0a020f060c0d06060c110607020d0f0303020d0507020a030c0b07050706060e1006 82
    0xb2105c201040507500a4017030100401241c0c0545880105500010300141c20170754660b207107517001b90300828541c20072105086ca1a001040003038142138012000521700201d03405101c0030000840c0c04280403500034540d012500341020025900d6441c0c1c80002017a03252648000d450700103c500100e18681080d101d001c040e5503d4401400601c481d043c3c1c400c010394091100c4010f118550080000803170820700c08006200110f402969690a10b400c14207038403101c000354074101645110035490086465003c4851380b00c1329a80c915152116800180d0515008400742c40290040804010a1454807402408485100340b4100445521440d04540880c902080140018400c808034031440c0b8220001d01140b900c0105000d00c0c01c1c4840d5200101706e140410110040394000c9282c1c0007070710351401410751145003480288010781c40354500502140300c0341d00207080b04416001103080640b01c0d00c121064140c015034140083c581e40c641400304030508450348403600c0301464000c6119442480b0207032200 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 203381160 1250 203379910 203379941
    0x50c060a02180f0a0923010e0f1f060c020103060915061407021509060f16050601230907050f07080d0b03010603020a0b0903010b040c030903020601051009060509030a050708060403020c0103 83
    0x3400d005c10b9030020002e00130080d0001d4100e288100c900c0d14420609070282c0900134840303d6a0408000d40e245520001c0c0c00526204801c09d00d1020f00c1001d03a24500817a580c524110341c2c0c3c3c8074140016070082102e0340000150030704200541400f10184d01888040f07074a16078905503003c0391281c210b4164003076020002d6000d15800c289a04d00c0d640c51000c1c001002c0300030001b620304815442d502c2000e43c0458285041043d56001074014000140700c510300401008685040c00041c07000103400c44040c04141030711070720004004c964454420030075601b08001c04c10081c0d59407451410400c6054002c200d0b10b000c0c55060440344407150a060084004803580a032441c10035030704081c1102415000000050382565840e240c0340410381d03d50044030034150f05a140041c1203051418021300748030701604172900400c0990076400f08154801c06c1c2c1d20480d4003d24081d521003281c1030000303092010100f0040e165204200010906000c00309041c0d00840c4a42c0032a5001c00c0681c0040d400e42d0303851a0340c00d006 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 203382410 1250 203381160 203381179
    0x1002011a0a1a18030601030507031e1205070309030210050403050106081b120c03060406020d05060a0b09011808030406051c060501170603010f0e07050406050306040b04060903050c060a02180f 84
    0x8550084020f04140d0140704041120304030b10030003207482c11600368001c2e1020781c400c1c4810400c0c4036440c1c1d50000940540c0101c40c12240d0503031562100420b840c11045c4c100000003c5020505115521110203140d00600d480d0300300200d0f600062494004d4001070720654680079000803c1d403000100040c2124030200704514481d800b408006200b12100c000711074500400b640c003c0d0a64040c000345203c0d5106000050325044c0c450012022a64014001c601854511100f80b004240e5402030b034801c2030091900600d00388012102c000b059200d5404a4010302c40490081882c0f078002019000c5161400c01000b5005550104034007541d83c7c03807190070301041e0242c83c6007900003121892142d101c00c018001207000a41003025030104d0304403201e540c2190300401c0044c8110f180078001c46005000860003040c01c0d003031a0300c4140322640041d01c020101542c95251104260150b402c0e50226480d440036601c980c9407451804004e54401141e800740f510171014803007007600c1e0190b4000264400908807454 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 203383660 1250 203382410 203382449
    0x1090b04020108060d14010f0c0201051506030c07080408030a0806010219290a0c09060c17091c0308010905010f060f0e010e06040906051c051f09021002011a0a 70
    0x6500101030151504008170425805c0402c04094004000046150002501028016400040700c0d19185c11104690402d0280010780c4c40d02c400d151b0032407030111160760b500c2c0c6500c00c0c40f030060711442d040280464004600040c0400d80400034000190a648650b000d2303a458200480e2280c0c4025000c0040034980450b040124180d124440d030b1500c025070701d4803020009248225101e40044030524061600d40700c210b0b0003594088800d10040c0000d0a1600a4080565a030444044c052030f0aa80d0030201141b44600c1780d40349150700610700141c1100304100100380c240101184000d018494000382043c00001c3c6640609000f5000c550069540c400b603589080403c59115a240340040d0401c8015031390283c02da61200001d10042841c1000040d1151070441485405850210b0303141008040c3d491607004180d01003071a0085550041c2c10020464918014000900c0723203d10207504941030000e0420340301c0d01540444081c235210080700d0660141c038000c108070003040f070040301e840000c0b0848004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 203384910 1250 203383660 203383667
    0x1208090f0f100e040f0603121710210206041e080d050d0f1104180e0f031b0115030605090f060601350a0b0915060313021306060e0f0301090b040201 65
    0x59443c4002040422651004840c1c50182c410941003601c0521440707005444040c1c2144c5c126221040c40200708405144c90f03100e989041c01c003403154140c020080941e1918014025000d40d460b0356000345002d889a488440c0341000c00701c0010908945510700c3d0380450803071000200270983c64246d41d103003440c019100b07251101504550500e01c90103902c80106030940300780705010340054a43d007900d1007a40c400d158070350003d03105c090802003140c1e0040140c076155180301100700e66000c013952801402d9001e2040d061801803400742c00e6001c55280e1060301100704145900081d01030072210048521025000c03504640766030f415a6103074081015044407220701a134844440c0c15100144000100041c0c10800c40c64008104403075034515560346006002d024a0210020758100111110083c41610b404011418900c0050803003c420088440701204540d1044a420314a003103025090100e141c0e59174001e800c403800410854440d680c01500021603080511403160340035004500c4020325190740d001503 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 203386160 1250 203384910 203384927
    0x10311010c1109010603050702071d0406200a03020403020a061d1201060308030903030103120801030302030717070807050d090506130312050f0a08010305060a02030c19091208090f0f10 81
    0x480700410b041e8500d440680e01c203101140203041c00e0b10301181e64600028001d04001403504111015070355210b40c0280b03444040300f911b520580c81240051418800f203c46051105c0e40480e1600f40c4000042180c803c0d81e154001e8400c680c400d42d0315506154613008103a40c0030622442d20460101e0105041070300d481c01034041035415016000002e10941c40380c840c0f81460b401101d1000080c3d01c000010401c00011105d40c200308140344c41e0111055045640003512031090140141006d0213162400c10310050550440f041c540d0b20554070b9903159a03d10f030090300c406030200304402140e24100002228140f4404544404000e54400c00c0c515003180d0703903244480b082410000030444140301035200080d181c0010a903084107074448500341d6255151403031400000800092001d8014001d0103204182d000944000d07002c40502d08100c2c1312034040c21220038005501c0030302d01c254040c144030300b440004801412807110a6410b0071440314100144000c1c3c40740c000d90030350030120041b0903240c8207201d070549 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 203387410 1250 203386160 203386163
    0x17070f03050f060f2e0e0a0803040b070b0405240712060803090103021804060305060103060e19020f1906090f08010903091e0b070c05090703050402091b0c010c081e010311010c 77
    0xc00d22840ca074900d036180391202e0360717000c43c000c01c60309900c9804900c0c180b2151002003488078001c6180c00e0502c20300d4016800b40c604000e0588030000080350400c0014404551074030000d44150712041d070030300001c0da82e1880c141c0309607012400020001010300304502800b0107807001c4e074006600d0482d401e0011002580308200d1100d48000c104101c3c45580c0d26805607800560080d0000d04407941541007620445040c00310701422940716616100354002007829000c1e0964044401420010f85500820000c0d120303203030181c0728031024110105880c0c1d089115442a00e0085c948056111784030b20700c8a00b02c4002502c081c01140014008200e5236040100c0c00d2140d1041500d00110319558010050190304660011550503120501c20702107818011070160303000105150500107824150041488400060801c10403071100c48028265040c0c41800c6400302280e542c0208040e00c020880144010816101072188568000e0010361061021012078180c070b4000b451809140d019800558403035020690 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 203388660 1250 203387410 203387449
    0x10c0b06010f03142e050a0302221506110f06010e09070f0303020606040b0618060d021c0506011103030403090603020304140109050114010b070f0b060117070f03050f060f 75
    0x190b02c03006400382c2e4000c4c06080960001c6030022203d012100c12415410785d8031350306290441d0f0410080e82d54201e9141201d80556461428494480c0d00c00c0c1c510710903140d50172030a4100089040010001c0400307200700c5200c2c0c0d586540e640240800c1e292a0f64005040307003c1a440200103022903d0080903080d00005008c0880c0c001c00c1d540c800b00b519801255000340c0141c0c00c1031007001514240790142a0701d1400844401c2d1600e0f10740715200540d142e1480034a40911404280210000d81550442c0c248180903050040341403090080080940710031564540002c000e50108542100c00005590195a26450303107200c135410040120000d4000804c19102c468022034295074404086c03141003c0c850051001084c01c4030036100c680c00380302042e0b21040000d0420000b24012038452038144c0305c100d500414007180e40d02ca010040701c0103c000745c8000d60001e044018014159004a00d0b00e00181d0302ea2002e01040d82c4100f0709000d01e0404071100c5800010119000c0d400385484041507621614551 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 203389910 1250 203388660 203388671
    0x5060d020d05070906090c0c0f06061706060f100219030c02060705010209010207050307080c1905040c05030103060c0512150d06020d1d010501031e11031507030506010c0b06010f03 79
    0x1000951141000315054880e0f8201c10307001d00804502c0d0040307001900c01214103000f202c1c12241c00408440c841200a8040d00001030300004000c0c0ba40c01090082c1960040c9540c1c00c001c40c21019200c600c2683d820b0f110ba41092420317006400c2010003408075074059006805c90601c040c82d4151803d0354074500f18104080b04030032400580d1860040c080f01805072000503202e05110002a10302240d50300030078030a500502c0c042008040010b4142d0070f9400c20f40d601115000300420000c142c8105070420380d403040c00c000404a0b0a94000c001c0c3d4100d0b40244004d020341114004203a699120308406c0314261a407030000a06c002c101250300c5211008054440010030f2a1074942008a0300302c0c0c030303841c044252103003132522031240c40004078940e10030040c000f040154503650301c00280d4440380074414408000388100100384126050b030f120440c01c0c0a0240c4900002c4500c010001020032103070200806d1610703002c103d680d48228002d00450f6840001518643c803401d00542d1511069802501055100c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 203391160 1250 203389910 203389913
    0xd0209070c170307030b09161b020607050f120f0301140303090409050106151d090c041d0109050c0903070308030a0f0e0d08011e03060b0d060c081510080a05060d 71
    0x1032400c0360030b082c0041e0341d9124207186000400340c5403107610f8644900c17001818004041507010003101415080d06000ba52a07014030200c1a20400502d00a0f500c0500480c90109204000c40c201c410700720081c2c10764213a4044688010054011012035800380d0344203100500c00042c030190b43d681036240080451307040000311400a4240c1c1d007070b4a4110b402e41d4544004200c40e030100402c904c4000003d060006106180c0f00060a000070560301f280c3c840e030080d1000c40c050b03040d05022500a0b1124141080c44405c0310240c01046440038490700600b0ba2078400001d50031580345041d601c2c803c400402420f0080d1a544a5540681024146c2c004441e5101030f1400481c0c1c0d244608012101c010740a842003a00c002409010010164414502168041d0300700030b5280f02d90701450300381c83d4403003400602c03090304a0101d00414a540002403049103880402c4141e2a0000c0c4203901c00ca00302e4540c0c809117580d40c0103110400c50ba0a040d80045140e000c003050145a0940106a01c528090f0000740700d620070b07 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 203392410 1250 203391160 203391173
    0x409080706020d0e1b0105030f060a080d050a2c150d06090902090604020c06040821130c0b0f07030c02030a08040e0406051308040b030a0b06030702030a030510050d0209070c 76
    0x30b1100070710f01d2541c2d181c9030b108040c0140205290081580ca645a07424500e00020b071071484014803082d00d00b80c9c040c1c000b46690346d40d0070908018102c004d080741d823200180100648190720402041c004501d02002c200a1110f0141c105000d031200c3d03009180c407480044081c80158a06c003066040215001e11850249080c140f06e00b00003004801d4011a69048900502070b03132001c09480d26000b98010401e04214401c0080d4444e00030b54003c503800e80d10410381c0c5030072440b5009081e4001c80d40301c034002030050144d059001c1303000b100d008141e159081941c5400007001032260007941c07034411409000307900c0801c3c00340c0e84117040580050151440c0c1001c0e1369406e000b591140d00b001048120078424001888420310486600200c2c0210001c51701d14191a07003075031401644618600d602c0000001000040d180c0c10400d800341000e4000c41d103d0070510b1001c0c0d1260041804400080d140c08005a80e0186070303401482151405400042c5400840d0240021440000c2400051007403400c00d080c002042e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 203393660 1250 203392410 203392417
    0x3070210020f04030b0105061810021002070b011806030506130302242401020733020609100506060a030e0f06040c03060c030b090601030f06080a0b0f011a0405040908070602 76
    0x30100b280300da855056140110401c070060308030364000c010502843c203480482c8070000460b100c04071041040c40c80700350340403031420400002a4441c03030b00229000e01008101c8295034141c030941c00b15030343e072000046000000c030b81140c80090b000e82d20410101c9c103c409513220911100d4001d105841490a55102818507112916041054074440c482001140040341d4600d243c54204d030845808103000010000307646071800d024100f03640100c00c40010202461099941505108540c0002c480d0a100d0b00a0744902089851780300747d00030070b050241d4070805449003510484000b000c60307007030100c08081117000b4508030500c0c112511809880700310418003045020304c00c40c414404210800d0640c5890b8060b110107a030608285410308c00b09189554400060a62121007841e00241d1407980752001d00103051140d00c8800c603805140b8400d02802494003c140c03052144c422030040302d0740e8032601c05040200d920f481c880050018001888540f81c290810140540078184850610706a61540300481e0b0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 203394910 1250 203393660 203393677
    0xe0f1312050409051e01080a030e0f01120903030e0115050d23160617040f031d0d03050309010e070f0e0c0d0203070509012c040e0a0803070f0216030807080307021002 73
    0x5d440a103411810001700d4072450245c150b140c06801e0500980e600a032621031007a010324426040c60411000e184d02ca5030f529603815503090018012810345040c003034010105400c540e0295428244800318501e80c0301c60340800c03104040d04030181d080141e15405039035184c100d2607030464251080c60300c02d40d03002007010030f0032001c4082002102030b2178050b0180101090981c8540604000c0e4200000700f11008895000f071601420017000540e01e030007480d4494511800e0441d8008000b00d6240107042c0e006001d1072091a041c1c00030400301011500c0c00c1e42d038140500c91043c2e5a040800c05005803200c02c0c1e490344d0004804158031b41800710020014080e6001166024001400820700105940c0e208548614805802618040126030000d20fa0752a01c0d02105031801103072600401041c50004006103540780d500158810348070308240000800c941d001c0e103403da0052180b0030891400498080d010b0382100c1d0712003442841c00405955a03146030f0070040401e01540154007841c00c00c445240002c02da00f0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 203396160 1250 203394910 203394931
    0xb0a030221041a0f190b0a030b070221040806340509031b030c010f0215040c0302090106080105091801180b010602100b060f03040c030602040e010e0f131205040905 72
    0x240380f103114080b9141004040d500c01d0ba081105105088141e0a440d5100e21410040401c803000140c01042900c07903643e10040c008180c001c01c0000280d8045a1052104e5205041c02440e030740103007154200e4000c0e4003c041070b80c2c000f03001145054081c16090a0102c2c811006060781c41c0002c41d841403401708928034000420000201d403607991809000d40c07001c0702c2d500461510030020520100307a8402d060704190741440701d51164110b806000300201016281c0154001d00c103031405180c022807000152000b04c0c0541e940c44004100c3c1c9001d0308039a8140d5101074aa220540d4820285081500008111b050295a034000100701c1c10b100d0210122414040c0094206079454240300a240106083d04000140c1c94450f8460041d900d02c0c0c2100c0142025084032601c9480d1030500d13031080c50055200070221440003070001000c0321291810b074101e42802e802d0840bc2d42d1058000b0b966040e04640c80180d19580414030741c0081d04002c4100c824011a05e0103609003525403002d82c0c2103d40c107a8182c8400d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 203397410 1250 203396160 203396183
    0x809010809010e060402010807180b041505070317062d120c0d0f030e030604050a1203020306060304021e030f100c09030506190f0614010e06040b0a03022104 69
    0x1540c12640840d00800c07118001c00604a00c805050f84a040140000341008100c1010910492282240208500d00280d80181c1c0a54984100d160f640c098840e28807090040e03c0500065801003058641103901501e505052480d2500d140a110000a1071260300c1000c1c81c0d024060012003441c040113083c454080c08600711518010070205501c8020b1200250f0301108e000d131a29107811804a80f990307400300b5a0030621030b1a10301524000309040106030107200b0441000244040092200d030601d0140204110188000070b0480030303480f0072114250445020004100107061082100c0080480d40780032504007902c44000a040c0080008034507083e90040e0784509194102e4800d1248011440c10898035171032a5950741c41d181c050091041e8800c1855a801d051200d40340d0700101030307602c155901040995203e01880d4242015009494001414182d46c0705450614808507003c0c2c50000442c2da040a280b03a030114040d40c000c4030604151603110b250565089860014180698420302c0c06101 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 203398660 1250 203397410 203397427
    0x604110a0c0830060301060b1c020904090f06050f07140a030f020301170105010e060f010c1e300e1c170a1202070b0103030c02030a0c030507060e040204030c151b08 72
    0x7943d00107800300348264501901081701d000c0540c100da26106840d07003245100c0c0c2090348200300a0040000140c0c0013824210080d0802844c00c1d0400c60f001c1c4244400c01250f16200210141002c0c212502000700e91192200003042e50030303501030415100715140101d2004034201403941a03810030b0384a0072108100307011a50018100303000e818050038600b0360040c1945001e10000e20441801c46c0c20b107051003440c2c0500e03818031040111200c0100340f03601c3d85844220b2207103080d044e4010b02010200103040c403134484142104880602310b440121540c0d400c0711010b0340f0000c10605c04044031203c0419080c3c0d482d000002010f14200da1006880303e000c940d100c07002d0030b801421001203c003000703c2d9144104642400074000011007415030b501450401010000c500c0403a29000000b607018000e10320f0003c4c00001c21800103441d1003524016559900c004229005020581c01f07203020060400d40c040a041c082e01511114911a0160910307152140d4000c00000320080d0213201c100b55a140000601d003031317 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 203399910 1250 203398660 203398747
    0x5010e0f2109010e06041a07020906030d0c020121060b041508010f030f0c230a050111030d0b0102010b0a09060305010c090b07030c06020f0a020609060604110a0c08 72
    0x521076540000d1454890400460805462145005480c14010078600c502030079251030042da0040e000100d140c00c10401c000c110003103d500a090300301c0c4a081c0f03140008109040104602c194400c0381c0d11040d02043d02a030066510b1508180070f02e074048004c01e20b001010301c6a000300001080840446644c860500782100b82c030442d000070700781c1840414001000500c045045941c2142d030030060750400c2918030303c0c00b15101c0d082030748000380880020a185041c1e40c540e07000c101041408075000483c0a80e00c50040d29420101d00c1680e0301900103001c814030001054000a6030202e0500c000641840d011700054500f1000da040062140c1d618402842000402d00c50107462007100d007080c115041c5800b46440c7c06100d108001420071113286803071410130400e601030350120880e008071940c5441c401e0900940e41c10041b542c82c99a842404d000c60780c1410540300324104070340c420b41081e02e0081000c00649100c07981c41c8088030350080400c0f0107000c006103201c18400d500660b000f6203174078003c0c440745007 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 203401160 1250 203399910 203399923
    0xb10080a0f0615050a1202030c030613050105010f031505060a0c05010c081302060a09030206041806090c0e10170a05091e061609030b180f0105100b07050a05010e0f 72
    0x20700307015180c21810301c028440c030510f121003444945055a40c90800600407074108000b14071a0380c500c2e00201c1030010201030315011b180300c0c9101365528060030050104520a6690a10030325000ca001c03016118802d074801e03004400703240d003c070030403d4401d69075001043e5240d01040d803040024080c0b101a10410100b070090300b04100301d80c03a1111003402c0541000e541e9601442000744542e03c0061401c21003809005a003000b990014201340c0ca0f5551742c0c042e01c0344102d40f4030314034044d0b514141d008184101244a841142007599070b074040000800400d004000000490100034003150402c4602910b8170880d80d24410984001c0116090500140310303840c098500d4051180d11a07038900d8140344070000604264884003281001b650801c50000550f60152250009041c25108808004180c10142521104280d5400403514401c600a80e45822101c00b9100c84d201c1c9107081c541003040e407039280b000d400054043d0f4203a42c58150300d60340d02404c641600c07445800c0c0c0c0d00100300d4402d80200a0004 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 203402410 1250 203401160 203401181
    0x10518060702060a0207110901030804080127060917070609140f060c0a032c06010e0c030609190207030c02010219231c0503010e0c090d0b06040b10080a 67
    0xc00d040c1c184a20003a448000c020802c01c112035000c1007003c2032000760760000845407800303050904c065071642014008c540c4075000d460341035800c004641c00e18814040204400c0303c8a00c1d4103520000955403600040c101d084c0003a6140c09a8081212a91b00c1d020001c0c000c06102e480300007100d805a2616500350102c03441244107940000c40103851600001c1889544604141c400d20303a81e4407104001e4004201c1c0d0501c00701e915400b04544d82c005584990711030921700484080760f4540c6e13070310320581082450490302d020481e4401e20100d038941c14002082600900800e030300c40322000001000200f280c01c1141e09400184140c2c00440555070144581c400749903950601003c03162041e214488604003030307680a4081d5014a48105986a0500c403523150b080c0405002c1d04072487c01d6030000c02a07002802580519000240070a04120300c45040b40c2034100060300b00c00201d40035450310b002e8550018522070300f26803664098011781e41c41580200c000001520360340c0c214141000740e10222081d103840c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 203403660 1250 203402410 203402413
    0x7120801062f0a0302030418020403030c030309061d1005090313051216064b141b0f0109050618070803161101030c0f1817010518 57
    0x14880c46501030612000b0030450b00070482d0300b910948009003860414510280c0c0380c01441c1020040550220040c4201d64010b00c2c040024a0070924040480c030a9100c024046905540854006400b030740043d200746004103000100b0b081c4003007180c61400849a003101140c0c000e0000034400700c1d0340b4480c0315041204030008500708800f04814406846c00781c000c01c0d20820b034010304442c642c1400c025118403180001041c1c41420b603601d0018000454481045101c260704c0c6000b418200c030f50f10480c00c01c030307083d4105803943e80c403810000d41141c4000301c0c5a5002c028950740342c001079103040700c001d05010300421440c0d0251411140011f040022448018400e41d052105100102c2e900082d526008086134500200407140e6944c49407429540368044a250700002c11150a0050303e401c01e24049030080c10322049450002c0011421500040c4046010500c80325081410303601c070300f4004078400b201c0840304000e16204c020b4160b14540300440900e81da07454a080050100074080305413042c591010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 203404910 1250 203403660 203403677
    0x2070209150108010b070602090d0305030403090b090303040b0d0920030d0c0506010501031d0f06010510170114010c0b01090b150423010e040516091a041a0708030c0712 74
    0xc1c104030f410b2003030052014002c03400d24240819941181d2801c04000d18010646005140180c46a0803c450582c08500294270000d108801032044911501c00103020b14501400c1011035000307904642e1a848500d0f5885610030b0009810304442910419540d440104072449a8205490711a03120b90040801c8a00302080700003c8000410505441090030702081121800e100c29013288401101c520a620030349240042060020038054186c66042d911900112074005042d15101030321030f42100c2802d0520010802c55032181d0010004550500d050081c085407900c4442c40303035900b038104102d4036913101d421080f6440c001e4011003510a611400c01d040905d40842c0c43e2481c092b10068501c01041c104c1011026841040040980034004208002078101101401d07202002c10407000e021400610012403641d1140301c0d07281443e03850112161500e802c1803120b5001c01040b0003964103800052288000041c2c10b203001d50300c070700c1c501c3e1351064580c034042c144410880740f541f4040041c001c001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 203406160 1250 203404910 203404951
    0x90f0309150912080d290109060f05030a0c0e04020a051210030203030a0806060409180201030c0219140109050718141605180a061716020d0804031e0302070209 70
    0x1500840c1d0303184d045100c06444403da0040100a0103a0001d001c41200c51281104074a03001d14010034400324003a40c2c1d017900c5648408050343c0000c11038100002280040c400603010600b590010f05000c491b03441c10103100e4004201240580e08451404004100d012803039010b5100000611540300c100d01848401641c50340d00805e0300d03841140030240400011900051258491004407401086002c1c1c0070841070f4913281e903180d038505800d44224000390400b0384480742c4034400100001184488245a512071007030381d4507002403c0f156000220079540344d868180124005200600040914101011503600d28078001d50894050354050402410740c542031217041000c03134008880f40b0003141032042da03600407002680c042000c002411640309078042008503409610416519040788444c1090a407a25030091520070030004030800740041c5e01034040240141c3c4102e981d90741160007070404109036480d44503110180c500109140b004650001400e900b1428000c03c0640c0c4140160343d0948c0d600c444 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 203407410 1250 203406160 203406179
    0x20d1701050105031f03050a03050304030e0a0302060f0c10050f06030d0c0506060d02060d0f0209011101051324050702070e09010506030d0e04060b07061d0708060601050706090f03091509 82
    0xb0340b055170130a070304c148007a10f101ca00003d080061500441140d8121f40c0604d0018811341c000c54049000800319000d127030180c1020020002525801007401d030800020081c4c0c040150480c40066880c0c0c450000c081c0480030305446054028200c040010305289443d2341890300c0d203c80f50700c4040070001d2051a04c00032690201d001038000c0784c1103c4c0000545030900000e11a4040c108241002502e040c203800002c10705540104011282a01e480103e00f52240390142207510480f44c1400c4180310404070f07800a04400368007250b02c8400001c603040499410b0020080340c1c030494a83c80982e0024006010b41d0321480c2d4515030004a4500903c614940040800e864114110030082882807200003c02c107a40c4039084000030f011607807010387e182e4990781403401c0944081d00402c82e048030032050752803082070081008001d498896001b0216900c40100440311580242d4060f61856941c10301d400000e0581c0b44545400d9010380d0390542e00030304183c10b00203542e8007079640100340034041c0790400408a9 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 203408660 1250 203407410 203407417
    0x60607080702010804020a0503011407030c030905061302150403050307030813021e010302271008040c0303120603020411120601030519050c0f03091f060308070209060d050607020d1701050105 84
    0x2428a004d41d1152143e00c08a07103240c481c0d0304116031550070300c042e46010318684030460303201c1c0d00b10b5a0140007480405c44164126051400b0240c2207811203000201c12002440030036519610140251031343e0b84d6018040c1030b0a0700150000c0701d440d0000114401496407003550907410000d80f852a034440c0009a001a140f07514206501001000b04e0715106040d0b8000c2d41a95000c00003240d900074410100948208140c03070f081d4100d8803030071020412071021440f9540003845198805045c142087c115141034a080e02040000e8128036220312001c001070300c9900604641138010741c000e0342c44921094466040400040280341014035120411409000070300c590501c8480d080c41c0012141c071181d241458900c11464008184070001041c4841004002482500b42d021165800d00100c0440c102c4015156944405006031000384072403070261400c109001d400043c0240700c000d0081003a07071060b0400c1d004894032070158000b400d001015540112601c00700c0000580c0c0c42c41c242d810000060550b00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 203409910 1250 203408660 203408663
    0x30c1505160c03030e031908011a03010e0c040807120605060f01021009020607020301090305211003060c0314040605090c010507021c031803050d1706010c080f1303050105010603050606070807 84
    0x51800a00b82c10325000c0c0d8000030403280c4100030f83c1c0d690001460700e0b074201c80400e24818005060f0000014500300e00a4114007107280c003002492850b4600a01c0d004045070103000b00d942500200b2000031803a80c2002007900400f51684100c94041c2641031440c125100280400d005030300303821030520181e9000c15020074407503074503900285810080c00820380030702400d24020f4040d8a4140c12800f40b40e000000303045000440603011041d50164050030300c50010030b50308070b41e4445846c4005c2c000604250807480600c0c0882c40c0025a503986041c114032080829502500e68030b5441c0103100b0011814488020f04005c2030034054a86081d03580419a11942081e400da840300840a591041603c04c0344064405941100714200d0180c582c1003664544122004000c00300d25a4001401e404c20004555441480c058540350500902629150b003264010623103540b001d2020002042e00c0c5008074803840103140180000501d56042200160031100003804081c42103000348035402c0050080800c9a507403a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 203411160 1250 203409910 203409917
    0x1031821031413060506030703030c020603042f0a0b0a08060d060b0603011706060406080309010f1803060b040506010201090b0a0b0a051008090706050a120b030a0f030c150516 77
    0x34924440c224000c1c1091140142c0d0040058107210700c595500d900000340303038081e00041210780c55010400d46c0d1409244001404140314840102c0949403070405103a200b806400d048600d4000d244081090440451000e101100d02400055240c00c103142ca40e400360101d204498504000000060220340005190500c03500305041000f04001d00e0b5086141207004c0078008603165611945507502c11003644280c15002c0c401e5074000b4003580740a0161404494586000c2d62512441000440b10700090528000038010301c1c84034981c0d81d0000c0d450800055004450001d003d2400000b040f090f684060b00e15411a0705182522000c246882d83c040c0d080107024000142090350000030134010720040d032110341e20850f500681240c03681c0003c3e03881e00c00c84411040e1007445842c0c460503078003806240ca2000005440c54002084545194002e4082c2100102142c03c9208943d542140800408900b10009010760301c01a082201400110403440c840c000203200d070380380c00c03a010010950260a42400c2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 203412410 1250 203411160 203411213
    0x80303012108040911070b0c04030b01092406020a0201020f0d0509010c06140109020c1c02060606090315010603060303170c0702090402010302130f051503060a090c02070f03050606010318 82
    0x401c0302c100200c8000300f00301c610602004030f608001401c0c60700300410a07101076400c000000c0325942c0140072501503e600548015159080400d1000148050158021001c401c3c074843d0301d405507450345440003407080f540108005070440c4002405c01e900c01548514540c850449020342c103030010160342c4640c40130310b0300d0f651011450400402409102d05104051089140003140c0001203030000e05611007248102c1e042e0041c0c0c9010640c2524461141d80d006801c4680803600e6807401c0c0303004007481c4100404907110403002541a0b420201e0a0340000046a5211401c00405800ca5042405c89511151007409480e207510000d5080c45141ca00a108812110002c1e045a00035416600c0518065401400861315008803810001241c00348501c140b030344511160480010004480c440c8402400b8100700500e040c0c032420151003202842e009600a01001240002070400e29100941c0500010079040c10441d001508455426202440139001210400042105096a8551030b92180319503900b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 203413660 1250 203412410 203412413
    0x90b24190e101a090f01020f0601050418020406080c03160806040303020307050c0a0c0801050603030a1403070512040c06170420010212070501050906010509041e0303090605040605100803030121 85
    0x9101c0302c160460100100282414005808000302801c41d60340e003503403d0710002c4100c000690742ca4911080c064074540c0644014001814250400b0380042c040082c910380d01d120647c00901035030081e0b00305038440d80c06610303041c20501e400c1201042022420f444003020500700000152518030050011342817540000125a50314801e00841e1909100f02c1c0556424400515204440d00d03000e1154035000c0d0700f030001042c11403501000712245030071651600c1c410f284184600c0d600a170001040601400b409124101a2444c840c4c00188a14030078264083e000d42440406050495a00980540100c0722030030000094809001c1c210044412100c10501c03800080040b4609540d0051301c808140010603501c04100054000314020088242610b040e84e8a0304217000012000300c070013810328480342d98200f804111600821500c01d01070b01c1e003c200b20340161a100103842064078215000c66451003000030b0105a8010070001d003074144081c610310b500d015404699603940383d212035441c40e1000304074030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 203414910 1250 203413660 203413681
    0x170c090f04170715060b0c06070305090304051903050304030f05010608060c0f090d15060321140a05040308030f0405010b030f030307030b180c091002070b0304030507020103090b24190e 81
    0xc5135500e0400c8240200764803441d0800b841c0d040301e540c0c48000e00c07564000c0b403134003400b074040e00744a138100200440c103040c40c00c401c00c2200750342d940d00d850070104100004000702e0320500c001c1c0042e50203060070022a107001d1400e0b90841c2c210360700c1004290800320900140910703400894840300e5026003925103070300700300001404c2e5003543c0800a007121504450984402040d1300014200ca004010254002950301644801242402d54090001e0300458803070804005040103406000c0e81440e1090805469580d41d011550041d50106155041c1c0340800007081800d0190307030400001900a0701704440c14241c42d80d42ea01000e0906002d050700e48107602080d4552001c5000154901440c0e64001c0c10a02c52004041d8002140a8040c940181c2e4003800a800024104100c9040708003051071644c46440403107650b008804101c1c10107442d03680c002c0105500c1d01d081402450b0341105103008201800610280340125007080c3d00403850003049806400003040c1c11000ca546144101090340d03034451030791 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 203416160 1250 203414910 203414933
    0x90f0108041b030b06040b0a0e0a09080408030c160b1204060218030105040c05091303050a080c2808180a1403130303031a0a0b0a0c0606170c090f041707 67
    0x1c0d00c103200c030302c00081400031800e2050b000785416242002050401014010416460700035520b1030004200401d0302c0c000903034442c4150318051201141000d403203c2000342960f00100d050040340d4003200e464403418088a03c614000c0601c000090700c2d1554400035401d9000c0b0041c409130405502058100c41031031907a00c070598145004000f000b0600e4207203040d500310ba0944c002c4501410000c2d0005084030151001b9080d4a1b41548440303091a403100b4044859480c01019a48446818011a031000d000000702000c035013a21551082c072440b084400401d903440092080d6082009000d03102801c0a010601c0308409401c44080400350442480f4240ba6200d2000034402c8150803a2001041c598580e005401c840c0c1c00b0180c0f14943c003030039000c20041412600903610141400c200041c8a24090115004914031544000c503610741d4841030741000401002c2c228000d50481a800c1407645084500540e2007828248904d04a050640b200d6810316407050202c0030510001441c44140403052252 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 203417266 1106 203416160 203416193
    0x1309050604090f201302180103060506120c1312030801091b11120408010605120d081303110102070809040f1a19090e010501080d05090f010804 63
    0x3ca08180c12403840c0040104134007611407409842c2d40c1081c4801e0580c0c20710058441d244036480d41100006009401e041624200082c4107640d10f400544a801c00b616000c1c12850303076220700440310361041082884540d400d4010000b00050009103080059110baa25010b80d030361b03201c4108081c0ca1400d101011b40080910800cac8581d80f1800015501e07042ca402101c0c407807000204011550b078031a07000301d541030751200410702190600304460301c55143c84d90000d0800c1d05000f5802441007102610904042107102c0c5903200341885201ca0314019444d205c02159124418600a142a40a600c69a00650520719032403c803011701e22499009201c002c0c0740c096820080c10400000841c2074040510640800402245d401c0d4688100351440045070f00024443d410684590b2030f1050b1060001f080203000c100f210626155040307443d14584082c06c020321261200d11744001105800b200 = true := by decide +kernel

theorem cover : BRFrame.Cov 203237410 203417266 := by
  have h0 := BRFrame.cov_init 203237410
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203237410 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 203237410 ≤ n) (h2 : n < 203417266) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
