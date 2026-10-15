-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4935
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:12:42.221954+00:00
-- url     : https://prove2.me/submissions/7107a680-1446-4932-84f7-2b7a9471fd6c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 887410071 ≤ n < 887589928 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 887411321 1250 887410071 887410103
    0x5130e06040c0f050306041104150810061806120f0c0f06081b03060904062a031512080a05090117010602010e0706180905040f0803040803040b0109020315010305040f 73
    0x100310001619400c0c06844100f0703440d013013855034030740003078402516030056400c0c9940c1d0751500760000c1066008454000d002e175139580c42a1443c00083c54807850000b51920024007044030203800422110040480a000d09442e02d1001c0c00031416106010308003206c15420303d02480b814440220090444941052820b41d075040014001c107810380700c0e04080c1d0581d028400540f01c0301c2d402d0f00d000f07240c010065802c949940d035404002340129801d28010002c07203820340030300e440000080640b04a254502040d404843d40c40f010041489401842a2095490a1601059116041e0f5101d00700394144540e8440c1c0110060301c0307200f0140c242000d00c117403800010a400758190030200400c505a81111807458480c0429201688000c040c5144a0000c030010000d111258000c2600300b030140c0070305950101c80b41c580d110036620894061b41c102d500001130004020f5030319215401001c60b0103085085040510699101410303020b40e071410181c0342c0c004a010711a206100c140e00d20750151080c0e0034200c107 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 887412571 1250 887411321 887411333
    0x60c03031803040e070f020703060204170c0306010f2603180f04050c030a1a0d050d021c14030402040b0415050a050603060604090e0a06020a0201020d2405130e0604 72
    0xc40788900140303810391022803004000400c2c3c80980d880070419511650b90480308540e089075000b6105d085102c0c0c0d01001001c102c0728402400a441000e104410146000103914504100c8604040c06940540010024002d024034400300b99401c80701c0d140505a1910501840300401c00e6254049000001d090030110f51301001700396104030b058a6440d00203032420208000c5a10440300e2142c60703041040000c04510041d800b881d8034200b0b600507440c008000c1c1e00414440c5d6a00c0804861755404244a41502601004190032070284503200300c09a40800400800164084141240441e8040b0118045503100d8002c40c070482c6000d4800c0143d038804600c1504851801c2c42064050400e149011070740f07080490850340b01c1c0c5005001e0500d800d10f49a0000c1c01040640c1e003c1c2d080c1d003e0f6800305c6000a04034002040603187c26400583c441b11080d0135041220809003c4000d10b9030015070306554203000b00b0000c03007159030132281d040d022100e000d6540d010b00382c907000600740c0d401614200020800 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 887413821 1250 887412571 887412577
    0x6121c030203041103030a0903020906010207080f060702061b070303090f0f260403031b051e0105010603050a020405010c060c090b04030818011817100609020c2109090a0902060c03 79
    0x20260100c00340130f0300d60b8401e0603140e00c141c200311000034194030001d00c0035040003403d41d504008188105c1f02c2c00741e03a80c5415800c2074502c2d125074100d908100140210558100a4942c0005c0142c1603208241e0344444209803a208401c4000c040c9a241d4500c2c0c000c0c01480304510f00c4580c0c0203082180400804c1c07804140e82511210301403440305020218079100382024003a00c05982e49502c038100020304203010701080c40e442410232180b500c10724000c6d1641e020804020280e82d00300100108180d410040041d0541e6401004400c200344144810000d50ba8041d926403510340d0070100c0010f454050650468040ca02a040300c00ac5881c0014000104058031008040e08400c00c540c000c4007901c0385004442020300c900c89013202d07902c100028040e000310030b82d40006080e164000c40f10805120f040c400c0a94085500c0302004130303400f05000d1382c1c4610902162604591008404681900702c4803c01014060a5449070007014400c000518512040d40900c0c02a038005240a813913890400103a41c0d00e034 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 887415071 1250 887413821 887413823
    0x1215031204090c1d211002070f0b1b16031806020f0c040605010c201e100e03030414040204050303040f0f0b0705030a03050a0b0a0e1008031206121c03020304 69
    0x12100c180030301042c01e601e160410038481c0202441620040170f03011040720900740c40407050398055402d160b04402d140744024401d0510074140e0038121145404c003081c0e4500c00810f9010350080b83c4182e051b000003000c0841d40c95207074441d08500100c8060804a54150341851545500711501c500411010340010311a81c00d861000c04503240716004100303000958000c2c1c032485001c180d00b82c5407031001900a01c017194002d0801d0300d030507070600c00c0c00300080e001031140b80558501d6901500860700a00f824010b910100145003070011912003041c010030340c0da225910440761200c0e07080c98022b58aaa49404642c010702c0c0c0103007141d8455440c1c5040369001901403180300030106c000e02002840004600a51b460f00c1e4009006d107050145900741513004e000300800140d00e80d941c1c0c201c907a001e559101e80c0392010b00302c013922035011494114030a5408840300c2c0c206416a07481800b18000081e20782200b290f10003410344803494040324046680d4038180c0780344a04280400310407690043c07542c0c903901440c03144d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 887416321 1250 887415071 887415077
    0x51204080d0609020412020f031c080a14040b0c030a0e0f0f06070f0c020402070606030b190c030b2b080a180f031e0201200601031101051215031204090c 67
    0x1107650701c0f1a48220302c141e210b040040c4c1c80000040e07016141c014070003508801c001e02510b07112560341e40e034007100000c1045c0440c081402001442506840d0707100d031099000e041000010f5034245030b00c0341945103100400c1c0c0001305c0c40c0003000a216008079041440c01800482c02c4501c001d109540060b02da0361491200301301e0384644000907031740511a14088958219a0320780b0102c0c504181c00f031001a510020701910b003180c0b00c0b0360000c00925001003091150308055410304100382e0072000d41e003d41301d241d070702c0e9804c260134030704920200e0340c600300018040349440c5001e5444100c0443c001740310b1802400d02401c0d202c00811403605e01c0b82c00c45a42c1c0611680034000240440d125190402d448210780405004021098002d00c2c0b401011038092004030300504000c400b01001c41d001050300c00d842c1c8441a0580c000c140100208042c000000290460900b4601d040114000c1c0b4034000520040c490030a03c1c290f0800b01d0b0943c1c030180610150386551140560343e5545540b40000600a2071000d80c0c00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 887417571 1250 887416321 887416331
    0x1b010b03060f06150d021614070902030705090f0f040216030e0118030318050a0b0409050f01150c06140a090b09010c02030f09130612020a0801090302030415051204080d 74
    0x300030032420940c0f01d400014410880c07420ba0000c84500c0d900504240941a0b03400c002580485104607181d041c82072096107e500b20300403180c13181e424104190b02140600f401442405019074004040d1081d0315800d0b100c4420300c99030171001a244d03452400100f90000d10019a2450b0741940c9445031a145010f078507a0800310600e50700440e001c07a049602d40201e00b644081c10b00001c0d20500c20f050100c00c0c1c00c1c1204904a071520001200c1055503800390044640c00241001100c2990280542c01911000403001c03643c98901c600040c00081c6180340c0422500c804000b04001041d401418921000e0304074400c9403420002201c0142a07942099410700180000641e09480c14014030414886540c09182007240d8891944000e82100e426258014040d46070b08408032801e10420000348034241c0d4a840303001c4140103006090200c0d030400c89551341000204004280c00100f100c04032105511000380c03084408004503854020042010601d1025400748000d2055a001402104940030401c00c4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 887418821 1250 887417571 887417581
    0x30215030c0706020a0e0a0611070b0403050304060c1a09061005030a12030b010c020904060b1002030c0318121501030605130201090b0706020c0d03021c022106061b010b0306 76
    0x8900085851030090101088100d001a042e5005480f102d00c1d181040e10000042d00000b0321000110340040c40000c0782c1218201c071003041003100301d004004074400386140504589a907a00c9110b980036803814030880c40d04040400c400e020b88210090040030909985d03003442c00d0129250755098444c0c54042e501c0c010041154900031031203950b9661301565035034444041e9802a8007030f03c80050606d040c23218401c5e4000150f160b420364284618880c0d14009840b5000104004022180c070b2140400c40d40706014220000400000719420418840080740e07000d031005d40020080c8022071001c00c1e0900983c1c001d030b0361054001e0000c9041c0c921803101031041d03540e6413205030461515000003a00040d100c1100b001506107a9005003906405088054500820185d0141c0b4100488815800181e40002c1a60740030700a042818280e0f03800010640c50a0040c80f8038004405821224074041020107001c18195551407003115250041420410400da02c400f41d058000e02c0d070030010a01901420000407 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 887420071 1250 887418821 887418859
    0x307060e15151f080610050c0307060203040c0e01080307060f02040306020f0c101512060e030c060403080c0310090213090509100f090201021e0f07030b1f0e0a020c0a020a0306060302 80
    0x5490007107640d104d40309680c4210420011507403c01d605e0080c13120410103401113020900003003040718060f0401503541c4c185481c0182c641d0300154800120030f58464014000320f8030100407102000e8000e103002c030b40810340702c15404c0240708903880241140c0c07001a1901c214040c58001c2d0051892120569101c40e404542c5401980d2140192240d8000506070078400fa0032403d540a4401c2c1c01007a00190701ea0701400014070319032040154540c1135004a041204044d40b045e40a076000c10100852420340c28444003c0600c0e4649000d10184944c001c0380094400c5101d00160700140110304080c001428610541c0303443d10300600d84070220368146140c101c11030071a4040e4400d184d506a008000d010004005003462098070706541e40345002d08031100c129940304001e140d01942c040d911841041c2401c00603655075076102d840010f41d106240104110f80b0416502d9191b20512400c405640c98140d541924104503d0782e00081d0301c070648072004000e02040b948240700f40c0e44242d8400710400080c055030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 887421321 1250 887420071 887420119
    0x18080316060b090c09131e021201060518010311070203100606030609090803040f03050408070b09090627340318050604081305040513050c120307060e1515 68
    0xa18404d442044941d10f00d007041c0d880800310f01c00042c070014000c400312044079a003180ca2400e5400241e00401c081a41076080c0031441c2c018001410001e140030318071503260b04002e500c120386905059480701d101070301d0380c43d440444421a6004040c2c44140a41304d07811801000f187c051000000d14004000c2000302c3c483c4140c80d40303260030652044c2155165500c800c00481c64000403400c01000b4040099011810003100c0d02034906060340c1c580b9031140405104203510000c0849206158008190001c1e0300070f003001003420103c403d00c12450355a5549090b40003100c0038041c0d00900f006403850f100c0c101c02c248070f4078080d8045e551b0500c4440b14040d00700d201c620112801030070517046a408140000c26050003400050060304100003515510301c00541111400c403a091032400d01480c28604212041c8410b103504641164149603d408104056640f4002d41c03c1c010f182d10f5585600090400040210003269031194110071903503c0e00c4280d900c02400c45001503401004d50441d010505c48001d015 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 887422571 1250 887421321 887421331
    0x4171c2007080f040b0d0609050f040b04022103121602030c060a09051f09030806060c0c04020702130c0c03030f0209010c080717030109060806010e0f0718080316060b09 74
    0x40a041c01016294507110350f0102210350b00481c01000006840a904000351440c0c0000754030008200e41381c49000d5081c1c4400420071040100300c0340401c000920040c0403590003079012740d9030300d08082030031259290b00203161b98400380620000c03072601410b080d0310000c10700c80c0c2e2412060aa4100e0714000581c0d584c0a5089007441c150031800000700311200561101704414001c00854040405051001d00d9007000301070b410b0b03107003515003160800381900000c41c2c0ea009602900e4180c980310b070a0704483d80742c41e802c2d02800c2c440c40e00002d11000b035580d002400d000c6407400703120030090700f41402c0c400f610409034101e0840c042401e01c01060500b030b00034800c0e00c55009060b192014001307010350f00e01016500041c0c00321040484290480c086001c008080c1d4060545260001071580c1001c2c1068680136059000000c003418030810800703400502e400042d0018210704105004a00500d51001a40600d4104000c82d100c04180c1f48044520824500080b034040c100c10800d1425580c2400944503085038 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 887423821 1250 887422571 887422631
    0x90c080c01020607141201140f010e030606220c0306051c050c0105070303020d0c20070503190f1202030a030605040902090118020f040f030201090602031e0304171c 72
    0x1000745010712103132142501c8001c1c21526181b01d0450786c1c100450203070003510000b0f0103000d00e4441d07070525028503c040102400c1920320f480070900060f60703a01000f080f250040c1041159810341c0c1100000305400713080c1413401440000906040140117140c0e600c00c0a200349002055800d001da01d200003104185c0d0070401901c2d5011540e00192101d07403014400303c0c200740d401c05c010442e10703210384035100303240d560342d540e202c08105a242c0300c1c00110403c1c0b21190082c0c10090341040566000140320a120740007020800d0381e000c0f5802c084000f29060030020b460240d000180005140d4044010042038480740c400b00995601c0c1c40603c422901c032050003d401890800041c002000b0441155011061200d0050300d0410916050010b90300300ba071182d07040c4000d4103402e01c1190b03004200c1001410b150300c010741c00c0c113070b08400005d500c811100c21b468806400101140c140440c0441f00000c5070071110055944180300406400f00200088041d0000740c503148400d03480e45010841d8258000d0009 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 887425071 1250 887423821 887423833
    0x1216050915240a0e090105030f0309040902030f06131a0702062431110403170d0204030305090a0806070f03020306030f06010e01030b100b04120f15090c080c0102 71
    0x1a0900aa01c9030300c44202c1d10035200344003215000c0036440d0042103003011556600003480044414807020700c0040e044540701c0e030490400001100d10000a0b101c440e101120046074554040c00464104103007c2441d10b003a00910b01000002c9000100259031144244066100d1459030802400c4d0943c09882e400c0c01030f0006400309110800010034600c44c0000700501c0315000301201c0006e1920828400c8501d10341050b024504c81c0445044840c0744214841d400621920000446026440c03081e40801011062a052074003082e400384000e550781110704910455031603881e0305000d8503130780180601d94414000d4132800b24440d41c0c00b0882a0050909840764441c0ca4084007082c0d001c3d400003010f43e90507100303602c0c0c03046a0345002c014180c0200301150140300315504604050b8440d0313070010031080d00b070328501c1c104200060043c41100d003111240d030140010404030b40740081c850a4080805803440b00d0108141000c0b45141d070080ca0b07514803445514000701e55031040311752940c4000c00e030303140960060 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 887426321 1250 887425071 887425111
    0x50309071e180f060609030501050a09021f09031e060f06230f0301052e15080a021b030c21070f0510020a02010903091d160c0212160509 60
    0xc2d9400102165000d03202007000709203840810112420b80c0c4c44513002070700d03c000c10400e2060a01c0784d01d4002d5440c0034103102c90221600400c0e040c41044221601040140080d14480d82c4100541030103154000c001e03800054110a1a25400301c480c20240d0310b052400c1e104c400b82050780d11401041b21800c7e0340300c011840604d21301600080701607801c0d40d085400c2c0120464250b40a201d0203100324050950210303a000750f00706480c1000d8a2401c41410482022000e02800d082c42c1c4100e1103181c81841c140c1181e0b558050741401a0144031402140342c2801c0d036085d0081c0a0200140a880001004640880c8404403c001031101040c0c4002200301c001c000d04c1000c90080d1042a0a00c1d001d101120100c9500382040022a88840d00050050355250004e07000c160f4400c07000c0000b010903201b40b012000f0ba450441c10300c40d0000d04090090101c0008001d0308501403030068400540051a900f0b0302c3c004050019126101c3c10362920b04208410000f09603450b100c0550b9000725117682075640180d8107 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 887427571 1250 887426321 887426339
    0x100501030f1112040c0b070308060405180d0c0209100609180b190e0105040b09061e13020d141e10121b0b0319150e0403050309071e 58
    0x205078401c01241c032120802000c541c528000c0c00390448050041c0582d2074942804000f2000c01c1d0442c580d51a405c000c0c03400800e90280d403164010104450004150b00c402d0080e442e20400f5240011107030040304940700c0c001d07400401107003225000703507a440035590b2030400a01009029000e040d000c100901c0c4184403103000308108002c1c1c101c00c001c000652445000001d4001c1f405009080c2d003440020f0801d020b1010f02e04603460040c80d0599003444480e85001c0040e80c0040021301190041f03a4025140e40111014402000d00c1d48010740355102d41c00350400244080c0d84001c100c2c198030f0381059205d0b5100707801e00d907900d0b118034561900810041075161060410f030345d000d8410212071941c40c10224243c40c1e40040c8101552003880310080804090644481114641e440000c1c48001481080f400034582c0c10004400e00c01208001004c4034550005284000c8541100d1208144402004205600320b0015802a04038a040360000d55941e00410030200d46c880745c054203203004038010420000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 887428821 1250 887427571 887427581
    0x303240406080303090a03090602011803050c0a060c030b011b03090302090907080d030b03010b030c0a0b090d050a030e010815010906051c09050105160c050a08030402121507120510050103 82
    0x90000d0010071038680e550032051450f00251034600c029045007140d94101030300007050300014141e41c0020f0240e2a04104804260101c421014003803001c00589108151030900c58402420b034031400401913050810001401458094515808201e0100840030007042d15001a400540c0c1580e611040e98156400c2c0302d0500005085000079109421001c10039076024046075000ba03200c0da40c00661000240101806d40b0200ca200d030b4001d0700030410f510629120944100c7c103440000c440e69540d6610784001c10190740710610064500e01800d581c4408040d0f000500600145007642c0c0c09440fa107440c600700c080121210601408117181034020007505014502030990141c00d882040064412004000180c4444140403a070595481080142d549088051042d4495151a00c0c081c0149995170b125500e04140c540900b000001000007400c56603098050481c109400b07050f907405d100c0e003440e00340c4054025940b00000c2404140c4aa03005821741c0301d10b520510103144800d908070714150040d00104 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 887430071 1250 887428821 887428891
    0x30307021504080109080a1d010f1b05060103110306060105210604140f010f1509050d2301060801060603050408090135100503030705030f0a051c0c08090303 69
    0x42024030002034404001e100c5c0c902d43da8080c62105681e41c1c0003200c02454081a16500b9202a40801288100741d9001d09000400d12035403e00400746140d0101009a0a58503580103000781b0607040044100081090944000202501101c100d1b45030b01005403200d0003007408156822903000d01990006c02c09500d413540061025000207115400c101c840064100115165000043e45000401084440180100003090641c030288041d414900000b0b001600070701c42c2c1446540c0324030148081c01405150809400c51086424a1204204c003120340641440d03c95030109510b00f520010b5018000e0040d40c0c8110340c0802107a1400501c00c0064071090800c3e08008050350a480d540c5420b10521280750f05402d003030818034201494902c0c044a00526190021406a00b0500c900d0303001a40000c10740388000d141c2c500c450744807941c050085480c2c3c010102c010000b82c102ca074001c45046000d80c0040301501e02640c5120b2a0759501c0b0309640d40c0c0c84103a51540180c82101d080c09040d00000d110036202c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 887431321 1250 887430071 887430109
    0x5030a0513120e0108070e010c060905070b0a0914030a02090105130f050c0403050f152811030105090a05090715050d0203010611071505090105160c030302012903030702 74
    0x444259140e081c0d114074051900c40102d2141c0c05148400c0d0381241017035502004620b044d0080b04101c0000030052a00200010103503a2900d0700041008001d0210b00d01a2001c0752602c1d80720900504000c04021a0380700b0b04900b50381c1c2480c4a8210b041c0415a840300d5500905100701c2646441c1c00e11034405184c0314400c1c5a160340345a108110041c40c090309028900800e00e042d1130305e08508005007422010a035102030350303000c1241340055034031074800103901c420403408001c8621048040c085640c07c410f031a41e94810f19000840c0641c15440c0003440c160b500a4400705810303618081060101e4900b602d083d2101d0340001c40c208481622030300003411a152910301141007110400380e1005a030070170780182e004288205200401e104007080f20400a080394002030582000081000d4000d20504400780e04005c00042e86103158a102d600c2e45103942d0380412030310a00d507074a040085c000c2090708010f400c080c440c9152440d516030b04c8420601d10317a800401641c0f070f0111503400c00c060402644025011 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 887432571 1250 887431321 887431351
    0x1205160e030c0a030c090f18080a3b030f120307021002070b063109031b03080106080c130509130203060103060209180f060904061d0106080d09030305030a05 69
    0x183c0c0307564401c100214070554404900d1810040040140d54000110082c0700f071030481442460007100c42120585600a00d440303540d0349040908a0f003240200d034180c8044da0522001e4240400702c18080444d001c4445541c015130080e0008141e00d81e452541d0640d40340d4080319080340b400040078015500f00a050040f9000a210250844140d806c00d081c20344520460358100040c905009042c500e40e05070140e64464148502c074565000d1300c2d41c0d00c0310041007980e2003070f0382000c16001d002481e0110101c03c0c10450100f20a240092203000700b401244002480200410303180462300c8160742100040c510322210341414070040c000310034070040c40d07400302080c0c032600100913031407d0002c2c41c040c60050b2009690766080d5018881c0c400203859052003198950020044004100c0c1003840c1c1181c01242c07481c001707803500d003400303009030868204100d48881060b01c0613001d2401580100c0c101d43d060429504105100082610007a116200141c085442080010860441a0720641d0701c2910b002400074 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 887433821 1250 887432571 887432593
    0x1f0b03010e030c0105060103090309121106030a1d0304051005160606060c1b1401030b030a0506090a0b0612061807032909010506030714060903010509070302011205160e03 75
    0x3007540e00308020040ca0b40c00c006141c0501e0305080c010b19920003404e08040c0034000007641c0003440d020541c49180e0300c1045411200c010814a01d0401c00c103c0e05c018801da48138200780020b04000c1011104140c81e040741a02038010741000031042c5c030121480240034020b0045404010b443c540e004940310304488106580e0207000560741d21641010300f0441d0340780721164299241100b4000300c800050010344010400030840300f036410284e003000318028038001c02d4440a04000ca0701d03045503d40000d007640180400c104c01140002448044103024043d11030964907404284121510300c80d10300d5000350401c4001800742c0c6054209501400d0900c021645019502d498106641100d10240d5003024040c24a1031001d9001848580d0402c42c0c0038001c10040c03c007500040c0d40e400c010310031510001d40180280750f2981d07400c02514202031000d002031086183c50441c03607442d41e51600041b404213444030890120204c0a20840384200081290040000d0078070b81d06075051410541110303418819a84228 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 887435071 1250 887433821 887433823
    0x9030206070303060f0605031b0702010e0a030602030610141209030d020705100e0f060a0c120203040b04051905071a0c100f060603230c0c0f0309031603051f0b03 71
    0x114580d0b01a0303500040d03a90a0000300014007a642c0d100034100706083c070034080840c1d5419a0403007003e0301a0603c0b40d55208520044c5d421f00468078a13198043c20741380c0c0000512032641c00a51007079500b12494104440888400c1c0c8100040c91050403801005000c4000e812a2080c08a50014060800c03203042c4500e50702000e00740e900400c002c4a05d504103003a1490001418001c5010b456841d0000e081140c020b501e41d6036071002c005207a80030b400c2c0c9079804200b000b8010a055401c0ca1890700c1c0642d038916140c241404e921405680480d824412090f6082601d1000b03d207240c0c032243d006000e40901480c0c03030522440328204085000781d890040010420030001000341072900000d00801140308a4240e00c1c1404503049503000100341824800c55135004000e001110303645200304a04036013141c40e0503c0d40d000a02440f4011110351040f082098401c80000003d01340500d030440032030301042003941580d500f1010a102c001c003280c0c0300c00030280648203e0321154401800d4003000003202c84c0c00030002 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 887436321 1250 887435071 887435077
    0x2131a04030b0613021e09030c060c2505030102040f050312030606031501031d0f0c1203091507120804060b0a180b030124030b1609051005070f08030f10051c0309030206 74
    0x20101000c00091880700c503080c280035400c9d01d10f101304c401c10b0400ca0112481912000c2d0409442186803400f074090350403000c0013641c207002c0e0102400854a0b40c0d02c2d10102c5040000c5805454030a02c10b42d0350401c07500314544120307440b03030001400050960700c1d200b081c1064238150395040e03418544c071454042c24803c80d40d02c582c16514010002440c00f5a110750b8901c0c00c03c001480311782d019000d801020420a10000100c40340b00c4410750300083c4402c2141c4440e003d90062a0b001011074030203a8201071244d9100d0b8a00e4044e9010381c90400011140b070003000402e1001e0b11844001c201210300c4c0c410303042c241c0e83c4028180c0d6005800030038810314070745410002c0760411500c688050342400d818010311801c030320030503800300c24814a00300d0b4602c040170107400800c6602c1000e05c644510540445428421419a03080c103921a00c010010b2400340b6005085400031070301038420549080001d4004c0103442c0d205000c1300d01c050311141c1510841000c5060040205006600f40010305030000010380b240001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 887437571 1250 887436321 887436367
    0x40303050d0612121e08240303071211030403030806040902130905010f0c080906011205070e0702060a180f02040e01060513021b0f06070c1502131a04030b061302 71
    0x11002c810304025000c0d121000c0082500041c100e620417180869401060341c680218000c0309207944002c9401004500c0a41c034054250140070200b10b503030802c4000511544004145c2d1190300080451500031a968080d511010380041d0300c900100d41d41e410941d0101c0c6e80c0a00103070250303001c0003803283c03c038003039030100c000444040c2c0d503881c00e0100d1405144966a120b01d200e10b08400340d400e204c1085643c40606016486854420213501000c2207801c100600c02400d003840980c0b014500040003079100d46003194628807042c14102c079412644425100d40104640c0a400401c14500c250240301c02024407c401784a82e40d0b13150400306940d503903001c035070501140600b40965a51066103046c02000224441800e003680700002d2010660400301d003081c0d000351545403c001165550070002a111000008087c04510010341c2e8044048580e00100070f803455031910581d03101d85c0001c0c00d1801d203e03e1201904d02d100b4074004c0351040c50400204400202c1d8103402500700a42c200040010070cc007103503 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 887438821 1250 887437571 887437583
    0xb0c09062a06060a0302060d11091906020c0d120e0109050409111f14090f090705030615130303112508060a110a0804020301060e01090926040303050d0612 68
    0x401d90031888010400c40340e1124058960481561944d40400c0d101e00070400c02440c803c0c0ca40342d1340d004406140003a0348032100010169442503006c0702c0c1c0380c0c0a810b0203004000050080d80000c1045040c089000c65620b44c0c0500740c4810b03030720b6102080300c11000c015400c40c1000099000010150340302e000c0c60b0a558050003092118a10010400c1101a01c1d030741220210484c0907403010205400c1020241040001d060040e038958910340041c4411003210345c40e50f440340400c0188040268800003841c441c241c241c800c5024841051030a0305207000e15540302c3c1e0101d4140405000080c8140c04443d2031003840d8040724031612031007012004000e1504030611403150003c0080091b0042001140e030002908282080040d900900c2000d1510070744504c18140700400c000b0a00319202544002c2c000c08115051460030350b160f4800c0380140112044c00e03107038210204018521600d84089105207004079100705480e00381396660076500c58000c1c0e04030508560f0f840e00c0c000307603034006074088800707043c8100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 887440071 1250 887438821 887438887
    0x9060e0111030a12180f020d060209030a0b0a05100302090105010e04140106050702011806020a0b150907180e100e100b13170d090b0f040515090a120b0c0906 69
    0xf00b11411036501c90410607002451748403210200d02d402c2c80c1030702c00b50340550703070180c540080307050000c064411507042c0c1d60548586c0c15050240040e41e19028041e00d0b00390b006100da0b440783c0d110f10301028901c1c000603510940031801003003150300a114620941401900204540846044d40c0809030000d034040c0327001c90030010b861001c540e4404107606036080101003007900f42d0b00b4050300035074072002d82d003008041804580200e150f8070b1000c0c020b429040c40c0141480850304d8807a000074405c100040e0050300b0042821404221242c0b10229244502c0f46c4130484030100c1d10342080c02c64030280c0035002c01c48d0055400d0001c0741c1414070200400c000700064556900707151801030403903621045d01610640301d0700049100b07049503600035040320031600403d80031600c1e02c0b91540320401620450713103c00e61209406008c0c000d01310a4a0250007180011503400e41e4055903000c03503102c0c45900f42c50081480f12143c0003d0301e02c84844001e0070f42070001522041c2490b1017103104c008448070080305244807135000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 887441321 1250 887440071 887440097
    0x616050d0503040b0105091b130501080901021e03070903020315161b060c2703061518051b040b030f0702030c0a081e122509060e0111030a 61
    0xc00058802054614240d85149419155428000e106010b100d109600b96000711b941d02444031202805c204a4000300c4e9500d00f1b664102d860303107809900c0b40a0104e1100000030795115810f200343c2e281d40c41d040c6501740071035500c09400b00d660b0740020070460078004000340200150301c1c02c0101c012629030070f0001c20f840342401c00e440d18100501480712010001006034100155002030101c4283d01d0b804000415000310301300003030300c00c40b0081d103045116061441000c00c800b210840d12008403406000d08000c000324040700071400e007445005010800c0303180c842c01d01d24081c055000c9036004580000d04010181c0540384000254401d03030003040d140c1008403e0124404202c040d590704080c070b80c0011490302200081c080e441e82051350b000743c180300d00803134494208409103800c0001c0001041d11b01344d4440007038403165404035040d90000400306c0f01d210880341b1140e4013040309456160640300c0c1c5018034603080c02101d0212031080403504000c9211800c0040e128100060b01d1402d045e41c45508840541c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 887442571 1250 887441321 887441323
    0x1806090c1403251d0a060c030c03021f060317070807020d080f0a0c02010201141b0a050d0f020a080c04030803240907021e16030b10170601030201081305060c0315061605 74
    0x1c0340072038621a001764441000030b140c101c01c2004050b540350400c0c614030035060809a0420003001508100e4070001b0100c3c400c45469a030028060328841c4031b1007070b58459001720884c20b50059a00080c100c090401c10b81005d482d100418007086841107103d54071300030500800d990240c2108846d080442c0114140b60115a028000d0918500c101c4c00c100780146000748070500210265940e907001c1c040000b522104542c0700ba4110341d8000c606203018002011282e030b202000b0340c802d65600000491380008500d0310800c0204503011213402800013821a11011600b00202c0382045d83c141001c1040c00100c180d40d29071403001d61190006030050301c070f1891715812080c202015801d6061481e000320440403540c450000051098035006a12070f000c0741d403070070300080b6208060b4000105400d50052400c0f81e0341000111641640e100384e80d03031929915981610403030300e02c00f08070050140c1c00001c00182001404400b031a40700502010850a00310200d0114500b0b40c4402d1181c80c03805142c11504040c040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 887443821 1250 887442571 887442617
    0x30d360b040b0301090608031204020103020f04090e06071413061803060c090905060a030506040f02011b050f1e030d0506010201062d08030a0206010306091703011806090c140325 78
    0x7c000040d524008800800c81d166460062009040c164003081141c21245607500395000313000004820007084505001550351568229580c40c001982200d240c000c40384a00306581d6020040d41c0002d0440341452401c2c3d13804491392072260010060f099002011070064014020103c03040d48079202c40504000e07202c070695000030206405100d6010080000034400100982d10a801880044800d105480100c511003460a000300400131102d0541c014840c0109034400070341060307000c940c1d8003241f032803031014492029032943d40b854000f80022810b400507600815400b15051000262068a481c2611280816041c2c62a40030b03490050f0309400003410320740d250250540000841c105a044007009544010502008100036110724040042204121020190700404c06000b43c5943e10741d09050001511007105c4071166003040e074005103005d403603c00e41001e034005940303155843c5e8007018100c0080e88007070310b0890034120190380305005103086411141240003d903503001e00c2a51032010154288 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 887445071 1250 887443821 887443829
    0x9091505010522020c151509010e01030b070306050306010914100b03060618090c450a050307091b210c0e030a11030d360b040b03010906 60
    0x10328050040c44940ea400c00d000400d44082c100d040c210303141004600003e4092140070440030b100e43c8104100c011000340c0f0091140d80780c0818903821401c42001c001c5011400e2168110180d075040040c0045a8018080c60f80b00310503040110b501030f520790120b86003030380980c004c945680c0c0c0e628202c030303003c041c2011541d00011070226070b500075810096000c10912002d00036510403140020b4044507050004d9440c000c810700180450f109103040c044200d0315a200f00781c2d4a0010b0100d0713102050741c44ac22207a0102421084451074850711035006109488110b12940d070368005441000042d1a40d0300b00070200c083c04680c900401c0075054800d039040500888031440d014004841d030600c10000d1240035071407044611b50000701d851228560280c0d16a0782c00e01d040c64250160700840d400f48034040c0d4203601903081c190100e41c252410698101d0316004000c1c030400c1000f100c0c0f03480003203402c80c2c0c130003d05180e0440c4409109641d83e0f11007039500e580c0b055004403c0c20a01000410049100d445031200074 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 887446321 1250 887445071 887445113
    0x170403050a0923060a11010c0c21020d0e03010b09040f060509240606091216050d030504091104050306010305060f06010e01120504080f0c0a0203060603010e0703110d0c0909 76
    0xe1500c0243d443c08039844181220700400c070100350750f02424801c80c8641000c42e0140300030808044850b1000b80809031307480341070703904c0c81c1d013602080880303943e03e0004d05043d9141c2d030240203190b04030704c0201d8040600603030342d80d4550340700c40b1748244ea40d031450b212074040d0740f0400c48411040024903042080c0e41008000508070303002800c0b100d1980c042c3c04161805500b40d0088412183e40da00009401740c05a00e032081d42103900150b00036010000051030801e540c2020032031000859503002080000d00319454001e000032001d02c4100640001d030740001000103070303482205c0e0a10361550042440c0c49026072041e581940050240300703001021746a55900803001f841c000020240480c0044c1011204812000540e5541d100040c00d011628050728864290b0381106551450340301040d50ba40d0a441800743e10900640002c00c0c40c901d814840c01680d441c05501401c1418556119151030506019006401500718500d1100040c80400b00c04050565481b001450f40d000c0e0510000d480340d0f0741481011 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 887447571 1250 887446321 887446349
    0x21605010f020312040c0e09010c08010b090607150e0d090f050603070c0b060103060510030f1a0a12031404032108091914030a0c0b24060901170403050a09 68
    0x40307582c0c044129010702c1d9124201c030302c60b61200d25000318030f682d8591100b01c803141d205050020318101900700034070981055941a9850b40c80e400b662806129000780f0383e034014003c110079000282d44c5c01d110b024010a90380005405420400085c5c02c0c4520111041d00103180d054080c081c003c00120050040d080944545095190074503015040c01070b00c800191020076210005140c076880f07a04140051709004c0d1100030200000300300600507200c4119110314031810245105034284030302c0d11031040184010048580c080c58502801000741c1107050540030400710401d01200340450500030402148a120180c190500b106100540081d1054200c410000e07020240b00c0c040c00005140384080c0d51042c0d0030b4010750401d18003550071058081c017400760750002150858200c4c0d088001401058012907400205644240541c000340202c40c2d0500b04007425040c0070001c1e810540b000c0d11010806042c044500141c562001c02e0401048a0490009030001500054694010076010040403020381c00c0107 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 887448821 1250 887447571 887447597
    0x4050f030c03092107270e103201050901120b01050f06041e0504150303091404140414010e010204080606191a0c011805150405030405030d02160501 65
    0x34a91003000d4801c0c0c80388110706006418051040204135030381d02c200d02190f0700c15540d074040030700a070815003201003080c0d10403055580807922030080c07802002c00e58000d805802c1d000890a40100808404140050001506a02c144000758111540d503202d41d01045e8141d1f15140c20081200c50580200722090043c0b8604c800094009103440e040d0b80d400c82d034502c0400b808001186c094000c0303511490b4941c45100c0c4ca0720075190400d035004181c410a5600303114560210600d11412001c40c8001000919010b000300101e03003581c100a0307000b09000b000490b91124445542029030000d44043d1a00b01081054280d984070900c03600e42066850380082d809c080c6800201a200e21004003464050081d201001c2d814081040201018203020680345003082d03880c4814807819003041900300700e15032138241007070304882440d41d00c03019155001b8000c107002d0505c075484244c26600908120381c40d01c41800003040c01d5806121010100d030389607008002c03841100b250101410030f9588064140018114141 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 887450071 1250 887448821 887448823
    0x20115060e0d110310180c0f230f1509041a0d0303090f050106150e150f1303060c0c02040b0a1d040f051204150311161a01090504050f030c 61
    0x400c40a4200e0b16020703407412400003003800d044141d0800c5c000d2074034100080003000030300e1020398803160050000d40403050300e5816500c949403240c080c0c01c903281c8941c0e901c1e0013002411401e455410401505080c80d00341c51101107641503044101c260201c02002c0792500850502d403103003900300b81c507101403192030810810101e03a00c40f4881130043e04045d16829013030b003840046410700c00c40039030020007040800e07075688810309a18914007c4000040f402403586125161109150680ba0201071a640c07418181c401202c0440d440030a00c000000c00d94031001001c0349c828420056031410700c2c6c6526035090f040384100412506a190454801c803100901400f9081d0f184104c20441e00200226174455140da0410003407281800b04010710034072403180203420300c1c0040400381c001c603120070101220020454800340d007601d0362094404016401808a4546800881c0a40b001c0318080c0c25421400c102c5041503038440e032005d80080310310703545800501040040402c03500d595910400065420130140084031 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 887451321 1250 887450071 887450089
    0x3200a02100b100c26030f0f0601080a0b0f0a0806060a05061306030902010c0c0f090c08061e0a080609010606110304120204021305040912090603150320030d020115060e 74
    0x11010448049045010054071484284445810100750305124217030b010400c0385580200c4628100c941000c0104100940068440d401010141c4603c0610750350b1a160000900d82e00c04010b80c81300c1040c0d4107071900e44450820101030031061000e00100d203040c0042c800d0400c040c0d40701c5400b58170100709105600503252225002c0c0c41941c80d0110f502e2100d0b0004850021400c580604102048400055103e00c0c62940400b2244e485606111040c82c015003a14280011290250420103441070301520b282c11610320b44000038001d040401c0e49484070602c0d03140c000b0844814115030755a801c24805282c02286101c40c2d202000019403500d8200520550341c0392681c54007d000303940106101050a0f828030300c0c4406010054000c1041c82144d060080000c1d40da0641d0030085280c462000c90064401c0c0a075001c840c02504004400614607950898550405604040200d07002411804540d60602c18429911002e0b40045204c403c0700641c001c1000306940300c0b40500118036100719085d1115005 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 887452571 1250 887451321 887451349
    0x3060305010e211e0a0302030406150e070f030e100b030c03010e030d021c05090a26040b0c03090907090609061e0e04060b0a0320030f0c03040303200a02100b 69
    0x240c50300107111200c04802e84003201c030134442d000400e8020486605501441c4101d005203414044440f14803500300c15040136029442c40e002d17005001424081c041c2c510b100c203404403880d000441c0074151220f203040800c40001c4000094850383c914035039240403c40b403070040204030004c00260000e43c000f135640e48121405131440e540c000c10a20030401080b010340d60030950a40060040e071910040c07440d110581d242088a034004021b400c10b0541038044070a01d210010044486d142c5420560302c421207403c10072502000d071004101d100510384500c100580a09111b86070115440d082c90f2018000c60526045007080080c11002034844617210480d50308446070600700501d90b031314018045800b805003034020b1403004100054400b00e01e80e155204120400012409818000c41714010402500c020f60750114507101d0003000c00e0310019000000e5800522a09000660481414200410f0300500c411032200d83e8000c9000303125150148540025401d101104200740040030700092020310000b00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 887453821 1250 887452571 887452633
    0x20709181511041509120b0603010c0f080c0904200901020d0309020f01080a0f0510081605032107050f060415150303080a0b03100b04111c0218090703060305010e 71
    0x13540c880c0b0540510711a0000c2c0420480b010740000d82405c20381200041650b840c1d019600c4e101c910003c59200b2109070741406855030300c922642e11184c001101c190800000640d109690302020b5204071140b00e08135180150070254251640001800a801c00d0381d0507811000f4141444100c100603950408240f10a1109007031500c0140c8841b00b10358014a00d410307284e04106d00e004140010359110f00343ca03804440e800e0b02251101e1200b0f10f4887e6101445103e8140c040d0306c030020703018107114034000b10400100a0750404c1d08022098481030314010811050700c4060700f14400748814014640381400703105050030b1051140d1251580801101c91003407002504200c500c06c003041112400f0f4000301d108000040446500201003030380440117240c0c0f610840e00c1645080c00c403d0700701d806d030350071323101702100d0401e82180c010001423591020394408503c03104400c1a90780c1d00403803541c40203034031400355003181d900048180c111700d041400c4602c006100c6106038080044c8040014500f00300e25083c040ca60 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 887455071 1250 887453821 887453849
    0x903010f180b01050105163e0a080a03020712050a290606030402010203030708090c0a030b0604050a1803030902010e040f0218040b0d1118041202062202060a02070918151104 76
    0x4000e0040d0040203803070142c423901d50740100e01c0780f02502c001c000c02010000c90300c020409030343d0411156a9404040300a0260f00024001c00580c01955121b800c424000c1068402c001aa0341d00d07480c602c0d100c0c5c840030b0000a1030403a406500c101c5aa80680d000b8401c0d030b01c0501c0d6050540010355240001094001008000c000241140d0b03424003944901800c0075100070740319616450501201102200c100e80214682070014100201c14010310307681d10760380e5140700201e00e5607880c203d001d00b003100700c1a0705000300404504c455071030b01d11401d804500c0b81940140c55448142c2c2e0381a40c402d40b060007074803a07401c004240e800ca554520f02c55613030301d0b072114100240341000000b04a01c0901c1050944a401000b001c1009029000f0850001d03510107900703554281e9245501440200c9491446140e142000c40d2248010300301000146200d09540c01210407031a9140e501c0e000b80c41c0e41c52900e00f04041810760f07902c20810400d08030020020741043c1400003110500c0c400c03185000d0f521400d85205070701 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 887456321 1250 887455071 887455103
    0x2070b0123091005150307230f160318050906190b0a270b0901033b0d0302090d0b0709090f0522030906050903010f180b0105010516 58
    0x840e030916032400302800c60103030392500c0c0041c40d40f1040980708942c050b0759640d0f4608414006101200d01c2955a5160b40340c207041c0507000f1040c548d8012402ea85e00c24003c0100d412418034030000340c100d2072200404010070881d140341c000c001d01410004006c81d003003402414042d9a076000c1d003142d0701107004d503410403580461380001088221154040c00100f80e000031481611584084800f00500700c0c80c01c1c00001203a1010724060841c1103221318101c1e49010700c03180700c085d81b291f0001d111144d8844940524012510038503142075801c540305843d00102c0c12210b00200105214260341400142011030901d840794021802c0502c41910091000040c100003da81c2402505014081d10584104010601c1d030240c0c40e400601c0e0540b14524403202c569140d900b902d03810058480e9903a8141e4403950040c4c40c01100b903400d500725001040d030554842c409415907804078441d418494600d41d60712081c0c48058240a0312980040c0c01007030411100b0854442c1c01e07200e1060004c1c800e94001840d003a43c64103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 887457571 1250 887456321 887456369
    0x30b03100e06370513060203040507050a1706040f0609140a0b15010c15110304030e0a091803030e0705061201212609120a02012a03081003020d080a020c0402070b01 72
    0x171042009001c0c5102000303120600031b0018503241a14800d8942188854480d004030200a1104600704640e81c40380b030001c1d00040d04800c2172043c0c24810b4802107042c00c600c1c0d847c040007084050100d03001e50300160103441481413110b4175940050603203441d040b50310901741c0001d0551350000006000109041140f4000f15540d0b0b0010100c0f40a01048136106c2c249480e0080400f080c0105292090221a001040f40340c01840707000c294002c07101d1039901c5010190b4040e130280141c00540048d50107035610001c2d82d40c403104001c062240d03000200380c4a641c14004500354601007a452101850030321742c140d20029503280e1417404590602803901c010b43c600051710031094410725890640002414904640140001803602b0708903100362628504030411200d0b00c041c5644e211021043c00c10090791803c04240200840c0360400d40c611808011b490b03d0f034011a0300440f002404503486000000d540030700e180e040c0412a0800c004680c1585021141c1e1a000344124040c010624101010107080c407000d68 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 887458821 1250 887457571 887457601
    0xb1c0615050c0703080a050a020c1008010909170f0a120c0905120f030712031406150a090b070804150e1e0f030f0102030a150e07030b03100e063705 65
    0x1901294050383e07a01b031040d00405d1038002000c0c03034015200b00c052908180c6030444010102d0021a80c07400010703803901a154018000004094450302c00301c8120803440100342005249856102c031711141e4070820240020541d030400032590f8002441c118540c440c01e40d00c01083c2086403003c0714200d03c0a400350003642e08003441510210558800001d56030200300900712021006102034804000ca052400e200c041402011190a076004111466903030301061200007910700d104091030604259615103041100c542d009040541c1c032024007180411100c0025084501550260703d4036520a01c0c240000c141e400d560340941d81d141c22024a0a2052034480717040509004c1001821240000c803e140e22500039881580c170800302c14100200d4460500c2d00705070b1a0201c4800c0c002c1040e00d035655200c11802400700c912051340c10b01818540c450f00d480700380a0b240c405600c620240c42c0504200042d0700555401409a5500b03801c80d8058114180700f40520b44c8074030000401c04103441d511400d80b451031079 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 887460071 1250 887458821 887458823
    0x7050a0816060305060319111512010306360b0601020a030837050a0e01060b040302100c08030a020a0806011b060905030408010c170a0209090c0a14040b1c0615050c0703 74
    0x241d248110f07d0901c0b0520001110400045e9807240b401c14298103840d1051003107130140021251024010030004846074408461615805080079001210109518030418013100350101000c2c401d05520a002c900c0c2e8269800a400340021f02e080c0c40c0a0342c0103002083c000380070741101ea400c10912151440c00b000008540e445018144202c42d514081000040c9400d9504580d0103282942e14018000140700e10010f540d032084a16081515690030400e074090100b040104010003428403200140d41c0c080614080c070080310300540c03600f0100b40b000706030403002005503042108a40c2004115070900d010b0303451250300045c2c04503110342ca40c14003501d10b10565018208640c0b0b4074001010042e400400c1094859842d2004a80d6480b1000000d06030b0140c5030316254020f0400000ca41460080e40c0200740303041c4035003490004c004508410314000e400c40d40c444019007000150300a144041c00440d070403650200c0400f00449800e00850489940f0440f1b0368800b4808002544030424108000303141c025 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 887461321 1250 887460071 887460103
    0x5010f02030403031a0a12021e04021c0b01020313170a140f010e0f3a0503010501080f190c1202070f0b13030813030509090907050a08160603050603 65
    0x241040c0c90010700914180e0044005c010024004110303a00c0c0485004040799004008844080c40c19002c2084080200450345d1181c14075030040289901da0740050300b81c1c0b625590b861040b154042070310500b0b82d880c05a9450454004018507804403107600e11a4007640c509802000700001d003001c503146402d000c0036000d00b43c5020551140d500c10f200089007485040850b0081c84117180e00d0301e0a07686d6858100c080c101c03d4002c00d022013558044810514401c520300510745000060b850944087c2c8451048014001000040140105d58002c540c154101664500a015a240c52103c0d456091640c1c3c0b01d0003100303601c50031016680c510660b000d8600c030040040440d41d94000345091010b1121f210000c941c03102c841000200e00d500b0700c0e64a00042a0503481c1c04034150380300f140a0074840020341d422401d12006200c0458523860740905e8cd88260784075070040c2507039402c02c0c007040102e0f416a0310420302c540c086d03101c04268904100c0102d007111441e05020405440c2e00c000a03062010884d281c00c24 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 887462571 1250 887461321 887461327
    0x60d030c032321060f10170c1902030724060b0301122a060c032601090605040e0309060904020c0f0307060b09160f03060839010801030b0405010f02 65
    0x2000c00c100c0c000f40034280d05480d41c4088041d21001410448034100c40c8030b540a4181c01581c42c1c00d090441c02d90340042c031581760548400310303032484a1f60003071000d64501c001403a010030b103001041c0e41c0313008018a81a003800190b00f492070715911407840f0914152102543c1010100308416680d40f0342015003e0f0110840464807503031a0700c0b5a01c8420304200e001c0e00c0f0000c034001240385404e0030050054200c00c1b204003840c445400c0880541b07443c01061000c804109081619083c0c400200418030124200306810304002d5145c5850702d01602c000e034110398444c510344452000103c40c00004c0700c402c01c5050b81c650b51641e0700c1500040080c0035590107403146024007550409040004002800303602c2c86000100b1010350407000340441030702c003240d0301d10001404030b02200b07045008a0060900303c0303203443c010442c2070300c4000c1141418010110301c1c0760213440382d0a13030f259110b01100d00740c000880d8646d1041807580d66030008103201030600c809411280ca89021606012083d004107098400562044d5a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 887463821 1250 887462571 887462627
    0x10f0c0309050111040b0f070804170a050705060f27150706050a1a06030a150f141005400618030c0b1309091a0a05060d030c03 56
    0x2411201030202c4040d4030b0140380340c01d00d0808400303a03001c0e201c48106103401c04001d00700600c415440740c1d01c240c0b01081e041c400015040f1111850054400ca068003920300030070780e03103012403400c1e01c40c0e0099403103100180005000261580c0c141c440d0002c06031015a0040020510940c0b071419a1039070036040f605070781c40540982c8980c8020011540310348410483c3c0e0303854890500464000e880e8001245c508105a0340c02071a0141c00382d90406580040010949401040072481c1c44c41c95000c540b0760804010104501d0201c0120105c0141e400c0d200308a51100f01d05004140780b044903101c014900031440e00e80c64440d181c050301d000720410818140400c4080300b25040c2c02e4090340c400d50001440002501d00342000700f59400d011640d20032841c5010a003415903403442034100201c51034541c1c0143e50001204111400b40c400b040f4041d04000000400c00408940301c83d500411040d480c070705201c2070000a45424031000f1030a60580781c100401d490510301142c0b103031030344016002013403d2502816 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 887465071 1250 887463821 887463827
    0xf0b0a06061106060604170c090f01090608120409090305071407090608150703050c070f0b07080f07020a0201050310030506071119020d14160303020a111818010f0c 72
    0x1a00740c880644810404080010185954000445045810981c01e10007004401003650000d0702d8403242c0c1060380e6a0080e2a000f1510000088450b1491092154010014013030184110000f0b800d60300050b09018121a989000d107110b24030800400654038801001858465030542e0311082d4040e03056500464480c00e13007030313070f40207107000350001036240c16000070711244006500ea2241e050401d2080096407119030980003044028001c0601d1142007104000140c44800d090400e02c0c4100300c1e003002402c0200c001050764100030844030400c894030050088a94001030600030146c4c0c2441c0440e034a954809408490301d051340c0c8020420300c2250180401c0581200366414409a20300840c3c00c080c0c000c0c882417816140701140030b500161502800408500101d00381001c060801007210010440c6508101200240b6441a40140c2100c02d01c10100070003128003040304101218409000d5130030240881050350007070080d410050340c070644515182d02c01c0d040b9444842220b41c0c10070121080810103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 887466321 1250 887465071 887465081
    0x30a020105061804050d1d0d060e010f0e120c010b0a09200f090d0204090b0103030f031404021f02011d0a020102120c061306090b01090207021f0f0c0f0b0a 68
    0x184160600c04222032500f280c0c4094034825a0800f000b4068100d9204081d240c48803a0b04c000c1030407031959511410076441e00f03078844500c2e5100760000140c1e101d1010000d401c50702200e07882e601e440e05241440005038000503040000c0c0c441f4600710ba41c0c076507120100070b006014080f009900401944030001e818806680200b50500030400d000c448200c1c2c02000d1621841028030a480da00024000741009050a126182d52039102802c0040c0c3d14800ba2541590344100360301c1240000c5055040075a4aa450300892071508101020301a031400c055001658029440e00000320b0710b2494481d8000c0e1074805d400810700340f041026500c40b00038280c0201134550fa0048030030b9001d40b01e040301030600c1c56944c4046032901a03c4402800031911020541511304100100075107240e52182c880e039000c5090b100350a40242854000181c0d104994814042c480ca4203c000c103154103c200709800030141c1100401d035040702c03070b8036203240601a10f10300801d008e0500301016008034108020800d00301030503408 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 887467571 1250 887466321 887466331
    0x8120a0e210c0906032a060f04081006060507060902130606020d0e03030309060c03270c010e0103020702010903020402451c0303150803070c0303110706050301170f030a020105 77
    0x81c1c494140214007402541941680d4545c1c142e80800c41c40b414422415a51100c1c003000ba00b0b41505c100015800600d031508040e800456501c000102001480d00402c143c4141c3e440b40d0390180b010360f140040140a6010300400506240c1e140c0804104550700d01c61511341068200b4030400c9800e80b500c10003950761480b804840085403c80320312001d07924002007500d03c2486800c0040030550303510300d40c01c0082e4002500390288191240c3c82c062a9100f241d00724050b45481d200100900d401080005150305070010b425414584104403440c00351341e01070381540c2038980503100940c1d10b01408aa4030b0b0407000c1045140d8581c00c2200305021100ea141090b10000c0c0c01941c056070240030540c00300100010700703114001d007418a000842002a000c0d8201c3c2074030511120204090591302d01030306003154400c10b0304560001d8400c0041c0205a0000191140c41d1201c3c0000d281007410030034040d020b4401800350001c0110810070803480e00b182046a00707680c480a01c140e81c0c07141034000021303010f0041519 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 887468821 1250 887467571 887467573
    0xa050f1201050a14031011070b0906070906030507020303070e030c04020d051e100e0915010311041d030d0213120b0f091f050403030e1c14030108120a0e21 68
    0x1c1401070219013400c0e502005001c1c2c40744000c50103400c03008180080d2180110b500c14000c480100b030b420369546104580c040081c08107490429030081805d44907400040603d8a000705018846500200f90303a8400b0b014100690b43d610400c001900d8a0282801640d100b8000680c00c000031441c0c0d00300d41c2c010030804650000c2c03025250200e80200380103c550800607a000a0200410406030078600d4000240c982030310b0160480d10b02e5071034002c01c01d0704160380710f03001d440c1586810300b01440f501c111514880e9543c0a03402c0350908251722441410042c80d49180c0200307110100400412101005121020740d00b10017801910b00300200000c01c94001c0e401c1c944020015010840200741d00041d0a80042440c0070b00f00c080c88284010000a8070580400d5a62894809100030400c49002c40d10812048035800d000c54550040003a0030000903010400707828401041103a81c0012102d020269958130306840710052130040f20341c83d0918854030360107009030b20b03010b4200c00c0769480039002041c000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 887470071 1250 887468821 887468839
    0xa0509010908010b010c1b050a0311030c2d04060906090507090e040b0415090c14120c031002031f0303120c180e07020307060e060f06011b080a050f120105 68
    0x802d040b8201e68240964602007480b0352407040c00a03141800907000c4050303c4203406452030312140030800854003a042101e401001d10350150a501e4108404015217000301c45090358a0001e000202c101910107428600d40003400e501040a5a07460300081c01608442104009160f503502c400d0002d06401e94681c07011400404001c1203950340781c142e861145030490446038403501c956594882c0d42d800800c0780201107964202c0c840000302403c00c041c0003088100300c41c4d000000c0f450b00b000007025a215045c9425400071580910b43e4801044115214034082c00050b120364501003030076046d590038040340503c1028804040f0405030800300441605100300e2080064089501d816101c0c2d04000c50300c039114119400301002144660100c0a5010700b052054a00b002000c1c0da510080d80d1003480007500680016040011056017040d440c0e500c120309203030900c00503040e80c180000c400d499020142415138001468030040c0d02a01c02c485904805c0c01419035200303810a0000c021860a000d402e104040407 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 887471321 1250 887470071 887470079
    0x40911010e0a0b090609011704030c0606050303040501020a0204050606070203120408010501090c120c180b0d050f070c0803070e09131403030601020d1d04021b011808040302240a05090109 82
    0xc0d5501e800351000809424645032013402080180d030080e50406041055420500440000120390b4a0081c2d1081c0c840c3d00b955442d6260074030a40304160041c9000340d1043c03108024581e80050200080394054400040b1500c4600c0424100d114081c40690075110341d2800d660b109401d01c0040c01110710100081100b070b40c036114002c0907a0216914a00011521031443c2c01ea0052a03004804203000ca082400c034140000403500301c48145d5034410327407192501081c1000d00d400e090054907407081440c00300c44990f2401c40c1e405031800c2c03140d40c0b025043e030502000240c440f07070203a100c10f9803a10300140300141034070308400c400c03844000454046846001c51507040301008030000c1a2405020142c02030003141d110500c0880301a2440c0e030521020002e01d00482c04161190701c010890300803000c84400d009041c4040c2942511000c10092035014000d9040001156015040c0d8041d40ea0488031000d903490041e141d034180c0c21040100d0810700500007202516950481d00034107003c1ea080e00c4001646a41d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 887472571 1250 887471321 887471329
    0x909050a091709030a210e030303010f0b1605120c0d140a0f020102121608070c081204060b040507270f090c021213300803060f040911010e 61
    0x86480c0140100c2540122000359076000340505281d0901130112517900d0565191445810303122441074100c12058409400059408460300020740ca0a4000b0741c80c5515040080b50701d15818818085070501c0440c01410701505040c441075a2078000317085514082c1184d200c0c564580c05019101c440b84281030120a0b0b03a40038200382d0254801880c82c40e4107012040c03106440f64003100d00c104045540c200401000d401c01d441006010383c109001007000c1e00c0024071b01400c80940076060000b070100200a50000a9955007224910000c01084a2040e1200d140000c042c1003a01d00f5554490304140801582d00c1d030180c800200d100c00740c0024180d4065840440015040d14018507810b03081c0042c0900862005401c05010340710988110b48056440324102c0031a50408003ca010700c00c03c4020410108206444216000307600d8001c0c4044e000c1d01801c0d406c0c600c02040d800800c040008030006030180d031a101040016a00604203020500c61498640840d0448001d12804203c251010190500f0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 887473821 1250 887472571 887472581
    0x13090605040b1e060a02010f0603140708060f060d0809060d05160906080a05100503060a1e0605010e0d0618050115060f051608090a0603051005031b06160605070909050a 74
    0x3e000202030412540a0602c0059400260300005664886181480005103407143c3c00c011405544081041d041146401303082050a030300440044d03100030140156078404100710b60f00b204048403004001d09540c640464103000702c0410030350241c3c010400b00040c0303107603030800e41c841c1048103c2d5580c0024003c0041d101c402172401244006044170001504000e1264000c64010000254500040c0c1d50b500010f803414000721000c2400c0d03900d44c43c0402038001500f0b8250303900d5100480a001c01420308000905243c0c241c17060700c0c460700401d040c00c07003070100603400085101d00c606410300c0c3c11011130030580e020b40f0044031031801800c140080099010300c6054803103140807446c0c2c3d405203802180146c82d8169030302508145c030400f0303042149074043c1e5207240a0300024515130b1000300740e61030440880607400c04540c0c410303400380d0429007203c4001c089101513200c0869003140c8040d02d4a074041e6811a800f200740d503004103c1031070202401000341e04620044110740c400f807024010341e541c54200c0d0701951 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 887475071 1250 887473821 887473849
    0x22503080a020d0314070527060403080c01050601030b100c1b0902070308060d03090e0c09060d0b0117010e19151d0a1a0d140114010611070b040501030b030313090605040b 75
    0xa1090006240d00c0a00c2c051510b00c0c2500d24200c0c23032100c0c100070002001588a0380c007c561040300003448035551282805525407005003401e0801000026130f011a100780d1807081c0300020000540c1c004c2d0b04100c803416421030087d0180403540c01c0a51141c1e8000000d510030b60040d800700700a0320016090345000b151000040d40e142d5110780402d46400d00401036001701911299840000788000e003155241e82000c2c000203030a0705c00c041b401d036205d80c002404104044500340650440000144114502290013581002042e411080c2c1c03400d003800c416000302860b00d106458102c801c2d100042050302150a40c0901c0b030030900744c0b0080d4031a0443c940842c0c1d0380800045a0451240504050b883c00c0d00790484c106006c2c00c88481e02601c2d900e88242100d0031038803030070300c074240410051000030b0703011003202c0311202550700418402703081510b105c005000c1d61040d0b5040540340c0a101c3c1c2680c40920a40d242c5954800c02043c4003030315500c20310b016168034080e190003580360003a0319050345044e0712441041 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 887476321 1250 887475071 887475077
    0x50609072418030f110406050409170309010e03030103120f021614060729090a050303011a07140303010614090d02040c030e160510050a022503080a020d031407 70
    0x1401401d08141c1d10489100c40124070039840c0d40001011600440c2c01081240c4144a6250b100700700200b0003007115404e800190180349804803032000980485100c10f0401e0240309126142c0c0e540e1200b550251210780c81c3c1a5250001100010401940000c00d10480e55661500c0740800300c1210201c0e901d03d600d26411b0f60844a140782048440494000c10321800409000c851500400d500c50b0384c00292a010a034040780d250f0007402c40122000c0622a0300142d8800140001c3c0d129520f0322030b80c87c001801002c207843c0355045003100d2014a042164042d59011202420361000d4461643d140e8000744900404221841d041040003c0c10004880040c007006000203801d03105134092000609561404100b031660303d4150720000780b030030030500781144142c04c9208240d42c24901800388910710981d005003400320500040c2d00c01c50b000306031805496050100010701c14082c00144800715540c1d0302c05448040b000070703180c0940d9030103d080585414036071410f01003003000383e07011004107004076044000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 887477571 1250 887476321 887476379
    0x1030b0d030c05100903050c0c03012306030a05010e03040e01141e031f061e0e0c0d150f1d0f0c0d2009091305030f0d1805060907 57
    0x30340540b030581c0303205014034121496007902003030b85011a580ca0038140c01040000ca405909900d040210f0301c0381c50310a4000388400080d4201c1f0448404030320948802c0010307c440000d00c00d440402200282030b411030000c1c03240c03503603800d0110345940c41406007201100d03400c07002007001c0c0342100800408110152080d20300010040135000d80c0d40ca02c0c0c4401d40c0c140500180502885c3c400c20080c0c04070301c41910001595460030f50620044424040c0d6075410440410040000245035110907034407040e003607000760740d44144e408600010100780b101502038040701c0310042268889011840709581001055900b8801e0030745143c5c4a042c0d007144c00c40b642c3d8408000050721121000040c18440400e4400844d090708160403d41480980400360522244086030f44660b51a181c07a05e035801c00010024003281d50709a48071580c0324800c0300c40707084081c0c000194000000e5200d6105402a045240c02c4080008841c43d01ca070b01d544064801b412140303c0e10728085610f4081280740740c1c0d02d00c2920075400e0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 887478821 1250 887477571 887477573
    0x50405090703022118010b030f1513060207260c100c0e030105090c0102010c0f140a11010e01060302010311040e01120305040f0e04020103061d0a050c090a06030b0f01030b0d 76
    0xc0a580030180e000741040741041aa008103148080c04d07801541c050754811030740c1c030219584d1402c564a140c8228444c0d48000d80040c00100007189004920080010f004555a0380c07070231544458440c0100180404c0c8009401002c0c000350180002c0400c000d6107001103840910482c01c0050302a03200c980b1950b8010b00500c4031000895404514620424200b4420325041ca10029003142c10854104400da048212160280c3da0b0a100707500c458002820a4124100622002000c1c00290b06881d00c01d2880000c8c0f030407103507000301048a10941810b0003804a003181100f81c80c00303455184000c0380440d0501c1c480c031a80c2c40b242001c0c1c0d010b46460244082060f840c0419006003000030050030303010300c030040001192204031420100058038005440200301d0600e40b00040440d01075070b100c9a000360038110004000429112210340103440010041440d031030308000d0030705038031695488680c4050407010004400741c140d08020840001140c2e02060740008000640030343d0109080140e0041801c084030b4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 887480071 1250 887478821 887478827
    0xa0e010f0506061c0b040e070503010b030303010f0905070c02060c030703031121130c0f031b06050327010f060905060607080a080711010504030c05061f1401050702040603031e0504050907 82
    0x107525420080840c10111203400706c1c0840b40418071003001034224580034451800e0034025044190b800f94000d41c6550314100c8901d62070f69242c0030343c0000c69100d0003c540351900c00c1c13a10074480fa4008044030b644840e806081c41d0b507944040c2044011900f401003030003031600100c0580b240360002e00c510341c2903916000c0c43c400515000a0010304d48410005148011a00803c1800040d240c01905914420300350705050003031000301012110714108080701030003000d9202c0d0580b90000c0c00000c2c01c0444642c0c6001280d10082c94040c0843e01e9860100340040003d2150401821140303e0700381008a81c03110000d0103036600ca100d0003d014100204040141c080c81210155449451450040703101011b00c401d15003951020b540640000c0c52150612060107800e10002d60000088410b10361400024003840c00041458032901d241c2c00d086007500b83d01a4012002c80d9221540244100800d03600c07894090401c602c1d800a5040b0885440f400b1110140500211000d80350000c10b002210780c0d652a0071 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 887481321 1250 887480071 887480107
    0x191208040c060507020d06050c0403170c0a031d19090e03040b0f130f0e07120b1807020a050609010510060804170d0b130c030c02010606090b0c150a0e010f050606 71
    0xb20b801003268086d9001060035440358034050011061229a00e40c034504000c0a0342180800c01001143c082040542402e00081c420b00f10343c1e07141c100151204405100320503021803144905030040f006a00f050780812401004030146c80c8025000c01040304033500c500d94900450003210306110040040489031235001020344400480301203505d8400351a10158001e00c0303803075844080030184603010300c007825800c01100211542418010000ea00724640014014040d100e400b054941e44c94004c150502c4c0300b88070010302c854000007115081e04014401034006d0404031180000001144070109407180306003407403800b4541188040310608020004040c01d80d0040705c800c19000e55601c0f0074002a00c0743c00703801c0391a505928001a000c00b107510040c06445000d6105411a45004400d0281503040703110102540c410b0a48180c40b00c500e26905450703d20b400c2c14481c040d40006042040c80c0c01903400c1b4080c0d00e00c00c10001d001d6142e004c80890213446040c3e88180e80141d0510504509a10880d90 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 887482571 1250 887481321 887481323
    0x316090c2c0307120c0303020c1816020309060403050a0b1602030d021c06141f140f04080f030d0608150a0b01030902040c112a010f090503191208040c060507 69
    0x26030702c019988a450b00300075003210400301c4094050405c100309254040c400318244038010785112003007800d050004003141000034806002081c4000700a1002c92003003054619a206c0a060f80f41d8454aa003000340e030711220200210f58000201c4002081140004900241c2d402950010f40c03d0840d10080319010350800c041c5803699903804d5288000c6405140540001800300c08034000e958401c42080c0641882e0641600303012251454250724544c0d8481c112140740503c0418868603aa5180f0703012820384141d90020b621881081011698400b0200040009041c2c840302042469510a0140d48074528040511000b15007a0b0000e2000001d43c0c2020b4228201403400044c0351006600280455420807950b02c0003500001040030000400c00a00f1200c032462119124501040200484801d1001d00302d141008400240b640341030b4025418100038140c001d0903500b5260b040910f00349071b0b42c1840000e480c10010800b11042c507d001e80d07003132800365401c1585a0145800c1c000b00ba0303401ea012900c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 887483821 1250 887482571 887482573
    0x6180f0e07121401060b0309160b09040207030903230f010b09010e0910050916091b0c0206070b04080a03050121140708030f18060a08010e060f0316090c2c03 69
    0x505000c0e0f03020203115690180000d241c91540700d040c0751200500d807016061003540c8206d14408244155070620056031045030040b04d0141e80d48000d484c040b2220269548012304e03035020b01c0301d40c400d1404040000d4020003581802c031503400c00007000e02030076201d4016806800010f07000043c0010046501d132281c1c4072050004589090000406403c200e40d8125880909500400b007155034030003100d0040030007420f600c0014000003040340c60000d10322084085810a0241c090350780700c00c540700c070401e40310601e4010314054940c0c0342c1f034103098606901003001480001d1821001060129056141d071411010000304061100b0495440020f20010028024918440c512000810520410042030019883c0241c136885034030b403000d007842c107611811010b80303d030109020840740790750b00c9a80981124410304210308241c5842d004103002c0c0c00f48000203a01400790b20068829a20b14002c010221034424600b0050160030940c1103402000584e40d089070104406459000508400c818641c0b01c44010 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 887485071 1250 887483821 887483843
    0x601031d012007051216050d020d0e0d120c0204062304200d0c051908090c1c0209100f0807081006060512130606180f0e0712 55
    0x9114051003914102040c00a039100c2d11030820740c0103400344141041d03441000e40ca00307109083c1d84050f00c90513152001c140003107010601c8800040b08150b00149680c1201c1924141a10320b000251111404c106000110712402603984040c107090019004860b0440f28096031040d6a00088070ba1018040069a1003529003002140c20045d50125850303140791000b08250740f28060042c4400d6a83d051045444021600e1910300c1e01c4041d84115007005088410024030b0b56080501520780740101040c401c0301ca00c90303040da540032541110200307001c0c06102080b03c900b90384a000b04540131588034503a00c80d04200403541c1c001800d01c1e40d5001d401c20386100811048640310f00b085c080284040c0c3c001e40341d980c80110104111102842036081c500c0780c82500344942410a0400b034158820020400309080100c00003034081d2403030120016065070b00020a102d080d5442c0780030000d0001502d074a00e1170a103091180c0208000701d110b418003002e80c281c040d18031140b030840e0040c46040341c0711040d6080d11403c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 887486321 1250 887485071 887485091
    0x6010c03210603030e030c030601030318090609060302011e09060c020f090f10061815020c040c180b1303060c02100f091205070512030c221a03010b070b060103 70
    0x5648040100c401c8081c00140c071840e5041c000d21514201d10018001e802490303114425441c082200c0e4152174140c20500201c00340980303001150980c0e544001f5000380751240200b880a070340e07000b00f0120b82c000d0381c4030004002e02d4400b036003400c0d83c4180c000c004520300c400208a56406a9503e03403455000030541108990b440e808580b01e0102200c0004504000c4800c00c0813540015906030050181c501e0091041c0c0340080856004041a0091039078620780c000d000f03c9030500c01c00c21400c00358400b510a200c4602680009411201035525061002440003000700f800503c0406941344545100a0142820b1650311410020900b0407202c100714042d035042c00480c0c080d180500107407525080c0c0c000485106d107040a8081d4803003a040007003080001c000503404503000080355402030b0a0500b280340e40fa266a0003a003164881c1030100700c2c01114613202c1208a50341580510206c0e8080d140700400d04019090640d810f2100340644601c2c444107001700350101d0540c280f40c0e0303401403040c10000340c16540 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 887487571 1250 887486321 887486357
    0x91203010e060103110322020a08011b09090c2321041e151d0d02061806010302011e050d022208011e090503040b210108120306010c03 59
    0x209030081d52160428030300b032203115680b501c01d00c030018403100310036800d5042500c2c0c0f8410140000320180f00c1c403104a00041c05558070342c1048001040644c008001000300c0031080302d4070201c08030300742010800c00c5800007070007803943c0034903902d04640d0364601c101c5840c11001d070003045150031211891040280441001e01c500120125410302c41040c0a4004d4a858070f009440d40c03410001d807451640300b403031141c000171702410940d4030301070b890a402240070040c00c500380c0c450888255014049100c2d41d41301e585402d03008500c190254a61291114540411041c641d61b240703001e00c002800901d1008a0000301020f500f0040148505450550300d042d074142900b0f006c0e40c109501c0010700400074a4008492442e04c03500c84002c05140d0001d10200740340961011070041000d11041080f500c3d503186004000060081f140586480c8040303035100c407055443e005a404601c0d144004501d02440003150b500c900048c4001c41012554583d0310395610240116543c2c003090380120f082c003401e40021442000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 887488821 1250 887487571 887487577
    0xd0f11030c1f0e190209061302040b1b010501080a0807051903030b04050f152b08030f0c040b1b03070c080f100b060403030c1e0303090b0f19050912 65
    0xd90b5080c062228410301e4540021118500c007007081c1da50201000003400e21540708204840ca40403501041550341e03000114480c0c5d410b03003003440c644134400580403900c0f440b4100500b0098000810000703000c40000000ea00b220800e01070300300d281d8000c800700000505400f004082d9607210700192058100e84103e1083c2510302944e00310301180d140c07114030361141080e1181540c010250350081d8098180742d004000f0190101c804140617000340018210480e140306800320109014940494100b4620301305580300750429281001e000d80401c3c0030491501c02d0341c0c2503030103951080c40301c3c900d0124020808540d0381c281043d512800d002c2403007980045002d01d52880300901121000e0103000004103d01c90400c2c8500e00c40340301007071a007410380c11903071a84816142501d900d0b04000350320785000c0c00c00510000c1c0854248090600c002c06640030182d140e049000300c507200f442107049070303140c0f00081140c000341211621841c8520b44100b000150305a00039541005080003926142621558031341003540c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 887490071 1250 887488821 887488843
    0x90d060509060f0c1305041d0a0b090610081207061b03090303062903070201020f04030c03020102121602012304031a060a0302030a0f1502040608041101020d0f11030c 73
    0xa0000b004104203050010b044070340c002030031090a407411400c3e40542d0017502540c02414081c0383c0e100000001a60180180300c85090b42d14200d90806c18645801e8548000440d440c05003400703076002194240302181541d0050b9007940014000c03111000100e8542508023040549030035450341c460300d60445094042c1d0082500e282d90110f03001d110350602074151003031130340300b1021305104808950a22010401c0c62200304803000b50302ea900c0e05c1e0000100d000e4069000d01e145112030000300001080f54044d00041128400e03000c0d10350a0701200c1d4100414041e440f420780e0040c0804000c00015846480d001c40114109070314050380c0d40241d100042365822a41040300d0ba1044141e1600f255105500641e50258085849180140c11035010079141c207892940208004080340024042041c8411103000c002803a0300304545442e5590030050642c0030544066a001c401580300b4800c5500c0030440d84075204440e2158803040340c01c1d400482c0d445101e40e2032860f4502042c003894003090002d100502120b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 887491321 1250 887490071 887490073
    0x9020409150b03010b090601050403031206090e0f060f010e06061c110a030e0703021f05040302060d1a1813210819140c252004020309060606090d060509 67
    0x2d111500c040c5400c55032107042c218802e604000402100b03a80c040b048805690341407601660204900086201074002a0000202c4c2400e242c1158100e150006084000d1743c00c8104131141c680f02e01207030f000400360030300074081c03004044000034442d410301d100241051481c0e14030050b0303400209143c840807a40308148400c144000081c2c0012860f601d402003180700d0400f40d0183c01414919400111007070400c400b00c031603804905480c241c0d0240148250350041d6005010150b8400c10810001d006109000c04c030300601004100e00c6241c1d091692200c1121403548842d1051500c0b1039031041c01c0c00441001c21074140d080101650100d6803201240c03030360320110b0744405500e42400340000305c41f0050382d41d000308400d00d4460103582d00b6104041c0c103500690fa80088541d00d4008500c206a1401d00304004130b80704601080078810440c0f41d0550b5800b03060f4402c40032024180321003c00c0107a11059801e6285603000002040305894081c00130810382a00a240c01d81451150f602e44042e80c800300c803d1066 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 887492571 1250 887491321 887491331
    0x209151b100e330403170c07150c0f0e040207080c07080f120a0e0d0609030809010b010906020a0b060415032105070b18120d0905070801050115030902040915 69
    0x2810703604029031000d00e03080c00a640000204400d8499030040c894a00e83c4207020700b1400709084c14044d600c4060280013400c010421880c110119290542c45410215895002d002403090960706a10074141000070303642e80d1080d1201c1d200e6044408003840924035a11590070002c03000002d803440d00038041010b006001c6d000f651314240b816401e050384042d4243e026040700c2c0c00c000030140c0740c030100d800040141c1800b1a41700c945901040c204117514000500152829220b031050580102405100d901c120009110303c032000001140c40c40494401c44004da03100200103800038020300f20300755009001400001c1d02ca0b102d013a15001651480d44203407207070f005039601750381c0c01c00c003000c00c00e8080c007120300300305140503c15aa002003081008203654000b91400e06540726950003030014580c2c05010581e407644500c80c3c104540010310300d19004803020b10402500003070f0b0090601070305049a19030300c605c403048013140f0001d0340541031850701207a20580e640d0b8188005140b01401c03000402881000241e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 887493821 1250 887492571 887492591
    0x4080913151d10052b0b070c050c060a120f020c010c0c030e040b0a060516050105010815010f0b12040602090303120103231f022a07090209151b10 64
    0x42c06160103490721400104859050002e41c99001c01032440425080b880c06803a1640c0e400300100820204008180d02840005d00c140598424101800d0500031400e840c5da996101c0104040ba01c19a040c54000c507020f20810002007074554800403a10b14640005480d1a2041c1c0000d800c5944511802000c03449800c49030051550122031100c20200c19542000100310b00d400161030310f100c2d1f1040d4000c020340001d1580703891940e011602d002951000007030000c1d5031200b484540b201c00700500e0480e506041c500000301a100c40d405002100c10710700c405890030840c0418081000c030300a01c00d03101c071f80d000c1080d46559242000101082d0203100a24036165046281c40c0002090b1640c54444105c42d1a1a80c00d902ca40030403402c0242c1c21250181d00d07171051305d100c1a80070f80208020082190484040c0e50b8404410303141c6044048641020384034000d868184600172070040d01c030110b4115a450080c0714040340b10078000c2508000b049401c0152800340c0345140c1c54004901e209120081e1540c1d40c0740 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 887495071 1250 887493821 887493869
    0xa0903050d020f0a060b01032301180207020d020108041a1906060e09070e0f0307030506250207050f1305070315050420030a0207170304030906080408091315 69
    0x45000c0d4405044000302d0343c010f843d80e5800c0300b00060101d594498584000360f00a51080201d680c1e10b00303100c150003140000d0f01e85216000d100300e5103006016403640c0c40ca26400d100701c60a0a900400407441017009400450f001c40c03000344200e80f20480c980346104403041c420721051181f4101c94010350b51150030940003007a00c000e0b030f0000f41440740c003400c1c14201e0342d6141842944404146062040d15030420001503003a401e0400c41501400f808034040103110022038860720488003000170f0f54107208141c0d2030050307040ba680c40b100b00680140800340030601d000c540d4640039220003030001020006d6901010111001500d1540200750303120b400c803c54140c0001e9590050004560400480100e500b41940614007514031610301140000000c4054502da41034410031030b0881d134000d0a082c02c0c04510245903000350b40c02c2e00403803006030340017444905c00c0207040d110b150300900c0103003490074180a104510300d94010388003180361502d014105180c081080040200400c881003848946904040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 887496321 1250 887495071 887495083
    0x40f0201021f090c060c030c030f051e04050a060c0203070e0712140702101b20120d06151403070e041503022803240f0b0f010e090c0c010603080a090305 67
    0x20046c00241030761031000c2900b1040c0481000e0301810074026071080e80d1002c40d114428192000416100086150024500c0038050001e40301d00307840513001300717803038035000d440768008001e0087d03059000c0d06083c01741c3c00007110301036088040750178503541941d6000540025604500000c2c100b19084108101155030304002050b18001d4102003003042a40c130207441d0a41c0514184200b042c40780102101e5038400841000561050100c020380717070078030700d0b1003c042c041d0360100050b96002424200d010406c401d1440b880e071600d0195480e40c1d50b5150200c41e101d001a0001080b82d0f040c0030481c040b4111780d071142c0c001c406a420f11150001d058904503c1042520200e00070701c211a6241c0514190822003581c42c02c1040d01e4000c208001c61641c03014a001030580c0d0003000440080c100041c42030000d034980c100d41500c2a0407144407541d04900001102c049012552450b4088038482c013141b140188000141418030030000081001038681c2c84001c03250707000000f100300007940c10a040091280074829 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 887497571 1250 887496321 887496329
    0x8041206060f270c1b02010e0d05030912010e190809040c02010c1d032d0d0c14031c1109090c0d0501081f050705120a0c0e01020d0503040f0201021f090c 67
    0x400130428101c400070060790072000e406007410002540801035a00031003440828060041c2003845800c150310b131039034403500415200d9004a080002e480c2c218101030040c8910100038600a1107179030b103510000542c012159209442068003040381c84150348aa02401c2c5a00c240303030b00081444242013500600d00320b40000a807030400385074481e03c0984d503004501c182103080034846001c0c402c0708112140c0942a00c80300701403d01e00ca6900e10800342a00803010340100744c040d110002c07448000070155030300c0c2c1c800c00c0310701c1d104800300000610000260380e000390310b5825003102070b508180c0d0500c0440d102020030390710885003044c0403c03440d5404d40795001d030318007401092028000c0e40c600741c0400342c0340cac1000305205803200351610001a10a80700d041964440141c02403c80070a0034480403003001010711043c00400030313a50b40503506955000244210a021250342d8051869445d41c4505c141d0204405080f4114040c07291071507100119844408840581c4400001c1c915000b45071060700380405500c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 887498821 1250 887497571 887497649
    0x2010b011b020a2c0406140708011d0903160f0c050d020d1119060503090601061805330c0d020705090c0a0918020705010f020708041206060f 62
    0x9458001612003800c020120754003440d500c04e44c05101c003801e00b0300c94605401c00001c21092001c10050002da41c20858403104040c50070141900c41036000c03241291700b4003848044d41c12400701c0d070ba0f5004e00301619039030004410040d41e0821a05041c80c800e6009180c105803440e24903a8810300030300580396004401808200c80010016509038040f80341c00b5004074002e000744103070303c0010b40380361284080c900300584000100e18101d5180e42c40641306801c203580740d0000d44104000443d03c1402103d582a85250452460b0440c40ca440100328124031f000c06001c4210140e00e00d210200181c01c02c3c5030708010300d0302204685507001c0c01d1143d4035110006801303000310340c09060204260303211315250a0300b111039aa0038540e07131105c84905980100342d55000071210707200340d416030f100d00740241d028052091081d00244407061000781e002040e40503943e8084d0040c90200410450130303120500f030340001e501c200c07008503100381d450240000c00d5a0b2a40051500ca000219642030074003900781c50a441c4003076070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 887500071 1250 887498821 887498867
    0x91906050609010f180f0e0403030f060f05130609020307020f0d09270b0d050321101e12060c03051e0402150403051f0b15032a070302010b01 62
    0x2440074941d00780010034441c4111168045d03014100340c20700035016502d0311801c0306542c0d801d0900c651342c0c112801d41c0064500a15070401014034084c84080b580030031520040c3c81c1c10142000769410b448580ca14010346d030795000154901050015511840e81c13a00035000001522080d5820810741f0040c0c001040260a81844600c00880300f00008810884a81580540c481480c0004106002c4500c3d840848070144100708840040140440ea4607100c8900e1062442803500807500c4041c0c5600740c8140c1d0844050000c7d6425031907440d5845c0505080b407000f15035039031042c194024006016140c05480e1101c900032039405004080c1c0115902c90240000c88060a58420200c005480240700301c40e02600380f41e01d58588001d0307501964001042d1100c00c000c2c00c171441590072032106d038404c00b542000700d140c9261800b090101040d27021b43c00000e1071661602810680b00110742c680c000c940340e8520b8803449110300302d4040c0440038030075000000d40132510400944031801207008501c0d940c040c4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 887501321 1250 887500071 887500087
    0x50105100207031a1003050307120914030a0f0618053009010c05240405010b01090302130f1409010c030e060105060d0b2419020d050301060f0e0919060506 68
    0x1040826400c004c0891460000e4640c0c50462100c00c0c0b05501c043c005101c00304504051001340201421100943d80f2580003840d1348030403000c120b4249400c0c565141e004400e100303010a04284894031003a204420000302094080c00071400c3e81400502a14503134424100400080100b451150700d50004280f40c0381c10b40d102d1030a0344618498029554100060460300a0811408200300c403c1c41d20302c141c0c0c110310000410460740d4210703422142a22a0b41c206035080c5441e5009141050941c2d40190502d9043d61041841501502180303950310911580c0f000300b200310031480040e260048040d070300007040200d04504001d0940d1b07002100101c483d0450b40c0104075554400c021030ba2100c880c00301c0458915001030000c1e503182545020900c4a00a90310006503204003900140b10b0700c4440300b0684418450100c04a035a103684511041c00718000f0001030207080d000b9040b11701034480311310303103084141c41c14404075070800c02c20b072000780501c59024a507c084d1102070080b10043e00e41030b80c0560a040e1a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 887502571 1250 887501321 887501333
    0x302090c1c051b090a090c0c0204060b073804080702030c01140a0f0e060304050109020901140105030406090609050a050102090a0b130b2a0a11010302070c03020f010c0b0a05010510020703 82
    0x7290001e00d043c9140040e100e80c00d0749030b03070543e4070003041d6034101042900d203e0b410240422a400900724869442d00c9408102030f0240000c1c1c0700c095401010103101501000318200701c803c842e2804d46c40c0100c001004200110001c6206486188200b054549801c0944141450b1800784d0b481315041c844109a210740e43c00c90601580c44c10039140c50703c81c00719241c60ec015214049810b40d0a0b411010001c20002844015000070325102e101b9500012942e80c1c50450050b0f500003a254140051410804500031032196044491507600030000024520b09543d9554076200850f07408441d541d4010403401c105140148802004244c446112480e141140844d0800030000e03010f4130b41c403c08042043d03003005004400c907040c0d01c0c10365002d1644c50a44d800d030344dc0d0f030703405041c0044800c00e007403950303014040d40b080c0242c45100e90b2104815480c5411a407c0203000300d01c41c0b00389410080c1d039903001000b0500c40740c100360040f088080c0000340e6505040034404802503070000101954000d20042001402c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 887503821 1250 887502571 887502601
    0x30a091104050912030c091807020f030c0309010f050c0a0f170406140307020c032a0d02010e090703150b04080c0607020a141c05010b190807031b0302090c1c05 70
    0x180ea00c0c0c031304d960ba84c07058840032240c01042c0042c0d0304034403c00d0b41000b0704034103225107138002d204070b030220b0344189069800310b5542d201e80c1034030070f03070307607041480640c0142d4000d140042a510795410040c0c10410065009490520301300703400d03594800350740f42500502091551103030b49066100c0d50a0329080c1040d402602c85038009a503040c02c0340000000840c160b20a01031a001c010b80181600c92130386a83e011041c03110403041c3c0a5900c0994035a4803849454142414070304103606855507180021031808110b20302070010801410316484030b10100075a1b0706422140c020b00041f240c2507071100d0504207100c0c904032000c4401400340340100021700140e40d4415a080c02c8400e104141c0d40703000c000402003101c0c0c4150070302d00d40d04c005c200a00a020040190042042e02d18280d403206100c0c0c010340d6085080200b41d118100c49504081000c0c0041124900184800400c00c401c81c000c46503294040740c80301c50202c0703010650b4580030402460750342d070700703044a03c010b030796408103100390305000c80d0b10b0345220 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 887505071 1250 887503821 887503843
    0x90c06020609031e0d020301060833010f0201200a12060311060c0f100b19030210030b0415080703150203010806240d061b020303100515040b030a0911040509 69
    0x20044134800a588118000710b801a2680c81c5056450307595074080507220300d50941d05c142d10306800c0c07222280a9030110045c03003540507006507100500c0400000650b4002481c80d41a011075480d20054448400c40c51458140120a0310039143d40e40c0403104010503200340900c00d46c2400e800c01c07200f0004036822058024445104550007a80d601d00c4181141c42c000159564021070300034000d6043e00c0c014161b000420340d50301524070304145c5411060301400c820361400001c5d8402c028640c046c155500c6548540c10300790340070b00001913501040c1c4008600e0a11688100071039800040244204054040080d907417000c542d07025030640d4140844c15403102d50040a21100c4a840599903403140c00d01120003200d03140207007118a1008080c01c100000d450516500c003543ea103c0b840d011030552002080b20b2160748904000c1c403515080104108068042c10100326a924040c4008190480614011070061456400c0001d0200603031a21800250048503a907118a251804000c00080e0110381840d082d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 887506321 1250 887505071 887505097
    0x6010512011506181509050405060306070f031802060d02031f0807030b1308070c0e0114010207050d0203071710050a060302012111070515090705031b130f090c0602060903 75
    0x1111401d001c0b400c00d0119a001104850310807a4017030303c180c2c003c00244181c950a41d01070082b80d5504041c981d9641c0154de0010015000d1072440003624402d505c41b4200842002000da0710950740e400003903d640000c02c0c480c41082e03001040c00780c86800091620302c0c0000708500c0c641070510700030180d03854829901c400b9208001520005288443c0501c1f1240d2956008602e1901e40c1c40c941015800400ca5000c0d0060602c0d00000200d4907003001c003001001550141d008006a03810841484101000a20304a23014842c20030042081241ca10483c01c103180d5050003000030000d40001c00090301d8010301401d20700d81c5802d10900c050703640041e00c07044141c203400600f0302030200b0717050b100c0082450031105102c20101141c0c2004010003c10b40302e040d8805602c0a80c502e0b19228482c41d104e150302d1103641e6155010388010700ca08200d06403403c002000050800910400084030701042d140c1413290000419a10482001001200030f01a00944442d2004085074a81407020343d0781c0e0310803110000e401d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 887507571 1250 887506321 887506337
    0xf0303090105010626100e0411010e06040b041701090f050f0d05120403050a090902211005031c020c0d1109071805150702030a060b090f04020603071d0301090506010512011506 77
    0x54101c4841c6100030807d84400401614044c02d081d40040d0621209a000a40c4202446c01d94a4a40c0942d016520100003641c07070145803200368451500307100b40440281d502c881e640004100e224003802a014012805011025040803415007014890000d820070701a09010f0303200c0541e12950000d0744240d25007003603952440161815601c08000380d000041c4280001144800c0c850800058201403810300d0650b051034851000b03501e200612401707042e4050380300500c40c0d0882d0a800c0c0d480c00c07017000280144d8001202c4d01c4046081c1c2a0b401506607520041e6134505007403402c001e210168840c560b03140c140ca80900395203404a006407036110300e620401e91011311100320764000e4110344a003603006040300d03201e2076a840c0c081e000d00301c04452140305618041c00903014100d520719161260f540185000e02d580d0b6143c000b80c48018001e09854045800e8000e010341603242449101403190182e801003546602d40010400304c0042800881f03011b0341003203a2015035a240c1190a4291103850030130f000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 887508821 1250 887507571 887507581
    0x3060e0903030f19090209041b060504050f0906010507080301080106031103240702150411010e120c01080c070206031e06010507170a05121305010b01050a0c0201031a030f0303090105010626 83
    0x4050441c5c1078019601094407001e001c03c000c4185803c02c85503d00075850010603981d8003040c0c8260265106240e00015203032801d01c52403500b508074941c00368050420608185003030702d440034150802d03000311340c2980d502d20050050044050180110701c908400400000c42c4c8405e150184c02c90036809400030041c3c2501003110f0714001c0c0001c4250070740d902d52040305031419003002310488211175240d5000c41c0c0c0301d0480c04090b05122019214405030702c030081c4000c450034001100c3e4214010719005070070806021000059698400450089240581c008100020329141d083c0c00c1c140900481d050020412048001a4141c221500880320100c00e564850b0180320382030f10b00d4401c0c42650038004504000704044000350075504102c0303901031402000140c2c048801598588682c02503d00815041e0040000643c840d402614840c0d02452031224140d01700404246071249440d42e50442d0741020080040030f0400b4030030640107100e81c0c5030a000540c8150701c00405840181d00c800711741c02c98900000d03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 887510071 1250 887508821 887508871
    0x20103020c01090305070210260601120e0109051209150c19050a0510150512010615021b041b050f09030d260c160611030703060e0903030f 61
    0x20705992000c0d40244401d0109140080040d0b00201040b03104204541c034120080b40b0031009002e0700c020b541105600c0360908204802600c100429171410000c9020341d11100411368003e44544c1d25240340089009086494458200303a5a10380305042c110090298101d0795480c484104088540345030400c0e0345140545465080900115001d04020b90072040070b0f00304400000c4410280c3d00900c00c0d070b081c582c074084941064a0b030122004c0d021f1003055505210074905550968051400030000282e0140c2e540943e0446031400446e034405604036641500401c8680c1140058851040714100402078820b403c0208a00a13203000301d0400c940031540703100200c0c2d054102c03405118010203c8100946448001f0004003015110020000801801c505c1405148504134000c41201d42002d083c84224402d007004101003200a40f089901c8910032088001c2c581c00031409100350744d5001c510582402c0350518a0a0007420144e11030380b08104000c9007041d4600c006400c0700814001ca500000399502c0301c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 887511321 1250 887510071 887510077
    0x210090f0b0903070308010905040b041205070f030e0a0501210209270118050609160311130801241e050303160b01050307050d02061b03030403020c2407060902010302 73
    0xe041d0718031503050190846000024000b160b1081c2d0350074400343e0703c4e01d0000c0706880d010345d002000c0d5401000414001107110103106c5140e04203180c23030750a24a1644540b01c60755001d02d0240e0101e10784144030903450038450000e101902c02800d001c1e040c1c0c0c110302c2c034000034081d00310006036000354081980300d07183d03445894102040f081d070041004803024541418500090078480c0311482c61081001214a600d035001c2c05110314001054440304e41e649002d01c04050680b07001d9401019940c02032440343c0c2d149039000d03244015202004144a230309040409085410280c003001181030030750b00160700095000072480075034540042480045400205004560360507401295141c0000b080c2c0a55800f21407401843c01c500600d00202140d9849050588034040d034091a40c0140078500da010160401d90b0040000104041c941a4610800c1c00a24207680007900c0803401600140da0a480b2450b0906100d000101c00c00d40482850440041c840007074850b00d8001810b19840c0e4800c1015a8045c1c1c3c10303 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 887512571 1250 887511321 887511323
    0xf071b080c01060315020d0f0501080d0804110a06030b09010801270609080a030f0f0c09092703020d0215010b0d09030309050712140a12181e031208070210090f 70
    0x200140c50500461245c080d401180071000795501d0900901c41580c1d0a000d16030480350301034040d0070503d0708408220707041c0100600070b40c0e004008000c0d800f5241c5940704142d00804140d680098001e1005c002c20000701c606911560550f0b041410b064141400c000c00c400107501030350300e009140c1c5080d2801d98050300012030003401b00c1c01d001c5000070320240c06030810031441520890030009902c00164034412a003540300290700060b40c24009000241059000c070058064031112014132121080f03e011445640307110440060b04206401100b45404000090240b644011030000c00c9d030618100d50450300404040780000c1d030b220100c900030b03d8003da100c0c062071900f040948643c2a1a2500b1128075500c1020859166581521259a0020101c0d0041c0303400d0b84507140c10075041c400d16084a51030701d01c16402151a4150f40c0003d807a03029080300e40d5510b40f07070500e00b01095145041452003940015008014051003104002000382d020580340004021030320002a9494182084814100f04000c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 887513821 1250 887512571 887512583
    0x4060b0a0e100c150501080f0d0e0103020a110d0302120c032a0d0606030506010e1203030c0906040906060c020405060f0a060f2007030b0718090504080702030a0b0f071b080c010603 79
    0x4d041d51a0f00550400c80c160784081080700c1e000d444040034203a468030b103902038070300081c008c50842c1940d40c4290000c103a401e14900c0c0021001d0303140802d1030b092011421081003ca030340028141655a180d4000c40d6000d04c441d011182580b0300030311500e18201e4080c00321018034411605041001c00382c40103681800c2440f03501001040d4861034044c004000c00e84441c0d0110780441b10a003034905d400a552082c0c00e480d0b501950441d11410341128141d0800c0301c110b40e0142c410b020114161400d071140c080100f80d15911058019001d006100840e10090441802003500c401c4100480e12560b09020071901c0702d190051401c051500304450304000405a00512000043c40d03c0341c40b88000740c90025a8001c00609269445540041c0ca00da00b88032103034007220008180401c035180880e40000d5215000e01c1d61a4076203000d56001034200f1020000450707040001d001070004810040c1c14103a400091400e14981c2c2d0b403250307106488010340d000d000521902d400204121860000c1d00540f0045178064 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 887515071 1250 887513821 887513843
    0x2106222015190e04230430030f090f030804060605030d0c0c0920090a0b0304200f030307260301030c091404020109060c2402070204060b0a0e100c 64
    0x900b020700070b482d1020840000358844246050503d440c0c03084030351440d01028241d0809000c028800041c0c0c43c01082524000c40c7e98801c28007441d0f10550700110b405504505819000000b0000350499000e040c000d940307103280402e1980012481611030107060307010b0234103000694441c0b03014005480650005600b41c000d114400d038ad01500800304c1c03c4241d1080350f110030159214030041048070504003003500c850750380000096064200000900c816072024180700311494903440b000706158000d0b40c0480e4500c41c81200f60300e041680c0700d150801c042d000c803502c10884102c0000a0750741d005001014141102e50f01100c1c00c03040c15000b28021082c1220030b0940c03a580e4038285002c2c0001a841980070042c2020741c05c0d65a50003107800e039846694141c40da002210f04046044455460000c81111182038121700c280041c1526031007012000c411000c003580d00d0381c0c6403040c44142c5907190311218070141c05004d681d100c03079000401e0714400c0400f6030b0070072100c0d0901318048485000001010b40114840 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 887516321 1250 887515071 887515087
    0x60a1b12030204031112070302010c03050d0528060f061107080106060c02100201151511011d190b011205100c0c0c06020f1203062106222015 62
    0x1d9005401100e014042503400030850380309024070b00d8840b0b03620403c00d03040180140300540c01035a8440440f8040c1c039007036013015110454441126425254448011208500c000107400c105080040d03014020909100030791600350b880480303c04902070001030040c2c40c00c0d02d40c4110820403000c0c000b84502802840f1903a6210b0014100741d519003c164041d184a111415615005002d80f180912001180380075480c500891444900010b4054000b040b01c1c48900008030442409001c0039031403840404c46a0b180945138080c60000381c180d650a145030003c0c3c4000214400003001d6044802091000300d03007541c81e1510074240016139400d101c41500d0494201d48440d8460030402e02140b0829001d2012600e03014203030380c1e030303524401c180516520001c00301c2c14400551014682102020704400440314191001d02d50707201104405034429400003080041c41c1c03051180d032480c05840c45401540100a94580740d010520700c40811040202d4081c82c06031507120700180d10b048030740b5254055240c91003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 887517571 1250 887516321 887516327
    0x17030c0a0b0a111801122a0206010f050a140301091e120c0f02121e060a0c0f050706090c1208070203010c0302090612100f1e08010b060a1b12 62
    0x1540c040414a107000c440c1d900800f1070340102c41036031140011401d42c1102440044550194500e081152180c0303454040c07406403e013986100041c0d0083c0741a080581c91804001d180c120160300004512408490801040e181d00004006943c1001802560f10390b0040110b80900f044c00c00060060410089500620505640000074a0701c0340603030004110031f40c002111886004400a4250f50342480310100614100b40c13400c041c11070103c1a80c00f1105100c1003551b03950380d03802d000035550300190f080140ca100244070312075000d03100c2e05241500f0079803003074010514003403048014161903030341000c903003484001c0d5404001001260b030162410300c1985071801f819084071343c04070b0080d800c1400f0100400e001e4002d0300c0c01e9400c090004c0d400c18000e800c102102c581c0190903058950200c08011508407082c5000c40c02410510201c03c60a0b10070150b94040640c480c3d10003610b50349440092140ba0f641d80741112000380da01d141c84201c0c2c600030041004040d80c0d03240010000c50a003460310140c01d030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 887518821 1250 887517571 887517593
    0x4020415151b0c090213180e0c0a0305071203020f03030a0b0102241603061703070308010605090a090507111f140f0c0714060109051005031617030c0a 66
    0x803060341d464545070b0300120204050340102c80010400e030400803042c807185049a01416214205010782c500c500d980c1d03440c2041d040b4856003504181502c0300480c0e050820200114038541d00300f40c4550a5042c516100c0907103680c05400b4003981022601090000c0c544200200c030f14041c3c00341e050360b60301c3c00c240c06010020103001c03590790301602a00710030f800700300e0741403481c008281140d050009907562070009a402d11200180d0b02d10034960348000101e440c1c0320380a010402800000c00969072003000d401c000c0d200002c1640484200a0308014a000503220b1000c44012118032280c042802c0d01c80c5442a1112a050b1b821001c181c841d20003149000c080f40301000070140964042008071654200e144c9503465021202c8001c046006004100b540340384000614071140940300602c030400b00c000c10340e410080c0c00c1c0d110000701d80e1158280065040c0004244000340400c400521080350081200d24000c8054814481c1e810000c003421001c031181481141c903801a10010765103803503c145841e0403484 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 887520071 1250 887518821 887518859
    0xe010605030f0a18060b060d02040e04170a02030904051003020d061413051b0406030c03080c150f0a051503030a050c010b0105090a0b0a05131410030501050f0904020415 74
    0x42c2c080224501a400b48103648880032109109003c3e20460348039040079102a10030301e80c004504110b2964400540d101800141032090f0282902c0d003014108020f11545031100701305101010000ca0991940000c1110848030082d0740c040b9440d50340c004101c0c00d05c04075600194000074910880410002241d21040e00c52084a40703100840c0c0302e16004041d40d01110320000c042d64007009040315200a0054881940c280c0184007052a0307403650303102c0c44035640c254011a4400070208442108040030700000c800201240d041c890030749440d000c4000317201030240a54101a503900c02198458401d006440700302000982241d6449101c003400401e0340d400403964069651a2405164007503200301c04480120100800800d009800d00d0718140e10b5511114811091044c03c000c1205c481070048403500c02000000c00306241d1010034020b01440301852000942014034100061125a9401480030000c100c2554500401e42c0c1d1480820003e00180050840d00140d4120002d0403110884c1560f048ca = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 887521321 1250 887520071 887520091
    0x415030221130b0903090402040807141c06050402010c060c020307060605030d05070308180d0804020103050604090b18150a050402010f03053d08010b0f031c080c040e01060503 77
    0x40519010306101c00015160100500703074202c900030114107070002c8582c001c02204240ca151101040001c0d08903841540500c0182d040884100003030801c500b225421a403040d21800e00207029980000030605020100400c125038880c00310b015a4810074500c0749a41e48040c0812242000b00d001079620b402114003104c200d4204940805e00f402c012803032072600d00c0191034407414007020355019503a000e0b00500303950010016256840031100200301a11480c409601e650343c0a0500d40001030649138004e010a005070300b0100d00c00006060050415480038409182c000059a48480607040451001780c10040b03000c054240035a125181d4080b5002e58402d80700c1003130380c0481150680560344200c8595080781080c04501d0016131000724001007092414542c1180905c01a035030007074100c1181c11914144c0e5460030100224284160341000b500f8044000b410305c480340d051820301c4001c44000d8002082008004079445035007403070a0390302038486511444007940e11800c0c0141250030407074100290b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 887522571 1250 887521321 887521357
    0x260913111314030d020f0a080a180306020a08090307121d09180c100f0c1a0901050901150308040b1602060d020903060a020a080f07180e090111091c0804150302 70
    0x703117800001d44555100c01c20014105c40304454649601c1a00144411014420b030104581e480c0c174a4042c40b94081d5100b60340c0140c81c0d9a480d00d00400c002c800500140c242d80c0200103003408a42072183c980d185010515046000c0e8a1101c03c3e107112a2007600c03900e4100060314244024003107240c000c0345052040030206d510b6000d000040242811120400d000030442a1041a0000d803003905c280c08401d015082044040d40350860012001500700c5681d9440c0e5982c20034403500d81000c0c024909558410b0303041101e004d0130f680ba408280c0c4218441ea14038400d0010b2070038019080d1003d540c00040e0000d20b4a81c0300d0300b85c1d480d8003010358080300c140ca200f400340743c0000d10079460300c1c82036540d0010310f80c0d140300781507481040c0004902c00140418081c003e06903218200c404911420074090a800b13410307558a81042c01d2100e00791001c18410503040c10052190828545030701d019a8041058807482001004041c10220010b10541d041103519910300b400c1004ca02c0c2c4c064000744020691402c1c0601 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 887523821 1250 887522571 887522593
    0xf12111005040e06010212030f0403080708010b12060a0801020f03041a0f07030914010507030e160308160c0f0b1b010c02100f020409060326091311131403 68
    0x90040394034030080401d1062006001d190f0351a6412580024180101da001d0f96605c4030350003050f001203030340c20a000d04c6502008109030748104155040440c070304100c038032941000e40690a81c09225019507030740b481900094181d035148a0b138100102003100c000c540c3c4d1a41c1c0e1a00e41c506600485d8240c60407000c0800340341e54410301030b02e824030075100c65400403110b45074000201c0146c4411401500d40740c0130304440e84460b4800703200341800b400e06c90310300240d00a03008101c03034200a001d100203c2c403c0d000c0c540800102d00700c18201e07a44a003c3c1071141c1031001d4035242070105140d072900306100340012100081415451034004101c1040a64150040214619071080c20b80e03030820742c01e00041e00301a030300200b41016034009074401c621038000517051a403181a80c2c030845401d940195011403840220902820b01c00004900c081407240340d0600d02031045011991501518004402d40caa5500f6130840315000070040d190b2850043e0303a0000380075074540c0c0700c002c50a400c945681c071038003502e50569 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 887525071 1250 887523821 887523829
    0xb010807030b07020f07050904081c0204091d0c04090c0b030103050105010905151e061c050a2702010e01031d16061107050d050708060403051c1a040e03040f1211 71
    0x10b45000d500c1c000421802e411f14003800014a0040c00032601510144480d038083c0202c1803616030b50700ca00710b000580320341c40c281c1d00c074080d5100b500c200c001c80d00d50301d005500c0d00c5901140c07400159a0944001c1100c1259242020700d5098950240036658030100000c02002010741156048884144040c4aa0f484d225641f913183c2401095082c1c0c44140459840034501d41c0c4651248e4646008008900b004508000304810248280030100d00981c1c4d07204111180d50144101800d101004034807071a003a4110b07a508440368840d410103810300001c86820f00c00b0707a209030403e042c42000501c0c6101088003140045550f40310011041e910381100f1880400c0e11842503140e103001a0100005141e42c625010500100311301c41002603c480c0511030b4042404402000724500841c4280c1e83c02d5525610400418100303402c1403000c1e40100e00b070014000c000801640d040c2c070595000c6070300013000c03080315a800d4a144101c2e03000003030f203030b07440794001402c00c4240c0c4c0803042d03c90062014083d1031414070204 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 887526321 1250 887525071 887525083
    0x5060f0708040816060e180a0e03090604060210050711030304030305130606080a14011109120c06030c0325081f091b03051510120204051306051f12090f0b010807030b0702 75
    0x26103031f40c0910340700250000b010b03600301c003541c100e488050b2460603200b10007041c5203034000c0e007025002d42d04c88040003001c0900d07841090340c03182140c54104103000346041c10540340d00c0043c002500b0591500c002c0f03401000341e41002440341d540316004003e01551340002e60344844d800481500c078842ca502c4444190001030080340703800c6601041c05482c0ca041d04040011810a0410042003845030340d81d1130030746894010043d8000c0c00313000c000c0da480340f5210940c60b111054111700d0010080890310303000c216076002100c10f80c100c00d04d04079a00a07101e14128034203800c07065920584c40c1c0760a1540b40001c1c078800c64080400d00e240d44d6001c4c4156580c0f030a1000f02d256542190903000610b07844164041803040720840d55503c240200585071503902c0f4001241031120120f00d4000c10782c3c40200300a2031418000c11100ca0b207034280441e251000e03080d0040c0c80c032100000300007406900c0340f5a2030200040c5e840d18140382948403039a9001c2d0758458400c95501d0301075000403035403104154003054100d030002800c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 887527571 1250 887526321 887526349
    0xe04150b030f210d050705030910020c0703060203060d0b04110315040507030308060a08010c090f350f0307060b0423071d040c030f110405060f0708040816060e 70
    0x109002504080b540c900220b60303c200000c10390091045070096901801520f0103140d41e5039a1507100e041c05002c0a0070311550002c1070758110320401100c0540000841c1d003004894120320010303201c0d90b5140214042c0040180001c225850400c00c02040102c1c061042c01051020707011140034030300600048502c86c100740c82c060800c0d8000313403040000074400d005aa0340301001031318041415a07540441070079650040304040105011001c20b002c86400c201d41c2c3c400030880c01714842c8491070b4000743c00034000071515600b00066604228020b20719800c2084084c0d24a040c02100d95070481814020028084d0a1007140b0990a00b060303c540300d40c2100c0c001200300001842c40c1c3d402d459003841a02c003204140344210511607001c83d1050301d69120710a00749130440a803408600e0038401c021200845840f03445003050000d080c03000b8070039901c4040a032a040b2450780c00455861500e400c04881501031035100311014461402080d0f40e040749280400708440c2d1944880c2d4001982c00c0800940d41010301d4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 887528821 1250 887527571 887527573
    0x92004090207110d0b06180f0a0b0a0b0d02030f180d050310120506060301110a0c02060f0d06181401150f140c07030b0604051b130e04150b030f 63
    0x21040c00103044560042c12210700c0f400040080c40a0322000c41c42e0580703400c000343d905044c6801008454141120300c024194184240703403e00345070108221844403c05450031140750f60301c007820440c5881e80801200500b40501d00240c4640c07010000d01c01030b520480300c1c8071180340f010021511000901c00651a04405100904980302e03815034203c4054000601c075402215203100d0000f1203d070724080007042103015038003612051034490141401e640d144100040c3d940c2081106241c419400303403101c41840da04031009580c0f241001c41c100c0050080d00741a070f00b01d030324000c0000307261020340c01c80c0504c10300c3c0d16200b0700001c1040300306d00c0e00c2803038244201103074030f0300c2c800b0b4602c5a24822620344141d20b0650a00c00c299001c000030502c8150020780c02d00c6455404618248180040d001c1d1180d07012004583c01d110a180c002007101d4013101010071000c1142002c0345501591240140c000054001400f0890640c600740c103002c08482c40074009044403d00e8140140c426040c04101c040c5e01c581104 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 887530071 1250 887528821 887528827
    0xf11061b0c0402120f04030509090a0501090e0601030209010501230301080303070210060602030d05090a0c081b040605060a113306040207030e190b030408040317120103062705070920 80
    0xb519007170445005200320200101000b11944c181d0307800c1415400340c840803500081d25810525400211076021045e0b06040d40800c00400040c2c0e11850150305507030b0286484403001603041d0250481086007035903001c15510102c004510035400001542c801c4d05960b00b21886030190910701c40454410740a45401608100040301516500d03402081d0444411310803503600b202c003601e0701700c641002ea82140c010703030708801c002d2059000b40c15101c0045810443c0c041214074039240c000b40e014803420f400071081c0a80000c40003a0104148144008465200c0c3d044401e000310008680140d100f00c0c0c150a4a460000049112400d01c0d2003546d1103140e1686071005068201c0e02044141c0d42d1002c1403034001c8101d92000302c0c4d40c50f00c0401450155100d0415280c9844c25840c003889020708844441c41600c500b4420115220110707001d1a0440341c020000007922190b8803404681c0800c4040e4072050340036000c40b0b810802400090100c12112400d100300414403004a180525103014013009130612428 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 887531321 1250 887530071 887530081
    0x12150a06140a1b0f0308061206040b06060424090614031f1206020306030601061106220206040b0c010605010e1011031b061009090b040f11061b0c040212 67
    0x75401420503014500b000110000642c0c6080a85140f500701110a0321503910843c0c00c040d004040c042e082007003216803003641c1010031885561103030014009040e1403c2200455915214202140d01415145140a25850800a030b09401c0c0015807034100c0000c8810303400162082c0324104455410190140d01459501ca0782004e050b0111550305980800910b44030008500c2c1c003001c8080007071441604c0250700e13072801c11704241c00d003d016888501848109402030301030403000b090456200d0f0004800c1000014460420041380c405020000d401480024011800e031035040060a04441ca000c028000280c440d80112080c43c101e030161600013100441241045000c0d20030701d00040d058100700c0b41040c11000101c038095181806040590700b111060183d8801c80109101c007808410f0000e01030b84166a030f0f604096940244041c151103482c2014404000c0d41c1100b00c00000e1000304901c0d12010040d4a1000c1c0a1595442c002c03d40b05003001103070507040c01d0094410000014883d0000c070341c0c070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 887532571 1250 887531321 887531357
    0xc0907050a0908100b120606010f0503041a0403080a1d0303010b180406091b080411060f28030b010207031a09030c0a03030c08011e090c0c060212150a06 67
    0x51030304a0a11120306008103e200301080100c0388549010004594030b0006018004501c4145003402d820707030070100821810380d810110701e148a403c186031241d07891b5168104070b0181e00e4000000c101440500041c0810326a2105605000d03001207031042010070341d845540000c40000080c0225113030003c1c401089001d581d01c0181c1104d0300d1409071045116101c400141c1110450742080302901da039102544000d21401681c2d004582c15400d00c910030341400e45600a070482901003d41c4603600011342e155060072550284d5100224820b0322a442151080080841c0b02440d410f104c000b902d40040101d10350700c000303999012243c00001d801d52806102114011600f0020040400e51004000c0001000d01c01c00c10340085034000d0390001004820310b00001c240d18010f9205101107130900c80c0182c01c50350000000405c44806050010300ba504020301660706a01d10807026006600c0071400c1c408428644490724841c25240c0c894464034403001c41000103c1d4010b005000009000c203184d0809501 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 887533821 1250 887532571 887532577
    0x304020108061c02031c1404060e0d020a0510111903050f280f081b0a030b15070503090a06030903120c0519032408030a1202090d0f0b090c090705 64
    0x7400e4030f24500b860480e0300840d1902c4604a60305400404070800d04101d560300010000c40315201c454450715041c64040300808007880600018030441c0c50b00940341c2150f82d0042c04030000d102c02b0340402002c01500001030314410b0580300c15070352030150095404052240e020a01d400c180e0588a060034010320400c500499003152841e00440321641c58400c14007a0122480052501103175650001d0300703103010700100343d0407010346048421003244002100600d55141070390000710031490006054803113000010000107950807001303103c40c00012070000b800f0b404030080041c00000e5070f503850303429a0f40c8022800c50740205800b9000543c0700030014080609900300e00161096450158108000d41d01c0118914000711400c0c80425910402c2080c011480b00810903642c241342401001103151051850f220b200d030380e0b030030010800b0840c2500c80c41030603541560b1101e1030103040b090701ca0040d8540520700c112010000d030303101c00c2101c001500f40600003542008030680a0140c03511501c4209061303c55030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 887535071 1250 887533821 887533849
    0x703030207021309051b030105130204152301080f0403080f100b0a050403060506030d090b1c061d0f0c04230306090c0f180112080705030c10050a02030402010806 71
    0xc0d9140c9440f4120b8458065004224004d001604a100c000c45480f45540b40c2600840e00a074103004c10800350f000c000b010740f020303190191404580c59404110000100c9515000700000d40040e44041046031004011860495401c0e281e00b1071548402d400b614540b00200c0703008001a02c0d0380000b40542c1c55070b1604e140c20031143d00f02d41c070103591203048903681600440d15100c0007450204040003840000e028040d0000d005a014018024902c0700007002c484103801030314042d40300080c03040c602d0780c4415520901030031500000c1058607200d54203019181141c42204448040c018042203060040b034018078040c0e1400c00b189490a46400d03070120045038400310311049410100300c007000d039490500000d8842d9031f0140203020340075800c5003007200b401c8048025038040c05440d040c55280300107005010b41034500024a005031160790345081c0442e0300ca03910005003903020106010495030000a0095200808028240020b643d40d00ea0716080f400304680282c0000c003802c0124440d4107118038500418 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 887536321 1250 887535071 887535079
    0x6090411030a0605070e18040b06061803030c0a0b0609100e060604030f06090203061509060f0a0f060f090b09100c0c0503012a050406090b0c101b1d06070303020702 72
    0x440b910f454030422180e08541e21707008103603040304200c100d02d0080148524082c1c1600c1c2400c0300d05094656090810000340020301600380050400603015122061041807903009040b290786184141000f5210340c0038441c111a14071011000c14101e242c640140c0e032040400384104103c1502d4242c40314045600904043c3c4c000300104000f1011a11410108903094021540803034043d210340f0516103001402000b5048120f2041c19480b1103a5a480f242600b2040c11078040d207040900c90001a100c82c2164454a111000c8170310025416421211000000301140ca0300007019a8910301c0c00c0c4188a0000016808500b00d22030340109030249455021507406516181d00f2251240c01007421210a00c1d00369000c030900105601c18075400d44462140038034a4604030341000e281000150240c0d406008408120201007030608107088100700c80071b2003c0e4071a0042c402c8101140c014503010401c000f5150018444100700840301f445082d02d01d008071409440c1520704001f03502c088000390042102280c0c8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 887537571 1250 887536321 887536333
    0x30c030609061706090c0616140118120216031b033302071109040f060219170106052520011d0604090b010c060606020d12050609041103 60
    0x419015102d504007902c580c2403000b409000c0c600840381307019002092008250310580c00802645c4030442034a94254480d0100e00c03c207401403609008800a40040300f50942c82c00313a504101448403104000411b01920b031100152401d00d608a032101244240c64024048000040000407544518040d0301201da003140012161696075841d8100c40545100d100c43c643c003000c1004548050301c048040f06200b58003186007042c5a0b076581406951305450700d200c0d003c040c00040c180b0091628205440380d000c00115583d850f1400302200b18541c03071400b0b000081c2503110684600390740030301c110306868140e2649400d0040769000158140621450307583c4035640c203081c0500050809074a013215647c005001c00f04400f5a0b0b0005010a205199105601e401410309204503114001214280c1e165114046403141c2c001340140c88000403403e000300498500b07200040e10303a42c045074072010328007256200c689150b00c10601d2000d0340c005a42580c0e000f04008003180c0092000c0b8102044088080e0603190 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 887538821 1250 887537571 887537579
    0x20d020d0f0f03050c0c0616031b240e03030403120e070e0103141615030207061b0e01021c020c06130b12010609060306030503160c182910030c0306 65
    0x60480c01c000000c401241c004111160101700611885030050310079038003e8101321403400c0c065041409000c0190a100c030401a02d81da408a9260040c81c16030049010b000002c09402c0214000c0ca0784000b00301400e01c1c240080800c0310011046a0260343c056484000a2800300300c6040280b1108907407440c2031280400020303a0700940d40d25940218001e50000c100d98401d1201c0600301000e6400300e0401100501041c8088042c903030086c464490a4500181c54a03014035201004001011480b881c0c8d1100700d003140c4400340d05c548130314485042070742a074403403e19214020280718811070300c0c0c1025030403100c4502920305000c00640308456083c00b0711030700c1c2c5030f0b0355034080100e80c003c102c41510303882104018007039203810010780f4000700070b186000c0008501d0341d01c0b0700d03459004418600120b45030001502040c00105450340c40604a04080108001305e41c08000b001804904052100c212005d51900c41038006040013070408040904041c00954032907108500400c0042d181c2c0d82490340da042d000c2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 887540071 1250 887538821 887538833
    0x11412010e191406070f030c03020702040905101514040203131b0e010e010e010b0901090e0109151703090607050109061406281202030f191e020d020d0f 67
    0x60000d01500585002c1d19a003410114860541d1080800081c0e20800600920315404404c0d417482c96040d140003d107050071880128043e01c500000a9071060074020910309010000c5200d00e10b81c030310031008121120380d1450003141103a203032041400d140344945060005040c950010b591002c0c002c4c00e00010001c1c1541c0f90040f00301c09481e081c0c81101c2d8200306100c284814591030740901030280008000b5894001c43c078040c17100501811030030380d4000c5804200f0f64050401c032005400650740303081440da12980020010060f01d181e088400c1c412040000b02c01d600c83e00e082c69490001000f452804902c00184035055000030300454403996581c2f40007010480c1841091407200c010403280b082c50070486e040104141e5100081e00802c00c04070a1403800a102d0070f00181200c9051849090000305030000904020840c104d20200d4010100c0340e41d0a00034012554294601c540301652807203c0e06500d55181e109001d00c000c2d00f142480f0700c1d202c05407034414082602640300320801107200005a07111 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 887541321 1250 887540071 887540083
    0x10b04090213050904050a1208090a111206010b0c0706031b0f0c082d0a0c0b1003080f0306040c02120409050406091a09010b0d050c0d0602090613090501050108011412010e 75
    0x2d0310b0b20341004007260200700c4841b060348211242844c0c03049e03d80c14100906a10b4183d0305a00034091203541a122400717466010741e145404424030b00380ca03650740e0b551030001d106034031200030b0380c0e81070042a03004581d140c0648110301c00b41d00408000304640321340450a072210840018264240a4215420800036100708018142d010000c900c082c01c0350040c07509800c111203180e08402081a0030703c20741c92482c4c1d000ba1600000d58001100946c1e40d110781e01100c0c2811000e40000d440e0345000200d80e0340343d41941006500a21040d00d04001d4020f207004126111240700c51301c00c4122100300020442e801d00303034118940280c0500d400103113550060355602e1040c9511000400014a01c41c2042007458086c882c08416030307000e4403100059031099a48640759020740407210f1085440001c2d500921140d83d0690704101070250416070340d0005c248070980800705a20909210600300130003c1003651007603c1d003904940f072801d81301440703506250410610841c003e920600965844229500e243c0c4100f140c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 887542571 1250 887541321 887541323
    0xc11030c06070c03020f0a080a0b18010e0601030203070b040605041a1c1508011112190c02060f16051611091503010e0c100f02010615080708090105010b04090213050904 74
    0xc0003c545245105125901d130f50002c0703140c8580b004038010841d101e800b00f84810301c16070100310180c280ea180f410704000c41e00d150300600c5207903207010804400308500240e0603040e130340200c0032144903640e1000390014500c5031313004e40c0000960520003002103100100d4502090b44021910a00300780d240c103548081c12a4455142245644408001c286001c141401102500c80b00300203106e18012224803010600c01c003081020b00c1d00d90f00d00094540d80c1d13007503030007100300b000c201051085030415003000f581e0f004140c0310007601e8010400843e150048841409400c041551102400d08803101000d007400d0450810694800400c28a0849265502980705108400c1c100d00d136401c415510052500f144c0b400001d4401302c0e44944051070349655400c00d0102044c0440c5002550403411240480c00350081d0382c403422040e48040007404590b07800c030300903601c101134540da80000c0395220759900b403c0e14402e03c10360b11200c904110a01c14800560000c1c203107070409094445d0240d40d902c001c1212201c04480c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 887543821 1250 887542571 887542583
    0x25090306330b04051903020303030702010203040506150109030308040f17130e010b0f090a0803030408300a0e030c060103050a0302010c020d0519141206040605100c11030c0607 77
    0x504080c1c1c0001000c501800000c6a20302859007055290001c07032185025040c4645020082c0d038603603591541c80d2101030750340942a030343c6900306401c010340030350800d4030111100d005450000e1401c4162840c01528042c0503504c00410342d00d50788007907421007030160003a224031148202030f40c08100b40950000d144c007028207001d60344602c2845040800e03400d0b034201c1c060110354680100a11101402503d001c01580780d80c0540d14144040006c444042a500c07850441c040481040305201b140340c090942403080c041c14120341d1022102d022074140303021405240106008020030b02c070a5882d40854880b151140c05c80e864410711001e01890824264802c940f242d00c00d8150504055081c00b030801842c0d543d00080c1203000c890071001e041d0380940d55040440600d210a01801c5130b104400c0c030b400c21900d0080c400d50f02c2c408130340000200902101c4580c02503040c190b00150300c0c1414140c4d01c0b0a0b821580d51031025500c643d17595507000c509000381d69410310508070070341c44564070580280310143c803d01c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 887545071 1250 887543821 887543861
    0xf40030b0709060915031803030510141f0905120c330702010201090602040b0c0609070b0d050402190f3b190218150325090306 56
    0xc9404030a141008012108020a09400700486a04a0144011381e0003400059041d03810100f0106c0c001c16000706040c4048002413000303414950164440c6000324402042c0c5454203071240c159030641076220341c140e070704070b2000c0707001084a04082241d800050700e5032502010103541c580016448090b01207094085800828168501340381810900b5441090240b2890411a40070a00c201c21010311400b040b10440002d50102168800c0d40005000e0798031910840d00c40d0303141c030010340c800d070007010b500c001601c10000803413111313400081d400e021500310703001841ca04440d101d1070381c01a00d000b900c1247c0100200165004408071400820080c2825003200550349241040102c9032140b028000e4034014000c5540a8202117103040c1c5049032158200b0658040e190314044030740300001e01085465844c03012900100040d42e8012034100100d00302e44801d0303d107800c690f0720b08261000703449141240050a00c1c111210801405950f10014903050001e1981d0703507610303400305a90340d0803102310008500c5d03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 887546321 1250 887545071 887545073
    0x603070e0111061501050a02010e01110c0f06060a0506090432010e06102a060605040e15011509170606040e0d0c03030e0304050d06020c0705060f4003 66
    0xb106040c07610141e0302c4000e080600702680b590005400041c13003d810410001100c03920103000350400d055000340c000017000b440c1c84101d0301d40802c0e04400500c000074000ca2040c160600800036034a030065030700402c907000040c078000801c803642d40302443d0103030400d844001c600440e941001410200c0d191070160601c6410810000c80d05441058018902e80420002405020b8641010700d0207515501e050640c110210451071820f00e502014803000c9075415002114100f01c100d420207000c0f0f46080c0d0b818002060350705802911180780981e1205080100001000f40e00c4410140800a0340282014140c09844880c001e000c0d2129001640d521780c8124103105240c00c1621660528101d0480581107040b0225002400080c4100c4050201501d40c001a00c6842d0309204860040c20002e203c0200390b013803482c084010b5003001c1c5820707015005950000a00b418410215588007900c00b421915011400001c482800c00c10005c0e2180012780040400740e0b0407030f0b41c0d0796400b5070703030b410a40040d42c0340343d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 887547571 1250 887546321 887546327
    0x703050303010b0429030f04110909100e010b01080a0b12030a08220809012d0c050c0108040804031b051e0f060901020d03051506130f05040c0f0804110603070e01 71
    0xf03081032074013044401d0400000d1000b040340540343c00143e401f4a080264445081c801d03050041e81585552102c01d07c1c09200c001c04000a003c0f0f03d01441c41c90510200d014010080e00307d501e41041140401d610200182205449910000f041c06005040c030401d850381040c06071640d00221100c40c04500c010081c010442c2c482480c40d0100c030200202c40d4040392680e907580c4441c0c0114903080e818010a4030070f1302902c9180326100c000704151105110701600c10048020240611820291801d006a2030424015441060b2262182c6d401c4443c032481c140c550741e207207034482d8800c1c4207010080589410205107503445e012203000a20b4203150020121500504001d841c04142c0345140c07003540b0401599001da40c020920761440c3c0124240040c1a6442080030403207060040042644000c1c0003501c40815648444d403801a07640540924281c070b83c0b1503061004560401e840200440c500b090b250700500d1189112a038420b12560455901d1a04100880c00580081e10003a02140200340d011186580c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 887548821 1250 887547571 887547599
    0x1202120c130b0a0906180b0a0512100503070b1c020412110d02010e06090303040e0901150b0403080f030603010b030a150b0a0b250b07091a1206120703050303010b04 72
    0x2c040503450f26200d407403030024108024921442007400404640284504d00c04e0061100a0402c4070314540e441c0035501008240e94440740200702c00301d44000104030100c1040c4000002d60f500030f401400b11900745822059950807c0448500c00d00c01131101130078000b09070015200600140721194005c2c0528904120301000000841e4007401010401c400580c0c1e0000004c0d208540c15940e2541c2c17131680f500030a05510039a08450b0390801c40209102c40c401056100c01080f001400300c1401d86901d51518000318880c3d403201909410051000743d00d105020001141c2140d401400014000b84600109081c114000030690b001c5031032540c41044400903002d800700701c4500302d50715204a820b00d01d003942280250301151203040041559600c08106182c150f0390541e402810b031441c0b81c0f80c84c01c3c00604082890180c3c804141030754034004402c40c4401c040c0c800c01802c0030303010b115540d10302c01072011120464000083e41e1042a0300040402d00500c000c1d406020040c80700d0340d481c1d00304034034020141 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 887550071 1250 887548821 887548829
    0xf041d0a05070516061e0213050307080319030b0f031005040b0702070326070209040506091009080d0b190b190203120c030c1926060109061202120c13 66
    0xc40301300841d0040d41100702d910200103504c004005188010400150310380c99170030b118500401d10010f000f40500090303c0c0108200e07042101165800745d02c80d200313541c480c0543c914411101c080c40401d0303404c02e800b0741c000f582c1042010300b40d0060340514100291500e520103906507800c503034400074441032000d481c20282e4081000e0005000c0607203580e9a07444c0e086100040801420426510148c0481d0702d50708035060540c0041104d040d5041c00c0c180305488103c10707919090a0b00c40c84024544c0740c0c03a139000f40e000741e641244805041c80b600b8a91f032406010300c0181c50b9031210004005004550107101d2040241c50055a0f01c0d0b00d03410150103281103e10b405492005652007809840200350604c60403642c45017812126649a032100a05c0740090702404007083c8020009889030081d46a004407040c15404101581030b4000d220084012080c00094036020700042d00f10030b06014035030040340000300c228540c8000514103580c02c00300e8004417406450100b14481c0015003c9000520460004098 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 887551321 1250 887550071 887550077
    0x6041118040b1f03020d06080303090d0806010e06070f0215030c070201030b030a08040b18040c03140709030b06011b060207060e1e0706030e0a050607020c0a09021204080f041d0a0507 80
    0x401c4052500071804980d00c600d540400d900007406d0705003a040d68018100508076502180d49a0030412819074440561440c40000500000001903240d0300c01d800c00d03034028601030404d40c5000081d449801030541e2a51040e83c0142051041c01400b8900e0310081d41b056482d03551440c4c5807036a1784001407d448030a00d41d14801c1e4400d10340100800c01e144201c4089802007041280c1d10007034054922140d0354640d0b21180e00900c1d05a03420300c0c95415411011100000d08101481580c64500941b1040c1c0140000361143c0074500c00190316500903c81c0ca01000400c0a058041540c103a6401040e07078425802100d005480c0c050a0203135030000c020b000c2c40d13800f004010803a000296201c403540c1d82c0c1544529800c0503200c104a02e0103a4060048180668001c0c01f500c1da0351500120103956803a02e00c03843c41c0100c0000c280000d60035001d20940390143c4940030103006649880d218000c041c0c001d81d4110310103190801c00010310703070030301280200740040b070205046041c600904c2c0c00c1d04448004180c2418 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 887552571 1250 887551321 887551339
    0xd09091a03102414061e130e07020d0c0204050a020d181406041a071e020c03060c0c070311060909040606062a0b0406110d0f0e030a0c0b06041118040b 66
    0x13411401e40c0d10040d10b02015142291110310002d001039520b0140400c0440c9140001407840c1704001069084080e035912403082d20381c0b610303080700072030313440640c0e0500c81d000841030150301005292a4202c40d4124103940c0002d0b0410604012410443c3d0000202203d005070090b09002045103c103003085054648101609051601e62240301c52460786660583e1596007500010b006940a1038600d0004020380c985000d071509640303006950b0726021804140f00c1c1c822074002414080715001100c0e0342c0030340354001d802441d20755600c04c0301202002c40155440181030080041c140c9404140a10650141c600070850502d040c038040c00751000c0070b000c8008030420010780840520740305a2040519441444200541d8a03810600c00800c55005a64840a0000b540b041500300035003120008010461081006903210007559940744107854420011a0884c000d04e0b02054505040035840750019002142e50880c01000072810742c0811100a11103046a12030f41850410b40b041c5c0d034422401b130b640809 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 887553821 1250 887552571 887552579
    0x40e090c090a1512060903230a110a1703040b0106180501050703140a020f0f07031112010b0d0c060806040c090510020c0d0515090d09091a031024 64
    0xe2100700180504621500c8414104040d030714a031030f420041082071002c0046902528002001c0c115119090700021086007103c102c1003901303450b2201004000d64a07611302030800c2c009441c1c0c00d0761024246854000d00d0304840c0421401084d070070b103042859280d180c3d240790519107080e8428041e0015010410b418001c000c448103c040800161a000d00300781740c40e0401440d0807079261680c0011034255180118261441a030005a41c102000700d0405840d140050301202581d9039403103110241203040d009895448a00740540381c407a40c2084400041060109007000c504600030b01d00c800c503084227441104202042d070000e01507400405c01c88003171043c84258036008100d581140079462240b80b070381c0d41151595000f00641001140b02801000d03e15a003414500d44500030b51808800001207800020b41100020030340f085042c00980340c6010303250411040340003c0c0503007061076030071200e20390003814070341d804105070303000054103000124102403200020524032207850600d001135070710090244 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 887555071 1250 887553821 887553829
    0x1005010303050d020702131b0909050f0604110408120901140a021b060903150f060a1208070f0b090f0714010203030105300a0c05010c0809010c0602040911040e090c 72
    0x6030f60f046850001580381c0750030740000f030301c14940c09040d603031280d2130214903e05d030a1001c00011310b022031940b19850014ae4403035082d4180c2c0ca089801c150326641c00c1000480398501584442d840d10b0300b180069007041d0711404d2640c035010603034805001444001c58208815070740162001800007c1110300c1d4203150520002a5880c40360808400001d40203803a02c40c40d68032183e090340e8601d4001001c44032880b0320030300c00c1c0490710015180c0b41c051441d0000090514100b0003010f500306d80c02c000c03031040a0708003038036000d10725009041c00703c5500e9500a070384800319072408400343c00340301040d0240c031069200518a40c40c100680e80111000c891101c1210b036160380200039641101c00036038a00a22000042d5120380d49011b80c110b03119100d40c0b0144205101a0000e078211405109a400078041501d074001500c126081600090910904128070b00c49940b003440791001c3ca620824000d0308064449000d2400ea402c0c4a00481c4402c5012904012100c45821825007202002d0b000d01594001c1c02c000c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 887556321 1250 887555071 887555077
    0x2060d1a0a061d01050d060605032d0f0408070605011e05120709020906070f0b1e060607020d030201060f060c051b0102030301050d05191104140c0a0e0d02060714100501030305 77
    0x1c004108a8100c00c3c81e180c1d008908640340c0b80384121040003029210000a4074a400c00c0c7c0d41c43c3e6004500c2d400042d14000601c05561852020075410b0030aa9503085e9a0b82e4517110083c400c8446200c2400954009006d60044c58003a02d41c0c2821160703598034241d182c214a1200b54480307442110256503d1552400100764034041d94090344025a1312a0700401042440c440c6003c01860b8001841c56a0140620800c103180038901080e507030b00c89400309620051442c0d0094503842e900440c1000048018074110701480241842400007040d41a5903e0b816104e03504554014000f042d405034407001002014050300034110b11071102d61641c0d440c84c0300001d6580c08140209402a0708200201080c08402c03c1070300d0b206150340e24002030002c0e0610b80030ba01040c419481d0360045040040ea10030382440d40d803c052240740006403d0742441c00d2410201c581200d001c1401d604408146130890140c0c031748000030400300c0e02030b8070310018540345084a54908400e0198106000d46403600600008ad404012 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 887557571 1250 887556321 887556347
    0x50601120b1c021f0f121104140f030601090c0e060315010e03120a0f11032b230f0601080405060103060f1404110102011a0a030f0f02060d1a0a06 64
    0x20a0210002c03880441c84001c886803410765140b60451880113a240d00c6400ca0250001a54400080e08003409002082d1104181c210314400d006100c140445090306598107400d4130010004030b58524030601090820000b031f04100c03115510b40402c0756140346c00146c100c5264106507412031440c504002c00d0010701c1d051000b40740c10014250034000003650b0030482c2e40e030071a0320035075081e58600d90b246018120707024004150f0701180d1640060840048040161810f0340c06007070240c0e400c2220800065510405d960001a2455680d2804615207021004007640008408844401410402d60348600704000030425810042985c040000142d030215049044aa21000c0803038210310015141010307044a041003801c500e584800c00083c00000b40e0003c0e14071000ba00200040c8044403001c14400c0f043d404001e811415890007000003488040071400d44500404540007084d40300d0340050003030342c0f294040054103520382010700c054590748030300c01d0600281100c54000543c60f040c809000101c801d04 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 887558821 1250 887557571 887557609
    0x712091205060f0402010c0203250e24060d0f0207060f091a0405100e031b0106081e15010e010906060507030f0f1806020d08010801151205100906050601120b 69
    0x3241c1164040c0e200d400f00c05900800342c40f02d1088884203007951441d2034107aa41c0142414800060369000460704034000d03310200e040840f001c6030707404ea204440301d881e83c49802c040100300e2903005607428807550b20b0210080e000980c0d965400d00780700382551003c01c1c0c3d20b18403d1034130002c00c0001d52203c0d03910030f2001d1001154602607440d800e0403400c0503400b11031182814100000d021402a021006050312005070100034080141076402d81d00b00c070070501802010f036004488480400140ba00403003000d0601c401260400b60074070310551038500d001c0c0e00c200c5040c4420f5005200d001401c1c041c01001c6c040525040c4c0c1410b00f00d4a000f480030f40222480000d00c07040141d020303c40303449080d142c1c00028103540100c400303a9440000039035545104008100266490001103980300060191074105042a904048113508004030310382e10650360300c01110288a407503514402e020b024000c665905009210005039882e00134005000d1480424000281ca031920050403010ba482c3c610100446007855 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 887560071 1250 887558821 887558851
    0x31409030a0816090b040b041d09340e072a060e030d0e0d02010c090503030a0503250f45080f01020c011103040803040b1902071209120506 61
    0x102c141d542c2c0309a60403205e40050000f402003542e212940c01802120080c105d000c04291107407509440b80401510345894941080320800c0b400d4000b00d0104040c031030705090034a40701211060584100c60719521004512040604001b00c02e03400c0802c4400c6d0041007a40d40008441811014402c444041c00c0205200c4e80c030f100b06c4068000c200196010b80d804d0000411040140c000f08030b5031043c10b40030700c0006600740291521154403c2e007c1c078085880c007800450510308480130655507601300825a02d132865170500b2075214100c103c105003aa014268603900e0710008460380c010007481003c019101d02d2202c0705050405055038094024010585a41e001b1a00d100c3d201a006152b0960b40301450910a0130b9a205402806500402d0300e40c032414000c011400e540403508500303000440b00a00403100c18800580130550041c0354552200d43c004286402030701c001c445004070f800c2850140c070441d40c0c0b41100824dc070f0300f014541c000342c90403c0c480c40010000d0350710789a40d17150081c05501503502c40 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 887561321 1250 887560071 887560111
    0x910050118030227090f0709091e030905010f050a08130501020906130e071b080307090506031f0b030c040909050c0604172416020a0602030106031409030a08 69
    0x1da446030051030b401081440d60910707010041c040700c1e51910101e5a030300140030100341013410014080302d81400050150824074580b40d005002014021401e8491064540d03041d100304801e5603e00c0f007014403d44944003951b04081c00149200602e600c09000d00004100600303200e40c1203c05039600898220100300003195511707203140a4081c1c001390070b4001360301245120403003901307107050015100750041c864551358403050b0488440c0e07580d516403544040c0c2480711034040b84440d0f004607885200703400d2081074503550b00041001c0d0707030044521005104031400c15100400144805000408042d01c00034154100030f445c10b50a44240c4c0300e0030146039a920a0801002024845540d918000814841c2c503a691012146030039400038a0b030980e640a1000c108000d05d9031001c05010b000041090100c032a030368008811840b2001e2110708081d4810382c481c003000181c0600056010b403d19603004101e01c00c403414910005480a8025220b0f60801d0042800d016072000380d20b58040030254041c3c0003c1c281c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 887562571 1250 887561321 887561357
    0x303080610111c11060402010906081308030106121d031c060906081609140105040f0905161719110d0f06050106120b1e0103140915010509100501 64
    0xb00280c42d03030041c0606a40d04415202031501501e8140d0291202d181e9a078100f030003103440d11003c403402070218100360070070300609104510203070740a40c00c4004805550790b561911442034000343c1c00600012484003204e00d20a60034040c0c5070200402c00707402400444100c9c0c90540324020882602071805820f540184011150b42105000b0000184100013035a03d9080c450f440700d811001c4a04c0c160f160400006089086200d8610041d964007400522a420306042101800e0070f00a0700103426100e1a0700d0703000c50001d01a07051045000c0000c80b100b14540b0003910514601003401b1507058000c0300c0c80101540261029540031540609030700c00760001d52001031080700ca500b80242461403480200010003049502c0681640c41d90f44842c80341c298032406400c1a20485010603404c0501c0c4281e0070900020380c1122402130105050109586842060007070944c54120b40c5000203903c400d10710400e21f0120200d5a000d46019031b00d4004600d010850808413a520784521410000b6013902c440764420 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 887563821 1250 887562571 887562587
    0x140607020a06050c15011d091c0e01050d29010512060906010215010909050c060a05070308091207050312180706270b03150111150a0207060207051005060a0303080610 73
    0xf66040c01660607503125908140c42500d010240d64a00c0c80280104e0400740c0e000400c9e13000000800c2480070304808403032013250407407001080641401418030045003030710424080d035242c0c4600c9121814050007074224080c00191400c0d50b048c10b1080800c010070740542520806940407006a034018400c0d2503500040303140540010749055101e00500003c02e251115801420095009501710340101109404001551103484048000310700100401e0300000c0c0031300c02c0194464400030640d003203002203590548660703002907012070f032940000600500d034000c1c00209640080c1180c3c1106640e800100e407041d0b031409940101814480140c2c42d20f00403070380074880b110056100d41109490316594800290164005130751001c070400d4030001441d601d500c1080c006607910391060080c1000b992413000010314070b01c0a01520001c0b9001c01c001404143c49000816105200b10001c2000c03441c03441080313003121005088548950072403041017020030b5021058030781104044907045ca60041cad510301507039068 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 887565071 1250 887563821 887563843
    0x3071a10091104090b130c050a0f020d050403030c030311030901020418060e0103082d0702030c150307120b1e0901060e09040201030c030b131b02030f0a180902040f140607020a06050c 80
    0x182007e2650015541c0403001d000344400a441b4698074151641003640c40f9880c00344a0740c0050024082000801d00c00d2001c401118024140010752043c16110b1156a5208031240c0c00720b41e40000d402c0000c51240d102c5842c6106030390b942041007904008200701070007410310019040281c0406d040724105400131445a4007901040138441c0f24002c010780b8042500420401d9110b03000d4445240d4403420700400d41c04100e0503009003186544c5c0c2d10041900c910204604003441d2946d20b00c900b1045132505002e00f081400203491f40038a030b0070400200106143c05070095410403d10440d5900c0b1525022002604282e090801143c00414074070110010082a01010340c003074038550041d440b2540b9a8401034120350704d0400032100011041382641d403031007501400301200c0000c01c540c00d1168440c1182c903440b60555400300002641e1800b49105981040c1c10900071340503c01c2003004030240440a240003510155416400c2001c184c0014420222511a10f001d106000600c00301040091011003580 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 887566321 1250 887565071 887565109
    0x90a08010207150f05091e16030c080601080d050405090a090204180c080d05070b06010507050f0f010f0b01080f0c0c0109110f010219080c03071a10091104090b 70
    0x600307014181481c00c4050030900503c69407904440c081140740354003c851260071884014241c10045130004070840300d04180000d0b843c00f5214034841071034503800d100d8000310b02900e00004003501701071920342071400690010f0040d5000312201101d00350414180c41c121201200c0350525076650780004030203003000c0c5200951140c505248441800d0b4007080e942d1007180600303442d42c2482d0303d840d030700342c0d0340c0c882000004081481404103000180125450542c055010300d011414121f143c0e944524140e4200c00c213030402e80000c0b0780320000000912540c954980010028000311a0202c0068100640a032440030f00f04030010001e03002590fa1022140101d0341c4c03c00030445c0c00395a060080d002c4040d41e4009100300c50b24000c4591641c4005031640310107404c070003071085410482e81c0744202a8812209502e00b80410300907039000c039000c104060341d544919603072142c03985440314032141901d003139400144249140c500e10354145403d200c02c6c0c8080e20081c540c00600f00701d1840001c1c007066180c40b144200303 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 887567571 1250 887566321 887566327
    0xb07030b1011070f150306051009030f02061b06010303020c060909150109080322051816020f06070e18040b18070902071a0a0603120509040f060b04150311030c090a080102 75
    0x4112030006500c640317804581d001c20070640c17250100306403400030481074000102408001c0c030108211f12003550b481807000300306500d0300d0250b042440f07458990321082c036080c0e04030000410500d80c041c040c5040550040b1200352918405100043c04100d01406004200c0003481c9034116690084003080040e00751070302201d03202d200d1140c10300380c818003110699040000180d40090782e82403a2a040700c0074000a0b1110348141e40d0f41402c029084c5820394850114860f52000c0079503000306100c014000c468075a14041426904424042d004ad90200c029801540312800c02c00460a5030611a0300b040801d290707070f0503805070102c20074508421034001d100c22501c001441020005900c134041190304800d542000f640e5030383d200718000c448580c40040c25003507014078140f01f5503220390000c044c85180208006a40040911301004942041d004034034002d8000505100c48540c842c100c111081217890305000d0045002e80b00c2c01540409401007400340300c0481d00b181c441d51244442c4010301620342c002c41d2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 887568821 1250 887567571 887567579
    0x9040503030a0b0307051f090b040b030711060906040b07170a05010609051503040803060d060c030c08220b060a08060a0603170316120b0612040b07030b1011070f 71
    0x144075031066030541100ca2034428118070608000c0b844000319007004007071103105c0801e00f20f045038110001981e0300402943c0d89000c1450f800050140010b0714010800d540c0301d190040018180d8000c82809103401c0c0c0c050030030084110800940c0c190702c1070380b0010380001600c0340070341910300c40000404050095041400c1010071801644501d040350740320b990301c1270200e07030394000c1c0030803940b81c40906401301d4010030000d0042000c1c2d100035500b044000d05140c0701e42c040d07611884111010100d0490000e5194003450031242c2e0700400d05500445234110305180010103d2040b05041c040c0c05e40204901d00000000e600c0b60303110000407004004c0442501c10a2070052030100040c11a404101c82e4461020201c000c4030701400266481075040c03884801c1c00d0041c1d6042911841c103100b2400301c4c0c1d01d45582c0c5851845e00d03080060700b000c2e0310742c5409100c98101403404107400e000041403507080519141010b405076a0304189903103140c03881d01342803015051400c85242020b515820004040083d600002 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 887570071 1250 887568821 887568823
    0xa0b060913020604031b180f050106050c0304060e03010b030f0d02160303050412060b030d17130b0412170705070227010b0f070b04080c0609060402090f04020d02090405 74
    0x910540003140d101a456603010598612103422000183d00b0500903c001e100240344652090802e0301c3c980d4020304e00980d9000340100645642100400300ca0f00c841c40a03044050300e0080501501c41c03428403d003441821502300b41e8900452017200208140d0541c000401e40b001e500000c110480074069030144101c80d1481641d83d90314260410051040341114514103543c0092001681d60503901c6514042c41c001ca1a229444a01d10a844155640c18420207943c6c0400c40d0806521058a42c0a4807609468518034000c90040084403c0641d04241c01c0001d0321103482d086e40568404d00b07403900d03000e80c50411140c034050b01600f44a080c0c80c103004d00100b9904003000e0030801c0d00c2281d214400c46922080508046805030754030180300c4240c0018400241554054044082400c1000703090450b5074440c2802d5040642c1d082d00d420f40e0001e40424492424040355a002e243c03c1c00600381410325031702243c0c0780c41004100c10807412722070021901b15681d080701003076a950010030b84d4005040c241049 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 887571321 1250 887570071 887570093
    0x3060b12061e01050901030518100506010212070c0b0a11070605120c180f0301111308120a0c0b060f040515040e072d051003020c0712200109080a 64
    0xd940309561807a080160260ba10141a918081c103a541c43e0600c0c0c115030041d0003030580a801168415042107816615040410a045401301031071408600e9042040000e4205442c014014031100c03001c000071001309141d08450750407125403003d0710b542c41c1c0000340100c0700c001c001c426a80c0307103015101c000a426540200074052031204001040050b407140380d42d405241c81280007481001282400009080c5464850310f40e902c00e01600101c0e8800501295101950290105280030070401000b03222201c0c040000101e0740d00c40101c281d00c0c0c0000100d014081941c1c50900512400c81000040c040392510040101c40c0c8001400a200c07d040c020b40d507000c0e039050050703100d00035864030020f15242c100000d010821500800000c0f00c6040207101c00c03060b18800102005012050040001155181d240c01034194030403a07900182c549a0314608941020340c82c0d8003030301c084041c0c00d00000101d10036421a01c1c0e103070a1100042c0b26201c00b1070050300e140042d640541980d01405d00ca02040c04010080 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 887572571 1250 887571321 887571331
    0x3021210060f050f040c030e070e0f070906050f0f0405090901021e040b1e09032d0319120f060f081204060507030f02070f1d0f06130b0103060b12 64
    0x307000039510350107100055451886650740c00030480a4003c0c05091603400081c44000030310b004103201840100031444c144c2594803610070901203004000421404034180c941020326071408081251911800626500039443c403012103000000d50901c105036240100d40003840043c0450750079141031060075000750414014400245601042014145101760031a0291141d5000142c209112070007465144c0a0204981d841e0310400c218041c40350741d00b00305c00051804400d106602755140c02c403a903c05c80d018a00840c250394000d1114000d1100c40d22903901c40751006181007002529110b41c4800500501c400720300762680303080340c042402c00140c40000140c0e00c00d0348c21101e8201010904000c07e1186104501c00a041400001c0002e0f1003440350205c92402071048405082d2680510f14500d0b8680d4030071301c0b005900c40c2c0c20302012030002004540c0f00700c0c1148184400d180110124100c4510200d02c8541e02d543c5440021150303009510003409480500c0542380c03a2842d0400c074040190013512 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 887573821 1250 887572571 887572603
    0x1403060a18240f0609150305030a12091403071b05010801050105070503070b0702100b1806010503060312030f1801150b0c070e01090e010b101b0303090813030210050c0303010e10030212 81
    0x1c041026001c06c880102201e40c008015840d04d000f895007120b800159045044815440b030f5400c00108100c0c1d2414a50748104002955403012640341218106200a44104a22282c0300c1c0c10041a0303080920700d41100d000b820102c1d5078640030b240c860300714455008001e10241d40d410902141039400520044810041001041104001c07010401c0400300000d006003000c007510005070095115101a5400803006070031102000840d00d068051600100e501c0710181e28003200f001003442c1d070103c2503660380320007100070000100c0101c000354240300180100441803000140d807602d101c1040000034024901d5400030203c0356100e6460b000070b020352001159540d82015240e411516090b502810703600e465450fa5290700c4880d044a824146d04641b041d41030640c4e491400010840550003083c00c500c4091500079a03e0442c41003240305001d07044001d04028003031201c00a07000d40002242d0641e03511000c19002c039500c0351602000760140b41c0000f074100c00800c81c0d100b120080042e0341d0b509440c1c844 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 887575071 1250 887573821 887573831
    0x9020d0f030f050f090409030203042103232b0606020715020d0207170a0605010306091a0c1b07120309030c0e071202071b1403060a18240f0609 63
    0xb41140c0c940586500c80749180800c1100760002e10b004e602c0444c3c4540310340152070078155605a140c06151050038100b41c402030b6805c100040503070280701080c035000c091400e100303441c040051890150051044203111700f50480c2c0170017040795001c9001c59100b41ca501007400b1141c8c6a500081d2034098070710614101d40d01c080c0c031641d54640003150410021a45030300410b00f06181064204200c0301c134441000940c06042121320103d412130041502844c0200000300340c0201601c0c114205c1c0042491038080c0f0f0300036405010490361040100d0f190710a03400b400d2442e82e0303004410181010100d601c01607644039042c403c0f408141c2c00402020490303000f41c1807429003c1d40c46403500f6644004a864400045001a4000344141c05902070083c2502070b02d0106400740c0d0688034090313000e16603044400c2c40f562181080d411460300300015079000400480600001101000c21041d084042a008000300d007d020b040c4030152182c1d0700c400c1001e03001c01c02800b01c64410138045004210038001c8081150401d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 887576321 1250 887575071 887575097
    0x1051b091917010209190812031e0106080601020f0601063e0c0a090603020a0303050d0e0115080c04150302040902011b0c06080601022b0516150b121f09020d0f03 71
    0x8241b25400300c0d02c0341000740c010b42c6080c00c031500c00d0b40e00081c00d106243d4400c945054140d160548558080c0c045c41d00c4000882c01d0600000e032a0801d403a4901d49564481c0c4c0040c000d141d4010070324541c0d500c1a21240980c1d00347c0111440104004c200300d0300030401c1505032056401c0d80021079030303010003082d00c40c5128141c0303c1200b03100f502c01901003c1c1d001072070510208006442203000f000b40d011460301c00542100308070045801c0d208070b00850f011480c841d103018040c0c000e01303000203040400100c80400006002100e802c19032080c130320000c1d22869a801e40304c415640510b440350741c4102d2942c00d15104190500e45421040d00301d02920002803803a00000b04107500010b90322075400c62450701c5100c040c080800c0003600040c54103140c0c2c01c1000500118103549040c00c54504010b10484855182140403c52841214080d50407a441454006610134241c040030071004191581214400259604100c400c0013030560450300a40041c0d010240300c081c80b00349142c000301c0a1290707803818548851 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 887577571 1250 887576321 887576359
    0x303080603161e12050604140316061d030d05040b061e040b041512060b01050724140f24030d111203160201051b091917010209 56
    0x40701402c850b000102841c00d00080c41401140c1d50550b8010300c00090050300c8100341c180f0304648150480b07059114009100400207080d803031400610910f00211f051511032080d5000c41810058040d0105594054110540034840791365038980b04000d0441c0c3e40c0d90f0b280102c40c002840304a90640380605402d012481c1483c00000c150f00d0039655080ea182071100210070040103014403000c455010380d17203100c4080c14002da0034680c8000d102040602c401c00c4003a0404105680c0c0c0f40705024100035080001d4170015000e054402d400d56282e282c0c2e40d00c60010030782c1c4d40380240800896039401003d50003c01c5030050a001c80d103803169a030482100084010311464050b1021403e03022036241d0800002140d065200da4480d69601000208a8400e0100251500555401921418403d110386a40b5024164090140d9604010404c0046201580c01034510015019000c4182c0c0f10300d5050700c0d4000220002e10070a0050044418400c000c46403c1000c00e0003944400c0b005401130160840111344425 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 887578821 1250 887577571 887577583
    0x13020f0a0903111c080306030a020a0602100609180822030c090b09071b020f060d060e090c011d0f040c0e15130e0c312310020c030111040303080603 65
    0x204d4000c440d41e000b43d50360300e486904014500d90701840b440700c000001d40c0d20946420001d1400360040c101d001c4000d1a07001c1910615009100e500d81019810011010031258558a16403c101129103401005040c030402250507070110f10103296889010090100d41e11a1808031620030804000791845031040c050799072001c990007030118024049070000d9100d5000d1800d1041d100070701d02d03145c0b00c8841c800225076030410036103a14500c2d0f03200001d0194041e600f80c00c4e604045514004c1540c0f00c10540024000c004982c02c051010054400d038480c262101c110800d070180b030042003480308007184400100788000c03400f82184290b104600e6920104500011501c490101007404299141040304440c41c0c05c1000e000c540c01da4030304210354000041c0b8a01700c03060400d09032240c00a2210161400140c084039904200032140c80c29620304401c03150340d85218925241514003841140c0d14500c16800d01c008070101d16059400c1c50068000c0321400d01c000d105403482626022056200d04052540e44c00c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 887580071 1250 887578821 887578849
    0x1c0206070c0222050c070614090d121b0c0b06040207050307020906030304030804030503120708070f0e060c070608010f06020f1f090f0f022d13020f0a090311 69
    0x200280d1518002d410300c3c03003220090314082403209561081014000701100c0e000c64104007125004039205040007a070340a6881c040342641500001c0341000c01d83c0684a00e1702840440621251460040035100b4030b801c10381002404409040e1080c2001ca00900000c4440d082280d400c82200001411441c0900c20b451140f80c00100850900c500c42c2d00f807100400c000781c80035a041c03005010000c002001c607401072001d548950050354036000c15450742511031001605600a001c19142000003450340000300d801031000d0f518144522548a034041081c5100300c981417241e038050301102180060300050f025040741c0712414a01c49607980c80c5000c0b071315070707405038076060f05900920705903c1e500219a0f0754140078401c901d0b00080716a240e1340c418986030842d02d402ca030380c2c0156000d0142075103845802c0310100c0e098211407903140c0980b0102c80310040d0400c040c16115540314545030143c48526410f8034403125409181990740c091200010b0f000310305520003200d010040c810183d04a040004101083ca = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 887581321 1250 887580071 887580077
    0xf0504030806151e0415050c120301030809061e03091b100507030f050c1b0f0111030a110c132408060a0e010e06070504180e03190c141c020607 63
    0x11540c000300d030382e0070700c40e200542001002081c0800b1a611422080e440001d040c180c480320354540b181d6507940e0410311407200c0c2030327040e5001b81300404c04900764038102c4500e20002c0701d980b0342d00c04000c0aa1041031410840e40081e41d04080204105800009004403001c2403188181c428140414100252400507850340d03000682c0c24001200000d0041601d0720107003000707040080c01d2864281143d4940450400102d1103190500301d0803402e03043c10a45060300c2903082c81c2c602980440608165502c0c800d4801403010401e01c0300c048060502c0501062440a030001d0910341c1c03404900381424041c00c01e48403004160382015034002c1e041101e418500045501e00340241c40c16a841c6d5517810000d200b0228210519500c807140500c415806002d024030410380c0c0e8403119182c0d810210210720000c441c04450385440d01d4071107652051a0000250340c0d101d000250041c0b141341c01d080e13041322a2003d00c3d03801416511804d050062401c1e012420300041d900451040c1000180408200c0e520301c429543e52001c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 887582571 1250 887581321 887581327
    0x1a0f0901260708061f06050310030b070c0b040b011a161b0509070306080c030a02010e06030a060506030703020d111809070201020f1204020a080c010801180902040f050403080615 78
    0x280e034000c00600d50940010303800d54030b0880d82c41c2269410480c0850394415601c564001c081e030000726560442c1c014026a1601c80e00303628000340d08481d228140c1c01301504004001000900c40340c8500c40c13081c4155400f40090034181084d2400c8900c060080c002c2e014204801a140000d480707194055441e02561030156004070f04aa4940084c01d8005030b401609035000d1600104603500c5a0301040d0041d409a81d002608505d031890042c1812402e9141c58426040094040c02503a801130345860711940031201180d8945540380808000e0005500c035942051001c0100040c05030543c0c003418144020410500c01c421526642100a1007100a152802060a10101c0c102d003400b030401e60f0312014034000140380c920545032200040e0400303660b90501045c0b0108100860500808000050407031200034030744e65035a42c2c00600700c03800500503040795105030038480d40d2040d025041070790829006041001b0012a160511029000860301a004104000b010805505250403c1c129002d190740078603013 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 887583821 1250 887582571 887582609
    0x203031b03060a0902070b0703050606161707021519090f27051026191509060609140405031b15072006010506030610030e011a0f0901 59
    0x26074101800c0207030004a0304802103040070b003038801005124010304031000c451401000007410382d180100118000c81c42402102141034510468040040c2c1c0b001040f031020440c20b0024015004000d0081d500054620754000140b0a2000604964083c414018250405101d066a451046e48108400481e5084080110200c804925098801c9003803518140341400d0b0b0800042e80c80035280b402a481910008102d100080a05694070b5103c000440c40b01020b0b4001d050703203946601c04820b80041104039400c080185042c48180d24018007501044407042e1400c1c0840107007210b0099a01c030503d407618294078500448401407246510600071483e1050b030360300640740c038913824184198070320500e00785002041d406181c082c842c000c1030b500c017240c003107101c1c02c6d045545000c480070030002e1701b001c401407100380c90740c13011282d1000065900c6898174100d00d4044000303040a03415500300e540717071003224484004140b11100c098070b0100c03520402c0b9038034042080224a03080c813540d403402103d451908 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 887585071 1250 887583821 887583871
    0xa1509051902070f0f1b05010804050a03080405030d0f0f0f150b13120609060c110a171b0f070f050603041403070206040b07120c0f0312020f0c0c0907020303 69
    0x340d2441403120004031074007a52485c81c03441480307a04079000402c5c0c1e8000031003403446000e076000500c000d181030340d070b03038101620384944a103013034000541084500c1c00000c05100c410001c41e00c00641c0c040c01001464003640484004101700e42e20410814240214801e00041c103002e010050440039001804c0c0900e0000342d0351450f40164140301780303807400710400500c41405219952460b8043c01c404a4030242616000048030b0f02e02901204cc0815200d0340440c2000c0014040040c030303400807000c4404c0c000e00c1d089021034090118009400780c00d0342801818442c001c0788490701c0700620130032105403c4c0c0303c694482159600780141e136007102090001a000c1240003c2c01a000060b00040e00c2c80d1030b140ea0040345a03a48130b81c002100c101e000207407440402074604004800c1d01500c2c1b4151040c10130035a602403041c80c40440c041d00300001e4240d56101901e031a0704551103142d0498045030b0399089040c07141d46404190303000c0e500c12009039000810a0b4004422244600c12042c00c640030b044540b4a44 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 887586321 1250 887585071 887585077
    0x6020111091807090b0f03150a0b070303020a1e260c0a0e040b090f010f0b0306090103020f0f27160e100302090a060e0306070f120e150a1509051902 65
    0x1007400c100f4801000030308200c00b0700042c103a42d5540b6440640c1c3c0d242204040c041808d05524281c0200401c140402c001d5800405845e100c942c545000f603075412081d00100d5000e40541ca2129403003500c4a40c28414580205042841c4590203946211051484084042c1c1c44000c070341c0c001036080100010013016104020003640710800400010706c3d6864200864030264045650307040e0520108018001c082c090410a0010000100b031181385240440104a8046041c44000d004020f0010440d9403555011840414404041c6c1502071891070780c1e40484450303400c1e54190141a00304030204151002c40d40d01c410600034030703480300001c0d11040824002038512480300c00c02050b07800d0041c0d160a6035002103480003881e4036510444403042e428200340c1441005040c42e07060000000d203d55890380c22a040b242600200400014100c205040450030142500f00d01c0f514207001804000350001701d80e003c00340d414805c5800c04102034a50890324112541510000203104031601c81c0c0c444c00b1015002 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 887587571 1250 887586321 887586331
    0x60e0402240912150103061d07050d0f060f0c0503150f031b01090e090d030612150f0908041d01060c05030f070c05190501111b0609031c09060201110918 67
    0x712006910390410042d13081d8003c0e0812118107440c0c800f03038680310454085401503d90301e40c000e8141540f41000061800012420081208200c02200400e0240c0c644c840141f0881d280f1090140c940010401891580215500003200c0103a015070070340c6d8140210b544413401c801800078480003105100f04025520302c02445410020001400304400c074a0314513907401040254014100c0c0b2420315009402d4820344d410a40046842803d6080031a008001c00c1c06d018040d10300000e40b900c29010204064407040d040507049101c002000200707030083c0d090103440100e0260303d1149690301e458045650303488031030010300190304c10b201d103012440c82074009203e243e1040c003441030070325940e0700880c04103034010032a800d1204240b03800704002d50704421100745450705000a041d4080010481d1250300100ea25003500a01c8042070503903694404001031544800084e924000e0640b040c0c01c02001945140581e800550034400120709182c41501034a50340c00b4028501c0380c44a26008024007100c0300100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 887588821 1250 887587571 887587573
    0xa090e0c090c09182806030c050d1109041b030c050a0f030b0406230c0705150c1803010f0213080705010516033621020604051003020409060e0402240912 67
    0x8040383e4103171109000c811040080300c1d008030701300b0705d1400c0c100800c0304a540150b01803041c40918400240c81000c1c1e030011520200c90348112500d560412140400041030f01c011411072440e004402d2280440002d011a1300031100ca82c03000c1d869003103103840d0b030b40c4c50321008001e004050b011400080c1181c000302c0d11800d107946081c80854050300c0041400c202603429000ca01c400149400c14031406024842d48505001904081130502083c0c5589620031490380c80da514001401c820070540c1c082d003205600c50004103065443d0410307111000402c155a11454a4920401e440007407a94083d0090782e100030300044180d1848041070300d082d00c4005a00e89040d0000d8000c10501c5c44101d0345104a405000c0919056051207040c00140c0c0321002d00d9043c09008070310070042a00040e0f942900b214292502610204203409900100740c001e030096800c0480054202500400c100d0700c1c1b420014410340c02110108031170704845d64403d071180c1c100c0c226200112002c005441542c14581050105500d2003c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 887589928 1107 887588821 887588851
    0x12010f0312020a1e020a09020a08010807060c02090a18020a03150c0e0303030a09140604050a0614040215181305040209070504060c110a090e0c090c0918 67
    0x18105002032110034600e021511003101b0503009201c003031400d54440c1c40042d40640340c14000d0044251500c240b56001450b40d01c28002942100d4019201a0107525103043d610081c0448149403610f102903401d0704401070301d4501d0348000943c002e09a446094000412010994142101040401c50040306445165030b021048a400104450002030325240b1844d04059100b215041c103413141c0aa03034100403d0101c08200b4032842c62240300c6c00c2220320b41c0128220b074005030a42d00a900309490f000304007c11818903000b40403092129040010004520000880b03452070b0410600800ba194410700085080c415607158204002c3d00b04903081900b0898014042c501c1e02c54064112145255100f4194464072030140c00740048903418014480002c4000b80c0d0340c600f82030001d015003040e1303002490480385d203001e896a4010050110341d003090a0386070700106050191100c9071f240c9100d = true := by decide +kernel

theorem cover : BRFrame.Cov 887410071 887589928 := by
  have h0 := BRFrame.cov_init 887410071
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887410071 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 887410071 ≤ n) (h2 : n < 887589928) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
