-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1306
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:17:17.774042+00:00
-- url     : https://prove2.me/submissions/8c5b53d2-e561-43ba-9a0f-ab95b935bb89

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 234712230 ≤ n < 234892086 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 234713480 1250 234712230 234712241
    0x5070804090b0109050f030d0804170a020a060b0a050306150103020d020c0d03060e06011b060612051507081b031b030c090102011b0818030910090e132102010609 71
    0x55514a0b10354509454943e48000c441010b00001c84500e980308542c0c01c00300703070b544c01c0e10044c02050000540100c1d003440b0440d61007940d0030202c0e1b501c40ea40c03038503d414020b40342d41d80346408682c04c46c18615413000500c3c02e80400380c181d400240007410a640c95a484210022805e0340c001e060690030801c50041507414001045c3c1810040018010305c407400e040202103560b19402043c03100082028880c51303a07031107820b800d24203080141e200240005800e1120090042e940b00c118100030240440c41008030110740c01c5942141c1c00d92141c03643e070700c060003642c254000710f803440380d1007850b04211200b100c10813014541007200c0a00d42d0074008551440802e1a034002d03074a40d0090350004c11094400c0d80d09015011216081c10181e85000b280260b000c0e14041000c0c040c4565410088109010908104150b90000750300034100c4503200c501c2440500010200c0c0114075959060f600081c00c9440d9492003031601a81c048203080c01045410441c24006080b0290f00c4219522414001640030550244 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 234714730 1250 234713480 234713489
    0x605010e0403020d1809110c0604030c031d01020c01030903020c03010903050c01060915090914070f030b0a18032f010c020d0c0c060c1e1109130b04021005070804 71
    0x484803039041900b0082d02d46004500401e040220380500c2c40079031581c1e004508200c542d000c0700480d8106185202d07607080c0c001d5000c0300c5a507124500820090582c0102400041c0c0d000e9181d4000c900c2c00c81c1f410121104c0c0312840f20340542d10084848005521a030b0062901601a01c140c458400361000003e003500c17000c1f00c0a03000101b01003042981100f00f07100d890700030410042d0400512650080f006411380c101c0c03058840c0c440e031300c244480900c5880302078405481d100c0c205982680381c588958006d880380c0c90005a80c040c003100d000641c840c010f80305284655a400840616500e95541d00300d54042800c40c032811200c080c4000084242c45d03000030f2865861100380080344048000c80020310340120303010010208450081502c010540e81c1c008282614000e1404240d4054182000d00c0000c0040c00301d61400c0300c0b40c2200909000080108810748241140d0043d1185c5034588004568101d50310f01a00034541c0201050040c94201064102400070b824440e080070401d484240c01600103510 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 234715980 1250 234714730 234714749
    0x70f030e0102010e01060501080c0c0109050709021801050301051c0203070b0c0307060b1009030f0309170f070b041d1306110c0d171f05060c0d0305060d0b04021c060501 74
    0xc9166070207004010035500407500820446142000007403005034080c0091040e28400103186030807007029040314030342d20303000f404480f105640c1301c108100035400b1300c60740c9140d800c4c07010b14040d60b03600c03480c01c89040322001402c0c01201544110303040394030bda110b54201c7e454400d41d2800201125400d0103400400340c540003440d150807660401d0760941d8000316a081c8144512440c1255039a0051025010740342c22003178a1100c60a10314041e1030016003608895414441482400d100340c00c00280750091805c9601550401595030780600b0450107180140f60381002c14000314207089030301301000d5604c800d221602c00d804d810140c558008a681c51b03c22000c02d500006903408124000700030507001d40840c2d00d41400c2d10301c03001c444545074560140030003282220203501c0440c1803005010010207880000c0030b15580d9425a4101c507505c2891007a4032010906001c0090b9407450140c2c0043d400f43e81200900e05c8035a81d6600700300c2840462961a00485030b0500382c0070104d510743c840c06020342520380 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 234717230 1250 234715980 234715997
    0x150f06031b0e060301063b011517010602030d0f02070803010f08210d091b090c0908010501080d21021603030f0e0a021e0d05011a060a05120705070f03 66
    0x3140a24080b0000d1005019a04001040041d10302840c928001005c0d80d00c1200da0702e9592010000440452250500c0466801d100125004003000344505001c61075407241030080c0d4156003110100c0d4001d10401001d60000d1007014010344490b042011185080040146400700b039507242d4407113030002e0f08460105000301f242480302640401102040e50300551104150703805200080b03013680705030181c81c8181b0b51500c100300100554070460b00110317661059030340c4405032038014102c000c0820311440700014040a40019983c201032084e10b040e95250701c05440c103400d04010a880032040301d103030986004150680700440c0301c05480505900701c4a640d401000c03004508004060302c15210821506da880d04425080c1828000703810144145d05861a400712002422040080701042404582008034808654204841903011020034002041c7c82c600d07462210052001600500e461100812400c00801142c90480c120b226400201ca14040e0301e001c0156071094090401f85204501048048 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 234718480 1250 234717230 234717239
    0x2070e091212011d280b04020a0c02040f0c1704170412020108010e1510020309040e07240f050c0a06110d050708152106040c0806070201020304150f06031b 68
    0x20818480d0040201c0c40c21810117908401ea1100d034030395011044095140042c0e80802e40b40c0000c41700000c000c00454035907106a5003d042c05d0440c0307004078400d41c50400b4507030b0504414400c059000304580e40c0c50000300c10043c40c0d64807401010b03009541c40e01801c112031607007008200082000c1c201c505601e9028001030b200143c01003c060300b0461107115208100000c6920f0b4032a000e00c030302d5045588500703042d04440f00360b0852103480312040e082401c00c03651a014010014040044030398408035a84580d03119901601e41c5c0c04040341c0c440014510840f040c62891141000c3d2070005040025140000c48a81e1524101d88007002c42c00d0782120301185c0c258002d9140d11405a0190341400e0240d01840c1855040c0c00708011014118820007480c0505401d110300c10004080220000d82100d105082c18205090b0f503034900c3c4a010058483c000024042e584107000f524010355001d0b9020700782c003038641c4841014101c440310004c2d40c00d68886000011459015a071420b140ea108000070045061 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 234719730 1250 234718480 234718499
    0x90a0305190606060906050d02071128050907020c0d060b0925090305070b0a02070b0310032a12050c19141c0836040f050702070e09121201 61
    0x196000d0001e01628450800c1b046801208a4081920002c0b0040c0c2e103e4142c680807054050b403904894100d03140880f518070115100200a000001c0001d0060f80b8a58540406c422041c0c12504000140c100c0e260914507401d10140c424080d0384500404036030955040040f540c2000229400c1d00130108404050800200c2c002070b00060030301c40c1c0f03012440d46065031526507071100c0754490900e070407000003a012007052080c06908003812401c01c6599482c1020802c150340a200e07400241e5100085110300c0100b000c44c80b030f40d0700c17081401001888a851a02d4114012100201003e641a00400030ba085d441d6940c42030803000401a0003100429500b06001c0801c1e252101108034011000760102c43c0b4410304d104036109005078440402c0d5901c0300d80d0a1500382072101182a440b03880340c0d1030210740c0003402160190150003810b42e0100101d111259001040d5242030301c50707101680000100f03000400d205224158490380c1001160448403059600c00305039403050100440e52041800103201500e079 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 234720980 1250 234719730 234719741
    0x2a06021801020c01080624160203060705040e04061e0f14101a0306060f04060e090709121106220e18070b09011704050a0204151802090a03051906 64
    0x800380b000b00840301900e80060710302d5802a0120f4490200051205002d885e00c000b50740c0540085502580c031448289450310340b08d11016403c81c400d0080b08002942144108107032401c56032001d03410540c1d0f4540d41c56082c01000a0b450040c00b1200d20100001c2110440c02448094490304000052421204c0d840441a00e0007402001001400c0032003009060b5042101a01010180040365681d849a400048a034402c3c61108040381001180000d895a040300103214014029280040c1607900c6901c02c684c030148a018851820b8004056500400c4e20701d074815040c0c42c00941010700e8850a07410f40307280d8608004c0c1e8000084030800041c02503082d01a000354000406800f0007004600940480e5111081e90282c1e0001c0e500c0440c0d00c00c0c03603030310955020780140d554003240212428142482034440c03021540582c001c0303040408440e80301c2a50546002100c14414505660032031000003800650300449807290320020088010011070ba09110901c0a6010310356000c425000c286480025100b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 234722230 1250 234720980 234721027
    0x10b0706110a0f0e040e0d0804030305011202150d090c09020d0b1203041215050f09010b01020a120c1b0609081917030c0712120605060403080405012a0602 68
    0x10240b02556940c0e410991140e000c00d840d040c9083c8480d012004100203101e07410301c48a0f01e10401000e11080740c0c0110b412400380d8000c0d6818082c903078880ba0002c4402c008043d000b500403d4411890b0281404040038242c03006c8007200100d01d1281e542c0700c00e03c248000c2c0c0c22040d11710780d0020b47c802c482520b6214891034500305540d803203d03440700410540e4403800741c1d21454071988002c546041c200221070700d183c6501801c910040002e81009900f051400340102c0381140c01350310300b244007051036000042c14842640e000410640513081800c00321100b403c481021500280c9501c19641541c800c81040d0307001d80480c0d5110211145008000b43c0303003815080c3e84004000b04946c6040201c0c945005c2000c182c250b5252556907605c584003030780790500c43d2801c00381090002c0d404003040158041d042c1201c008080c14144103c58440341000000c0c07081c2d2200a0024000708003c00c01175000340d4001324081c1c103c1340d1070708042003201121204e04100c540100d48181d80000c82d1007044030013031550726245 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 234723480 1250 234722230 234722261
    0x30f06080105010e0a05060a03060207060203070f0804020a170a0602040305060604200909070507061a1002010c0207140307031205031b0702010804030c11030a11041406060307031a09010b0706 84
    0x3e51401c100020603440181035a20300c0d0b615800024007545819400400a59100c50219592602d0b030500340300a4005071141c100003807944040030412407044111502483e00100048450340c54031880111581c1c8200c180d030400c2c0204030305000414409c0c07010348010740c0600007a0841d8070300a0108000c90b0000b2281880c01842e1210110351840703403409480542105039820415925001410384270ba01401100805203030500c080303240d00301180e9003442e517480010354100d90030f040b908200340d017a00e07200100f00d00180d000100800002c140c20440d5001800c1c00b805544085460307440d40200080000301c0000803450000c284003185d10421110819469140c80c40c0c0e00b0b150440c0e0000301111000b0b04040e0030011059000d400340302051281c0d4003025001001ca03180445e26160007504044851402c1d48514545481040c00c0e644900f1403030310642000300311601d51b03500c0803030540007807060041812001c0c5d00c40001c2c031001e40354040114060420700e8005034459882d0329001d004d03a0340540c2d1142e4078 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 234724730 1250 234723480 234723491
    0x40f09090804060507030203040314100e01050c090f13060303020303090c10050708030a0e1603020910050d12030906020a092c06010c060e030f0a0206010608040c0510020c030607030f060801 83
    0x490070301400d450079142585000e5994040342e00701286580039940000c4d0500710708019450709040c00080f1094105000b000c00d209400c030181a90742282c4003141c0380005030200b040380756a80c0c07a200005d2500c6540090141113082c12104080003107890680003140980d000105101e0030160400416404040441c1d441880140a2100408034050f06030001c2201381d010001c503c2d07100494001c500c0c405901c1d02200e03a26400040c0601c2c0780144d0f444140d02131050100455200d4102c40c515101303443d400707049104c0c0d4440e640d4034901c41d40e1001a4003001c06a40311248400642140000d204424103583c4041445080c0401951f0484883c0001c1c2d00084203580b200c44245469540d043d0701c10400d003094646c1004030b04048000e003081c00e000302054000020204034111100003d0014440b40e0380c00c039000ca070b0f244d240c190352009064a001d042c441580e0f000304400c3c03400c01c40084800302c5500c1910014400d00003c04e15007041584d0807004641c0300d6818aa84041c117104682c01012040b009006 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 234725980 1250 234724730 234724733
    0x11040b130819020303040603025d010e06030f10050402010e010206040c05040f0207020612100509100b0d061203020c01020d05121306090f08090a090209090712180305040f0909 77
    0x162441203100f03400074140c0225100b502410419040e03c02448a402d903040c465200000644091120388c030180962b0030013450b04820f8603800040401031900850140c2d02c00d900f00840c11040c500001d08166041c842c00c1480828003c040c412914020001c01340814142420301c005460b41030320b400c1c41350466102008101c0841c2c5080c2070041140c3c41602c1c00200c3e5401a902c20001c0c4c840d00d00040c0d0007000000da8030a1059485503a14403800104000c40d030300a8940d400c0000080381501c10958280c1000c40c00d100080c07010f00104480d0004aa00181caa5560700f16500c04500c5c1ca0002c1c0c0268100310b00c600340d5960103000e0b000702000e440c07400c2c52a00144a5512220f201d020b00500101e0014220b1101007010310703400030920039044450710104080071300c0c010f15198024420756004405210001032000c90034026111040c174001c1c211902540e404c54225864074188071480c180c81c0d02d804540b0045009038080340c02c3e0724081e03130303840380d8131810090b6000c50610907510401c2481c0c40d0601020 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 234727230 1250 234725980 234725983
    0x610110606090912040803030f060f0303041e0504111804020a0f05300a0e0a020d0803040c0905011202010e030f1e01020c010606030207030201140f01050411040b1308190203 76
    0x20741c00801140c0c480c00588903d44400d00d040d003100a02c00d1019000507000c18500c0b0004040d610480c01e18083e007016984240074001000e0038001c02c940c140d4030900c400c1c000c2017500701c01039440c2004001d1800c0042d40e2540080c003a1030f152803840d801c42d5000034480508000e00d1408900155017901c09501d041140d004c0201811071000d4282c0030071001140024150242c900768000e071038030031845521144401c0328004200201039404034402d525041400d01e0701c10001ca0004c00441d001003c81d43c0b81c2115445072241544024412100c44800300740100b401c2c0386921805010345440c9030003125606c2280300142c5804424140e641c0301358407030b0524010360351700003a01140111500b14040081f2001000d054068003808108180550a050f4041903441d8143e0190030709034029402445203000c0c0765240e2050034020340e590844030345450018007036410250030190b000300c5a1805903142c550f0781c80c03460750307139410400a003d0280d80580342000640003c000110010702c441c1c4c00c804204c400c0e940004e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 234728480 1250 234727230 234727243
    0x8010f0501140f0103020912070e0912031308120a2009060a050c0304030b0103150c0e030a0201050906220f240f030b12070f090b03070311030703080f03061011 70
    0x40c0e20644003c4220000f5911a40543c0d0038220003400c103911000d04085580c0d2550b1007802181400a0305400150001400050701c0640e203411020841c5192264034446502051301e52080ea90324000300884540580d10b00a518441d095039080000c0100d2100b00003981503080130000b00502e4003c0c464400720741d41d40002c444102c0c005080140c0c3c0ca0456031b210500314000c59001800402d2218000000d00c240d111107041c0c814107030308080120407000c1c441a143c91011810454041c0c0c00f084003100103500890003415140d00040009040c01c10000700a890b0000c40384c41c0d102c1c004005001041203a0600d0325402c0641601c005a00f8410001d144110030075400001c014100040c100d400007a06000358041d1a80d414003a080d0740e414078503254041c2c0d0359095842440921401a03000285500941c82155001c09004015100d1503141d40ca403091100d4510b01103540c03500685200000140403500180348182403010520b44070320b0940108018003d21401c206d080c4907a10010808002020a60 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 234729730 1250 234728480 234728519
    0x1170a060611070e15040b0d240501030b0f040201020115080a110a081005040f0c060c05061b04060c1406071e050a0c02130e0f0307020406050609030a170705030a03020408010f0501 79
    0x40681c1e00c85600000e001d0240e8910345500418151040b6051259029903a01c0e2700c1c601d4154240421114000c0c0c2c4222071007440301130058801000410b118103030000140f07400600500c00820b144200d800601113680710303a8048038065012220703450400c4142043c45048100485480c12aa45080f00c0c50f5140d00c0c86142c01000190780702c000808102400c0034200480340c1054084d800b550b11640f0141500721101c00c10740e214850b010008102c4460742400c0f6544400e004400781c02c140ca0a942603c0d070f07000080c000ca4600c40b4440d91640c0f04182007001c0c520400859542060176000c9100740310054078124131820401004011300d10750303e40c00c00402000c841e1305550702c2c0802c0d080c03210b042c00280102103405025005070b07203171820308002c00405480a24001c4030104031069907481000401e100d0704280d290190044d203c0703680480d2400300c54410601c4803062441c64015195242810360f031000d00c1c200c001c65404542406004024492400107146800040001e541840640812244c40e07616 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 234730980 1250 234729730 234729751
    0x130c09150b030a090602070b06090a090314070203070e1312020601050307210c060503060a080a0b0601111207030c060b0306041109070309060203091c0507030e0f01170a060611070e 79
    0x40b807507468044d404450b446820403811900d400c1507150100e011107050f540c075449407540c0700200746424058801c69000c9549602c8800f1201e842e410380c1a915003002c14140d070b26005000d4005851494911400e1140c00c0d0b4030300000d02c8902c01c1ca040b5004c40540f81c0d2480031544a0b400510240c0ca0024400054521560003038401c05084004405807100580d40113242100c042000142140c000001c1d6000d0002101c08405451701c45c4801d5540e10401e4501170700c00d50030700020071007075401064080d000d8210768007500c005510a1125003415480210102c000074403400c981401e0200502c40c05d0115031049001c3c0c070441c02d0a44400801001d0301890611496500001c24040f41c0a03034170400c0d0b290342c022000d40d00c9141020324203850310b00042c06072050308400070300c44d16207034031640884040c140e1640b40c01d00c1405040040c0090000c070000c149040c0400080d511582e01c0030b810b000703881001c031040041001400d009000b400d80700c0ea600100410750003c582404041008145e0b00d034010007104 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 234732230 1250 234730980 234730987
    0x1050d02040f0e06060301180309090b15071505070c050309012f0106030b16090b030405010b060706020304030201150501090e2203080717040213020a120203130c09150b 74
    0x24002c262144111250514002d505029018041002032117003130708800030130280d100041e40140c4400000c034002c000440c0190300340301601040d840389035140c9026012000103800a10010540c3e0300c080400c0c0c0380c2410301028101070120500649602145070728041446443d80c1e511346983e4000c290b21541807241c90300f0220752185450040211800304c4d14100c80031401a900e1550080900380030507528003142100295090035a141c44035640403050707551007006841c1603203030b2181d5000600b0451340d81d500d55105040d56a01c0c40043d01c0c4180c040d01e001662403e12345006030031078240ba10011495036400340200042c1e0f0304821080300311101030082d621565100c00c0458001480d400315000c2c1da150f29410b840505902c40f146520450881d1909a04d22500b110301000581c42102c0007903000155003001880100c994000d23116050042c2007011003900301032000e01c1640c00c21604202b809040c80742e5142403000f001e00ca080181040c00c0e0410685040350b2222141c1560b502a0f8280b100000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 234733480 1250 234732230 234732233
    0x120c3203010f050705120c0405062a060c1b0f0c01030903030b0904031e020712151508010509010c0305060a1205030408030a030209130b030a0b07090902030901020901021c0801050d 79
    0x70341280b0030303402c51440c0070080c1385050200544a9004514140c001910300341c00661300d039001008860030b64100901071070604036090800d00c0380101007116240b8910710b0034406000420200040c034003075290f01c0280754940300d0ba5494800d03144848800d00b1040d0b0700461000800440c0410345528aa00a10b0046003a40807070074240c0c047d200c210762a0790040444001c10040c154045501000780c50050182200b010001104070f0b940c000e940940f84503403802c074040d9400154006501d00070000d9419000ca000c154088403404441c1c00c030f500c9040300340d4541c4100420480c085c443c69021882e0784c1810852130030b0000128241d22014043c0384059098604c030001400800c00a036002000703e4030803079070344040d0050010003a401c40c500190151001c8d0290b4000741c041401080904d0401a00504040703031592103983c411040506001c0034081c1455001c01c0d080100c0c0000c0d8420032910001580da141c08400091074894542405403054030a2804030400c03a500002c202d04642e0103e0303020062180740d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 234734730 1250 234733480 234733483
    0xc010204060f1d0d03052b0f050f04051203040c080d02070e0c04030b011224090203060c0703121509060902031009020306090c0309010f0207110a0f1a070503040f120c3203 75
    0x9000e05000308a00c0302c40101f4682450340000b2810804041c1c1844175407501c895481e1042c0d010740d401003068029608808030b881d0080b0141d940503000305100482c055440b09011f0900500780da9171001604101d00900601001242081c3c10184804110303241c0383c61910f0700f005409040c01816854228505100e00384101b2126203600107100c0200c0000e0300d412000c0e000c000342001714081713019011b8240003c2c005c80e042010f41e56020b425407250501200d000820b0720007466504088900d4206165010400080620410000d001c44040c01a034900b420204c3c482001225030280920b6401001080581d80301c50301d00c6500028480300080c1c8a07103c6000541c0034010508007500e0036803011403900188903080340c0300e82c2244416101d0424058a40010506c10b0996002e64081011900c5058400800f00402030241c540100d098a003000d4031201e2070003e10040742e106001c860320000209060180400807070004081c001d169654200c03054422080a4903041000303c41300c0309010006001c1c7d1030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 234735980 1250 234734730 234734767
    0x90609040213080f030304030813050115060c11030c0a0b0c0c041109101107060c030e040510150e0112050a150e09010f02120c030c0c010204060f1d0d0305 68
    0x40100207648400703401009089011940c4200c800501c038614010124880100803640600c1c0c26a031102519a103803800c580f900701c0c00140c00c0f21030b50b60f0b490008951807080454840584940d80d80c034850500c1c42e00388411646103018982c0d100c0d80045454082c10366403801603004950300d84608544030b81c031441c00c8a003803500240f145a0418101842205107074080300041c01c041e4801c56880402d05c034440781c111040c042e44040300c0c0a0b94010300302804203a004034142d6400e144a8680b000c1c00309030840101c3e059030b400791a400e002c40100c20044c801010802c00f0120504a645000300e49a103403100002c00aa21031298110156941e00100d400030040e07400100050521440e00c2480c1580d41d2a6580561002c555601c4a0352900c417a00803815000d000b1a0402c02904c51140542c4d00d40a070402c4060348007a0140301c1e2704008002600004001b170000d00002e1a840c1c40f0b220495410748005410f4070381440610b510400f540c000000240e50341c07001c6040c40c40d0540b5003030b5221941c60300300c01710050 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 234737230 1250 234735980 234735997
    0x71103121905090105072f15040c05062d0c0a050a030906050f090f01030b09010f0305150c0a0f03152702210603100c08040c08060105010906050906 65
    0x1048101005584141012036100e4865a441c040100741d881c401c070075088401c151114000a40b030240c00c501944401e2040312051540c1a0002c8100c50040103014a807080085100060102d56410130003401040c1300604010070080e13514524042c1d551211060300d4001c0902c02c1d0041c1944004508200030844c165224402c145089500c000828102075a0302c0c0c101000c11000a80000c502185880c4250140c8400d4900d07403040506122904080201c40f60305004c1ca5810503540e4204454103540b00e080481c02041400c10310386040c7d045003002401c003003824046801d0b44a00c80c0510604e80c800200310b0b402554203181c10780c0c0a03584e0050460144c80d8a1444400d0304c0710486010600c1c020b2020703180c040001d10352030303c4200404011810164041d2001e82c00780c10600c0c01414070340484008819520003001030035507220f6403000c3d4203801221380e03030980400040d51202c1000304114a12594401814401c4000c0c2200d61401c0002042404a402498100075010078400038580741c100a480a10 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 234738480 1250 234737230 234737257
    0xc02070b120f1005010e011101021201170c0103091208060a080601090e01150501080412030b0a1401030e0f120d0e0106080102210609070503040f020307060503090705030114071103 79
    0x4540008007030000600075100180600320307110220b0b00f0b0f02400801c510072200180c5a07400c0c0c44040750015104203141014080740c0355001c1001e248038600b6000340714086e084141446401c1c0c40860601d9261035861199103050500d8050500c0205102e000300d0000c1170b4992030242c00503034034a0003140c0364031259408152a8400c01c1c0c00800c0c0c003007103a0001c41010319604020800d07e90901603030011502540706040c04034001c1400318011031042c000141c1040f501e801c2c0070444038213050119145241d16480303141c0480e4554030301b081c81d40e4903005045039a10800010443e40600001c107039143c060505000d51007210010b148112000341d40c00a4107400c03906e400030400d1554802286010758481c00d2503050140d9440c8440486a19800c42c0c1c900420018114001d241d60f52074003034a5580c8054401e50300c45c0c807100800c00050344d00b0801100509141e41c0c840b0b032a401c118071414a03011040e08698031903414040200e41610300014056400200d52400000750707241032084a00390b100b0000d010a11 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 234739730 1250 234738480 234738487
    0x3121104033f110c0a0e060109120f0614060306180f01090c03050c0907080106080601050403060c0c0209060612040807020a0320032404060e101505040c0c150c02070b 73
    0x541c1040714426414102c070340315a2030070302c1d008032625150307038804880c030f9803000c40303d5018010440040100c540c0301d903060401241c1c003502e42080c00702e1405009421a85500ba40303012504005050203002d03074108070286252100c5c1415000a03403211f00c028401c0c002c00c6400003411101030300800c0030400c42030410000300242c9185007805811690306020698581c072400c90384140500702034a8140c030400c415661915142d0914404807180303003010b890a4100401032102102085045c461048500001e803200b16100c0e01e5841071000402c0000c200b503128040600402c00c442c038a03046131942c010742c00178400355a1039807880081c00068054002500b072040f60300101411120b10120759005420407401c440c400c00d13456112010800c142e2510390b100c3c8040c00042000203941d42c102601e144500c03c2a01c010351000050700b4100d0b0480400880c5039803590a00f081542854468a90042c52030b140810380f00c0c045131120300e8520410500046066a10310f1b100c1000b0f032007480043c01030302812100f83e68 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 234740980 1250 234739730 234739823
    0x120e01020904110d0b0f0303160512030c0a14040b0f091206010602030408010b03010513020108071707050a0e0604030b0705070f020406061e0810060f02070b070f0312110403 76
    0x850700301108013050a032030314000200718a00b07018504901d40000740150714064407401c0c0181400c00340d08044640d440f030302e0000c40e4203841840c09940b282c01a020905d854445c1e1a000034001e0041000c0c0b80030405082005101100b141400c6071504080c002d1003a5072403260f0404100001d200031507070300b04c6000394400401c1503607000c0b00034011104010020f10005442504060894206440c01004035110540240065004414040e030000c601e08100c04003031003500c116918498215001c1d03000810004000c412a50400401d110440003590a2402d2905684e20a02d6201c405020642803100200754142004200742540f109954050f00a0020550700c5da009020046d030407000c0308010b1182000d422240e8032401c8540c1c41040c1c8041c120280d10f28145041e1850030541201408601030f00c8004100c228081c00204039103446618041e040d00050304008081c4010f039080440c0d450b0400e8591050035000c0025601921303004040190001414504202010640c2c0340c0700d014003000e2508201c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 234742230 1250 234740980 234741011
    0x30307230f070b071b02040b060c06010e0907080616050c160e0609130c05040c02030c0a050f01050f01060f0f091d09060c07020102030d090f020904050714040606120e01020904 77
    0x2c101403140680d107005403207120050f03820b4200c404508030184203011600015240981101c80130400140046140c03190201003141040000d800458003110142c2c02d20960440130480e01e402000c00b10090501400c0070b0b00300b00810741d01c0c0009042001400326200e02410000c2c00340100303034006100d11885007640c81c003104c04000c00450b1818030501c01840061244c90071001ca40079429400f00a40302e103103090030100f2000b055018140c600b144402d10540c40b11030020440000903500a400814400e0208040e6909464000b040c5159001c604001003200a0b049894505440041d05100403010820303a42100d0203030030759012542e120400030f40040d4204103c420390303000c7c45400d001d4401c03580d85c8006c4903184e8420020004d00507401040060040344641c1d00c81182d440c41541c540c0303103044e99034000a9610400361000d072040d400c800b20410101f000c040c074000b541c02c0152401c3c092207103005000752000080038081000151641506902d0781d20a50450340640d20040040003100c25a5440e0b8 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 234743480 1250 234742230 234742237
    0x1506061911070506090f1320070203010c030204031205030705120106110d1107030b0a0b03070602030307021006030b06060d0f0c0917120708130306090f02010206100305030307230f 79
    0x34002c01c640419242440021180785000190501c030102000c0418000b140404540030040035980e104144800c5003220003410042200041840c0c0b21a228010982103600392020380090500c10807040000803149003500041c0032060a00e42e40360f40c0c602d0310540e65803041001c40140c80922400108040e6040440d02c910070417840300f22000c4100003001603036241c00e08006000c0d80e51201c40e0410028401f040c00c1d542c000c1c11450081019030010000c203242880e0340d00301002581000c01005502d0f40d04101010810b410003030b007408030f149142c071113070070000340508504d004d0f000000c1c04a8100c00766800c2030800d041d443d032007040300c0105840c1c01002c690050145607104110105540241c580000b286d0034803c2002c00c2e020700d02507131a81d40041b154094000300c1d40d00565144000f000c90031620400740311900501c12400702c9541440024140840200900f9408401d042c1c140b020540c0042034035440134082c00c3c10b00d580360414940354219003582d400000d60300c8000540740303001c00c0d01c01c018 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 234744730 1250 234743480 234743507
    0xa0b0705090306010f1503050f0c0f041a0901120b010507120201090b0903040515041a07021305070306140306070c0201030f0621060e06090c0105090406090f0603050c030f15060619 79
    0x606006c0c108034130f800ca050764020707600400c542c06900d002c1900042000300170050f8009840445207410390b5600810707a01808074030001014600030400345480d50300328a822403441900d0700c040191400180018200d4041c0c02d001901690034441c0c52100c8034000d40c480c0c4101c41d00407000510502d4886801da5880d4424010705004500922000040d00b401c8000d85055503405400807a0600380031100719010380040c88107aa20420302d04e2010b00b082450322505000d011555404184c890805208441d41c46d09103085038086da2110381048801ba40c0700b00903000311035091030041486200440c0c00c01c003928141d08110042d409144291b080f0214140caa2010107200741006d010442c6820b20312602c0709011130709060240c1001c2e00c050540c3d81b2903070080052401c02400003414940b10740000e4111003000c41250b10701a500e042c240300380441045251803041044006114000d41c14401540b039206129600e41710481007004504035a0341e982c10342e0401b01c000031802c6c103500c2c01c0190080032001180d62 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 234745980 1250 234744730 234744749
    0x60302040c0c0215090a030b09070302030705060a0806012706200c100c030314090a0b150d1b0302041113081203010312030b04021606060509090a0b0705090306010f 72
    0x410707428040c020101104000e400030004102c0007886220142540c0c44021050360003a4981e4000c0700156041c550540184960b0000300821400c5205041c5450780e030b40c0025109000c1403040074141d50b4000d82055020b0000c0c64050b0600d94070b003412505401034440884003080da00f5a010a0b22580300140e044400c83d100385600e00240f1303401a564442401c106201e401c00c440e040c8648080c1d000350705c001d1300184289000580800c0d04140343c66815419666062a80c020214110600001040190308503010001c0b04011a00d00c0c00050f0f400d400c689001402e2203003a040c0b50000c682c03444482070046801034070900004081d10025200c1d6400110902c2c01e512074904c0101d0781d09000140440303840780038040146164256241c180810030050300f46030030903855500c511070355141c0f0300240400c03810002c519006089107140080686400350041405040c100003040f40002c000141c0b00c040b0b603004075408050b6100d02d94111118829400250f8062058400014041407034000c01001c551313081c0d4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 234747230 1250 234745980 234745991
    0x603070e0901210b0408070b07082403100b03010e0d2304030f02040203092104090b01081003081e0310090501150917031308010c020123010b03060a080f0106030204 72
    0xd001c43c6141c1884070303103a00a08010031080d00054200f82d0594001340180c0c0c3d031342d0a10080d80c2e00c1401e0f44038100c99150004001c0302c20320400d401c0380c0341080c203104188080403000030516800700780e80d0304404c0c0078090b0081c1c41e00325480b0203480070346c0400c5035255081c040c1c809901d0240fa001c2c1110001c60003031a0450009031103141c200e42d41809a800307032648005010301ca00c2481e001c00010b500058554100741c0140d144c088203c40807281c04c00c3d414400b9001550700c507840e0241c400100e40d05201c000e81442031903810080d031446500c0b20202034a80c0009500d40341ea11003c40000d078100c0703034854210035103000018810003010000400c0100c808180d001e20203030703881d40d0000c002218030807605408074911105c140564810811030160711030b2880c0c112401d0611140c40e206580303e075070703005429503551004244141c1d50b080c054440310307258000540741d0741040010300301c80d504d0301441040c0c45200040041121075503415a850010480f0004a800064184540c2030080407140320880c89245010b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 234748480 1250 234747230 234747239
    0x1b091d0d02070819060f1b020c0a0308031303140f0405030d0507030e0906030c04150302040506030d02032209020f0310050a0503070509060418030206011409010b04060c02010207050603070e0901 85
    0xa50002070399550f01c05030001c0d290101011007400000c01c0c0485078183c444042d1002070119201c2c1820481001981500d980c080581c042d09110312001c4150003082204c50034070201e007038041129044001c562030090710200506003110000210300c1c038001c030243c0000395080c1401c0244003030701c1035420440980d0140c3e81c00c4c000c08c1d2058030a04030005c0c0811440c10300076541d440d000c40c4040d4001006401d13200380300340c1c140004003100c40e05103a90b40b2070300384421b06005504161003030f641c0c8001c1c02d03001001000e00820029599006e10415142400008070103204420f40d4440380d0001850307160029502c940103250205074a030012210311080301c03c100b100040c140783c0100b0141c01c039a0050041d000c000d061070244240210300078070b11034200d5100c042d4001002c050300e4442c040c450083e4050041541040320003212900016000342c032404590006000303010148085600b203441030304000085ca105480181d0821000f035104642c01a40030080080071038000008400c0c001c8210341c1811240e0300c5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 234749730 1250 234748480 234748483
    0x40b04141006020d1d01020c040501090207110913200a090c0f090f05040e072103090608070e0d0f02040c0810050a0f0302062203050102090907020a0f1b091d0d02 71
    0x34200000001402681600d5117407645071403120800006105075441450648049815030b1001c0c3c0c005000035078009842c005101f81e100c20f405400904542c1480700d410900501107455281d040c02809021421940d08140c0a401c0c112038600003001d8072044046598207001401800c03180342d22070100d154030f003158031243c0c070035081d110030340f6070804445503001c0c10401884001e00012040c2c140d80d202d4028046040e410042e00b0040500142c2182d1441201c44e20b0001c1103e8601e52010050040400512240c642c01c0050001200d80c252200b20040401d81000545045580c82c0650403900c2c0c20b100c22011940702000c03510603101744a030080c00382d40d202c0c280400610948174000e40c1e074104110a00062a100b40200103000114540034842c40c04900b000d51108003a902c1150181e60024104845040400800e0380c001c034280041c0030800038070384074000d01040841004241c0307200c9082ca60032900b50b101d9031001074980d54504018900341e02c8041800c0d2890450741411511640c1280b0012610 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 234750980 1250 234749730 234749743
    0x30501050d17030723040812121b070f060b09010515031605040b0a12050c0405030c150c010204080c0306310206070f030f03051b040e0402040b0414100602 68
    0x140002c4446012141072201d40040e00701501010402060900b0030f1845190707040440c089500c40d100c03290351241360003a4145026015032030680012428410703180016210720210b580301d40c24510100d00c0b4260954034249030700c41c00d0230041c0300f40c001e4001002030040c03a40c050f14410302e0550f144801644c070f46040281030361080714010b8490404100043d02c00748461444c165940d582d003082030806440d40009200d5821118820001070000303491110060384034094107030000c40211403140b0b0941004080b070b840310641032610340500c5184980041640c0118121032451069000843d00c490b101e9001c16202c2181d80c503042e2081c41464041a5460b9510301000380c0340c100040411070a0120b4580500c4c500e40009007a44c3c080414441500130407603404070150404e110350340300d24901c4414200502224000750030f44441c3c0b021103180851804080f01110183e4500012183c2984e86a20005026020603882c19402900380392440c42100b80c0070550500405c0d091040c181d00a445040881e03071a00e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 234752230 1250 234750980 234750983
    0xd060b040c1e110a0203120c100501050a031209030c0807050f030d02060609041a0412111b0d1e0605070f080f0103110102101d0c06070b040201211803030501050d 71
    0x10b1803050400c442d80950741100c02516580d00b5240e24010036000641030201b080380400858400184900c20f04805118002c0412441c0004000f554106008a0b050342c0d03403804000c0600c4a03140c3e031400c60030301804003100110f078407054039280541c0715585652686441d11030503014002504000740603150102e00c0d086022074541c0180076503514030040044486003c1c106541130840c46c000c1d060b100d001500d416100c1c0340500b440c840c01114003040148003114a500310390003500007a503980d415010050000c403488008440900c06010305007003407030301051024415080d0312000c0401c0e008000d21a000079100f0300c420340741d01603002c14040c001c2d65400c000316034045842c8100001400011490540086840f00600c119080d0707006545400c02110260a4086695110070003600c1c0c0385401001206c0001e0703429543c04d810701109a5480184d08c8000d00700905106031024401720b0303245420416044003a43c19800e02ca499007000c01c407100c6d02c207031040940000342494008a00c0d41004c5e2200401d49 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 234753480 1250 234752230 234752267
    0x106050d080f0306150c01051015020703060506061b07060f0c0812150402071a090102040e0a0507051207050a1808030706050604020915091306060206070f09050d060b040c 75
    0x111a80d07415036060b500060586a2081d01c0c04071159001017a07030042d140c0700c40305400000b0141442e0035000c40352043ca604c094590380540020710051540402c0340e00c1103a0b03100d04040781c0c5031100300026100340a0715180f0355550400c00104e01c440d03900003440c1000c03124981c070303901407010151500300d58900558101a0014030200154a0311070044041181d002c80c1030302964200c190541c0010f0141c0c1e000480503542040054600f41c0042076903c003640d0084d0880c4021131819203001c0c03441103c4000101010308940c0d441c1c0014048601485c21104003003400c100380c0d803981c41c1120025107160005c0c1d580c2d40000d01e0021950b10300b43d018034418002e4943c036000640c00d0002d140c0c2d0340009054000c001d190400d409100c80c0c4140d480d00700085a981a4440855464100306010710121300b0803032610082680c10f00a0030000c03a500070a656400c100a840d101e800d881460740300350350720101c83d800103070800c403507a041e28148040c43c0d106110880c01264148000800c0070030840302111040a190603a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 234754730 1250 234753480 234753487
    0x18060103050d0c050c13050601030b030102090d030311070b01030c0f0911040b0702040b1c0203060c0703080c030a15060305010602010c020105011401030b04062303070f142e0f020106050d08 83
    0x10034000d000291080e44901d0403517004075404000701d081d590030640b01d50400e0340c8540601a0968040c00355400720f903801e400860518064500040007291011005000c0c15a42c21040c1d028583d50b0007140e00c22508001000740d1542e507031801e00350f108403038070600e000208010700105406100b80200003082d100c0c07103180d60515080007215803003540120710480e4040d6451100360025150104480007050402800c8845030300540141420040c000b82500c2c003588080059000003608203207041d812020b02d0b14901c5d140e42e60486181e00074506d420911217852108900007410715490341010341642c1c481c0e80244103a10f0414803d84c2a94828002c0c11f840c806a0080c0c01c080b03500c02d60105009040050010903034640d107a41c03c2c00d902460b0360b01e0f641c00c425050800581d0f41010030044005140d0aa41d8400032480e10f407072040715100c5401c420f4031483c010814141d01e0365a6445540142078441d8259100c001d1100016144402030b10782c804c05942802d20004480c80c2c034000000c034407074100b0001ca28 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 234755980 1250 234754730 234754753
    0x3050310240305090a140c10030603081207140408010515090906060613050d050a060e06011404090f1b0513020f03060d170715050a0506030a12020c03030f031806010305 74
    0xd46002071404201d482401702c68004911460107082e196206074000d0210010b0f244180484140a50383c890141030821008000007102030044440d0342e9000561440584c03500c0300c04660380b510307907141440000c0c0d000c94003040d03155044d8170641c000c40d000c058000204420000f402000300d01201c1c00e0855070420f44c0040c4007818000000e0610200d84008420b000361100d000601c1d03a813039500192003135400000038004000c400e00c00c1e04050310b0040b00030320b81985000c55040d00240441d8046014607115034104042006c0350100100203a80111014601c950300404030b5a844c11511a482c032400e85840086405040da100f200d10f00052a11400e24581e10f00040c070002164100341140c8e80000901036030100c407403000192191078851b030301c0100d01d602900c02c0b050a60704080c2c1800407447c130f1300b420f0250903a0300182c030040850340300400801d081106001030341000400655560503020001d001209101003100451146079440c4483c130420740c0c00260195100003d00004000342e103d0781d034440 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 234757230 1250 234755980 234755987
    0xe01080a050c190905040e0109020d060902010507020a060503041502031005120a0b0903030103051213060e180c0a180602031c0204090f060513110418180305031024 72
    0x41e8821420009280307030040d16601106041c0040f040400000d045040c144101d00c2c150190b19071010040c0c0082c41582240d80004400c40300c0c042e4010203041e42d40680504590284d8180d48042d600181040c04051707031044007410a41c02200c2c1141c181102c469400c10303020442c82034a02030360300041c074800d0351818602803082d03900f400c011140c1184640450700c40000d502c032040038400d030548800342d40ca075451464501c0c905841400d1003d44840240603200b003030514244004100d03480e614200f052107521b00c000c207101d0303284040303482c2c0c00e102c000f4100000203100340c0c020b2180095664840c031805195101d40c6440b50703054010480140c208014068814601410f4200c0c40040380c07000618050351565071b001110616070310522099107070309080195140500015038400b4010205100c00000f0f083c000141744107174020304203c0b203d9008000c40e0446d0652000c084509141800c2507102500e00703010348107410444000b0b00101c1512408a000c6590080e0b0108a01c100040c88a4610060500342c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 234758480 1250 234757230 234757241
    0x261303020a0b0106030c020708030a0e0d1a04060204060905030102070b0103081b19020a0603140c0a140301030f0b07140a08250c0611040609050f030712060203070801060e01080a 78
    0x540440c031541c007a6402203000424010300820341138900103a040100e0314041c0c10448a80e00c4203995820900207608000d070084030381c501042049803010012182c07868409000c42c44240d5186116160804000c1017010a40c014826502a506c48004240c0d42d0000c040c02d0340b048034001400000c0400c0100f000504c244040c01e06030340b88040307844661304500a0146800300c2c1d4054901c40c11031311010300066060000c0704c08082d0105242c1401841e495124681111002071324034070450800084121003548101c1c2c429900e02841c1900c15a03d5959085c01d8035401c00c03580e0150380c0100214080752500d801603c1e07070004034403c0300c90541440c4100c482524603845c001e10507807a424030034410450107129540e94901ea45540e844046a00d071481c00d28408880c080e00740341c80c91200410092040030f030441107031811a40112000c5070b07100c181e80b01181c2014403503400a200d02d0b160040c0582082080e40180d441100d00b42c2d12140247e030303218402c448100a44145a000c26030410110300c0300903994004 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 234759730 1250 234758480 234758483
    0x20a050d0c03080a031a090103031e090f0f1802041d0613052511070302042003160f020312060904050f0f0c0f09012d050310020a2613 59
    0x50306650703071244a9258404c608000000c0d035501d42d080340304940c911074a48104810385140e596981980c0d4040c0a222080310f415400c98000d04041030120b1040300071502030700c04800c5d607540d00e40d526103054041120701d008682d206c008403110307840541040d209840031030381c1100c0040d40c2d07410301b055041e201c820094032490701700c04200510a0f489519001c0e16010710003920b030350081c0a410300c040c1d40c0c0e5101c04103040360402540c1200e43c50f00801c00035841040d00c1e0126800506810300e1103502c606d0000040e01090f00c0040030040003214607695031341061003044c41d101c41082a8503588220707113a10480a50707030790b14080500802c1481c1041400507a000e40724008440103001001841450040c0d00501c465480d0b000948410050800e503100a802d048240c0c0e2a00036941009017001e951403820418402090821020f401d945d00148100c074000c20001d0191111042c0783d11101c00030754003c01004d80400d05101104c2c142841580c584c51540c00c540b581c06109440740c2c220500b020028010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 234760980 1250 234759730 234759743
    0x41112030904060303052701021c0e03060c040302090c040e18030904060e16021903050a020a0b042d03090621110306033f07060c1106060409020a050d 66
    0xa101d103464a02c208800340d40a07841d03003500c90803010300304249440b24860300c8000c4c001402072410b040c4d800080c0e402c80b440c03886058000511402c007044410103e41c00184ea0b00d84140c1d81405142c1300604002c0086c1ca0094802203610754032801c1c080801e02c200d1203000c400ca08401c0001e940041001504012150000140d074a0319031410009401e8588030f401c02001803030000107000c200240803182d100c000c0c81a0010f060003a0020640c0382180b46c6810000d4103110002480301c105038402d205404207658803241190503420b00717050284203050803a6550340c1800f040c02c4007100d1964100b480c004800d515954207200e05080c600102d0380b012102d01d04002100c240e04400300c230920703076016224a0b0703801c4081e81ca440e444c1090401d441c010242860741340304243c1e04c0d1101007105400e94403040349030841c072041144031000306030203078a84246840609002d160a01240050707501042981040030280d08540c0e1701c1d00c4140400c0122050030030b00941c01100d03180208400d044c00100349456502070003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 234762230 1250 234760980 234760987
    0xf030103060513050c211b0406060e010903081b060106030c090f08060a0905010204080a051c0311030c0a02210a080601260c04030507030506040506010608040b070302070f1506060210020304111203 86
    0x3d646d0740741440a61680c00c1c20480b42c4200c407214102442003500500c030b01e140205418580b00000f801c1d51101d4000a0140f01000071405810b840034502c3c80800071000048544c03d680d00c2d01c000f13000f003003180c032900b0008084e1040080c030803000c0014a4259001040074118a440d110002402030030110310864055400344000030341800c044c0040c010aa0151001e08944555620304403258402440e101d000e151404000c03426480000d82581c0e481140d41c491541e0300d455001c000d91500c0c0801c0b0055910b4040301d41e1440c0c1f103192032406042d070558035407211411629040010b541041c2d4141801c090200500c8036813200186c506e40340c942244e003c0c08560718094076500e4090401d0700c25002a0703100d512200030721040140400c1342c1401010f03285485906802c0580d110807030004d000c0c042c9000c044e0041071820600c12514809100a98011082815070404500c4900907055500c03c08000d40030726544101800d1007030007160700c40e1b40d10403034644c1c4400034141080030310403912040d00da49120a0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 234763480 1250 234762230 234762289
    0x50609130b011812140106060e060a0c06110408060a0b03030f0703090b03012903010503030714010f062c251403040809130b01020d030c050706020f030103060513050c 73
    0x71100300001c0c4c640c41850030707854030890070440401c8a070302c1549415685800e204104090348081c401c8025031080398103c0c0c0d5a81005c00c21114200d442001404140c179002805483c60401d200400466480744291840c5950320048a8100da0340086102d4040e08104040c03017803054104000c2a02512904102034407070344480300254160026001034a1440044114007030081d113413462004110302110b505031035136041902080d01d9000f00c813002085046000c0741d050030808213401450300110700501c20010503541e1034420090042000300c81420b030007030b00111003401c01e03242c03c2d40784607000c0c4d500300b500c45104421b02d9004101c0303484c1c22002000510254041c00800c14001513026a000705603603502c07201a441041492001e00344500c19040ca0700b102c5000c0c0340d8020900320082415800d000941d12210780c000d80c1c13280303c0e17454000e05851000803002001c4803401c015605aa00071001000290b0f2459040c5001104500c40541940d00502c010b1f00540340001401d082103140098070210400c20 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 234764730 1250 234763480 234763517
    0x2010f02030702030a2303070f020a210609060f0509160609051e01031805010c020111120f1510090e010b0f120601120606080f0702011505040905011b0513050609130b01 74
    0x44e240c21141c9c0824003113603805601d0000c0d1084054510302046032074040c44585240050007030f45034001c0009460b14010014005298019002d89100000a102e540b0b48084070544800220543c030a1501160401040f01e51299502c0815580e01500346498190b001d010403034001d9004d00454101620b90b801c5800c0b000c0401503081d107440c03144d000402c540b450b089019080d1142d010001040c0e4005000804507141800d810700d80140600c000c1c6c4d034094407200b816002c1d40c00120800303908001d282c150800c04644c0b103064101111503003c0c501006980b107620006c624401c0300c0340c0007010001070021110b0320112580310381c0c205205050005c00c40342e014003104143c0f4050791100010070034000c00c11039002480740d9000e0744401144000c000c04480d43da58880d040586001e035074080d0b542c8034003c1d0300b00031007544248040000012010f1000c1d0755814020016400042102050070302c042c800900ca081050548580f50402020341000b260005014001082c9a0610340c1c1080813011038940424003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 234765980 1250 234764730 234764737
    0x40308030406060905071b050f190606050d0804051207181a1807030b0f030609010e0f120a0c020409060c051e040e071413080105010302010f02030702030a2303 70
    0x4a946819180d1400b41851000c0314216407041c81420300744010044d000f075018680c65902500340300d180103410201c2c241709180c940300c1990758585204207500c50700e2465000f01024001446584103006403034948d0140000d0410504004041032070901003844107141103213444900200c008101c510181c0e43d0401d807014007920a0150001650710412640700c20130154112086060542c3c0d507160a007a4040401c2e00b03101f004002d5070805544500070481580d030201100541a0010204c1d02d01b07040014200d802000181c6201130144140014100405808a00341c0400e02d071118440d4240030741d1140a480000c00321031708907802603807a0390940004145200700a04505196a4662200300c0d442061b81603c640031800011940309100c20408001c14410300c55000505142100030800002c0107500c440c043c00100076100d01c801c10b03011039802d80c15408bd40c12030b4001d1380d89400150b955031050341caa103e01180a9010b400041201011603203058508103410100340c542900003100d008030310304640 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 234767230 1250 234765980 234765983
    0x51b01170103063c050703020702010806040c020f0a0515090601180f0b030a0308090601061b14030c0601090c180b030f18030f1309021201180b040606020f2b1b0204020403 75
    0x1407140513000404e8658442c50f0ba0026841c1000c520380001500040c000500091029218076203274414402a98401e0288101f240c046004903000503a840c83c1c03c0e43c55403481a0003c0301d50110b400012203924002070254102e0307101503059001496001e035208050211640814140c54a0303a98006182e00c04201401d00da5000b680c481c0c000b42082c4443c1e504184040c0c2c0080100405041c0c54500d17404042c1c0461040c0da031180c0d91586214a0340480c60440c040d08480000302e004070000012202c0060300080e40c3c400140e43c921011003455030368000603180342d01414000b10710910014280c110070700039050b000110400744410701229003401d94a5a480031702d610600c0080032580000a840b4084414083c1036041d001b0742c18000188800a144041403142d100c03205616441e2041140e00c541c81030744041000341060000c180c075920702a64811107826000d0709849110760094002e82041c8150034003040c10005505e0b02c2c00e860004407600303006580900c0c0802e00c0d8600c245c3c0141e40310301c02000110b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 234768480 1250 234767230 234767321
    0x30e011b03090c060f050a0305060301150b0315040504030905090411041505030c0607050d2102030a090b0a0506091605040f06030504050f0f0604080304050307050a051b0117010306 79
    0x40340c640700b41c503da11540402d051285c401d03d010315003600001510411905841e0008681c4d0358031000074054664024102e00413425500c001c80ca003400280214800d201440e000e2602040203070901040b2503003110b015000443c40d00062126181c0f9140340c5400c40d0280c40d166500d102c011000904451840115031012245141c003040f4600703040c03240d102c01d2041252002e0070813009072140b83e01c0c0c00c0440e42d05010130a43e84a2243e0204800c080b0103040c030a0b10034119142c1c6821045200141320700c041c10f450080104000816001d0386000e080c0c41214007802790318a54540c020002108018508840d09200040c4004900c400084c0300d9800108030654010480e42814105581080803000182c200e58008408080c0659000181c0b10740160384414031a56070350751420310714114000c9803002055030061418460611400042c0c0b0440344000b08060409a0400c0005684680003040ca41c00d14403141001040440e010f0362091500402c2580c2c22000e04150300704143d07851185901c6403070301c1e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 234769730 1250 234768480 234768491
    0xf1406040606052107050c0a0302060a050112020f0f1c0501140c04060e011b054602040506010203070f0f06360501020f0a05040509100b0a030e011b03 66
    0x186400d000d080028009400c1151070041c8401402c0c1d9540e0303045080088003507140d03005c22801da110381c0880700c82801940680d08520f41500e03009441c5c0c00103640c80302100e8140741c000b01b6049941040e43c500158000c0c40c64083c0c051040c20300c0423000300d11820a078044001d0810b8207080c00c41d1655a03002600c47c0000088000343c07626030703800e4000040e03c0404000e03800c0c40184082908810040e08101090802000350440707a003400100703120082e4003c0590058111448841505501c401006c0eaa48014080a164820301c104c9201c42e044454006610b40001c40030b000d8102540101e1b00040706205491414650b511000500c070003d4000f10b84c40f0401011b030307005000c1d003442002c1100b500e07001000d040700c40401c0d1410240ca00148003007146158540c4242c2000800d50440e5805200c0c2c00310281ca2715062800a400c940180c4522401121590000368070403203032003020000e03907685900035400c0c5039240d0f204400404059000007642c1d07580d010584034094080605441040e22039402141 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 234770980 1250 234769730 234769741
    0xc0d0c091a040e06060303042306040e0612211b06040b01140910031b031e050705040b03030f1b01060927030206070507060605040608030a02070806060609090a0f14 72
    0x303d508a406004458119030305100c5a513402108a40880b800b00f0210729058191201f9503007034520040c400c0340c0c0128001000111104020161841454200c0d1204007080070b04840c40d48640501030a42c401040301401c83d10300745202800b4010300ca225001803505c0c07541d132050051074500c0569040e0303040c0c06214010450180c070148420403412096640070054103119080001801060200400020f540b548010b140a15800005c00954010382440000300104650959020060384269428043c2e8003000c2001c5c2040c0c000e00034000c00180c001c41c540071921842c581107420441d507440700a50185240304821070700b4020b0902800407454000358903030708250b4054016006d0040540b0b80c0160a40041c0400d402051042c0d03c0409070802e40d50b80c024500c1c6c0300c2d0082000703030050384e0300070702d040008907001070700001501605045408a81c91b040d26106096507a8108407805580440100701c003ca96040c9040c800340c111510010120702101402000002e8507607001d00c04201403144401c011 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 234772230 1250 234770980 234770989
    0x610020c1f0e21160f0b09011115060f0d080d200a0f1d03070b09010908070b0309010e150106031812180506040b0702060a0c02060705010c030506120c0d0c091a 70
    0x138010b21852400450f403914100408031040d02600c00c5101c620404907209241d41d01505403496521000c809491034200308201003488544143c540034003a050103980441c035800c022030707008003494010450604200110012001805000d581c4072300c3c007090344074252505241c0d500540407284140c0c8450016100381c0e03400420300540d0b038a07001c1d511130060354800c40e15203000c0352004c266250815000d0b980c54640c5c0041e41c004881e9441580e10384a007440c0094981144800303103000740c0d5984000c2c0300c9501c480d12907a9584028200171801d4048040040100d540603a025007001d1481da6400e030704954070303500e44a0030700141c07401038804101900c1202c29080d42e0031820001a2900f142c846042a083c108180003d0052640003806054002003614006001d5103a82d480998002c0c9010ba45e08518681140648140450300b40403c1c20280400d05915002010a4021030344900070030440071a0790801000300054141621064003181c000318604d401030048503400110114860302c030902040500 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 234773480 1250 234772230 234772243
    0x6050d05070521101806170f120d200d0b01030e0307030c0204142706070c0f060617010c020c030109081605150a050610020c1f0e21 58
    0x10000c10030100f01100140403008000c81402c00c1e404070507000b40d43c0d51480030070003202c5900031001035103460b101c01d2940482c1d40c0108050b00c180da03030450305010440780451340d40c2121400c2011a0b400400081a0b03110984015180764655001c003c6441180d0004003800c02100c04480000c2050008040f102e0208a0141c020040004c3c0307010410014204280b5889000300b090007801c000500c141c01c415503503240c11000c0c07003031080752070320b105818821102e004008080d8801b084070b542d03a41d0b0003456184c010408510400c46503d40c0c40c0d0054650360b9201c0c801c4140c0350704480072656224045445281003800007c04001c1c04000614802c0c41903020f0720304010004624880d0381020a0071001600780344c20307184030701000f103000e611a068070705d4482d041821045070506a00900020000c110707d2540285e4004c0c00244e980407807020364254104d8880880803607444e0400301d20742ca003080700940b12028808240c0903103070483c0852000c0c000250101880c00e2101c041c003c14003410340d00d034003061280 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 234774730 1250 234773480 234773491
    0x807030e0a0e090c01110d1409040606030b280b030903070b090c04060801020c0703060e030c03030f0f09060f150a030b0109060806010b0a020705010e010302090904150f0207051b0a080706050d05 85
    0x2810407032009103000d550f10b45044d401f0b0010000f0b180340fa02509a201401e55050f210018014083c0c65100c600003030080200b156114400c0240101c00020802180c050100c0e40c9020305e1a803850604000a0201552000d04070300454881002094003081003641064010143d0002500900101904000c00c1c0c4106400c18003c9074410850032407405800600c440444c3d62001c030214a40d910000380504500940c00c2d003d4841c00000b0030032550000c0d0410075849854030044811080e02c3d417402860303840008548204092540001046455100d6240c080c0926001412030848903100d03901ca40c140700081e40250512500c0d560203220707034801408040d01511004404038100991039600942e04d107050301c1b0309410300c0082064172025902c0398046a694200c0030f02651154202842c02640c91580380e90551841841c0c50154a2010380c640202c580c910b0f0400010002172804240700d40509480c400069030141e414030000524038030070710602d00104220f03200c040d121003448240905940d80200f5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 234775980 1250 234774730 234774737
    0x51c0210020c0a030209070201060e070c02010f1b030309080c07080609012403080309030d09080d0608030306060d0203091c080406050709030b27160801060f0b04030807030e0a0e090c01 81
    0x2e070708035070315003080c000100d9804450801040e110a44240e00611040d00b05010221122042001c240e0b0400050030045100780d0f100c0344d041d011440211000c4002c1e2850000c5a0070100c0f1060210b442904941e9002d0702803443c052078021680e0704075203092282d50003c0d41c150415410000c02d00401c0c4521020410f4803401111030416048101641c0d00250000600c004408408202000010416034030121450f040030070a089150820003003941065080d800c0c42800c0400c042286403021050f07034011480580300e542400d00c0b058022001c1d4000070f0800e006803007008250141d031500c10f514074468500c591100071050420341461401d07944014949000c1c04800041040002e2001d0411944000800e1310341003921610003e40c07160a1040c04ca9009611800d108004405c0c1c58084042c12101113100030004140e680d00300031140301891280c8044801c040c0030070004900d44400400c0d43e41e100e46080c03518050246d00080d0faa04181e0044003500c0c0c5110200040404100f000165080c2c0909 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 234777230 1250 234775980 234775993
    0x5150a080105090304050603090a05120c0d031103150d0501240b070b16030b030a051b0f0d080c03041701020403030306080105061e0607080d0f060f1409060109051c021002 75
    0xf1030994030700c034170700c1114090b031400000554141c10502100800e41c2e4080c0507281d20400032510300809410001482480e401000c13841c0c0c00c00c90003071003075100300c444c40c840e2541995104c40c40c1c440740a41c09902c954004004410310380001c4c00a00c646480c4125a4206070782940004580b800f080401c2d401501e050300d1304003c040041641d200c049030340a00340007000040607600700400c401400c1c01c0c0c200b80d5010312a40381c14801f00000496001701d500c8e02d45201003804080001080944051100c1060b0003d515420507404190244001c00814030008101c80c5001d50ba1081449040040803c2c1d0b0b405035030101d070074810181d060260750001e05402009008a0030550000b40d0320720501c030401158002c50041c000409d4560740e040d600d03d940c1210b4525141d040f00d5040e400649590180944081e00e40a000301d000e20440c0d941000b90740d0640c80c1c520541c103110007071186101001d8065418812880c100084507660104403103811802c03001e10b4501c2c1e07541d600c1841b0613281600f1201055400c0720703 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 234778480 1250 234777230 234777241
    0x1103030c03360a030806150d0e0c0d03020c030616120510350f06070f020106090f15050a0b0d0b0f03060f040b0c0a0503010504020d0f05150a080105 65
    0x940540360000703401005084034500c41c018203200400e481524102100c1988103252480e480411103003c0c0b103010751142c50345650794004118003c45140c1c01d800119600b4402c1e81c0d50544598881181d03094500100d8007006141e03400030350820000d503c00c80c01684503407050240c82c1410704c20179412034003c408500e40d0280e80f040161111411801107800c0c103980e000090030303c03040414407000400c00f01c40d07440c00c0300340444150045150025410b50071504603031101821718400055000d8020005800ba1003140c8400400300d9074010201e15090866403941404035000301c451040c840042000000000e5860101c0d0028800d4540769022138820606007104002ea524208125011030342c9184000500c90b64a400207803060290b0081140c0501c140d600f0044034103032580401b40501c1c001c0610360941d030303200341441030a44a00c07815000014018030040009080c66006400307012659140802c1c1c2500c1b41d00d07104200c5000b00c40ca01c4030070742c890701203406030700b400407003003001d400f250000340681d1a11 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 234779730 1250 234778480 234778501
    0x1103040f030312060302190815040506130501140a0c030b030705010f050a090b030f07021203040206120606070f0b011403032d0d06030503121515091302040b0307110303 74
    0x90310015081c0000c0c2244590030201d04e40c000c20245500901440c0c03c000c003001401c80140960107550718910906045c100c0c5141e10041c0c0034411540500205915662030203c6105c00c040702d00700711003540d2180d07000a039140d11018498407424002d9800110980c030303004014103446034694030342e019400c003860510042e40e00c880001406402401c2c40c03070355055010011180c40c4c0469001c0e8500403004420701650508490b00b690050700c6540c216440b04d03000e84c0700300c211480240d8009501510400502c0040c0350601d03400d40d40440000e1175142800d030a519584c9400100b800c040354132913907400c0140316412100d10b0180c0070940c107400650400106030307c10b0b11072030400300110032000e0300c1a518185566a21040751b246512015051107074a50343c0c50080d903030b500a43c0745d1007030146140c400101501c00b8000c144e82d23a454014480d4080d4810aa110409948000c03016a0030200030645520048000d000800091030308526150f501e00e01010002c090003595942c1d20b030250010814440c0c107000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 234780980 1250 234779730 234779759
    0x5160c03081503010501090b24122205010b120f0a1b080d08070905040e1009110a03050703020f01020f060f07030207020418061a13020c070f0f06110304 67
    0x3410308086869444442c1c2078000c68103864510ba51560078840040b03903000968100001000041d00c1d46105402c8800020a94032081c1035501c0f58600280803120307182068078150342d0000841d0303201c1c47d440200c01048041c50810100c0070368036607455400b007400509041414101800006c4003900088928030003250b1941e4034540040c1503011580d81c0e0b12081880c81000b02d0061040c00c08440340c0c15984034015000b004211003104c0410a491340020384c034100b90180c1990a2034041c0030702080c04690b03980c64010030103042c0c01e803040740c000c094040c440e45034941004e0203540901c0c001c103405440d62041000c042413105c3c6050440d00a015080c00980c0000f4100e5009031103400b13080b055903941c980480c000d019010002c3d61007410300ca40980600c02c07003c45020080d000b410240031068414680f40140e551044e031564200c2038452043c000a082039000e411b00103000030568024a03a610310341c00a1900603042196880390021b002c001c10303600450140145c220300005141014a020f002060205 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 234782230 1250 234780980 234780983
    0x414030306031e01110c0a06050a02090625170705010f09050303010302310f0b0103060501020d050f04030c0603050601021c0905010807050d060b03150a0311040914100b0405160c 78
    0x3001c2c5621243e4454003034000508909450600075200c2100060080e43c4910560080d101d492920780464222041da000f00d07140303004080c068501d40100703071045401c03c0041451040300c0d0f00460f4440f400003a01c440c2c1009411b2035500c0c045848a201c1e041484c215042c11018100582c58640100c000860204c16241165011500ca206a98889144001e00748441010320204c3c003480303420a2202010303600c0001c10b80841c54080106d040b402c00198100d84c3c507030241c1e90150340700584407030070340d441a07008100e1125440185820300e99241d442c0c640c030707054903002140880e1720341d010012103523410044089814101044d40306601c00c000000307170654445000e654104038035a4001140786000b001201e01c0c080040c40f00b0445e00d03660310b8070313000e6541081d0b41c18240014000f000c40000e290001900c01501e8100060212601003442084010403108004464034490040c0040c000d40080c0045803415201b01008036100100008000885a0082c0035a80c41e0150f803d6485603d40c0c1f0024907508103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 234783480 1250 234782230 234782263
    0xd060f2d05150d022d120a0b0307030212010902100c15020306061b070303090902040602030f0a0315030506010e0a140403080c0405030111070c0f061d06040f0e041403030603 76
    0x70380014411840c0e403151400c0b00303c0190001074000ca802d485c000c0340c040020107a400001030600c2041c80c1090030321995600301c00c640c40400108a02d101264072241c1541402011209042d0752a0f000c903c1c1114440400b695036555542e8441c02c0d0b007080a0980584800c610703010140c24a10341e6001049a03c4070701c40c840c0b141c0c0c0800010b45689680c001c0310306011031441001c0a5000c903403603441e9030b00c2440c002200024605030300050b6004050013560706841e041e4000d18280014184200700c41c3d08036031a04ca04050303d481910500e50000c1c01d00d10065401900586401d40c1000f051042c52040584582d603035a242050f0114a140150b1400d0313005941740c45c021a2540b1015a404a82e014a030000380d415440c2800142200035500014603029210b0211003581c0c903500d0204c110120807602c160000708000d140840c400303207440c039190300201e40c00518203420301d0b440d0341c0d0540780d0381d001381c010500c02a0100184428445515580da140400b614000e41c42e500d44031011035280c442c0d000461841 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 234784730 1250 234783480 234783499
    0x1092a020a0b01090509011121150901080706111b010806130606020c15040e01120c1505031807030302101109040e060415050103030f050f0d060f2d05 66
    0x9038401d019000c01d8540026120000f540c41e254481c00034601500c03a42c0c0c1d103618000803d105410950280c035840890004103a4054002001c082c0c0c5440c8000d0521b00202104006045550350304100d4a01902041c8003c241c5103080c0100941130b82c04082d41d022181e442341000c014814080d01c0300a600c2c100078a4030700352684808010446100100500c11030a40c1010008204254001a00c42d01e9120848116020f40b0703c4c0c8850010324480c90040f1602d0f00ca044006020000440c5d00c1020386500c0780300d07115402070780e0310082d0300c0404858030b0741c00005100006100f02421020b0a03401e01406150150071450b245660181d640c6980080f00d20f54252030314503405400743c9484c141c2d0410b80c0040c0c8140b1a041c9820040c13074680c401100e0403506101d0042031145518501e215aa060703d40c941c0b1110341c2641c001000340e8164214110a500361391040080d64025450b0f8003401005040c49001c0e0481d042c108640c992181d82111198400a2681c89215100d00f86c5190510100c54098910110 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 234785980 1250 234784730 234784811
    0x8090303160e0f03010603050c15040305120304030c06050f040b0c0a0f0f02010603050709090c08030301030c090506062502030f010b0105070f0602090d0f11040b010507060b03011b020105040b0109 86
    0x602c0700f48207406560551130804c1c00028040d02051004085404a43c0e8619000403901fa92040703008500000d01181c1c0050104082460160020350700715001741803406007950a0350311030f4199001140c02602081c80d0b4014401040b0413540348540003d107402c503050401035522002480d01c0c40d82640704c2c0c1000b4140341c810705040d00130360040002d550000251441140c41e1506200500802001110440345030100010b102501000f90790581ea405506811454078002150000d030001030315082e84010108a0300030030842822200724108020826101400881e00405081680001c1480d5499060102c800240d030f0b400b10440302415800414450009a43e040c454006c0c010103500c960080012488481408180100e00d091584a40310400c2d4041c03480c000c1c042071303a0002c151607000c01e4090144500240e015000404113070406000002c0b0b0b0882d0140d02500e0080b220341030300c0580d6450301840b042c880707a0301d001800761540301801c0c45041d448180441607810080c0503200c0100e41650300c0320 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 234787230 1250 234785980 234785989
    0x50a050103050919140a0503090906040c080c0a0525030e040e1509010204270b0406050a05040209030109050d0c03081b0a110c1009050f03060613020702060408190308090303160e 78
    0x41754034284800710b58901106191131683d0b60b20500d0303c0e52042d5043c9001803d20326041c00390f1000d18000360f50b84030f00d507240c6414903141d0f40c1164444c0030910106100c09a401c400041348141007002e051880444101d041c200942696100c0e54114056030034000090303045c0c9000516100407a0a40c50000015602c0d030341581d0090040d0b400144080e8902102685142207420328043d140c503141750f0810150600030700304000c40300588149170300850380c0a01041103151903405001c40e11009000401d03114440c1ea0b07a40e0a2905128580c1c001c249596022020f05920002c1a988032920a640c1030010030b0601c1100241d01071608594208036208a00f01c0c1c80400611075641420b5000d803d4a250300d01000b000f82030209240141d80c020344030013020300e840d8036002500700d00410000d030401c40000344850200b000382d80400c1050307820001c201300008480900300464501c24003a081112420481c500d4020701e08000a081c1c4845a8428010b12221034942001d00d100307080c2a0030480020076410001c00c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 234788480 1250 234787230 234787253
    0x2d050c01110c010c0207060c1e061e060f050d0b060904050703050f06010905150a03110a12060506100215150109030506040605070306050d1e030215010b04050a050103050919 76
    0x4400c1c80210700a030301c4a01c1500148807048103902600d5441c0c0c0c0f07a002c201c0d01400c6034074003d4581100d031405800c003203503c0403980c000d21f80103400100f00359000764110321110411140a200c20340c0d55120400c601c9241c10038060160608403202205541d480d150b0b034010b40000303840c1d28030401c6041c010408000007008060000c6900105540c0610780c3c075081d20b51145800d200f4111f405062900003809d0b500042000402c60b040100099462415900c50489440e1240d540a40000d500c00f00400c0c0100c0c0b000429181c0d5101703820205840c9051018450350340c44481005042d580300d101030810680e144030126500511904000c1020710100300100d070b404913580d00260003805004180014000582c010602c218080d490034070010b42d80d0010302c80d5003010944003401c00c0041c4218100c0c0411420b031140e0b88180288106c400f541d0445801101e184800c0c3d111240380400001c08101c941001074901005100900b8204018a889030000784c40d445107030101080c01d01b04280040c208220140c1c107 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 234789730 1250 234788480 234788501
    0xc050606040507171e06010509180a021c0902040e070303081308070b0f04020f100e01080c0d0606110106052b020111060720030f2d0d0605012d050c01 66
    0x51001c0d508200740500a01942405c0309040445030800140455000300122000c0b43e1000d01142c00364080610203200344000502080012902000058007900030f40041440c890180840084c4070f081a01c100000c0b00c84461070040e15800404003080440d4101c41090b51041d61044030174400b015918050707206102c0c0707490003450314101c10180159031103001d4480780b0440c808d90729012019000d808114540d2800c1150100142100038084c182d54400c540607500016904505400c10440703001280a076a90303500005c0000c0c0076070000c812554024080d46005000c2918100170340101c840c080d0252403032080c043c0c003580325211400070444e449646500b0b40c1d04001c02c191126400d2a8000409090f852560f88480c441b00001140c4040300100c219848a0030740c0450300d02d40214114a0170802200401c1c40c0386000d40c114420751080c080030700034190b540c80344500140841c10600007402c4050b06640c80760304c1d80318943e901703401402000e45031144a003540c1040c0342ca4201742c800860250440002 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 234790980 1250 234789730 234789767
    0x9010f090b210603070e0a0c020f0109050d08070e090402010507050f01050f01080706030b060711220c0306080f0d230f040e0105060f0712110a0c080d0c050606040507 73
    0x102d5002e0080c03000c0d544050000300004041c2161155404c2590b5544180500c03045000d050002c10401131040c0c2c400b054080140c0180c0e0380ca0410481d000e030846891008c1070f1001d801c03101040900030342c440074440d44858107040c000041c0d01c0040214840000c001c1009040c028001810414000108604058085990001c2c8403070300e445d4292009030542840f52404511485402180080c000d010706000010007400c1503080803001c1d20340e020704c4403140038401d0b045034000d0040b41401101c4004420362448640c0c1c0401c07050103811008003102e005511502c0d840d0040c002403410b08401265030031009410380b4060411080381c0400c510720401c14000360103000400070f00185d00c411180302600032190b103426101c0050303a030345090040ca449590381c03c0250027401c209400000e1281070114280c040b25103403000512601040044c5004184141a40c2c0340320442401c101c803c05c104000c21100b40c2c1d03841d100503010482c1d0b0341c0550b82d00303014141c00d2146403900f0014440900c44c1d0100b190b00002d90b40c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 234792230 1250 234790980 234790987
    0x6061e0d0812070c12050a0c15060b070f0506070318061a10020a020910050112050c120f100b090d0311010908120403030c08060f040513080a0324030809010f090b 71
    0x200c001e0310314103004d1400c5132880e8100c1c10520182e40030314117640c010344842e16844296900d0740e490030360308030401c51581d82840c0e440b100801d124030b2200107403041c81d202e19042010b1141030b003800c0d031410000418500405043c031024030b08001c210402000004d910500104d040d0200c00111301d290f9800031049900070526518001c407a40e030001c0d000b10114020b9426810703503201c01190306d02d218158083c050101e94000000503010b1820f41c03004d6400102c0703908460520000b100454590301d400d4402102c03900c040030501807407036002c50000001301100c80d9168509007000000c00c94032442c441c005010710100402c0d1044000b4290081c0c0c0200c0e078840c03042692440000b41007004240160703801c1e0006854002010310440c01405e04030b0245030000c00d40444114410304000c0503102c010021804024100c80c90000160720f803000d0003035201309440105040004003008840303d00203a440f00f03944c094170075003000071503140f02c01c48814150078070b0161610408500162040c20b410740c401d000550000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 234793480 1250 234792230 234792241
    0x721020d02091608091b1c061103090d020727060806040305071205090f0d0303021c05072304050432070f0203120109180b0f06010206061e0d0812 64
    0x5a4140c90308400743c0d01c0b113031510b407103061080303030764010605070840380721640d100007031051520440c1d00300d510703000c40e50521803905c5650b03881c0160b81d078407452103002e20004130074030010a009020b22452030259100400c0340c18541003c0707041c110300c10001c89841c2a9401c0d07210103a043c940c1c00903001b901079501114601d00f402c2c038004000303600440c07090311002c42e040301c101c800903c910215210004010140b00f10111141d040003803184d10502c003201455401c102c008901c6440c44042c143e655075900000440707291800c030250920303008011031503681211144401151003a00150381c162003043d10b00080700050710a4103910030490500f02004c244c1e00d8286107101ea41000301091007400b00303554584401d600c0c0344c030980e03903030190f5184500201e927404014845016154404d4a08082e41505091046026100e01008079002c1d10020803294544040201558040282d607070046015a500d04a031210008402e61030380404109a206c1e0903161403203c140401c42d000d031b51464960f0f040000d69414103 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 234794730 1250 234793480 234793501
    0x6060d090b06210607050f16030c02031605061213081207030b0904021f0207090e01150e0405060a0f0902060c06070f02011e0209061201030f0b0105030721020d0209 72
    0x4440b054410090045003850110800207056501003031440281103540311090f0507515904490710301d005882c401d10408040401000f051a102e40c0170388c848402401d098014503040c022106012551610441010881d50729180c088841000d00031031002c400e40c9501c40d06c070801c802c0074a00502041d20201d41004090282d0320000d00810690f2400c105145c00706050292003001107034042d5102810300c0c0b00b0070805d15040345d00788481140e40b040c0d507a02502d81c0042401c0b945008214000d030307136581d100101505e0180046001a2840454402c0c42d49815590a5a0b4440080c0128541a202c0e0303201d4200d00300c1500214040c560007016182c43d000d040750045c1d6182e008541c1c1400083e00300000500541c010710940c8624202404a1802a400c0040c034030047d40c010a00603810500030403646840d0b0b1110440d46019602c101190203171036401e402e0104071540183c10452103070300418820400104030000003d081c5c5880f40c8454001c0480d4000030303499040102004c0d401c800701d04100a82c0b50311 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 234795980 1250 234794730 234794753
    0x70206090a080906040e0726010308250804060914030a080405010f12050c071109060306070c05070e04110a0603020a0e0405130f0302030408100b0a0b0903210a0f050306090103060506060d09 83
    0x1c0c1401602358858061019100447d428440541101d50800406010355000340082c0c0d8940515014183d8a070181c0c2d8688c41c441e0f1281d1300944c005041000c3c01c0c082d0381c148c0010340d140140c04900400281802c0d89034542c041c480d80c820340381031000c807950600025000358ac6148205641100401c90b91401c05c2d8808019030181100b01e80c280b00c82000810a8500303020081e0003080f000e4010b10341070356104000d80341140818002e0b03a00d031107030b1540000c40c40300e21801a4403c0384a041540d09401404c82482582c2542d43c015005250040c0300820109074003032110001124203e5000c2003e4a8843c41c1e90400d00140d10301600005082d4215820304da000001030040b81d8a0004403080b410328500c00c6422585200c0700749070b0201c1004001c0103080d400380043c00c2140c80041c282d0346100388081403004080c02c1100492154103022680010694110040780020545406cbc46451450403400040b005e1005010041c00d00e5034800c049401620341e03405544260304c2c0140304000140c12410800407802 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 234797230 1250 234795980 234796007
    0x8010c0504050f181b0702030a06320f0c0d021909090e07051215010326040e13150c030f3204020d02041a010206070206090a080906040e07 61
    0x80305400d40e10800d003002c0b42c0e400380c10445407411040c20f407035089404c105085e00a41c4a8200f44082c0200f101503601031090005062041d100001c3e00c0300d80a41100d8010242d00940448540d40000d141030078110202c45a030000209100f50010399500c20160ac00c0d00030301003002000780c4046050280090050300c8a0100241034407481c003581d0b681c455100580350010441031158000200421990800d640f00e004c0c00030a034810303900c01d10000119105088026881650280304400c903254030745121644800f07411004007a501e150034240f890f00b020542c8040c01c0c001e001844900c1c247d00b0f02c800c8030303103054140e100b41c0340920041001c04002030160100445990000c2e251000254909a00020006200030340c070b05e0038100e071481c903500c0e0211071500400503a00b060b0f0503140304005907118491580070b46214444096000200d0380024a0000020654810f55021109008581000090000c151544007030055590312400011881e80d001d0740c0d211410961007407080c4041141c00100c06c80342030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 234798480 1250 234797230 234797239
    0x1140d060317271813060509030301090615091203020c150d1107050c10032004060f080601020714010201020f1b0f03040302090711030913021306090b0d02031008010c050405 76
    0x4a107000701071030110b1031003d0281d0300980040018400c2c0300030085555204c1c504144804540e41c9070f898580540d02d04440d00181508000014814003a09104e000041d00c1d0321301002c1c0b03886a041d0b00241c00714101380158001c0140e810810300800d4401c0100c414410009044000d104096200308210740d0410243d0801443c11305446854006002d400d032007070f654110009182024541d024801000710340c440d9002050b40301d040032100c0c21880c0745400d504005241d809903441d850400c008001b09035028030721082140c40700600155a81c00954032003a1109582900c10306540c2c04c2c01030340288245034130810403d00102d4010a025001003000301014501c80540354503080031301d070154882c481e60200070340c050b40320000302c0c4805200e40030803810040d80b241100d190113a0040040c0e450040c0301d99078800e6a4002036030b5240c5205d19000c01005140340d08058460a04158083c1114001c5440aa50b46640400001d110f290b06921800081010000130000c0300c4084d1002491980903001e0103024 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 234799730 1250 234798480 234798517
    0xc020d020c0607050706050c0708120d0506090f190f060e01061e020d030b0406030609120e0a06050f13030c06080a060e0903070f020a05030304060305060901090204030201140d060317 80
    0x550814500f160340459202024010050815800399042c0c0c20000d40c8111900c1000707008100d401003044018000c40c1004000b42d102c1030b07489030300000e82c4c0004104500801d950400d0000c2d8900034401184c121039105001c40404440050000060150700a80440903050036000a20400c0030340c4054140c901641d200c0fa4025132103144003c02e0b46441c1200d0700140c1c0311105945015110368130030503824000400220390956640c55a07015514200c405a91801103080c048403440d4010081e40040700003615003204952900c0c2c00a84540100c0e010780e00d01c40c000040400f4800059072520380503503444526901705688429006200c290103e42c00950240307400c8001c40c0085140340312920412283c4004c41c5448525070700c000111103102d00407030b0048426100464030b5501132016101801e001c0d64001454544041080b00400060b4083d003085481000140050303640512402e40c005030b420f01140e981c541c47c0b83d08200030001580b0181140c810102404461042c83e0020300b201c00b00c50111480 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 234800980 1250 234799730 234799753
    0x20030906071b0b090303041703071202030d0f0b010203040e0a020f030106020f0105070e0d03110a0c090b0301180f0803040804180b0139110a06020f0709091a1503010c020d02 76
    0x141e4072130300e030325550706500c10f00042000d4444030440300b0708401c00e070007980d081c04601d6655580c0d0756690199a40581c10201d0f2038040d9003070782e114280c0f5440d8400001d05c01a1042d0380080c2d1244035500900b102042135000040e40c90f0300640440e444442001c00582c0d076583e54200c020344034242e40801d44000d50a000208003401e100d00f106c024159002810f6000c0d80205642c2034841e0113003082400868061012a6004030380301010100003005030000110301048248101401c4486407543d480007907400304000d001080c040624031103001d60200351540c0ea03032240d042c001a980540e074400d440c0d2844080c0300842141440d00300c54407d40c02a240d1040d90149445115aa40300f15942121410540040c03981c0f01041803031403400941c00f13034120400c0d030450213000c10743e0f025054001a01585c4500d0420f403413103100700700080041c07200c0d090070040040350b980c407650241e0701901010035800081c804158000d81c10000c100000c94024000c00882c80e65400194072107100c000c51030702501031015001c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 234802230 1250 234800980 234800999
    0x2010e16080d0c060b1216120506060f1206090106030201030e0303070f080705092106071403070332040c0b040501120c0c08030901090c0b0a20030906071b 68
    0x40076114440003420410780c0c014002c079140c14005a0940d01c254036100c810055480311042401d030041c0c03e41c080c24003041c0b280c1f150703600e8950702c0e07004810036240703021380030040b800104400c0d402c11300407580081c640340804002001c03880051320140d0ba0340214428017907206070540c846401c90307100307803801d100140380d608481d42c0380c0c0001c43d1110041012480070102c40c078420a90194040f2a50400509003e5030201183c2411601c026400d200b03e0b52844403161250100080c0780d10421502d0301080300c40c42e0503401442404050060824507813038950402002c20001002d0086000710307070002c0b50000310805803000034401a54165410300610300c0100b0074814601c01c480c1650010f031500314180002c061050010268403802c5d10070084100000000100f900d00218003d000f8540089000440760805042c010040da00200b0205010044510020380294440305d1325400c00101c001c00381e840c4400182540315425150707078011000601d00003080030781c24100c401d0983c104c9480385100d88920088 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 234803480 1250 234802230 234802273
    0xd060506040501050d09080c0d0c0203010b04020301151b1401021c0b010e09040503070602070f050105011e260706091410081602030d02070303090b0f010506030106051608040602010e 80
    0x1140004c00030052504501040c0d0043c0843c94451006185407101100405042051074407a203000689200140415490240900385c2d40c66400c0340c0852455140034010201d150300742c100d030400e000c403244141040c001900c000ca008030b5041411650440549000c1c41d0003980040420355102c40b03c28540b41c0c50b03801c18428490b0700d48041c0c540307516150000042102880e0002d10449151104014440c002421400070b002c651b482580d441c940c0e0195450110309488058001c0085002c40761800b200c1c3e032410360b2224080b41c40e1002080e002880c2901c94082044101c0042c3c4c00c58410120b0015001394000b00034004c03590703036110389084454110104412034088540f0031000460120100316072041701400c80d010f104550048a182c800004819420f0380c00040d82a00800d55629641080c80034807901d003507118200d0341040c02e9541c107000015041d8001802000704000010a0881d050900c06400b500030980200da055101c582d100c4000f030280540c040003418900034840e9a814907902011034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 234804730 1250 234803480 234803489
    0x1101060303081f0312051c050613091110050408010e010b0d031b0b0a09170a0c1401090b0c1e19030b040b06030405010905010e0f0606040e030910050d06050604 70
    0x84040343d0303c40500344040302440041003030140c14807100020000b0080c0080800c1c83c082519030170380ba01101c60382c01c09060b0002c2d004074040c0381044100a50b540c1c85c0240c4401381d00403000300160641c5141080010f9000f451402c07900010ba010000d0310040c0c1000c0600100c69004000f400060799411b1090f00f61428183c65540046142c440b07038002a0255141030140346080320246103ca007183c85030424280302359918a00139503143e000c00c049c0102002900000070b40102007900e068815000180303580d4801c400503202c24032110a00f101a603080d00701401403038000c10480b003181040c0c02580ca071b5501000c440782d0301079000210040010407800c162001c5c0007000a1020f1a0b24000c07009074040c2c48076424540d03000760f4901d0300c0030090b070302c0201071400759018000018811815240581c2154400304005407036a02c985511707520000d0000fa81c2e0341c040c03c01c2d10041102071004105510350300400180700c0d80018000d0b480021180c0c0400540400e6003003800c2401456507403c18000c0c688941c1c0074 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 234805980 1250 234804730 234804737
    0x203060105060d02120f1e040308180c03150603010c0c150915060306020912010506240c030318060c04030f0303021308010e010614041505120a1509031101060303 71
    0x10405890104043d15440000301005890410000c0c0c03110b405440443e03009640030344290602a50305114004c40c0d00360000c161040015003081d84014040e044010314146046074034103a22098854188103140b01500094100d40340c241a0344c404244644045510a000e98030b0864441503162156030102c2140d904500008401d9111140c00b40c003500c01201c040d21031464403603599891901e80c5c42400021400f41400584403802c01040099800112550107901e80c1400c2c20310800703540795880c0e102c8170a5008020080e298001c1d10345030b5240200441c180d42030002004003d05003440b680c0c5140700361034980a0303c620780d03952011004280900e010103010280c1100b094800039002e036000f41410b2811444020100d603a071456a400e60f0702e164480c86069440301c500b0070102d440043c170700355039032004c5506000c03a0020160700707554400c0b40d200300c910a1984003c280c091590600c100c0341a10b401211a811481c030402152004d0501d00508030002124440c0283e024076041c0700b0002980d50655 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 234807230 1250 234805980 234805993
    0x601050904030c050a02180a0f0605090105060703020106080a2312091e030709200315010804020607080403110a060302120106030c0203040801020d320106032c0604110d0203 76
    0x102c0c1198003640100c811240342c481c4a4000c0d0240e81c501d03454850b050b003040c009203940d1601030010400e4035080001c10f42014140a4244400e82d81d1200c9503055420a80d007460700c070031040c18100c0c090000c1c0e5216540c540a208000c4041c000302c00300c01d0b0440202c080382007441c40110104542e44450000c00310002c52800c0c802c850440c9414002d0203c1006c3c0e0039460688c4001c00400203040c02a00d5001404030795851102c24031201c400c5140452944800010034110314041035181200f05240e0151410007100c1000101150b0300c0c0410f13a40c078030340c00040054940b0b841e4030305440134188010202e40b00d01c039200c00005446100b8001c40b026200b009000d020540d103052400d50142482c1e180c0501540018800407400c030340b0902c00b5004011404401240703504072031030040e82c0c00512080021006050482c56400c10480c1c9182d80e044490074035002900b10043e030410040e41c2c3c240e00c6030004d8070002c01d038042420140040d005006a004400c02c030540000c42041060710f0003945002034042c5c010f071 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 234808480 1250 234807230 234807233
    0xb0402040f060b0c0a1b050d02091b030a02040503070902040308090907020309030d09090606080c12072d0f1803060f020702091f06050f0d0203060109080f030901110601050904 77
    0x1900580c405110250001c074149071281c0c6100c0403900003010502007030b800385d40410284802050000b05007071400d4841d0b1102802c14000c01c16101d000c1d60064010400000403031004190303400b074032030781400314280c16890741081100071010b0751040c4601817003841900f80100d0a078a403442141c003121380c8607003074520703010400041c048000001400f2800758003050000601d107880900c035003844070340c041d90f0701407410f81820f1030f150132126aa0407201c00c200f1030600f00030701d2110102c1101c012417003584010074241d60b5044103c606d11089405100d0603002400c5091000041120031041c15445444001c40c0784440f0102300c4610504418010181c286080100040b03000355103d002c0d00c02c0d1204003d480d0440c940c010824908066510a8410481c8001d40540100380031004e0302520071403810910348000103070022258001d420000f070020707a002010075816801074460708001c0846409070361600107461015510f9802801c040da0102e606207810584800c1c1c085642070586800514507a0070f034556 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 234809730 1250 234808480 234808489
    0x1c0503150d08040b04030203060a02040503060c030421030516020105060f010f03060302040e0a120302090a030222050901020d060803071208041401020403050a11030109171e16060e0a0b0402 83
    0x600c46264014a4244548000c1102c1074018000b0380b201c41c103001d42c1c0d5495441410b140480003004001080c0c81880148080c0c5d4011540c2e6403c050380c0c011064036074440342006040030906180164000c04080584529070b501504a580310307202d444030070070030b0581d03a100903404e0b90b40c01ca50246d4000503255040b0382542c00741c2d0709034025061078900010036548983c0440c044070103038110003c1d2507004a007400d00b00040900040d0811126290642c00c00b4040030105011300381d44c0c00002c1c800d541070b41d00f01354012200180d020480301600e03000d1200b410804040c90003548580394030006603003094004114240004201d0741c2460788540c4c4107520304827080088175140c1c00508115810305c01c3d1240358010060900107407001d54019005442c640c0900d00d44426102c1840380b405001e0703410b0049440c045200f4010420300c0c40c7c1004000f540d03454075903030000c80c1c2c10b8480090b03400d5144d01003010591200130b603060141d030910481c0308002d0b01800c40302130342d034801658074002e128503c00800100103081 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 234810980 1250 234809730 234809761
    0x5072c1504080a200613050904060e0d03050703052a030a0612060b010807031b031a030a0c05090901020301030c091104090c080f0c090a141306080a03021c0503 70
    0xc00340c031103040c2034070b80181906081c4000001c1d6001107428200d900e55074200c4045409650007104c250b8607100c0140302480102a1910800f0704c143d408500180c1404010b40004114203000e0003501c150a14082d0054010300c02a100b00b40042d03d004000740a01000380d901002c0e1301d0030304461201c804500203034076005a1004000900faa0344901001542510b00c612122403d4820040440c0310f407000c500040c14950300418010030036041922482800005240e0b203c0c07040c42c4c0d032601080051a00040c011644054413031147c061003000c40d80001d12120b00d0807801910303811680c02d407080d00c0344048a4240d01080c040900355410f620340c02c200c03000d1141c2c000399907590f20040080c10280e44d81c0d0704001301c4003c0f41c41030700860510410040c0c034100801045510200303a40c0301c04d04101e600404100400c02030f0044d452080c0400d803030f01c407080d07845441d00009800e5054045c0003141d1903100140d181c0c860b180d0b003103000d84600e041c40c0310030046074101080d00d0030142d40c03400c0c2541e481c450001d0000c0d0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 234812230 1250 234810980 234811009
    0x10f050d0f050106030b010b030f0702011a0d020f06040b0705070909121d10080f09070e011206021605070305060c031605070f12080105030c0111070b250605072c 71
    0x1983e0784c07000000039000d440b0560003820701411241e280e150003a010141c40c10700030600c4085914045c66204062140c2482101441068540081400c410301c080390b07072000e012403031030381c0860040740c00110196100c000742003052041c0c0940e40c4081d27880b1010015034a40100060444003005040e50016128541440c0200309403105541403103900c20219120025002e141d1000507003203000c11182c480101d6030250070802031002001c2641c0350510051405006008115400d10010034501c28450541c054070500c102c0d1545542c0400294586640e4940f41c2c1e100444031805500c00145850301e00d502501e10420450720385550a0403032080484455000140448050301d0042101021410b03501007101643c4450b00c900035694184010985407600321810b060401040384010412070201050810890b07502801d255217680b54012120600218000c181c140301e00f4200042c802d02219400981c0103c015894500001e12500c060b586442e01a8074942c0000c0b08800d046415414180000c42c1500f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 234813480 1250 234812230 234812233
    0x32802010b0d261c0221040201080a0c0201020c0f1501060c0b01060309020d0f030201060f08030a0905102001050403080f061c1118090d0e0901060f0302040e1806010f050d0f05 77
    0x6000310001d42e04001540c2130189803950301240c10f18008000d400c1d01d0040981400f8680341d2880c0a0740020100c80f802440786003050f440d83c503100e1086000350151144081003505503403100c0d040c000150368a07124100c0c515042c0442e10000264180269030100c0429003158010003103a0916805401608042404a07041300c5011030b9a00845c013107284000c84540301c4c0d400403814904e0a01c08140c40031310707900030800300d8100700300d8086c0076a00199214110344094a524040040000c01501c034401040483c403401d40e41c04c00d004004180651255200b0341c407946407217503591100d0015099541080b1000f9400904140c500c4801c80d800d04000340031148203801c410807071900d00c4081850200f001d2642c418001009003800031004081c44510100b055510341000200c2c9904001141100d040c0728510601c2052052040301c544a9011a8081c0002c02640002800c1c03080940151300c4202030a014603018600010403031405810603503040710340040264440d035600d070710b40c085c900380040412941d5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 234814730 1250 234813480 234813487
    0x312060d0204240501020613061e090b0901050907120f110a080309040b09160c0302121801020d181a0c0106090b120114010303080405032802010b0d26 66
    0x507501c5004140302642014840f1100d0300080c9240d10744010720b070300000d05640040082000345c12001e51040a003980010010490001d103031500b098481c036284805010354140741c480e9080c40007005071140a6044031000b0040341d80c40c0ca0003e030b129406d900840180d44030100b0070801141d118625007480c03174094410f00242202d00c10018120881960180c0c10350b0300041140c40c1c40389001d01c100c5c072450400792a031118501d402d407046a41140e0701031143e402e02507192200300516108200c20200b01c1c54a000c62542c4c0d2514124980d1084030b000300701c40c010b10910b0003956403a4480c51140020150441c1000c40d50ad04000e85011400c1c08009103c00307811341408040104442401030000400040c540003401c11085014071034030320121801c410305ca80c1488507007440180b0b10100541102c1d05890207020325103e51038010300354400c0c00340042d48100400d03031504100b1800c03c010441c0d480c00e078008003d10500d0005210403d210410b020301080e1030004403201d5090b010080d0b41801c052442c1c2c2500c1e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 234815980 1250 234814730 234814733
    0x503071a12090c033405030307020418050703050120180103020a0215100314060415180f030e0316050a03060902040e030f0702040528150b160b070c050312060d 70
    0x5005c0c8032480000d5640205c040d030f1100d01201d019100308080700525075009550a042c003190703070380c480d902c00240595a81d07a603041d020070380b1344c4034210059400b000756040c15560f4180300e406000c484d40e440002e6012032504100d0784031000300301c4594030209100c1702c07101c2041c0c4006500940100000d40700354001d0848041815680003841841425001c1c40c81019a0440c107006407403002602408109510501c14000856144c1d0314955020700c01820101d484159510020b00d468402c080040ca40c1c500600110f0400d40c000070980c00b81d81040c3d08807039810202c1c4162460031800c51142c0e40d001101c25105001107003850f01300658a600103800480c0021140070803914560004040b82a124400700b107810462805008a82c0c12000101c120503901d080303070102a25070240a81002456550f03240c1c8a05000d91401d00315000307040f200c1a03d9140d40c07034800104a04c0d0403c0c5001c4625080b1200000d00540c0a410382c6443c59404c00029818200491603828041d040074015a50010920b91402c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 234817230 1250 234815980 234815983
    0x405040e01150503071a030a150303020c090601030506100e030a050d02030d0b0a03150e01110a030f180819091a0a110718020f1905040503071a12090c03 67
    0x24000c40d02040000349524011180c2c000303803001600300d103119410010080240840e51902c0c200c0c14120003002966985568000100911410641c2d20f03d01030404000410305030041100c035400d0b5410790300e0003000c1e60f0f068011822034000f241c00581c0443c0140440b000284107604081680e5005000c40fa401c04898840714501070250303031a400140d000150440d003103150750182018071401520841e40c0c0b0380c02c5903907803540e401d6103080038000c50b0354a000300c511003c02508504400c0c1c40540c44e07a940ea6900180040103050300104601d80300e810140311603508c24890b0841c2d070702c064200c00c95a090121544020b880c00540c20144020091050004110603143c0404a004c4c582310796070071a500c0358482c401500540381c810701c0590039009607004203c141d5008000001ea4000c0c0c940040e034030000c1380703102545406005000800c51308045503038003000b500400204113031740d0128200c81d00142d55440c0c0b0b48158103115510610400c1c184852500780c9200c229164000858509a42510760f2400200f03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 234818480 1250 234817230 234817241
    0x60f1c080c060a090c080a0302031b0c040f0c201b0111070e040c150905060f120f041a0106050706020706060b070b070e12190206120c03040201021005061014040504 72
    0x1241c0c1caa07108180380170000e00180300c0004007400405020005450303100a1b407240184514003150324a0b4084101d1500005c0c480040b070007000500400450740307071000c20700007081078905003004103001100e02d282d412002a100008810040e00922905405059070400e07060005c00003070600c0342c0300e2400c01b900c0d0814800507000d4400458501d0280c5000c0c00e1011202d60103038031440c0b140d41c610486420555014102106880c810b4403440c0ea110001c00c04846c1c01c0c03003520000c0b101c81a0709020311541e46c556000090155018191a200d2255a032030708440103502841118041342082000c00300007649a00070f0581da40c000c42000a42c6907a8500d03100003580102c404440f440710510403c100a6044010f0f400300d00d4080e6110020002c0600400c2e40daa10307401146441500c04d07010000455842000b20b580d558443c4901c00540c1c00c040301001d00e0b5800c241e800701c0c05405020106e00c1a001c144c41a10312603500100490040c0701c000c24195510741e104c06210901c4402000b01203425112030084 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 234819730 1250 234818480 234818491
    0x3020a030308070f030603050606091008030a090f0b0a080703051005060301031104060807050a0611010b03030a090609050d0804030209071403070c0b0f0405071505070f140105060f1c080c06 83
    0x542c1000d02d00b01600515042d1040b01003030a040c07911000707102003200018001e5000d58255800c078010386484802e059181ca05610024081c8000900031002580c0141c4c40403c40e07458114500240b0f46030042e05805001d2000e1510014a030750000400c024429003181340c20100700c29900c244981c541c004580507a100f40c1050300c10810303600000b032081c181442280c008105003000703081414109000544101c04c0c5214000070400f014113950a094405c3d031048881c440020100d80c0d803554800d03005040d00909110b2840824140c482c0000c07a418850780320304040f54083c0b0050301d4907045508101d9490400f0309044100a0350114031544042c4503001907000d1031041d203894848a08030b150443d0305400c0145100055510041400300143c800240d07481a01c1c07d4002c16010021982d5084403540504c51011300141c03001c83c1003205200061007141d209108410090105580f0394050150601d085449540c0116a601d103a071450046c0301c0c40c64414500c41c0300080d00d41301058040f2480d241d0180c44 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 234820980 1250 234819730 234819737
    0xf120a02090112050f060d02030c100c0311030a02060103151803091514090402070f0510020d0c0309030e01050c01021c05010e01060804050307020915091806070e060904021303020a0303 81
    0x42441032581c214085452604003500148018170b801d0070a40c42d108800b505507170013030a41c00d07582011503a0a000c0c5500460f4050015851040300b008000e0042c1032200043c3c0209011074100c480b00310b8040102c8914403c0c64004012030703441c41d030380c0e00400c40c20201c030b40c031800d9a42c4480a07801103103860360700503480c066130f20440013501308103501104580d42003c10f01400203007400c5002c80640384c019030b40044001c070350050302e0f00080c0c28080d03624802c03100000d005000b104034585443c0040d80c003a02498480500411284001c1d020540403a03450103030140120b17501980c503038503961050009001043c1440d001604050088924500d44244201508407098680c00140510380400b60320f18014640d52525410509054690946911401c0c0707010b4000d0340800d00140030200e503202045040c92014103454401c1c0307010311281d078003a070324000c3c2c401e1140600700100d0f2105108014005980720002c120520b0087c0200401c0025400b0700ca04002d64402e40d48000302596810074a100114001e40303 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 234822230 1250 234820980 234820987
    0x82d06150a090b0319020a0803070b1006080906040b07050c07090b150f0f03040c05120607090501051306030506040b030a05060708010e010315020d0905190b010b0a0e01050f120a02 79
    0x3000c01252400d030703801030044640b9140205545030781c00100c0002d14120102d07121884c19075070002c207420440540000044d8440000ca050801035072000e000d20590310b4602071140f05807551002c58040300c0c181c07420003095001c40042404107190103116a040103041c01c2c4a0721301280c1d01100e41c103124190b404682d00c1aa141c45086460502c0a0001510104480468a030a007a103070108034500500030365244006c40400028104035032044400c000d0301004000c17a0000100711003071030f9100070803181e003000501507410002e080d50154090758441100c0c0c1000c00c01107410040c0880040c58000c05c200c8e4820340380c509082d083e403030601600c1c03001ca008002500b220715100078050088241a0300c001c02e1030407048010008a005541c00200018000602680c1c0b200c40301f540314068641300314003416600035030f10710041a9410382c10b0700d020f2038030034035403205a83e82c4d0b00c2c50b01d200d0340a25a00e03c0301080c49001040441d600c5400181000105c0d4007140d42000c2c24070200c814801d100316150380d240766001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 234823480 1250 234822230 234822271
    0x50301140112060b271c060e01060e0105030d090510050a1707020307030906051606020705030d05010b1804050408030105190f09150b09030a02010e0d0f0b0a0b010504082d06 76
    0x170907500c03a00c0c10b401e5511000159880b404521000e200581301c0c411404281e0707031002000b0751a080007030a01c4d1543d0007440010340381c6002d40100ca00038410036109204544018400c18041c5001d042200d0000748868000c00c4441002d1300c0d190702584251040180c00d16228031004111420240142010340c0199110121481c0240c05001ca80d0400d40a1004c14080071240c04041404503030860b07400500540c40d05c01e5468410320b14010715816281003414800081a0f0300f060038043e00c42036217000c2c6140d11100c0c402091200f00c40c0143e801510400303007003006210905155142da001610440b090446c090354501320f140c00c4969075000601415100c2c0c0428500780e481c40c8515004c1d20002114601e0b06000c18006a951303008a10020705100603505812803e5640321046102c060300501c1031001810340c0d1800c6251020221038500c0c2d81443c0c1140c0c40d03c4c40d48110151401e40b1841c00c001c2c24204000303003d06400c20440109245d1002d0400304c440ca1400088c0141030103031078101c0c08143e219856 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 234824730 1250 234823480 234823507
    0x2040b1305120703032a030e04050a02040b0919030209090f0c012d030f06030b06190b07030804110402040303030519050702120c030f0403051e010507050301140112060b 74
    0x15988114450070030710301c582c41512404a00b600880781c0c103082c10412248500342e01900d08114030100c1c20200d1003059a40c0901d070700301c01c050b01034520484082000b0b0340c825100ca0224000d5004074102d01405024600d00e5003026410889c0e424201402006466900c0d0300154007202e00b2525090141c000002040591800704030003a040002401d140d08907854100a026100701018000000d0100c0d8488410b02c83e07019900900b03085801640500010351a4100900640e03825181c040c09028140158506480a100b83c0300c26500b514600340c4c9000d081d6182240c40308006002510502c400c00c90f11704070f6a40e00d00c01400210700c41d850119140c580034100d03031118032003c800c01d92124240000c1143c0755501148000c82034826800040e00c0360b0040300004d1550290321801c1082d0100040c000c000d000c00094496001c8045612610701d8444802010b03007a078a0550303590b000f28500f4801846082c100402e1020301c004103140400c804594440f5507426502e46138000484810002a1000444607 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 234825980 1250 234824730 234824767
    0x20a170601020a0210031d1903080a151814130303050604090b070c0c03121812020a0902090117040308160504050f0105030c0f0c010c090e130b060d0602040b 69
    0x90010f02600d010b6500460180c54141c01c40d0000c0540d92a8031090320300c80c19003040701c121400400c84a11301c210803070f005100c000148065020410441c0010480c2e0054041e00c250000041c0300ba2800c5481e0003d1104840000c660700072480352601000101042201400c0348540d500c10102143c6603428207019046a20150519001c0c9040a0b0b01d400481c0313401034102d400031071601c1d02820540582c00c1c480c001c3c03010740d040100001c1c3c490002600c1a41e108820b10100f900340d1408508642d9280c030b01c1d0f100783c1d14020001b0341008401504028013101c9038003070030f100e0a0604140c0c2a40043c00e0803105002d4045400b01c0c04540c200c414880c001030590040d550101580c20704e60718190905002614001da1016214104103000000071501130350f050903543d90791401032699440d25041e41056001e8040c80c044000007420700280050880300000c08540610840c103c0300448800304e4403211500000180403c0e04203090303881120010b03c131480104014411001c07201c1d21800c1c070f8026291841c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 234827230 1250 234825980 234825991
    0xd09060204170d090312030b03030c0f0c100c0b061512010303020c0109030503030a0e0f0a050f0c0d030f11012706110c070626090607140313020103091401020a17 71
    0x24070840b4100d620f00d4002001c038040da500100380aa00c0d0381c206100b180078120500c034481c0c05000c0400c04080f070039000a1031580b164412429a0b0002618000380704a0799402e408840020b5984103850000c00c10000f0050b03008074000e440010005003030158048194080041c0320807005000b40100103069043c425903240d0542460703d100311500e0f42d29103a0b0703640405085400c41d983d035503070b070901805010800c3c41d03d11101e01e4250752205100d4100b85403200018a1061f016004625184009185c040b0350006059855142d100c0e00c0303d00780740125480310540302d4140300c56607110126500844c0688d10703250000c5207220301070100308d00b074580395095850002c00602a118207000342441020085544407d4032080e01c0d18920030110752011554014050491400d60004901130140149011942604c05c907295215915550740050f1102002e10017200e0305809640810b5503a00150321903041301c44070600800c821504500021201070032603100181c040081005501c0201c0c02c04600111107600c0b1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 234828480 1250 234827230 234827233
    0x5030303010f05040506061312210503070e0a09060b1c0608070614090a090608010c0c030e1c063303020607150e12211504050702030d0906020417 64
    0x41d45000085290b9107154014984119200c800240603500c40b50700b501c0070018200c2d407140f0010f0391000341d4611904104030a80349041c150040c0e01c00c8940240c0c09100d00c0681d603450a1071640c8042c011100c5082d2110300356401800c030200010442c03c5400360201070710310401c00d80d5807481e845540381170800421600c030810381d0170804104490f28012075030b40d08560650520000180c09082d400c0d80b180f0480c0000b43d0303c000c00000100310307507400e0762014054441d000003c0110000c501004e55041d002e83d40c0080000381110800101414a00921520103c018278400419401c66450780c0a880b001c0040821041071080700ea009640c1302c4001c12003a45210464620303603815600403403694424840060100c104801c10458102402d42c03080e0034011030fa4090b540350105442c2c1200341c80d0701c0005d0100b0800f695403200b0840c0381c412403020b03001c0c07000c050b452080e61502d002400041d0400519250070760009022202d030349030060041076001840b070800140d80740c1c00c082c403000340954051502c641c0da = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 234829730 1250 234828480 234828487
    0x10606020705030a0611040306020c010c08070309110f040b0a1707051008070503180a050d0e12030405090901060e040f0b01090e101a03030f090f030a02130f1413050106050303 77
    0x42e034a0101e04503031034541112020540a8141001e00c02500c101d900092016200045032071030000194022014050030356074101711920364660440560349100c8000d090116694020304240c074000c101c1c01740c05100500080792149030100040c0e4a030500ba8040080c600000201c64841c600c2404900b02600b0110703051400b1814808000b801404010210010703c4000004101c0d00c00039070040e245042802400c0780c068120510348640c4405c100c9202c0e1020400c44540440d082c074001c01048140440d400c011810245040108035245401802131504c0d9581c5540205480d0a41c1d85098803450042d68111001022440e00c081810340c16031111004616060700e181e0000f0000c10b005000040c01140803601040c0b0214107844020142290350345072000041c80190301800c44007800d00705074219007003881c42c81c1203400e1503240c400e40c07000250300030341428031410705104581c005450a0f0f0b80035400a81c0a41c080042d1542450580384040015441050ba9040004c24066400a000b01390301440c103 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 234830980 1250 234829730 234829739
    0x1120213082b0c0305130321030608031c0b0a0b19020316020904021807110f070b030c07050f0607080a0f09030f0f0e04050a0b0901060318230d0801080106060207 71
    0x4800209001140411450940c3c141c24107100780151031070b5100c1461800c04903940ea1501c035032110740c05144190252a21452044082d0183c42405e08071007911b409949800f4400040c080728400e8130070480c01c1c81e95583c65200068560901800190821804281d03940150403011401c5400017036813501191700400485548088158201030420741c103942100f00354842d440020902c130000c140407500f000d0b5040c1082111a48402e0307442040e0010010f81c1c81c4070442440980d1140c010f8000c3c03240c035440c01c1002c81c3c101115a401030200750300071802c1d44d4012200c0520541800e00036036032600041c50440501c02e0700c07503091056a049000e00a0b040125021990740a40b1502101160200740280300d00403d400a015556880e450301c0c00a00412907071803c0401c180007014015070050150400c1c2c00046000d41c0a0300c11407a1500740c41301c5503000e41006980d041c407495442d0318800561113500070b071440303014010009071501540300c0e200c1c0c451640c180704682e821141e10b90302050465000030800c00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 234832230 1250 234830980 234831043
    0xe01080d080c1b011e060b0f0c0a12051308030a0207050405060a050904050d02060f0106120f020415030e010b030307020d02060a0c141605010822020112021308 70
    0x84200d6400e1a6105a8541501e01d000303000d0030034941d502c0c22110041400592041d0310880440050b41031114089a180d1154021122107000b03203442d240c1c003042004c400d0456040031b080901d03196012603044401580e41c10100c82000700040c00071500228180c0711211000903084041c280003c0150304061017500001c5d0b84441e03601c1124065555240400e0341510351028903400340801428940c2242064074007513549600e50794080d0014003e040105090602000e00141210200e64a4061207255078440740010042184080700e459800c020000e800200ca0300440866002514001035482c2021112400e41c0e000125481c481d0b0003c010a8005030b584104d0881103d805840e000e44a00a603c01590180e04075000900044800400040882c20009014590035105000390842c1a17445005582c0c07441e05440c10340c40142c1014260a4540c02500d11403082d81c01490704480038008822240220fa000381e40d08141055030780c03000e105c8103e041151042c01401791480f00194001459480c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 234833480 1250 234832230 234832243
    0x162301080a09110a270b01090311040219030b010e030102030c040e0c0904020715060801050105130903270e0105090609040206070f120909050603070b19030f0e0c09010e0108 76
    0x141d59524003101050003003155000c0d02d00880641351003503070340d2285c100842603a01d1704c01c00c0e401114005001c8219083c00d0244058030601a141c06a2a905503a0346c031101d810010030044e0441d600b4400302c1c414414001490000701c4280d1000262540503000042440304141c503418002c1e80108180850320300007a003150304807509803a8020745900d0344010640d503442240c0038950f1207030000ca049024808900a4103c1d160390681041011030399419603a0300740d0300c0901c28558010710307291040440c5045ea8000703004840c800d1800c42080e00c07520400103400381d5222200f54040034a0403081c000042c06940c0ca901401045601401d1841c1c5440005c3c48400010002401000301140b040b04214462042d00210f070f170301000013600403100000003410300b04103105502540d0700300f8000ca211818082840e1094034081036006203408210202c80e010710318108203003400c056803240580000c41d004c1c8600005092003001515202a0301400c0011703520068204e81400e00c0c00d58010804000005480d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 234834730 1250 234833480 234833491
    0x5091906060806180405061b0f131d010305070512010f0c050a031104150c14011817030f0402061e0705010c030608032104110603040b07030e0c130908040816230108 72
    0x10900002e0408440785989c040d2071031031010010f001c21600b90b00000d051110082e100b03204c00c2d030f030071180d2064248002814284400303410f80c0c02041c1d091185040c01519403c01da65010004510300119003c61411074500c078030179600140010503034020761680f6029640050b0a8192500e0a150400c00d0810044100c18480c000340a04110850108541ca514041407820180000c21200741801c9400c0350800561808035821001c02004083c100902030a5034080d0782010a044140d980d0340c1e00703120a6520507004811070408021070040025920401062100d10641c0003003200113040401600707940098014600700d030424000d5031140c100340f0801c250705038040ca03500381c440d40311303810310410030609040040c0d08028000300b0031041c00540c12041d4012641071b50104001500c4216858640314084030340c1c1d45c400e110000e1101ea45119801c041041030180c9076052a0680c0d03a44620300d00007059030411600c0d41c0070700d002c000c1c002400d42018960303842d0348842078034520110002000703003500801 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 234835980 1250 234834730 234834751
    0x301060311090604060f0605040302030c010824120a15140105061e090402040303050a0801080d1b02031c020d0e030d1205092802030c12070509190606080618040506 72
    0x9000c554541c5c01040040400f0803c00130100e4440c240281180c1c46400103034020300c54440c80645551043d0105d900ca050b00801c852aa1076a141d850a00305244505075a4086240300d00b24400c0c0c0424030454640500c1071141ca81208802003104d8169250160100b015601c11001041240c403500c045841511040c9400600314403e80040d400901a0351078403030b08a407001c10003200b015007142c010310804d09251682c0380d8a0703903656245c40c3c1d5406485042d1000583c00e103015144611840324002c03150384002c00f5140210116100c42c030401c1000c0c181d080041e805020300c01040c9030400c42d000c68041042e0060b0a51000411000d000100011892214103580d040019031a03001800441070b0103500030714210503103140b44030301212100904004d81c440e001ea99840c80f60303442c2481c000901e0384548409018114648400c000000300018900b1a15450138811015004424401d0501614154130707404013030304010007400420002c405010824030140c109010209600141c0f190340900d0039203 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 234837230 1250 234835980 234835999
    0x6140f0402060a1106040c1e141c080d14010f050616060902130204090e0105090c09070215090115080f0a12020a0804080708011b0e010c0201090509040c0302030c0301060311 76
    0x840c100c1c0c040e0f40f105400d400e903000721014441041000445181180c00c1c1c0006183c1d008d0301105d0b10013000849100c0c00000c0b24400500e6040e506045955001d8445243c418080c007c00d6610f982207154400001c040010356030380084c40018005009a43c054580c0c020803104003400d00e00410134034400c0c9403840c401c10220140780300812410b90000110680d025015903c40e0240380d9495000c0d410500420701c1103820a0580d150f000d20500ca0ba6105040e0740d001040746041010030311942c1c120103413209045001c0c480080c0d03000b00e4602d9907140190f0b0108000a146e0650502000c070b2545c051300401201d030002e404010517000300040c42c44095801102041c01e070140442c059240036660880102101000700d0000345505000c1140d00441c6c551034024030040026018904485852510350030100718042d20407401c0307500c2100c84405452041c1400030545407543e0009074920f00407078048942030480305090085080a02c601d900079501139001b4006a411a03032004a24800751111034080c03003850 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 234838480 1250 234837230 234837247
    0x11132606071419080411030a020303030103061d0d020304080105010905070503040212010b030f1c05090102070612090c0b0705011d071202060904020c1b060a050306060c0703051906140f040206 84
    0x30084a056a140b00008039144406181c05002e13582c0865003907440920301d8407003641c0350a022400303014090b0300034045d502c5c45e82180d94460003468407011019641d00b0440492800b180300b04840c800750840e81d0001c640f110303d003546003070a40c2d205800c941da0242c203040c2480f00307440c1c105041d40d4009078101e07014070781e14045451650040094240180d03040c46858600c000220001c200b551600d180d09180007503800d03020b1400d5580e480f411032610300590141070300304001882174010b40c1a02400450200d110078680d101c03140c41c050355820483c03414800007403201c2000400d2007407006078240c03c0d0840381c04100054200b900c0e0f42051044031001d007088030460045554000488600d004c000340f0841d100c506010105540b9039250200707207007281640052544502c1d0000503200d95288950381c0b2880e6580da0000d1100503080313080d200c0941d1007030403c0030002030740034072001402c41480e1003000c044a109090030381c2543c00800c02802c0e0004081e00384028044d00168055000d5016a40300c1c4c0c2c1c2d00103c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 234839730 1250 234838480 234838517
    0x1c02030f09120a0501060f05031002030103020d0305030406111c0c09050f010f02150a02090a0905060f040c0c020d060c090605120103030503041a010f0e1501021f1113260607 76
    0x1c403c002803081d440c00f040403400a480a002d03009480f003da044a16951102a5000c100c0c8030a010196102403800302140000b40301c1e01c011a030052203841c1c0403640808010394051030350400c84062080c4d920444030028038908500c21402e1000140c036000030011314003030100b14103440a481e0039040007a2442e088802600130002e00c2422400081e1008180c0b410841c0080290004021140300d41d12000001405944a02609005290042400007940160303000c0100038041615035606010407170411001580d90441300c40d0910340a182e0101c0d43d00d81d8150300600701d982c1600810309100c001d000011050074000780190540354142441c1e42d50b501c4506100109140410b40d00ba40f4461280010a40003034400c154011204402542e0845480300c03806e20b01c01701c03421800c01c0d005034080e01500d1400300600039a03291903144040001382c1d1112050f00d5031751301e80c054591106500c2072000c040100250308a06c00319210604460075203807982c158902c507220440030f04100100500b070782d0003411281c070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 234840980 1250 234839730 234839743
    0x9010209060708070c05030a150f0b040e07060807090810020c0c060a110105010905090a06090819090f080a0503030f07030b0603072001020a0f1d121c02030f0912 71
    0xc02007219403079100924010045920080302115500001500000c1c0ca0a002400c08140c6510000c003c40e9000e01c0c0c0d4400c030080060842d05200c00f40c035203d80040c1c1d43c41da84100c030b84641020003e02880383c18010094500c00c0c0180030101080070b00d21040011260224030f1404110314144056a5040e86240e800e10f805078001542c4d0780107100151045440703030800c2d0740e94002408170b0002c0c8403e84e603920542040343c00883d02c000098020607984800140d043c2d0161400391310440585040c521107241c90b501098040200c140440c00e5101c091007100807190f5184001d000c5000104000202039880a45a0001034504400d0f015040e0102d4a1907000360000408510054001d540302e18141c0d03001009040c0f203040c4803446c5d0b89000d01c4002c0b41d10042c000c0701c00f0203602d629003450030641e02c1000c4035141c441039502d0400031035007010b80d512a507954031101c440040b0b83d001050b0883e5001d4014400341c128070403c00666204010303204200d0880f400350b5002c0320040360a09a5665101401c03810080c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 234842230 1250 234840980 234840997
    0x7050c100203060324010915051509010311031006080901050601020c090c040801020a090e0a0903050406120902060304060b09090a1208180d18060302030c0403020411040b0a0503061806090f090102 86
    0x1c50703000c3d06900c45500c1e254010704a50f100c040c140482c62302000800c1d14610705024a64001c1c4440c500c0d01c0104070300100801c8880e406140020703002c0b00a000c448102e40041d141c03541d1840301d691080040e42c0d44104881d800291100c001c128a00b00f4500117551354501002e4140036215000010706680800010340d801089008000c3d0f54598803500c000702852030303a000f100c0920954802080e85000350384184003085605071074040c0303002e082a206481244030000a4031403551124203241c0182ca544020310b004a2003074002151a0f43c400082000da180014200d80040c0c6c02000c000700452120040055002040c0c1454840c03034849126105648603ca1507030308161042d61070200045510909000b240b003800e848414185460362000c4040c1c0c441a174840310315510502c000d2000d440e181d800b6142d40002109041c0c0350a60b1450001d8003a00100b507020045040403041003c5410f2143c0044240d60304494880d006e0710b000f1000410301c94003e40200720000e003030030000e02c2c110025811206240c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 234843480 1250 234842230 234842263
    0x10203120702011b11150603010603081303030917070501121b0c02010206010b040e0a0e01200301031505010e16032d0c0201020a090303180f0905060907050c1002030603 74
    0xa28042070302901802c404941c80c0980054141c030000403901c5007800425400840b00039280680007140c050b4805400900039603031556070340c100000011040001424003031035281c025100741b46141005041740b0010307030001c0301a100d01d80800c0f451110103d900000c2d1802401c00610604104c1c0381c0c40c00819080c200c0806c500c03088894070402903040810590300718401d90856a55a0f00c07019468018001c03403081d1914030341d0f800302003150480e15401401d01642c4140002410040300804a50280e0a0042c020003520700000140244152071208910740da01e154421710071540b401150200c0700d000200729003006c5610386c503c402e10354480c0e003184e11108100300160344059961040075a038103407800704a502d034a01e40074801c400c2d180180240c94070b614240d102c2141e0186541c0b02914600d02c0410707101c0c103403c02d80303e0106071207905003040300180404003000907040c940402071025495000c0c111205000c02406035a00e0000d00040c2801c3c00c1c01d51010150b1072b40c8a900110740340c2402c000840108 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 234844730 1250 234843480 234843517
    0x807060912030c0c030f02040b01050a050a03090f0c170f01180f061508010c03050f1b0f070b0a0c020c0108010b090f0a0302060d02071b0305070603020a020c09090c1509060315010203 80
    0x1b440042054401c00c60b0084608100203800c00005644602c901030300e072004210240103d05070305009501c84c241840c003802000e004d540140d45c0d0301e141681540c214028100c030000d45400c3c1c00e0030400c10001c103030318420020446807000344c4010b4052005000014080303166a1550701c1005840e0300010030024400410303540783c0351140a80303400303094940031030b0000902c0c10340040e200030f104143c03550084000c44d5070406074400b00150b40b04150301020006070040c0c0100000f900041c28070700c03910721551850000152801e8100030003410042024500ea040004138001841134907010001c40380901411100385443d240058081070411245601c003039440310020800007110013080d0010303c08607125403d421034030120200c0c0a55010342a02000e81154000503045c440680658020000c0c0d0000c0d0046442002540c030000d51143da04550703110081d00915400c0b40799007820a16182d03020720741040c242c10b0424650114600c0e02000305000c10402d1160680d4130390307900a20460302d0030761066416059 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 234845980 1250 234844730 234844733
    0x1c1101110306010e06120a05040219240201091106030703060f0806042108060103050a020409050403021c0e060906070606031a09100504050a020108060307080a15060807060912030c0c03 81
    0x81074104640050118500401d00341162901500b181e58040240c089520182c854014403802003000074001ca810520721b4003a144101c0c11407110400904508100c5ca035400018614a03000c40e0865042d082560f051102010003c1d16045451a4020060b03514503120341c1c420000b10050241d590101c1c00c8100101c1000c42c10382c0e008a4040d100d5401011041e84160603400320742800e076605800480000c85403000f01e80d031903105e038005903008410484058100f54413545c1e144200c450646044001da801110201d003003240311200c4503000411070030100075004d00c4002007030a0303206030309a141c07142000040000c20080c4650024000c3c41e08020407003201745540c12000007142e8250341c201030311b03c162101c0b104c0c503030094000e5a100d00d030301c00301804000c81039038010350b500314029241c26410300a100c80412865400c1121a000b40c1c0500001020100581034100c101c402c10f80001030290003a54080c03100d1500881c030308080351004c00c55410304600c0d41c10308071240303050340300010034091401c5000030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 234847230 1250 234845980 234846011
    0x1b13060305010608010b0a060210020306010c02090f1b03060307051c0b10031505060a122117150109030f050c03030730080115050d020a030203010602070e07021c1101 73
    0x81c1540c80160080040c03080900030007d09410510851005074040c3c0c020b465204456000b840d0030200605000c45200c3e05680010031803041210f640d820541c80c60100a40c6d20000200038444000b030000341171840c1060030109803125210b011f441d0060040b045011842c0880755a40c00c012900025044000d00f84400000f04a00791403200b81c420b0f4103014813180610449109903401008010120b8001c9860088010074a10700341c5003c1d50340440c1240070240d00d441082d108249548250f4400d0708a5003405404640c05402800380c4142c5800714100009603600800420700f62034114800000021091404500c2c203601f14019542600000c2440010044035459024540d0000340031003074030380c01e02c2d00d03880710703d40354480304000154641c0010050a1081060b4004d545c0c218501a45000e240d20400c4042e46d011112110000c0d45c0000100b15095040c40ba000140c050100080390900300f680000755200101c0b010558444500300314202d02c14046d8540f482c03d400510000d01c01c01081800d01d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 234848480 1250 234847230 234847241
    0x14240d060c02060703020f1207050d0f15083d0e030a03060b03160516050105010f05040b030703050a0204020a03091209080f12190203070212030301061b02031b1306030501 75
    0x241e001d88181404100c0e00c60207402a00e004103590405103007080c1507844149201c84002d4140c0060001c10008007402c94100d00995400015070000441d0b000d5074030006c030b40003502c154421603240c6c218002e084140c29102810380312000c46042c4030462498050400c0001d80000869220407a14200341040078200c00300140c046540c01d524100110755842c40c0743c2c100c40c40704a03101c07402403020a524084090045020b4209030381500310389024601d080c0c0d100303401c460080e003005800c00c800407010803030351038180200919804240c01400d00b00340380d55200341e51884010002881141c011600640c02c6100798850010325030412210f0729050b800300c01c051f2480c1c02900a680c040e02410307420007120840060780c8440004a446c54602e01404404840c4c00c01c0c021204880450008000342009030741c071181a00548524500a5681c0754581030300980410001610803400b5100c2c00303410b00159801003005004a2541680b03580d89019503000500400700d441e1882d4400c80c41d042010081c0481580103 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 234849730 1250 234848480 234848501
    0x30703060c1205010e13052802030c011e030f14160201060801201e031e060306010e0109092f04050c040803030106120906060311040f14240d06 63
    0x1590128040c2c0480e80064070b00901800c00324449000c00b0481c010802010942202d0145050b21088211030482e90140510f54100e00020074542094401354070301402000c0e42c03420242008460101120351805c4807815014150f0241984c0c1c240c980704407104c0d5040070001c07541d01c004510041c6809904540c01da00d02e500c4002c0198640900880c01d41814030030ba00a030841c41040c80018602d2071103818a0398000b0340050064680f0b8501b58240443c446d01860059003c00694540d90002d0880078014280050590703210790712010040044070b40d014241410346420701404a003404481c2040700a82c50025510200c1d440551094209000080d4003144a034034212014400d6480c2c5144070340440c0070311701038000300ba0400c0004009442c0180c0616445805103240810b03090416154001203400d554070a6451640c1c80c2d031034480d1407034070f0311400205680b40c031810000f03440c66889440001e403000f0000c046600d040300b80e4030ba40040702d03003ca00041c000107044407071f2060280381280141c40c100c0503 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 234850980 1250 234849730 234849737
    0x902060307080f13051009050304090c09081c0c0f02010302091305011d190e0f0607050414030d021b0a120c03030e0909060403141b072903160905030703060c 69
    0x3c80d4132801c142c200b103000b55400c00c000303141c019120301081009201e000f804403007500c0f0400c0300040310f0a00e40240c805a44c00d944a034203046103012211800c02d16288211050b070864000c2040d401d50b0441a0048103d401091241e501101440180c0081c0f10700384030583d0000c1d0656030300a28204982201d416079155940100181032105510300030340e0000e172500160310140c44100d010b4036490354000005002c00800300d5602140c0500d040381402402d0310442c001400c005002c0c4080c00b900540c43c03040300c0040e170082c202d501e9040d10003900d90740c03003105241020030f08400c905050341c2e911858074007400c00840e850a8100c10751911846400d4240310817808101a0400c0400c10304d400740d003180c468030040015180725a15940c0071120381c0e000302020712422005210341205d9802c04548d80b82c0d0740e00e43e1001849400d0800d40034051710443e074800740d8840c000c3c54411804205184083c4ca4001000712003800d140810300300300783e840304016000f5030b070103104040f8000180403964119881001080c0c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 234852230 1250 234850980 234851011
    0x30106120209040b040203160603020a080601092403020c1e073303020403140a03080c0f0a080a020408151005060304080304030c02010c05010c03090309090509071503090206030708 79
    0xe50590040503a40d00103940500700000007804503013070121680d40144000e0589440c1940710085c1c00f09596180c0001000079404680c1100c05a00000581d800400908140b00898903040d0f2005001c0319540c40000b8003100c1540c1905502d002c1d4040c0c402c40034440f800e44090720544580455455000c1f03030321035400c0c425a40001107680c0c5103403000a0740105520107040b070702c07107500c4030005601c6040414401c05900700000004654880120541420490050b14039500e042c14000c1c0f007030070040e060b000b507008100021750200103810f04443d524040e504001300340b0340d00d9115140c020f0140c0d83c0110121300890307046030314000c103440581748140c107000b642e0036209465070240303e00d1740022100200300100030404100802c1c000c102e200a100d10514001152f980155241e9095800c9140d106010a88407185e800405422014090150104840c20072052a0045d96a603690b100347c030450712a024000ca003440407038442e80000404940290a81c2d07981d04180400400d680310403a0301054102a42 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 234853480 1250 234852230 234852239
    0x41d0d030f0b01052a011109040b010206010b1801020a0b0109091406060d0807050a0c080f0111090d1101020a0b0108030306010905010e030d030507050405030a050a110604080a03050a210b030106 85
    0x1880b840d07a564106940b01420b250641102c48801c41e0b4562629444412010491200c01000d00520034031803044c80000ba2550310000a22003078030154100507042d5081640140316441400064943d02140c40580c480e20701c04040050303092620421019120550b43d500101c0c0b80001900403000307452040d40ac0191140300d07010107a84601c0150340c600e81c06125080244046503001002e820201d0180c2d050b507000352000d41c0d650b842c03603500383d0003650301d48c021115a440c1d00a00384114815900310308103a51a000881c4005044010b495070001d00b60382d00c1d0074041c85240d1003000652609584001c1c041e4217941c43e9003050799a60811659540094040d20340480d441d40b0400142019180290003007036201140350003a0041c0c80e0080c191010000240800980c50340c1c00c2101c0601c05000d040030b00801c03045400e0051400042155a0340981410041000038180c0054081010740d0149007040c1c6036849050205c9000405c02d598440401c0006c1c52038180d41c0031507002c000014011002004a1981c4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 234854730 1250 234853480 234853511
    0x1103090f070501020d050d0507050f071b06020102070b01051c0b0712060f051806012a05060105060c0a030c210e0f0910090b0f0a0e040317060d02010509041d0d03 71
    0x10717500c030300055024031104990f4400d07600704541000580c2410383c02c0044001f81c24250b500200c20a65503006402c45400327800203000099800f0742102c0c4000d600d803050340e0319001e41084041c400c0e940601c0c03865030340015401601c80c0c0d1842c0e0551001c0f8001c1c1390305000000600c2032003130304143c20103185020f02c0043d171f4003162480e40c82242c40c060310218a2004100f146000300303400402840c1071115100a0710188040700000420300303415851282070001c0340e030500c9441d0440503005940156010441d030b074882540081c0f03142101d41e251034402106070340e42c5007a40695850003030b840d4031560b03081e0070f4105140d04210001c500e0942501d685540071078240030801d80b650141c5418100d81b0000f41d050201036901d030485482142e014124a07003014460f0045004113556501040342022000144000c140d406400c28175440f138600d0f0300c07420324240500014042854008001d040c000700181030820364542e50840170f4a103a1000a440302820880c5100d80c8550180003d0000603180504280b00041c2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 234855980 1250 234854730 234854743
    0xb04050c06030f0403050d0605060a0210050901020a0c021009030605040609021c020f1509060307030c02212b05010e011818020909100213030c0501030e1f1103090f07050102 76
    0x31083c2e050a25441d151816140d5038004d00e88101e4060b00d83d030000c03070603445000c003c02040c40d044c6c1c000c0c029461800640b078112032004d40100711030390042010030f070480c0c0c1c401d01d14560940c04940031400c800d883d4a09461b00303034099100030511801d01041000b4880b1540c0540881b5009844104031407012807001c41040360b901070025848044003801050310309255141410400116180ea4500800040051240c0d0011600c010000380ca0b480c543d500b0310b030305001111941c00d808800c0310b588048060fa03021140580607807e0b0345c0e800809803030006000244406401200701702420000c42d42c46450320404000b0900030500007825010340d80c2c0c030030007081c03040819958144803950485003e544c20002c4182c0081d19441041c07181e04100c410780f40040c401400a008503250400705a4510700d1301d5220102c0c00d0f840340f8141890103c0b030600404020950060460822002136609018000c03460010000002034528512001c001c024854500144040ca0303414200c00300c40c81d071995013004a80d58130 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 234857230 1250 234855980 234855991
    0x20405070807080f1306050f1506070b0109050c191106010f03050601090e0c12061f06080703050406021308010603060605030c060d050703090b07050304020909011b0e0613030b04050c0603 82
    0x9244100203008004e51a03000c540040034051201e03030310281c075101c0b642641c5060f50080c1c03680012100388105500f0705405985480b4055a60740d080103000e80352221401380501c20807403a02c0d1039034005050302c0c9501c0200c0740ca8441b40540c0f4070340041c11440040c03078070207441c07820305a030300c030744400483c007007034502e903210200c0c1d80c0705004001c540c0c20240108040e1010052082480c8501600e80b25035940e207501c5070201c0204403005000616001d20744c0e0b103070715255400030180c8500c83c0006004e00c17a4401041d40e40440e41d13080122f83c44d169441c04200030700c5481b80c1541c041c81504004201124190082070880380200000d1000d26110010551146100c6030403d0f44050204101256920721703070001603105c4840d080004040303c540d154a07400380704c2103800500284000007004210b107420381384250000b100d04001c010341c240a58500c0b403101c000000c01420b20191340c4685d91907954039003c86e502c000c0310700c1ca2050821ba0302d19010000b07e0060301c1c1110b80b03000f0740c3c10f102a1804d1460503a803180 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 234858480 1250 234857230 234857237
    0xc061008011a010509060706050c070c090902010f0c03020f0d0201060f1406160305120a020702030607170112020a03050f0106051507050c1512010b09010f0903111908010608010207020405070807 85
    0x2e0280015240355000707003140c80d04060700344101004036845220740d07841340504800e540c2e41c410141c030307000c007030340ca911740121140c0c52500880d00c2c0503036405510080b1002003414180c018018506090b850f10380d03c83e00301708040c4a0388054124080c2e06411440444800310b00070101180c403800403d400c03151420071103400030300601c500d00c400c4c50070150075002c140c000d0a205240c18203240010703c54100c12181d541c0c8642e0000384e46411820304100c80f079400f040d07916001075080c4030440c2d82c1c61419030610508011011003c0da42d070a5545d441d80010045902c0002c4503035040301d4905042c06040c451007405c0c46000d900c8201c0c9140c0c035880d4105d4104507440405010001180c00c2000b0200003641e071400302d640024085890031006450006018000d01c0c441e0b43d450781c00079000102000c0307041300e9640802034007910400c0050304074858010000c070115015048000394400304074007102e1a80c4841c0c140d41c2049030000d040c21041d4020002140240c400384400d03035030b8007410b4801c07403025980704001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 234859730 1250 234858480 234858521
    0x30503070303111c0501230d170c0102190f091401180305010515040f0209010c120c17040603060b0414010f0201060f0b0d060f0e0f060d080c06100801 66
    0x80c425400003c0101180301101d041441c000f4061500140509815442590350301c0181b0100b60000010282d00e0001e02008009041038404120511a200c1000b000302c03807006d0f41c1d00d1103003503010241da245d5178103c0000c64407405c16041018000d0101183c04002c5502141420f1196225045c2c41c8140e0301a04d0585540800f09001103d030390920701100c40c03020401b050040f00050f820b018890242e54403050000c0529002070401040316506114070340f0151041081c0701d07499030408282014550040c0755114100034040c000c0c0c400b0184502d00130400000782d12030301010101807000e070060342c2c0700d03560801c1f0071900d4020040d00c512440c0a244180c444c5c2001103609503220b1044440764a00c244004103a5940d584941d40c0a640346400111400340d001c12280c141907080d10030b000042a03a40300b03c040d840d24000421080201c0500082d0041185400240750740c1ca07824004904150300c440d04550301c0b400e064890b034132502c05a401c101100204200000c0f0307420140240c00820300c1900c04e1451 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 234860980 1250 234859730 234859733
    0x904020f030f09030702030703030c05030d0c020c03070f05010e04050402060708040803070308090601030f1b1806090b03062a131202010e0901080303060103020d291c2607051002041d0103050307 85
    0x4954bc602a82140c091104004c45070004d500307409140840300c00758005084061020040509140281e00400d8285030b140b20100301c030340e901101c04007400350b05403000240c40d1034500102d0100c1c0b2810300042c21892000900113080140040203000c3c00e4041c4e82c88901945030140d9042d1150000c0c0320140107600c4078000000881c00404101d000c2030680390031803c0090382e4600144202031000124690b44d6590030302001103d0340ca0207a0a4410401c4010700a9031a140401d0310090b2840005680c1203c01650b224118104208c201c03800300000640d1001019600c00380015041201c5074101e0000303013040281544d1b420001d070340b24165100f0380007071030031541d42600440003500550001c82d001034035001a404041c09504500014040042e9000b4040500d8828429003004004290300502c1c2c1050850300828400701191824200402648401031041c4040035100c1c099031801811034040c0d00784c2c2034100070305940144101c51001c0d0640229000750303050031210b84401d110107080303a00104921300 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 234862230 1250 234860980 234860987
    0x40b070303020901050c0a05010c0e030703120309080f040905151002070e15041515080c0304030e01050403020415171218010309121205010b0906070f080904020f030f0903070203070303 81
    0x2103d03e506140040c2040c602e204030310b1400751000000d40306a55505c0030120281e9200d6500c0039049001d40003054040e1031503482030002c0300d010540c02d003090b07502c415940c1042501d404547d0311150710503016880d00e03104d0b010900100016290f525800450004200075403c001020340c0361030000d50080c0c0324491410a071b1514006c002001a59011504504c1001c04e5450344550f4112001e505200d0314250309100310b0010080d40c100b000c2c000d105d05141003000b41e101d26402ca9502035894a0b04ca44298104001624240140d400003540681450040340b0842071007034904044464032071421081844890004d03807654036103107000c6d01e036413402c001c841c01072004101402d070205010314000800c01050b44540038002d9031207208400058880c8107100949016001d514050481508420318191101000590300e109003040105000942e60110043c805c003441920100b1030301a0017955901b0b11404030900d00c1c3d20480d0310500500c12180401d2031081c00105498041c0d502500400000f42941c8064 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 234863480 1250 234862230 234862237
    0x314060906130603050601031b0302030604030c03020111030a0f1103090312060a080307031e09062106150203121005010e09130f060e0c030d2c0307030c0305060c040b07030302 77
    0xc1c0e0440808a00d0302c000322100d120741c800860080010b044a5410342c609008040104900b02003034a002e040d040c805039901151103504251701d0300b4150080091494141d015121010050410500200400c501d0380ea4079007110064400c22402081601071a080002090205440760700c000d90060114011400700000c0e05600054000d22900d00c1a540d9a0124510703444490f040f00010285181080b900f0000700d40722402e1000c50425082640c00e001c030040450045001131600100c1c40f60910101032041e030300000c0500246440c0301260322410348040d5403503000041c405413200605001510700021021074805640b0140d641c842d07200d0b41030003040204040545150715416014bc01e10001440c160840300d541445454080396140321880003500b0141400c0c01c5c580240c002100c0c400d02e0a03440050b10140e0b4116a000c0c20306144040c00844000300360485c3c09425104084020092240d03200d0510110b034413440444c1d002da9030720a080380280c095481240d80482090051000190003038018 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 234864730 1250 234863480 234863491
    0xa0309020409050a061401090203011508071704030e15030115030209011115062b020111010902060c0f0c0105130605030c0706140603010c02120409110909010e06030d03140609 77
    0xb1900400300d860701030404619140403503807159510f03c0e8440b4840d00c440c6003401451f0b03000086003190f240842d0b40889040b803480003000c0048400c009100d583c010f5541c40b4004192601c001d40310f282030300c1e0141c4202510390000388510070f06450031842d0384640d0203e9060f50b5880201d0509445550b100358041d4010356052814000d02002010050400700902100381d41c2c0d22550100c2400d00720309210302034501014400c0f014460032000d20101001c50318002a150f428038000c81800155011b843c01082003000080d40700c240007038901c031181000100c099400600e40d003915214107841c1c00640e580d100d20001e0f03036040c003d044010000d26010300041c2d5440300705065254500800c03a40c440742142c452a18985c0c0748001030b428007190307060034840e0f044100a03600050041c180540300b6592fa6014070700c900303024561911303071608201012200340d6200000261848916585918141d1552842100c2441c041d01ca0b80301400d50a1344a400740101030b40b268101c04185454150a2040c00ca0b4010706 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 234865980 1250 234864730 234864739
    0x9290628022803030b0906060306010c020a050d08030a0c08040b13050c120109060b03010b0105041a0c0f0a030f0e0a03060f090c08070e0a02040f06110109050d0f02100c02030a030902 80
    0x581c160020700b88181140720302000e0912242440d154900903007111191110740d400390740031404004840d1942c800316034000609003402d40d03280d2614400078501c0300f150b403c034a82205c9015143c80030802943c01940c00b03003090060030301400b11030304030481d039000089902030200c2c42d944011920449941511050903070044041e0f81c01d074404000441c070751034a41c04050312aa0340d145516070074040b603071080b00103e55044000380003d621400000b404e0740101d010f22250581d044c49010341650040c000c0724800315698080c0d5248031200e410040e1148100c0c0c00680c0800c2ca42c07900c0c840700d203110720288250594000c0413108c4260075034031500028001c603a0300946065450071581c000c0f0302d0342e00c00040104044c0c0000c110403418071222203240c643c00b51814640e203005000070302000c0240307641c0800343c0b21036141010001341e030b2040303480c0504a80380d0040d09a000c0c01c2007000280f03600403aa0601801b01c3e40845444440308c0c00580100c81e1504800401070b00148482d1040f035101c0e4202806541c002417 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 234867230 1250 234865980 234865993
    0x309030901052d04051f080a1e0f051014030a0b060103090c0e0a0c0c0512030c0f04140a062606190b09090714040308030403090929062802 61
    0x2480c2d0f40801c1d881004400038002043c00c11061411298101542c2c1c648291910880c840c0b50380a0710905010300442d0038a80ca81d14a00e00011018405840b0605c1e0420148050500048140001c00f4180c80c40c2d040350b0152103000c07510b659085003002881c00054028070002d034403511181d4440e10050049410140c403180c0907004603494848403009414200304030305040c10300c280842c04442e044520703031060080d2510014003003038011800c10803840c0d20315240d81d038a540390382a2620342e1060454071094544042800b00391032248e0820b001c0c20040588a04251035103a80b4260f807150814040c8510700c803684244815282c421441d003917004080a02020900c203010403c0b80c0e000d900e1500500048400429007041c0d03480c10340302c0c041d084169420080da85030764041c04507026202e180405016400000041810144514181da0040c545580d080103818691744403406103212660380d0b2248803200c50040300c00c1d40b4042c02200c55007180768080400081003401c00c521101a1031041600307502840 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 234868480 1250 234867230 234867277
    0x12080907062a05060603010c03090b010b0708040e131104090206180102070b1b2803050f0d090318140a03060f090206070c08060f040c060809100c020703060b06030903090105 76
    0x1c0c080300345183c0702d8005484580351400c10705085982851059003018103084494001c50702c10510342c0e040d00c1c110070005c3d81c0c1d00b5450a01c5016880346d58461060000b51000f008101030040c1b00400b00140300700e100c1d12003004151304000036521a03000c003960060b000c100004290303801602c0c80008401c10f0059900c0c690382c0d282c948520360080100b8020b119030f0f816800203501d10521041c20031681d1440b88528100012802d10a1402c0c00c0000806008000825210f003402c18000e8524026800000303018040d914500203004d28070600301c841c0d40c90070905012624880d0b00210440107403018203a9990360307245468010140080703503410740c040c0355a001d03140c0160325080003c280350741c0581c00c02a0301603e4072a0442c9071210060000860aa103002130000140b41010310008484041c03601d41c0103a26140c41681c184503141034650310162a001e00c46004a8000c110340b02124050001088212548014003203030b44411a1807200d01d40040280508660246c00034100b081c400501a00b42d9803400c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 234869730 1250 234868480 234868547
    0x1a04150e01060c15050f131103030403240c02030d0f0b04110901170f0123191814010915150302120c0903060127050a06031208090706 59
    0x203800030700002e4030f030079081000d00240541310032400c091a13104000500c4d102d101c4040080c0081d1a242529249014850620250001c01c0e900444010280ca0b520366407858288030004030002900d45640b0a02c068100c407247e81e114105c0328480580103585030a01c0202c50400070300c43e602500c0200d076561410030445854a00c0355001c41c221304803913940d0707460202c0c3c00903140c018541045a6210040020482401c900d1310150341101c0400f0001400039400304108414165110a040e410a000990145050150a80c0c1c0b8007159503030300c150f188941d0007506c50340a035090a45581e0007079150300b004200f540d406600900300500701c520021680780e02c901074490f07049030000708000081d0300820502d004003541071105030031400c0c2c441030a02e04080030012039282c070814800c10034004005114103400319030503c20400d085440c1c1600300441d10f004a40c0c4001030155000075980d02c0902c440c7c800c000c900904141e030141d80c1c104014191180742c500300301d4400800704641c0e0b80b160ba0405160510950 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 234870980 1250 234869730 234869759
    0x50f0c030921090114041d130605090a03081b180103020705070e07020607030e0c101412040c0512060a09050a02090103030305190b06070227040b040302060a1a0415 72
    0x8210503680e5a0f480010001808502c1c0030021451940e0108000c10241150080000100203c21035458180da5a220103456080030708030050911802c0c501003201c0d042010800800e418400c7c0c0304c043e03a039140c041140585811101c00f01106540c2004000d080070924240360700c10740d82c149405450802e89076a00d13414041303594040c0054001050501072140d406000190707110126150410810200100c4182d40b0411b21038440d00030202010506091f510480345018540ca200350702d103a0307541040c1c0b0002d000319003c507815142d520385410082a2854400d40316031880404a00501c1591981348078407000340000102190140314040c11a00142c0382c40860354000c5000351400502443c2801c00141e59000084200d52a01d00c0c1407480c00036580c0f12015100d18503019030390785041c4401c6100341c40c01800d0340e01d61030240c02580e01c1000200300241c03040d144158425400d0b1440c9850300740c0610161222000d5051702e81c2404084100641020f43c0811340b410300061002c7c480a0703444402c0c10a800 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 234872230 1250 234870980 234871033
    0x406030206040602150609070c030503070e0a0f030308090d02031b0304150918150b091302040906061409091303020313060f09080c06160804080709050a0c03050f0c0309 74
    0x17000703024126015207044407850703400740d4150350b035840608c0c2c1040c00038008101d03030a0040902c074000c0089659603208204500e00090040c10380040280c50740c0c0080d840c0caa0303500c0128002444500040c110a4012a03045440e184d25001141000c1c0c1c03620801642d2812940d500310319100a1200040c0000610030b080c00240050312070114690034440d042071202035a048c0040072900f070420703920201d950305805004941030402c0071502c6400081c000f50001c84422540b141150003c0707808210040c0d5a4440c0b8100c80182e147c5a40c0f41000035194112401543e511503400070a510000384c20070940e00121404d1071092050301c2c43c0c5510122241d41502c030031303001000010b80d41d056044c0d60980014802c00940385450003404c19060040c00210703188107960301c40c031000f019040301e44200300c2501c050b1805041d11100b658007554a070ba03018401803808540c1030301f0070b904015170001301c40c3c000e20815000c0d03c94601c40540c6599034401ea41110760020301542e50314400d03511548c030004510400c1c0d02009 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 234873480 1250 234872230 234872233
    0x8070602131e0b0a050c010e0c030c0d0c05150c0f1c020a080d020708040f08011a060304120f270e0f090a1e080a030504021809031204020406030206040602 68
    0x1070355166110107610341c0a0300002c100c001031203054600100540584030450390210351040c0e440304113400485660190a070313140c95560800101c2a00c0d080d0100f40500c3d040c0c1c0603012030f44071000d2a4108145444a03801c0034280e50b0413070205001c9814031002d207001821107401d400d490301d8500c40d9200e00d13042c0c5240805080f03070805407000d11609401e4800303039080041c1d0710090031f070f8044545811450748601007118044a80c00903100c1d003040381110946008100440c0384408003592126403034080e042c03100715a4190042034945d540c8502d040c4040c5c0f8040c42c0c2100c404c65420000380d100791400707840034400c03002388447e40840741c060109010b0000309016512041c0d0030614500b0a0100311401e020f84501c00ca008540c08003c000c43c00090f1602d44907400500c400b0407202c241c0b050007280992440d000d401040300180003002c40b50949c00050043d4826503a20110a10f6005c4500c88070009440c001c200f0b41003004020071a4800310040c0360894001800014855600d5000405075802940541e000d03 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 234874730 1250 234873480 234873487
    0x705120403140106060f0e19080a0308091212040602031b0301061106090120161b0611060408090d06020c010515100c0201090501050a0509030a0507150504050d0209060d08070602 78
    0x18010b0a0003a28010100d03030400c85c0e5030361000c01007c2c0c044155406c009024002001c85607000c0b41010403a500100f09040a4404040d42c40c00c004101d90b03070860b40d0720224480d984d0902e24407000041202c3c1c1451403950305000ce41c940d583d0300400707580042e26548008400d039820703481c04042c9000450082000791164103100d802e1a1002e8205100144000d08a9140c08841034028849114602d142c12100303221a6503480c1a10b030070182070640d41d10213420172111402422100788070080303503025107017540c0303070541141d60500805541cad103070855004100c9001445107451030301704101100c214520170900581048403100130182101d40841c0c14044201d01460004070904000c94905107150301440d0002a480c5c0580003c0c1000c105440b9041c100140040c004030001c2c03090040e96220030700101901e20b0b040c1c80d07080203035507050a07000d006207803c4844a4000d90038061b0080720200d0b90050700313041400700d00d5020031085440041c03015411400c603852102c0051403600007814001d02c01c0b4801602d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 234875980 1250 234874730 234874763
    0x7050109061b1113022205092403010908070c030b0c0a08161101230c0c070911040e0705030411010f020a0b04060e0d021506060403030909020705120403 67
    0x30300200d6030702200a000072198040c10000c91407101e0010181c001d0007031150780400b00042a56100440030400000344081140411812054201c85506d101000003085c0f09440b14100031001c0802d4035010043d485c12030000000c5018100481c06000008000044248994492031020f500c0424105e0b015081d044081c820000c1440d9480d4018000f00506030401e040c030034000d800294080c104030008003402141c40c4006104071440781081e600040280014001030b0f11024124030303400d24560740c1c140e00c2c0000450020548041e0b499409191000348440307854100e8100040c40f41c02420028000100300205406482c1603074a03005813000d0351099039a00e42814490b220048500f400c6042000c50f1080c050312590000e01580f081b504640100925151072030304900a0240b0744190385a40560038491318442c0e000f0681400400f4110009200340e0f40340070805c032081c070988c000100401c0c031010f010700244e0401c0c1d000d4120b02d0322034422103008001081e11440036821584c01101e400080486070f12 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 234877230 1250 234875980 234875987
    0x90305210609090319120902060a020c090f10050603040606080105070507060f050613180618021f05030c03090c06282a0201090e0a0504140601060f0e010e12070501 72
    0x1980140c000b0f0246092040240c07102151203810841e9200f000180000c40c0500030441d4810200298010100c40d900c0d440c0940181d2244005a03426100348504400103803810381c15114640300e02414101d03420060700f44001c02c241500090000e845881e9602400b00f0f082c0002d2240314000e030170507140e06888100e0381c0342000a5a246070a0103981c42e042c00300748800b603181c0d02d440e010503011500e404a81e018604203442c202c81d408210103403000341042c0103040b60724401c41d140f80240303000350b4088580d1600c141010700394a48030b10b01800002d0081000400030825000a99001596001951207422000e000a00703203802100c00181c1d0820a0403151650390810808050745040a05280c507002c610320b82c2c001e400320a0702c1c0b00c2c501801070940c1c074502113a1041681c0d4014101100134144103007000004140184401c44045400c000391060f4070f2410a0009005070403224180d6440040d4036422030702f00e038104800c180c290f041c41044403844045944060300d03029620406002005803074940000113 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 234878480 1250 234877230 234877249
    0x130503160e1305030c0d03050118060f140102031b0601180b01021b0a050d150624050904140f2707050f0102070e010f0503121c0903052106 61
    0x16005200326401040300400358001030b41d100c01e90b54001c0860000504100d400e42c802c144056a00b805548004200b031501544500e06a0711018a84c89055181110300404c6511a0141c02a5900d440e5410000e603800803840301c003139000604c19a03090a4140720011564014003e10b0305c0f503034001c0b5006202c4810b00c5400f5041c0c80d0b00d009010711607900440b00103900c0b4491207084032010071700200300008503216001104010700f00505984000c8c519030400c181152494001c1000c1da90a182d03002400814a64907105007006000b200000d0440c130740802d8030168003c82080c2e401c2600ca0928101ca088120780152094444c18000745451801c944640101888010700b25180c2c003c00f445801e8004d00003031a0016180706481040c24035440000503840e01a03a54407a132000320801e00081407803440401810304880c1c0550460b4180036444141080c01c2c01150504c0000f03280d00035020000304500d030040405a8040d0400303924065000e940f8003008042410300940c2040c07000c051182c0b5080ca920390 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 234879730 1250 234878480 234878503
    0xa02060a0b09060f01140415030501170606090a05100e04030c110108011d0a060e04030c05010c0311030a0f09021f08160c030810081605100c0b1303030908130503 71
    0x1603aa00c0c9051000a04640780e1060341d203041280f900b002006c207541060848010b056030380c0c0b00505441043c0e00003005890709010344812080e600715098140324000408500514000f020f40040395600440d49008140003050041d240c02a01700000d940082c5851250249002c0e030341302080c07125075080042e101030503c00d81030b0401c06079500411a0b40d4020030030792007459400c0c000843e0360f00c81e010007201401003500004581d0384048140810150482c0b02c00440c24030510080c0400032080321300784d0844082c030b151010300b03800800c000b480100141d4400407800b9800080020040360075000b0071107201a4040d0344154103040901403040c0c60b04a41c0865001c0ca00c0d0304496501c60700306200a020740c0e038401008052140280c0130910042c0c501c0580b40c05807150b18121054000c030800c0d03813190b072051881070300c2c000e009488002408521841c1400483d41d008140c0781550386907880c2040313020031040030079006c141c0d6903229800010b6403040189600480c0504054070107051504150810000015 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 234880980 1250 234879730 234879739
    0xb0f0103031d03010e06010b0a0801170601030f050a1515090b280305030703020714040e1f110c030c06070c030e01080c0706090605070e010c0503070f02060f0a02060a0b 74
    0x10000203038016152100407802c1c0800101c4070000340042400340003034200d0007009002c1c0701d002003a8840c60001400c250051580c032a0001d0b40d0f10000c5000c1d10001050081c850307048000107202260360880910070041c4180210340c17080c000d640341c203000420140c5502c81c4a0b6219201003050210564014001c4c0046c00c00405c002c00e0b0b0040004d4014581d01140f920459400341400003840d808200700004640040940c4d564544518009459011a0081e10060441804c00f0465428075101d4903000a00c4000200302c08a1503003503e071025001e203901d18003204c1e1290301070710044004201504006485038000c58503400d02e1507095007025002442e03d41004110468a80843da116002040901c02803e000400c1e131683c1f05441c10030300c00d245001d081340c0d09000b01c00c1e0070400360303911a0784100c40315074034102900804401103034004840c00c000b070410f40c0180601000700d0b0000c01d070070170307410700c002d0040d840c1c85900440f810040c0c02c40c040c030742c006d60000400c0001c14884c90040c0002a00101d9 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 234882230 1250 234880980 234881011
    0x316050a0e0402030a0c0b0306031c050d0f060b0c070510050708040902070c12051507020c10080619030f03020106060c081b0114180c04060e0f0901060e0a090b 70
    0x4a408864030703219803041d1480c00700100301591010702c407220340c098004440040307071a1104c6031126190b1080c0c61480c0070380b2543c9003502c84002815200114500c040d91078a11703010040e1240c0700542440310310485415a40c040000794400408020481e110900b406020b000380b030801008100343e43c0044010510104000700000210004111010784240030b0340140c8904050524100d401800d4000c1102c80b208001018240030740003c0c480705070030310400c84a0041c0e03100401281c40304047c40109400802017506603406034001d1202540c440d001505500303c045407000c0c040000b01e090751090350790300e071003c058200340b542c28044d03117000d0f20740340c00d00c0701441109686006003071141d16029816200c8000050b4030340c4400307400c40a80c41429204010150a200110510b80304001076030103064443c22495a8003400c050048008490030700e40c244040345e03108100700c0d50f1201c0052280216558546001c00c42e01c0300f100901d40540c0c0012000101454540b03009080d1176400f4142000184014 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 234883480 1250 234882230 234882239
    0x126030f031602070306020409020d051503060a09030201330905010f0909020d0213060602010c080603030a08061801030c0501030c0203070203100f020c011a01030c0801060e150c0102180316 83
    0x181141c0d04540034030541504050b00d51401ca041081c280c20003010300d030000500103420341094010f091050403110741002540c941c081c03034207403581002c412103802d0707041400020603000b860f40c8001c0c801c1d4001c0c000451560a10310002d40c04103002502c14060000c458450700c400300c0500d60010291160540812442d4107000c440080c416143c400c0904c055200d541007021522018502c0c0401340d80900100855901222403401a008502501c801903203850888c0025a203e01001c1c4d018000150185280c40d003180d03012160040010180c5400c015840d0324201c5600c5500f803944e00950084d600000d4090800c0e00040c1990101a204030841d03005021003c00751b6808194466111154076001420f0820510780300042d01481035400790b554a000e0454428403003401c101c660a80090f40c0800220180c240c0c00d88034200d0a020700c0000903604c8404500750f00703043c0001444a601500818145503083c41c041e0b00b60b911186100850740d030700d003601100e03500f020000d05002c070000d064104d0440b42403 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 234884730 1250 234883480 234883507
    0x1106010e01120614101404020a090504021b030304030201020d0c1103180118060503040b0105010824180115090e0714070c05031203100b190f090806012603 68
    0x1801480c200c0a401c103000001c00c40c059102d407a007030510302c4a0501c240390240c9405c10f00707101403040c0050a001e500210a4500c1d06108941075140c10f510f0715554181840d041c88000d4101c840c8500d080c0000794082c5070300180030000783d4450f1b03210b9030002d070340c0e40300080160f000d85a0018282052041100e40022400d0000c025191412924401c1001c05000d4a0040b1a050328400d540302d4040341c45500030440640c0400210301c0317540241844d04041e6a200c00440700380e072080380c2112042e0300c4201e00f0148100600d68140c4401401002024100a001c0d0580354520f800e91140064070400315480d05525000300707074030b0002d20510402281c00d02d0001c4002d00100544a801c0d4400e1100040010400400c0c0340c0c9030001d000e01800312192406141803540b82c643c402c1e980254440110f0100062032945071007129503506450b01c0040710050030141c140d9040000c4000d4005104c0c5034030300440d5203c8100192070003000b8040624080c00000350404030404001d50b02414a80c104100b0f03034958440 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 234885980 1250 234884730 234884759
    0x1615060f050609121509160e06011418060d0905061b04090903020a06090c18060305070e220818030109020a1e0e01081c031a0906060f19110601 63
    0x9440380382c2d03c007020000160a003c100001d04c110171840d00244201c40c6400508203a02c44a002185010a40c40d00c0c4100d05403801103e4450009102a1a542c04035110a01034541c8840f1243e6892501c10200001187d5800120075240701507607400307801082c00070800c07866070082264821130418002140154440e41b040e4026500c103551544c03180420540700b004480340c03280d00110104402072a03480d0454a01659100e8111076034100d010612044090303101c0c6008a03540140105403040c030b810b84c0b07142129401840411280f14020060315004c04c000400c1c03410512030480165214228001c0c070440355002003985000781c1c5031403220801603c514108606503103031000541d200c603800c131030290001c1a050304581c000c0745251000240e07444c070002d818425095034500004501601c030808400302c40302d02d00318503070111840700320311110b08103c500c0b2a04190060295441e000b0302007030402007035021a140c001d02044080001e04419030100c00881c0c0318040d0405020203503d0014000050320 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 234887230 1250 234885980 234885997
    0x1118090415020307050405060309071406040803030103110111010e07150e06070b061f0905090708150f01090807061d0901061205071b1203061e0306020f1615060f0506 73
    0x10b500002090841d4012070540d03008040080409a6078a070050030300c1c0e100d070214818210b05a0040c06602d0f141d1801c4c0c13003030310250b414900065045030f29540301c04c5a841c030101c1c0e21505001a40040e149000301c05c0c02803407892507540e001000b42178030b4069001c0c6004a222051400c00131780389840d8050b55a10780c100d5454980201612206031100c40c00940105c20316148280e1908014100c00032007500055a1412203000301d031044107580c0d071201e040d01c03130510444c0d903c1c040061844c042c0941b1718007a410b01c0c949040c1071400080558640d01101d1074204142c01c020f010400f0400300f400d070820200500110308106942d0520f465140520240c14004038644203800140c40c1d0002a058a2081c1102054143e2410307290440f803000741081c003000d801e180c55442c0002c7c00e110001c82e01042202c0b142900ca050307407003c0561286143c0301c26009400c01c46140c41c0e002810400c24482660440c01808518000da062680400301030221a0486046500c440d40408100760108030540c0c550050b501000f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 234888480 1250 234887230 234887273
    0x110402040f18240305060105030a020904031107030503130f150e01050322030306050108070810050f0301110c061905010803040302091302040c030b120616031e11180904 74
    0x70601504030000b402c3c414003145009181c80710050701c6030714010440d1048a0045e001d88006036201e100303054035150595400fa40103202c58000ca00081c0c4a101000000d01e183c409440d4800d480e95111750665101c0d0300d00c0040c02c45a0076003030152035000008400180000741100009600d2402c0c0a003008200c084494140a80800003a28001c8902000180035a03c000c0e50201b21041e031030060001e03c003030301856000554540000b16032600442d500c42c040c0c2c01c2e000b0f04210350ba1a210401502d210111381c240d80554030ba0460f00d180c2044500a4200000d15030301620f403030318025110007925448071088c55800d60904004020b03400000c01220184e030f40568400380c450b6107508514003030800266000b50460319040785458043c1d80343d400034107407100840b0244a02941d00620541e2650103889151451401050101d07815000f41e000044049920405207888282503d480c401c0342d2003114611208038001030003d020307118032850f10007404811200d00b050750800c2d84032503134030368950400381c0300300f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 234889730 1250 234888480 234888509
    0xb0f03070b161b030b010e040c03080a1b0f02120706080606030402010509030d020c010e0a05060d0b030a1208010305070b0a30110c0f010204060f0c020d020a12110402040f 75
    0x40107010b100709450a90401d00754051150081510643d40307000748015038041140740f00101e0000307500d40c0100e0003160442d031440b0910f0704540b03cbc26075607032080c5c04480a012140341220f03000d0580c0c86510340c060b40a50840b5a0604460041c014602e803651524840c039000143c1c1031100b141c0001000b40c2250702a61466100da480e40300689092050344480e4ae89807252100e01d405080d8001407001c0c00031001c1c0d81d10100350240009120700340d806c900a90764400d600703004042c01a0129409040d00780401011a002d1b200c40e80c490710814100b8020800026410400510900c03804104110003401c001d140540b60000f80d4100800003401c04515103202120400154609484113050300b81041300d030303a01040b144104c40c0042d400c6600507000d145081c015107426003550341d010b201350340c11212140c0300c0502e01c0c4c0380d070001242c1c0c070400038400b02d80c01040c1015240c00f50b158016003c003c0d1101e281d55103217035050350400342d0303031301000403643c40c440c5004010600401421505000071116000c604941 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 234890980 1250 234889730 234889747
    0x10f0c0c050603150f0103020f0f2d07110102211b070f2402071206060806040f030201050f09032a06160801090209061b1f0608010b0f03070b 62
    0x29996403a40700c10b038008030110070b03c2403070400315401a603111341c100c030b06130142c404200064040c2c3c000c4024401c075800c1c06004d018070a80c403450003819140390443c0001047d07600392075250000c0b90341100c0c3c0341ca2500c010946404015540640b202d0b401401d000804105100c1c81090b40c0c91401080001034111006c00c2c101c4040780c0c07440f8140b80154818056440e49038503021000d54200301880390705800360404c1142d40072903548520784102000541d000d810700d1420400c1c0c00c1f4844c1280c3d0400c58407107a848070000b500110902865000d280f00700064001d6101d5802c0007403d590001e49000040c5200318148051800b0000c1115050f8094102c1059410b800e286a003013000111340d80064203004207010000395014031110a080070a054171854000c0c1d0300c4441003800c80c00f8113500d0681180f8108034016048101c6141c2c085c058684e80e00315041e031010b07400d04852010307010700e1923100b00d621200103000201c4d0a02400d0b501200c1518540c0381c2d01d95080000303a80d1401480352203d947d500041d42c01 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 234892086 1106 234890980 234890993
    0x1051504090b0708100b0406030b0916080402090a021605060a1d0c04021303330207020609060a0e0d050a0c1202010c0b070e04110403020307060509010f0c 68
    0x45250f40c9040c029140c5010150110a5502281c0c00000e10b10725000300500242c0380c17655011421403c0729042c411152009400d50440081400c09040e0356035100d2034084d40103404440100c50764603100c524100070303c98008104d070b070a440080e0500600200007199402050021010040080c2d800e041c10908500001d0035101600902100303d154506034015003440046010110040ba51343d0f5290005113011040b503507001c011105999030710030b002620b9800c40c41003042c415440c016407580003070b40601c03036814000c0c030928003c10724000041c490b4500368003428010744800c0450841e400d145581d400c0ca031000f03c400d84424000172503101d20420340740b1840c6606846100c900304242c0d030345001c54400200f0002c20441c26250004c010394803409450401c561507600241e03558110f00501d400c0c40b016412800500004020003403407642d0101c0c242080104a151103a01c0d0302003458140d = true := by decide +kernel

theorem cover : BRFrame.Cov 234712230 234892086 := by
  have h0 := BRFrame.cov_init 234712230
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 234712230 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 234712230 ≤ n) (h2 : n < 234892086) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
