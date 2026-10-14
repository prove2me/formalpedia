-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3589
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:05:51.310323+00:00
-- url     : https://prove2.me/submissions/954acbe2-8420-4986-be61-5747dcc929e9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 645323741 ≤ n < 645503597 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 645324991 1250 645323741 645323743
    0x204180503130e010521030403060603082a0c0118090507021c050405090606090414092b0e060c0f0d0507210207051302090306040f0b0a090f022b05 65
    0xe807055801d000410710355900d0300b0880d01d00c0900c9119401b80c10445515000349800c0c1b020542c201c098400d480c58280c803a9a40000c43d8200c0d00700396400b2801003281111008040048211851044220400900b1951110703980e0f07029445140e0421541015102c0c03200b038880035400c050035499500707000c4c902e0301100c001e54407100d54504c00020000742d61500c00d45400b90381101c0a4800250410010740c1e0703100e080c0071b140d03440302d050940c1095850180410784d001c01c1e00d1040c0240580406460801903400480381c150103c0f59001d100346015100c40007080b038208410340480141515160307194000c0707040043c01c003141c007200900c00e400340c14035a2181c40d0380400101103c500c204e800000800d5418008141079141c680d0000c096804084240000d00c0c141d03154200340791583d1400b600d0580c440b0b01003801c00c03070180c40445a11501000040810403840309099004140c21400c0000401036103d800f1000403d1901900856802e0701e0800c07101900d000001c14004404440403826803d443d0032 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 645326241 1250 645324991 645324997
    0xa0b03011809050d02030c060106090501050a080601110a0302030309011a0a050907020a0501060906051017180304050d0c030c05150304080304020a120b09011a03031801110601030305070c0e04020108130204180503 93
    0x1fa419008036000407520303500458403201580d6040c3e550301e0800a00030800c1e140c504006d418241030101c000c0c129110314034200104c6007031034445c0d13029548130f0810034000703800c1d00d58050801d54414034041c54002e054070303650506401c40c0ca08640d450300079294440164100144150302609a500b014400b0a28044581000701184e2003078a400140d106120300890b29601880e80350740780c0205174804245501c00720600c035444841101e041d20b01d02a03a40740022032400e51510200d907a07008980080080c000c950b03141900500d8141e41c04106d228501c1c001e0031ba584001400240300e0320300400400c0c02e41d1542c4a10b8405000c2c103000149074110241400d1440c1541103c1903e265824545050040c0e1880301c07030014080c1015000354204042d60040c00000e181468040d81004000c141c9494054000c220f482e00031800307500c48076030ba80c00fa402d0601510706c2c0c5070082e02400101d00180401030740d2040400703901c000000d0b1040c0c014000d900c0090090032030312000e410f040c0c05951030074060010100c01 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 645327491 1250 645326241 645326257
    0x902060409050105100e03300c06010819050601120606091e0c020c15030c2a010e0a12032004064121010b0a030b0a0b03011809050d0203 60
    0x822031204c1c001d4001146c5280007681200c0d096003100c00160460002e11203004992513802c1c41c100c0518903014118040707a0009c10705000d4603409080104104403007800400d013101c41410020310600450b49a29903030748018031461151469220180b400e00541382d00005c041d110303111080c00b503c0c10505650000d9482c0c441c4030324200340b0300301d520704469000040c06202460f0160801e29080749050b00d0300003540008114881002c010403007400c10142c00140401090144a2400e0001c103002d030410342107958000c2c440d48030364800c0345400003044950001c50759104244ca0b003c945c03088517020307540e90003011500c81d0700d003440085004140c40760000340725001c00d00300c0e41d02c21019809500c8a60b042c01e800d0744035002000300c045840700200c0c2800b0018000f03e404100d010300034000c078440b01c0074181c00927030244a10070310128034207040c16810702401107010b5003224045113103400c0ca03003400400c0c4018400d4213000005222003c0706e072995174000380f4450760044150340c3d80003003140c0f008e9166400200 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 645328741 1250 645327491 645327499
    0x9041406010810030c05010e0102010209030616110615040c18030c05010e15030a150e04110112050f0a1a0a03060203060405090a08070303020a0c0f030f0e0f13020a030902060409050105 81
    0x40ca2030143d400480e049940200c0403001d00792800700150744240b4282c5103141155001c1042c8881c5460400680c2c0c0038402165210b100710043e00c1006082d0711116010800f66042070b000e1111800742240b81ca011070728200ca002035901d084071401e84440c6846011010540310f2400000b00740401004200100c520a885040d441c2005104000c0c803490300300c074900d50210050021035800c841d140d100403030580344c12403580d094940784c0901d10341c00c0070101c904a610026404941150756800598500d1407103100c042884182803030348581d890b000d4018645104140d0b1100310004201003441107403400b00001d80550100c9440341000e030040d42c411030304c450241e8181808940440d00c001010252190000001804d022050350124040c0d880700c0705d00e9041003804803180001c103071240790b200e408500c40d440751040282c8500f0050700c41c204004005d4030950481c681701c41180c40740d0705034401318203110400607910414401c0640040504001c003a400420105021801c000a42d000c0d81c1621070481d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 645329991 1250 645328741 645328757
    0x9060607051606090f05130b062206030f05150f01021f0614010e0625060e1501140d030507061b0c0b0c090609040921051e070503070b0a020904140601 66
    0x40300c1724000c555107100e843e0300400c0c040115401c0311082e80c040f00d0345000040c440d07454000c0c07050780d14a215443d0012440c280c080c12030104582a01403040c00441052035070140100d00c1c0444024141021405146020349200701171148183c1c0b081c401603800c2800c5010207100074800043d603c0c024442400741c511000301c0c02d0000e0b1125806510351026613000242043c4c9000349441c01c61045140c1042d0305828040c0d40c5080303800044c03040c0a0304079074051401c010000d03d45d0104541103c14010381c04605000b094101d01302c450341340c92003103149690b054107006a0302c00c0346161503070040045e4085c500440a078003001d200c0c4568400443c0382018044c82140100e500e03045c1c012042031207201c00c07240d8010b400308410345090070142c104401c4d4a0080304281000081d02d1507090510220b4038201c00003c0000841c0d400d1914902c00b01482c17a4078a5468900f8885070340d44866403403258610280c120712003e00021464046a0102c40c42c5510280080c0480615160410006101560340c10f010414403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 645331241 1250 645329991 645329999
    0x606021011030105010f0507020a230a0609061107030c0609052409010e0f040c081b03040503070204240e04030e09090d050c01061a030a050606180906060705160609 72
    0x103000d1024040c1c801e5090074030307503468980103542620841000000b4400c003400510096640c13880d15600030201c0c6aa0303110040d80011480c0511800101e4451040340150000d10103294003484000a980702802d0012004100361032862410103140c0c0024055101c03580040b8035958048080c000702c60040c0d0700c81c00300002c0035115190040c090440c00b90301c88030038019a103881d03101d40211004d9010162a4500070345c1c0501c0881c059407003020200e000b04d660f10040c407809070148003400d030155407030103001411070078981c0d1104d80741d108034030019100725229601c0c82409010713000e41c00d10380245c00c003695806035aa407801040034081281c00b03401141a069800c41582403101809110380b40d418064400d10552503001d56881d004400311304003940d40c901c1e0201da10311440b00c44c0c603041c0d0f041c0c00c45c41e40c4914141d000402130315002080d0038010042070100b072419802c050480110000c0407285407900340e441c00701048180c080e41341c020b425072168110240040c401e0030200404c1e01c01e143c2c1c41c085220b4032 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 645332491 1250 645331241 645331273
    0x2061b12150108070f0e0d1a0702010c020c06090d0807060209120a060513030c03080c160302010207060b01090f090509150a050a1406150d0b06040611071a030f19020c01060602 77
    0x104510050104503815000401e0b85000001f09001c0d074440c9001d0205400000c01d203c8014004440e5400075079515410003121030340401040f8003080c0304440041c5008503503004030b002c0070007030903008000c04030126840c000c00a0a4042d074035800006041d608041522214071503460582810982e291031510b80465504404590303001d0b40e203034140d112100141760725602180c180e03a00801141c184002031080503100b1180c280c1d0491042d0013603001688481c00c3c1e0410b00100ca50030000c060600850444c1040000103c0d403d6208450030440005800e6a45200050800300c04081d0525500d060300100310352101e681e4446030042c1c1c07401500b0031805600011980702084181c0301c0c03581c00500c0e00e11080c650424180140a030120400f00803d084070920003284450b00145c005038082002c034048007115200030082e43c4000c0c404c0d43c0015101c0703034a44140600521018000e85084904440050f00e204000c1461034401110500110340c2c480d020304c0d5160013013100f4081d203c018010036420000e4018 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 645333741 1250 645332491 645332507
    0xb0a06080c0904020108150a1509080c090106360815041104090606080a03050301030b0901150e06010309020904060f0c17070e0102070807090c03110a02061b1215010807 74
    0x200a441c41c8500c2d120784d00150b500d207400408007482d4024484207403185840d0015180010900414540340e1a103a142004d0814895900031600743d0b880b2620f4400c0a55a00c82d00d03c0c111002d608010700300c485821080151403902101c44c2c0035150711040010a8011280c1242d81210446000e48044c812214119024540240ca02512900c00701040a40c6032401d0b520025200340701c0c450000d0910364038900241401510340d000d401050001c030040091001c0c5101e10790b03011060030002c01080c00040d08c240080b951502600c1303030b0000c90400150003039009900c40d040c002e07001040313120149018a02500603000d000e801078841030803d8882c2c9072030b60040000c1d95031301c500d2421803031042e550150225070543d0040001c03030461003080c0c400100100244a01c0010b41030050f00855201c6481d00003500383c86005602e850303050b508102e22080b42d0780c0400c0c4660070000d6414100400b0404811a0b54140512001000c0b0a0f21800501030441009120031840500071f0301c070ba01c416515040700383ca41d04 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 645334991 1250 645333741 645333763
    0x3061002010c021f0603210809150c0d0b12010905010c0e090a020721120c0f02030703230f0d0f0605090103060f020d05041101120c091a09030a0b0a0608 67
    0x380c0f001021880340e00c0f07104d4410300030901c507010002d105552a200d84040014045654454844c1140d240300c04136800072815511000440061031811040c400d042841d55000f40801040e400c00b0070303044490011500b000181100040c0034070703103d00d94005064000d28017100125400c0d80791002142c4c120f40249948050384c81c0c010419025a078035621a0400380d401190201c03a144035000713401c000c1080022003078000f01d20701d9854401e0384000c80d42100c2111071040f8400180080010f9032503149900208983c1d0666041ca03011000e114001242e0807580615403c50300c0e644d00105203172280185001c0641008000d1010500401003c00340b044116005070085641120702c0000600115803160024040c07400007000040c030b01030b40c06400804803501501c044811810707038001c0040070740e03104400d22a84002088200582881540c000d0021401842360000c01c000030031008540345001e00640d01c0001e4068103540e041c8055103000c1710350711330072510281030624210300801d1411000403815004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 645336241 1250 645334991 645334993
    0x9070f0f03051005120a02030a0305040317030118201617040f1a090901170c041a1002030c0f01020406090603110d1e0e010c0f02060f0105010e0d08030c03061002010c02 74
    0x41411305050007894504002c0e00003140c890710003114010784040000640c101d000765036482c0c80724154685003001c05a407100d0f04003250707420b00051100551092040304200c4030407a00041e01d0417100c42c8094003494160248510310700c040781403694600182d08405043e4418064201d01381c6602d840060701d40100d00800595405002081c012a402280501d43d14070041078482e0420040000107600303004242c02c8010360501086ca595140142004050050001103805228411482c28603441103498024080d2003402d80c0010f002e1620300920031110603104d01e4003914101c009400c4694080e40c01486914001034118100061143c4a07203d400d03840c0840e955090302e00350120064401501744110140e050994034425000703401d04c08d01c00c800a05055a002103400844a10054034074610801036000307540041702040001841d81d40354034156035003420b004400b031a2203070101d1520800c04600410082c400030a001010702600301852080c4021602403882075504c290403401e80d880c100085000d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 645337491 1250 645336241 645336271
    0x30209010e01022410170c0a0e0f19110705150f10031506080d1e091d090c06032e080318030c1509090906130b130209070f0f0305 57
    0x4e9131283c100103410064004044048a03100e040350311011003c00a50440da07840940d4408440c01c0010040d00200001d141240441c42c0c415880b80d24484020221000c00b9151100700204c03148036400030316501a902c24040d155100c514100b5501c08991b000751440705134140c00104100ca040079040d12447c002c00f83c86880511355a10450f107104241843d41186880e41d0002c01d111404009001900c40380b590365400e04c1d01c446920780480b25100b40e000c0e0400500c01070521202c01c02d42c00449828614800420065942820003801c105452034034660054000042c841054240000c00b0b032214000d4400c026884030480c000000e42c0034520400c0101e810034404602c0d660b081c186000405040601078400c030050210000d10200f41c285503054005501041031061820f00d003c0c078684c49403810317008202500b0001900c0c00025011000182145152400500f170341d030900308035000c2d456002e48415003d003004031020741091010219030300011200802d04007124400c2c029180288188401030507 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 645338741 1250 645337491 645337543
    0x703030c0803090a080a0305040b0c0f070b0603100e06010807061b030305040312050a020c0c0a080c090c070f0b06130b1c050703081815030f01091e0903030209010e0102 74
    0x707950401000c0000c21300500c039103c00820814401003801000315580003905280c1032070104e52200002c3e0031840511402d01c9840c21080c503d0040710076580d00300c50908441e82d10900060700d010078802d01d4488040c208000390000240000345241616040d02c141d4075540e48445c01210b90b01c00004800c00d40320f14140d00040860301030742c41542c01600900c0c01a0031590149868000d80384107880011585900143c03c4540c580280b00b50180c582040302c10710022803825110540c0c0e990304c0c0c04814403403c409804510051208021a046582d00c0403504101d11440e0400c084011030440380c490241c141740204000e000550b20034203142007401001d4580c40044070394808100540b41c80c0849540c842c500c000300108081401519090150200801841d41114144809802140c4003079490001c00d10500c803800702c0617400d6a065820440b4009904996118088080001451103015403407078035050400380740d07064004000c0e0810a0700c540d07040001c0d08004a9a691040c00e0042c503890f05154288 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 645339991 1250 645338741 645338753
    0x5060f221b03060209130b0d141c123209030418060303030c030b031b060d02041e050a08120711090403020a020405130b010312020120091003022d041d04140703030c 72
    0x1115101250080780e0120091041c0ac8005440300041c2d1000308280500c8101d4500701e6008118401e070074540c2800c00c101c0f111039000750034640c405070044140c0e845c100003519200c04005840080c8000074607200e003800da001401d801008903000c02c3d4006410b00d060090228000c0c0030b56000c608000d0001c041c5502c0d194107a2844419188440360301400030400722040700c07960300141000e00b00b899021002c250102a5070b9460004561000b4001e0b091008100802c07800440d003e42c0e0503ca181400d40d448582d480e01c654a540381c07140e0964004c400c10300b80070605a0000b20b071440f062081e18108180e45600403911621511440c1c0104407410210060000480025034103034450901d00001c1206030300103800301c0007001c02c02410a003007000843d03044801e00d0101481288d007152030804503e04580105141c0c560140034850070184460701d00100c030800d00450840d8010030b0420101c00201d444451036500c03000042e00c05880518040400880d419004100d060450342d02d07403a2403845d005155511 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 645341241 1250 645339991 645340013
    0x60603070e191e090c0309080a03200417120c0c01030209040b03010603080a0e0d11010c0c0810090606050405060603070c082505060f221b03060209130b0d 68
    0x3011066542d420014003031115080c46110480e206200700d00392401e0031000011240007840b03207030800d8104204100820103240454220300413914020a16503042c1d405441002d403c1c041102c0d2200c000180010451804200901e40d0408041500c81d140c440700902d080303a00441000da607003900b01c1e15601d40558007981c0284030004000c1d1021440060305000603085403142d610541e800d020018201c041180e00c2100741c0c024020480d9414544140c130345950030750a4041c0841814041d1021801c028003d000c0303a03660040070348404444120007410780040c00b51818a404440040c24a08040f0301d5103014020715100342400380c4164110764595204071108540820150f0310440f0406c40c644d20386802c02c0032045031442d08202980305004501c1e24525201008080481c1c40d2000c10a11a544c04403e8215155040e8480316281261040c10a111644401703111000c10b50b05080b000410000d05402510803014121020f4800500303040000e41074484d00c00205a00000c544640c4000603200006 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 645342491 1250 645341241 645341269
    0x60d05060a1d0a030201050910020c0d1209020409051c05070b060f1201050f0402090a0b0a0504050601030b0d11042301060f050405031b090c07171b0304030b0f060603070e 75
    0x1075421081d0a0724a00f441d00090003038005075180e10400414560801032484c07188222a0300314508841c0130815905d5020b164488010420401610000b40d81150071805103c0d40040040041004e50700c2d007240c1e211200249600141050031401d0a0b490192060722040c9070411052040c0b03070388440c10454480d000000c103951042140400e205c0c01c0c1024401d09103e4561400d40500364241401001003080c0000e14151005082100f041103584644068400303e40c019103000c25191548001a4040d011300c02850340c00c0386801e00d00324144807502d200e40480d810107131801c01c0140040f0b0610f0b0000d0310500c0603c0c46071a10b0200401540740324041000b0700d04000e10b002400e250300d4800090800b545141c40481c16510145154280c1c40d02101103500a090804518034141031992030750601050342075154003103040802e6034065810458100c1c0d00012600068995031600d82c80c3c441c00d00c00050301c10394400c9401d83e0001d850342c02d051049a001c1d580c0d685070f038083c6110160420800300d169900d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 645343741 1250 645342491 645342521
    0x1d0615060928080a0302030903060a1b03050402060918010302040c1e11031c09060b091b0c160b070c050d020f0405090c03012d090b0f0a02071707030305060d05060a 72
    0xf0240000d100c100c003c203109034051035454090b10109071602c040034040c1e80043d4508500380355400c0d110350105c8158001414007103425035030b90000804600503007100d583c004440d4201e0500e00254890307001c1c182c9108a4042061786c1300380303108460348421f0f64480c0c0f900c1041c1c0c2d5414007015000ba1000c40405903010103c0e850020007460401c0581f14403048050b50503100c40b009802c0110034000d1045404054070380322440d280c0300520300214014038140101c500c40c0000d172641015814060f503424440e046080006407951032060392513035800300e02c00b503034040d1920b400440c040c58006c9510401d00c0d00285000d007000004400c120007894090110310403031080000040312514207004c1c140c0c210103580107080020811501180e0300300c0140351040740c89440c2041500008500f81c5109400c0705000c0c02c0382c9041e950300380f00c020007481a40c2c2c024010040918010204040c94002010440c0c860350781070100f82c48134418088490340c50b05c030061160304007100184d281d0305240c0c011040c0340349100e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 645344991 1250 645343741 645343819
    0xc0f03010e041b06110d180519050603040c030c0b0703020c040c03091a07030f291206040b06210c0609040617030c0708060103030c0201030f1d06150609 67
    0x140e0ba541d0701d5031a8840390100b0140c5c0c02c2c2120781242403003440642c400909202c00701100021143c848032403a07008051060850302c029807240b2041900c0000a41005040d0981c2d904103030a2640c6507102c940700440d420310021380c0120310722641c4000d5400c69545900104102c1c0940d00410003c0c2400710040010940e4510304040440c0100030849448405a01d9000d001e0400400050a0f107200011101d01c80d401c0c5800c0052030044440c00c00f8022203003801403281c00d84079000140100720504032086291040e0b10501043c401e0302203806000d80e0040307414407022420b0410b050b00030640b4011003001d94001c015412007605101c1c0040c8a03c0400400025000b0740300c140318605181381078406400e982c000304d00308036600c3c03041120b04042c1c02540e000745165890355a004042c3c1c0c44d5040c00030704058945c03076003803100c44403034006100c1c20005881d00300c51254541062555428125041060700c602111104078030709007502200c0039500b01400c058491680a000202c00c20048005660041c0104c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 645346241 1250 645344991 645345023
    0x706090e130204090c080c010302040e060907050c1501061b03170606160317060103060302090118020409090f050c040b0d0b09120a0809070b0f07061d0d1101050c0f03010e04 76
    0x152040441c0944950171000b5074a0901050616007114034a685042c180304201c280224040c072020329a1041d81182e03c42040e40d41c1141c1161a400380d01000416131282002804248044000650507103c4c507595948003a08031039500307142c0d180b40d4040503000c00c440c20101c000481a412029510a002604103460014204135030180ca00d040f04040c0c1c000340709203035000c550030102c1802a401400900c4d05000303050640e00016a5508188501000400044441001011290156070041c40f098100704480546c50170009810031002104580e2800b0308800d1740c60501e002c0c0716101003e000600004680e0000f559044201e0401034620480c1c0d109034020070b108500f42c11f00501ea81046903542003c503003080d6240b10705e41a607980085054a006000c0303007030001c081c00241d80f051034001d03101141071005400210350389444402c1da0019805031404000b502500559111320184160000700640c1d50742000a400d80c1c0507501c005c494030b00c01000100300701080700340f419070446d000b101d0381d04a803042 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 645347491 1250 645346241 645346249
    0x7140102030f03130f140312090c09060d0c05042a02010e030406050a140d0b0a0b0c0c040c030902090a1e0605030d050a05131d06030a030c120c080304050102030105030c030706090e1302 81
    0xc04030f100072587c80042c0c04800e00400d1601107400c0300065005005103030344030380041d201041c001c24040c010402140000300340306107201c01d18000c000150041102c0070001c407940b62420192100003200304d010404544216105209980d204103034500a50708160402004481a80c05402c0140400200d403041e0780421442100514080d005038000241c100010307030500003941816481400034010a0080c01e0035100e022440c06050b0710200c0740051303000341e0091f00390f00811031100040d4000c41280708000c100410b0340e00c49009081d11881307020103002000440410b540f080c3c0101c5806422030780340009128004d81c0580942c80c1c0380d080950428040c0c4408140450269106038091810b01200031030821411f0107054001c10194042c01e0285019140501419904440100012210a00b039061103200d900d101d104113620a900c184c0e281000e040850207074000703024040c070034007960030070414500e80041c510048840343d8403880c50803840e2150160102d03c00400c4260001c0341c218101c0c005941d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 645348741 1250 645347491 645347513
    0xa030f1104080d020703050615120a033204150302091c1707240b0402130305010606050901080412180905040606060e0d020409050c030304060207140102030f03130f 72
    0x19030340100c0d61514908420b4601c0d101281d0107040564121000034070208102040300c0703510188849105844460a40105054250b040048001030040300c000c4002c141c0d004104501d40c060402403a400e0b508001100b44030b1110078004a800d2400402c4100511651365420b8841660107040041c108003105002c11203200103c480c4c86080c0c038801108100700400c0e0440301c9504040000c41c0c90038400941e55800d04641c0204c48103180c4440c21620801540c034a800c0b04400784006402951113059134005010300381c07100e0000321655400c1050216540d0f22410945803000300503564031b001c540325500c401001105800002e800c0181c080d145a182c1064001800014040c0724800582da1505013030070b90031500a900300004000c00b00c44281841d1350341c0460000072940440c3c001941c68928a000361410414861168140c0808240090a07940110f00203007218942c120204c0c0490340600120388a100d40c40118219034018004208072240c2c00340305111552148803081000300b1581c8440010360 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 645349991 1250 645348741 645348761
    0xa15021e030a06081b06070f05010f0e06161b0f05070605120f060604061b020405010f0305061501120b010210060e090706110a030e01140f0403061d070303050a030f 72
    0x10000000c1c0b0596041034450003000300188800340c003040d64480790402420746640074417031280b04042110014011120b002040c3e680d03100008002820a42c102c03800544403000850355036000307010024440308000c0784005652503066a07010b00120160311074a518001c44041521a100c09040c4980001c0d0200004000380c0740e940c40e003545a11090004003966000100716020403a100828024151140401d032030554456003080751107600040003240e0001030170003010394410308180000800400740541c0c801030301d010340252401a51034120000300079072494515400100c0784c802595940c0d8595105c6002208148152010740ca24020014161103242e080344120b1014071061103046441001004c00030489410004003081825403501c0d03d8901c903000240500100c12003440d01c81e840358101c079090141d03080e1850b1f2a000c15000000780e41e0441c4c00b08498003450310078032211a5000ca0220394940f108900141440382c2142c1d01158a40c1018142c3c106040d19810403100310305803805050080 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 645351241 1250 645349991 645350047
    0xd150c020307121e0f02030d05041103010b01020303100b1605010218010e032d01090c080d0206071b030f030e0a0b04050d03050106020d0f091715010f080a1502 70
    0x2041e10b0300305030768038110b200383d100140324a020f0140d400900d5906003004c0d80d1410b0400a034090482d42080c2c3c114031503280f040240500d41010001088083d4581c00040ea2056000b00a56072010005999a21040c0c85080076075100c2481080621900340c0108401c440066952420702c07415074030107017643c01c00a141078031b80500c2c000d0b0901550f40020345807081c00d400c500402c840f103000003644400c00c0203070071195002c0190808209207034000b508002074503503000c40b600b031080d5510680d094883c08203040301c9005002d5980072410303040c8a54000810264603000c40138182c022694161003044c00401e06e0b0342490b4031074404030100709051009490985c02601000412301d800d1500c141002001c0c1c0203002810f140000505c5103507400144140244400d04000710020240c04041c0c41003a255031000309845112600000d1000e808078926070140310301d07000c5240990b282c54062810142ca40940800c917886901c07038101190b08001d402e040880d1170000185460b482c0070b400b8905d10500c0080c0448 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 645352491 1250 645351241 645351247
    0x4050409080733050402120a080406021501030201090e1b19110127030e030304090b010e01020f03033603040302011701150c03020f060a1a15090d150c0203 68
    0x1400200700005800040c840184098402440483c0304915031441d5840c5500d136403180040d04644441440c1800d2070321607401c49210300207519040c00300354007600458005008489003603125800c07e9549605a035416103910341e0352414950300890f405001000c5110702c421401c0440d01382c111490040038140010380c0100d802e800da04002038100d080d185071491850703251010b03941042001d1100c08040728015400761205141a04007143d0089102900e240d260000140001700e11900e90720504a9480a88900031039941140c010380c1c403040003941c810025002000040c4840040c48004148540e41c5074460b969800700310741e65028045201205c031a01c0d03000040030302c255a0000c28040710181071070b07041a465030512007550056032004044405210024004508141c028005454001d0701c071411940c241c0707003060300c0001400c3c110b404840380c001c04900810841c00c0446900c064800040351951808241c501841045d0030703400302c255602e8602c2c001d054501d4903070707000351300d880200f0790b0045407 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 645353741 1250 645352491 645352493
    0x5030f28020106210c090207032102030406050c090d0605090a080408010501030c0512210c010e01060e0a020f0313020f09040c0618081f2c0f070e011802040504090807 73
    0x1302ca40d1400c0d1000a2a445040900014001d00751502940e80d0f409016072034440c940f4040c0d441d060510b43c2020b002d080100c4042c1d81d440325a024502c2240200400d2146071211140841d507486144000e03900308001d85107a801140c03e03600515048040c3e2003c4070180301e105d40359204640c000d50004812a51110f00402c280f00b0050b0181020b010210340c0a8803041e43c010302310b6590305040d5004844c4080e0764071440424a407000988481c208524003d103c40c03110580040d00030b004c68001c0703840030b9980e48081020010301d80309644100346022092171541d00d4440c000254122160700490780030080e41c1c030340c213031984580340d91034025449a82107003200d5080c1640501045503005004815003c1d00d039080084000c00907000403ca403103440b4540039140144c43d00b03070107024080e202648240442a6103040d03e04a151310081203e003000a0791940f51041740c4080d00c81959100310410b02d94104014450140d007410314654810a91400600d041d40d1000800c00303440041805640c4841c02080c454 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 645354991 1250 645353741 645353759
    0x705060109050f01230118260d20030903160911120a0b040e0303160e0604060c0b1e0f01030201030c0c02010203040909170711010f080405030f28020106 67
    0x15000781d02403c0c0401158148410401100c4403151200e81081a052004003640d00a01c01d208000030440592240c10303850b0314520403000c42440b41440b0620324401800002d08020078114a10740e482e65408010043d9100a02400058504111000e0008001140013036400304018550b00820005180c000b40c0f8101a28084541054031440305010404c00c041c0100100c02d5402c2e800138480c4c00001d0010700c00c501003401000ca4140c003918502c40002408141041e00d0503d1001c09155079500f44039860800c184450742c0514840c0d540030900310190400014102055507038041003a440d841c074010300e0b2a98200341000c05855840d005441070b001402035580c540245442c40e01141007054034800580d0000395030740708a21402d00900ea4070f0014100b004454440102070120a1030707441d480301c000b402c00d500c000e1003514400f808034555420180742c89020b00e814a1086400c1030256040c0020815504003940c070181440740002030400b0100c841c0e2640e0100e1001000d0154000241d8604150881e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 645356241 1250 645354991 645355001
    0x12160206070e01210b0d03050d150b03070c1e06140a02031509070306050d0b060f0d0f020f0a08060f010510110c0d0804120809090f01080d0e010e060705060109 70
    0x15010024011a0307200943d8210360142d8044075181111a0204603540d03601c0014078501401c45c0c1c1c00140d0746d13003020a1550010141c4030344109d560041000c5503c0412100c1e00c14130b64421042c0001e4103200084800d07002d00b0110b140c0c01d005980c0700340d0502e800d54810310b03220201075040f071b24140da50350f00c100b442c03030780d1a807070f9901002c0c803c821440c41c1040741c81c0001c03000440c0c8240b8031034000d940000d0f60880c442d8101c80300901c0c016091260441d5070b403404540d8440112403e80c010440240c0c69400b0f8542200102d40103a041000902010300f25000d01c41c603140341c619480d81010401000040c8507070308110301c1c0d204501c8802000b940794100400c00002c1810000c2e4038041041e01c54140c242d45002044031040308504a440040d2030800745040c1c4024001c079440005d44581400454051002c0300d801002d1103c01100c40904540d944128400125400e014120b50356011400490b881805988900c92006050502007900324000000480076808401e0031074141d00300000400400c2464095 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 645357491 1250 645356241 645356251
    0x804030c060503060303071202030d090803180a030c03052107031a03061605072a06030e0111071e140307020f03010b1012200a020c03070b0d020f12160206 68
    0xb05501d542040c01c0084d80c0c07406001805007070340402c00b0200d66964020400c0b21b1400b460f404003405640341d1800c24140c1d0381c20448285034138028600480c4814a404201641c0c6558151150b8481d1a0b2030b4504642d00d81145000710102d511910109101024582c9181e10071a1580e0380840c40402415103030000406112a050281d1b0104042c050f10f0600110785144800d80c038500f0544407011820306a00e8101c0d0b0080d050001d04004d0440c2000342a5030ba00d450903911552028806045081009802c8808d0040704850b2400b06000c14000070300e40000240050842e20018102d02c1010385680c5217030350001488003026030000900500b10700700f4201c1a031400317600710003c000d410001804100030180d142c01c8002045456010907058403520b50051100b80c200d180407034000302005d04102000c0c0e0041511902500c2482c6581d07005260020303141c3c0a40c2c028510050400544101c203c1c003a4200f001187c04c86103050009507054240d100f0300324401c00910440c281c031030707003040c801070308000f40982 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 645358741 1250 645357491 645357497
    0x20d11011b02031011130305011512031b0203010b18010603060503010e06010e04050f010905063102101202180901171203041722050301181205070b01030804030c06 72
    0xa01c507000d642c2c0070a440750319000c0c1640118051004a07a090498410284181c40c01c441d01c8a01006000c41580006c401a40b80014107161548404840100d01200304000300042c2c00a00004420780c40c0041000391503101800100312203070f410001880354503840c509110400490b400420215615001c2d400c001e040940c0200440101d1080c0f298481005008854040c403c4101040c1000070030003c00040e90b03503a20080003144100d01d80f96455900a030b81c11881c00e20400d60359031040001084846000c444816006a03d0400d82d00f8805804c88100c3c504040c0000482c040c0c001c00001e00086ca16045840d416460965039102000011403060300102c000c0f03503110703000c1e0101d40b0300060511414054803007060b8884c5c0c4d81340340c81003d0340c6e4217668601111034045005c2c940c031481801c042c0c042c3c8200000b04440151540c06241c00c85500302101c4030400c2d13900a5407000f03c1d84603103003000c00401f1441c00c0303480c110003600e80841c001021703401100d08000c0040d0402c05d000022401d2005054103103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 645359991 1250 645358741 645358787
    0x5010c030c05040e15150d05060907080126070f08010b1e090703110706020406080609070f36061e02191101230702180403090b0c010603020d1101 64
    0x1500c1c541c0c1c1382000900780c2d00c0c20f0700c40c01c65004040e519890801000590b00694030b640e10507036100c4d10007a06041c0d032510301906101c1c0101d00c10754065036420341660900b9841040006807070f031401c1d01003200140d10044030300410b540880da91400c04174940103004040d0020480810a0040c00030344440448042d103101e940100c82000c95031902c5420b03030040c40c42c0c82c021417101440003c4003a0792050400090070113200140016140e500a91000e1040401b00c540c00403070741c2d611070b06450440d0382001c00c600040660280400c1d52500e0404c0448501c00006042141c151020081060040b40d40184012580304008100c50312801c103113440c8210f5503840548403071301c0c2400851400407d2004000e140840348895a0640e0340b05405070f41c1c6010180341200c941100100000c0419405400242d0189005007801c40003aa060018180900d5260b5a101015443c1c0b441c1c801445c0c0001c05160465501c50b9000009a0b89586204242c640520a000180b0350103500140005041d59005240d9956903 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 645361241 1250 645359991 645359999
    0x100e0c03071e050f0d0c0809011a04021c05071707020705030d0f030905070f0f0f18150f03050114071d0907021926070807032102030405010c030c0504 66
    0xd0504524001000d0b150880204a2841580c143c040c000300b09140340c40204891301e4051840c4c01c4800400d40d0340d203900c041601ca102895083e01c400040c0c550070440d2180c00000c080c207041d801410000c540c004a10781004280440c90251401519502d0014011240a0350102c080c030000542191160000307050301890240882c0e15404078140501c1808407450780a002c050180d00010030382640f01c003d80d2195510740001003003580545c001c450381a408120045002401400044217640c03841d45800c442600d080da402003c1d10900c000c903402078403403420001d24084c000704138002551041c8004590381e100e284001500e00070043c1000104040041500c008040c017a503c0d10366954203644400040d603d0850503464004e090072040300c130b603e01c000c01c8028010300340c42105032100b80101000181014030021540b03806030050107481030b14208040c00002e405540034601f641480d240c64032340800d002000900702e03007003140d056030165154954074000039494850403602c0051030500c1803c107824 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 645362491 1250 645361241 645361247
    0x2010c08010f05060d0609050709030309090b0f120703050a0b040b0a0b0d151104060207080609030306090f1015020d021e07030312090f14101b030b0d0209100e0c0307 73
    0xc14840d01c1c0c0100d40014a8045d8241550080d401602c4030789024046414028001490702a45110942c001003085001060789142800f43d1703818140010110f01c44c016585040144540807031501003407a10840307000000080c424072038841c515028007110038051410303003440900000c008252800c02840c0403600011541e40c1c3c1c252404413504140b10140141043c5030200013080040c0310301e10902c8002c92b000403150b1b4001422829903030213a00b55412070b07c8500300c1564034042a03c0b107683c4402c0c2c00001518040418141c2540400d001da201601d280e80d035120003c2080d5419850401a0011007180040741e404001a544010916460000301400118001d031100c020740801805c2049000c040c03150200250040b00380b440c0c1108005240c0c1105240c010045c1001e514141242c1c06072841d0110203114074412038a402c018003e102c1c101d0340794030000f00c0041005a0009030f00c49080006140540c43e216030343c1703202e42c420032030504944c1c2c00c0200700260041d0043c04010784030004c0003088041a4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 645363741 1250 645362491 645362519
    0x80604060308071e140a02010207142209151406010207030203100f0b090f0103150e0d0f053a0911120723100f02120d20040602010c0801 60
    0x20300300d00180c440d040d600b40c528051128120002d014541e8440d00119001c0000c07443c006c000703200b40c00300d4660540c0c1d40e541da22843e50000c0400e512454125030024900b451180c588400b08500780001307100000b0340c0d1019107041c40108540803042d41c82901c0380c502441d405801c0d41044c400d0000784081c600e981c1c0042c0e035400d03602c1c2e0300081e5152151150801251150007000e0703942802005042545040c0c1c01e07610721854244019100400f4002034440a071000303109070309400b41c10401600c12803041c0300055400d00e01ea102994100402000b003d01c040030a02e6035008403400040d10041900c00000a9181e405504402d1200f01851300a0800004042e0038200d0f000000c140c6103400c07048031031916241491542d5226a40300a10100613034000f540e000c040d41920001150702000311002d0800c100c407600c11100b00e003c00350744a520a03805401c0c4d01e00240107034664118022071101084005c000490503040354503280d104000c24207120168084c0070708490f00d00c40b45003a04c01076161052540d1812 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 645364991 1250 645363741 645363743
    0x3020a271802040512060402040c08071704080f13050f030c0a1203050405030a050c040c0e09040311030903030f03100504020f030f0c0d1b14180108131b0608060406030807 75
    0x1004070440d01c008080c1c042d0b40013060000c100c900702d20003580c0d800ea125101254202c1c8134900c6c0ca4000c02d0882e0060030018084c0c10503617980c45550080e00b43c9084008805003054680744000d00c400c0790801c1241e80181600e111107504c10340c000385400c1c00e0000c04d40d680048240300303400c50340540c1103d48031410210304450b40d017860000e1501d042d042c00e44480c8100e41146806018007014141446030010b201004800b054404000d00c40c00068200c1d003008010f42070320341c00401c601c0030a003c24822000d03c41d00342da00c50281d070f14020000000031301c4c42d03104942ea84c100204c0841041510001c00e40b07124001c0601382c40c1545411034074a2008014800207090001420a0b1000305c1d00c8813924405035001c1c82c003020010440800007800207403401c03c1c55440c02000070003503403d90540464910503240845189656601908a01d00043d58020001400005901003a407800340100d0340041c80c071a05404c0414200d01014100f05004008050041003039014609000b400c01c00900904100d81d01a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 645366241 1250 645364991 645365009
    0x50c0a08060631020a080907090902100c0c2c0a0501050303090607110a0e0a0b01111e0c04110408060702030403120e01050c010e03031806040f0201141903020a27 71
    0x80807088501c41c40410f850041400d0452000c6628181c19801015a41c001c0c011101102c0d0300c0c1e0340d0b034825071782625100710b00203410080e4032241c80d0341d10b030040442900880c800c1d04103c0714903407100010400304030070300fa009008045182a001c0c8803600d00b44d64941100005006122640c101000300b5607038031031000c8090252000003411001e205160700c1030306c4005001090300c603003ea40e82130a001100c005490038a000e034a82040440198054041c12842d00701c180007400841003c084130105449003000888142d004044540b14213544510440c90040c541000c0c2c0c40d100c40c140b40d05149440d200030704107010340d07000700400d00104804052901180e0a246000c040d40d41400004030341c00e0086d080917249541c00c0000b9661411000300c043e6100e1111000c110012407901c414a40d540c850507500078144190120007400035500c201c4a61500300d0f601049180703001907580c5c0c8002111000d100c800002580455140d1905038007150003503882c102080d101c008181341c1244210000c145101d01605 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 645367491 1250 645366241 645366289
    0xc0510021005072c090c0306040f090b07090605040b0f0f04090e0705030d0306030f06022203030e0f01050f0a030e0f03040e011e0308030c03060319050c0a080606 71
    0x14080c800c1204a016a5801030140410f003003480e0b02500b0480e018003001c0d922032500c000c0d5405580e09142d406604600284074041540765481002d000c1d0b400074044c00c0d00310340c803051070801c0c0600c9406000d040c0e9200e6881d065080c03414010050002c2c80765042407040100401040000001c0d038070030754400d40020540307aa503400501d4100e0f0400d106683c880c0c400c050410401980b000404502c03a0b085417416000d80700d5031010104120110f589500000344042107455960012400b140d0140c02c0395880c0342c3c1c09581c450303c0034600c4428402668001c50000d41825030380e8120f420243c0c0c0c011040c0c0c0007030034210f09140c8920301d04103003802408514010140d880101658070f403006c010b662000f9a5080580750b41c0e6885482c1c1c102800400d014441c030700f039443c04001a02204108620045a411100716411622140101070781540041d20143e8940700d805045101e2484a4582c004551b01c101d00a2041040101c1803010300180c0368000c5200e500100c0c02c10003140c54400c0d0081d0211192640300c58 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 645368741 1250 645367491 645367519
    0xb090705090103050a050d0f0f050706060323010b01030c0c0b060a0b04060f0801140f01081005040501121101080105011b15020a2105060d02040f093206040c05 70
    0x11400245520865200c11500000401e001011079400a11805131094584010300030900751800507000700380c580014590601607003610b01c00d0002e8101c1c288115000318800c1c2d0340740c80e01c6500c0c0112481999114100030040d0920440034854145034101c00c4c00c050000802158014100c0002c403c0090700e00184e59001540960ba90200030001c0c0080c01142c1d92115122140180302d85003100d10100455100c1c0d001042c2180720001d900c42c01c0070000c04c0500c5a11445004443c4140040e00700b0103c070840500102d0169514000c0038007a240f010b1a8140c5003181f030030091901c540d403050306070520655400601240e680440a9080f11b0030307885000600c0c80140c81e2000d903480852411014603403000c209041c1d0320b076100030801d401403101000708551f40720360740b4541c0c100c0781c040d1030b81c1e54016005036002c4010b0800d900014178003800381000050100468075017400524428160050034402c40748840ca49005581d0218441e40581d07004160307929141e61404407141c01c2d40140ca1080c0c0341401c101e8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 645369991 1250 645368741 645368743
    0x31501030f0f1a09160e010b031b07060e01270b0109020307020c04022a0f19140f0105010f09141b0415050418020c0606040c03020408030708040513020909040b09 71
    0x3060643c00c804400054034101d030206443d814601031003050303030400032000502c1c100381c1c4880e541600c880311000c5165446008000d07240e60300341c19581a0059091010707801091703091040700100000c2800100b0380001d01d48420100081d0081004800b4010110307001c0491070402030141900c816100c0160741c0c0d1130342c0d6016441d0030804241c00f9030203800007541c4c44002043d06481d011180e225181c0b0402401d10b1242a92034082407001000d21341d00c070702d1001400300b01c0515036200c458080d50b04c599101601c2c0e18407d0800c029920303050485c0e91070300010080e9011071a107c00081480c4101044a80030030058034030303d81070260011441841c3c2000310010b05280008503802480b44e000000a03000241c50b010b00107410600c500100c83e070302024110a44131003402201d600e07080f060040d0040f13646241c01c000082c8a400e06900070103030700340400301c4c00d040d0400051401600849600d51202d10740420040102050031100381c91034010300441d01a6200c024002c0c1e0410b621425901e0140c1d0750700c1c3d85d1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 645371241 1250 645369991 645370013
    0xa080a0b060705280f0b0402130501030302010516090803040e06180108070305010e15040803090717012c0303012337050609060c010612050705031501030f0f 69
    0x35640c0a0400541c80041000005104031881920300d0307055080506507031401d01c0c6041040014200c10f0f100c00e034040c0001c0510040d43e80c814401448407620301d0244038040d003181c0e800d030001c40250390f442048c04a45000704510b85090006031514100182c20310300050349a014a203da08500041d940100d0019601c0072402c110030310794104811559030356003076480da94140910094800e540390004003090042e0200c0e140c03100000d400010b16164071159200640c50740f008080700c86da4003d40780c0200e0990403542803100005178450000c640001220b1140b852207580300944500246d03240c0c3d0100c3c0d1180044140c90444400b262007100a41402c02c0c02c144816001200c150711103981c0d40d03e40a102d0419005071380703000b50744184590442138800c000454038054040c15602c000c0c00d01c2440c01c01c0c030307100c5c004100b08082d9200200b20030755148040c556941d104901103d0a800c0714030144190b00702049549810a0101c800c20595455a181c85501500409000d070245850b0100081804001414 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 645372491 1250 645371241 645371261
    0x60813150b030c0d0b0403080c0f0406120e062412250b1909050f012c040501030f0201030e0706050f0d0b03030304060f0506012c0301090b0702010903230a080a 70
    0x50b05044e1051600c40004001114200d021401003c0416009185a02035582d003140d802c215501d820704102d000c1d13800c19500c5002e860102d407510711103007a9200a20000b401000d044001010100104903810003851b5800d5001d4020107810100700e13568040020900c0c4144ca1021648800001f00d045610700e600598210107010200007a48481410301000105401952681d44038412a00d890401c080c0310619405640021500c8010340004a10344d48013521002c0030b03403c0c010a01d2280c0001c101a110240e20546814488020358000e55070940550b18041c803902014016041c10711001030614041d5641c00c0c445170401180c1031601610719800740342607950080803a074403454240742c9900070305900160058050300344400b080350783d40100d485403107800052000401d200380c01c25213041603800c0c00e0020b03a071541d00c8200138404290f5075060305d03010b10541d0380085114826810081c00821281d000740d008880e00da00030b10040c2c1002d10540f10400a81d01c1d2600d002d48450340c03003001400380058 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 645373741 1250 645372491 645372499
    0x31d030705030312060307061e2a1103060a0507140a23030901060b09060a1101060b160605010501020a030c080a0e090a0605040e0309010816110313060813150b030c 72
    0x5040c0000c03104d80349405d2041c0760440480fa2899150711f002c44882c0721402c079030143e01c0b040b048a003490318000e00d002140b40000c00b04158601c16a10a104000100008150340c40c11110050300000d0070240b00950b80710380c00a07800c4c040d50800b958028210110031261952182c0301007401c83e0311511503510b24a50181040c800c502c401d0402c01e4008056105544030040356107040710000d816503c0d5810360b80040d0f0020906818054800c900340c0c0c00d513100d0440c000c0c7c95544c490000c2500819580605500311100e070845000c80404c4c030f0450200ca00681045040d544021003000010b5445075803407031001c0e440740c0e0140e1504d1400350300b61901820625520303401400d45080192500c9154015070403110102c5d010b20026200244207a1a440790b1a200c600003980000018500109010480803042262600c2c00062013160303521360071038020001d001100041d1940030051316600484440e08104580010040e0a515513203c0d2219108400c80051442d140c1030300b611640d4051080540e4441c000d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 645374991 1250 645373741 645373747
    0xb091614030609070f05040b01050c01060303091a0412030c0206070b2d010b18150f030a0b040e0d030509071a0406080112080d09020d0818040506010c031d0307050303 73
    0xc4050604504419103029114400c005401e0030360006001c022280b500d20031036445814501400007904025001a0601104200e0011151824850035005500aa4442000d00d0603d3b0721003601201400d03410014440500041c07140b6503c0c015806501c55141c100004580c02520204850b8000c03113a001d85241d9501c0100b0803041d84e03414600c02c2e04d050800440b0f404070014000d81c8a007940071700440e80400800d0000545000251110400594005014818a0029000001c030a82c08000d0500344c40f400481404008a018013070347c80d4564044805000c520205107180d9610101480003008154075403011607860941803000b070f8050001d602180c40c141032134130741e0001168440d1150700000307074010000007155800301d0032279150590301c01e81a510b0b055101051070003400000006036840100c0004000001d490b103001804090040242c840025000104010403103100405013418000003052200000e035101090011000c5500400c109802e015030200e0b00d08a10b503000107070184000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 645376241 1250 645374991 645374999
    0x31205180c0301150e040204060b0c01060f06031109010c060e0703030e0a06030e1c1704030e032509020c210c190201050703030203060123090a1706040b0916 69
    0x60384440c86480c009012118103070300080070316080f82c0101840ca030340c5800201003440840c141000842e0020b000030000300342d82d52210017050b100d038030020102c20981e5544108025081032114503070014000b0f414108450780c0d14000b41300c514881c000b10f46041040754207418081101b258007029005160104892210b602c0f0316000c1d01c19500041c0940c455030341c000b80050114440d000e041440f42080b00541031072511710011410740d580c207404050901444040c08040307101e6800e54544154041c0d9100390b1920b546109040c01c2c200300000c40c010903ca1a024442801c107801040000c503580c100d8016038031035004001d242003600980711107620000f46210180141c504070050701140040805039030207208460403a40909a44080003404520306002c01404240a640a5548294103041c408a902c80c5003903a01e20800c10b0300320024000300d000c01c4140c16424a040840064004494242c0032081031000b4240d40314401031008064144800000301c00060078801b0180c09005011407503440c3e929 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 645377491 1250 645376241 645376261
    0x60703060509100503071203020a06050408041706010e19060905040809031e0c0607061b020d030f020301240507080f03010e0c0a0e010e0a17060a06050303071509031205 74
    0x20340c401d9a104512141c007148124400101d5075003100c50084c010101d071490b1511a180ca1007001405505502070044d240340440d889000d445c0c416485084520b07034030343c00c06000e1595105004126150390340910018000428140c103160b40011004010f8a40090100314070b1020700360307a8021280301c9007000140410450140007410040304101c0c240c40300d0030042d043d90b1800341e941032415005035100301c50110f01810b140e001003e00d280181d101090421407a6820404206003842020059101554042541b5891300c104251820303198011b41c59949081000b0000c52044d403c0b0104900846500c07001c200d00940446103040c1c2d000c900c01d5158801402c2d80300c055002481041032048204001554901071101100c01900298860b0a00e817903c60004440c40c0402c1030303450350003002e12a00441e92400060350011440d00300c000a00c0326180421942c01650b0507a80054000c0d0700a10041000130404010160100c0a447c4005801c51050504481c80700c400c08801001c649060309001880740e03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 645378741 1250 645377491 645377501
    0x70614040f080a11180601050d0221071e0e090c0c0708010b01090902040b030f091e010f180c03030e031002160c0b1c0f240810050f0105061605060703 66
    0x4c0034014603101e0240e00400c1c000702c46151072207452180003000c0092020341c00340c005020038010445006042075440500032030700c21500021412104003000410403d1075003c1c4030680c0c08500881c03290040620390a0240c030b00401e80d0b980510906082c00010000843c40d42955a4201d4840032116215610300c10360f8020400310700280c0c00a1407055000c0ba030f00c6410300031581290881002945036640b20b801c80600f20710040c004a072180074030000802c03880619110488891490800065800c524102c07070000c45400c54040325608024142d981b01080b5403c00c1130003200c0c4c141c10f00020b0612100300080c10594a17071411061180301003405c6030081d200303814042c0c403a8445c00b90482c081d40c90304044100f900540041100b80c6403142c103940712410054102c0040440542804030380310b078800c5021064075078000350054a0030f4210508109401040015000031041443d040140b802c11650300c6c0f1a0840c140aa1030040b600090581c00b2a070480707801b40041074011041d284141441100200544 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 645379991 1250 645378741 645378743
    0x180d05190c15021203040f06090507230405070e19080303040c1503060b0d0e0304170d120c0804030e031507110d050c25080304060314090a0203070614040f080a 70
    0x4544280150b0506000040501c018020740406904603940c035610500000f100c0403085a4040d2545180d0000840401030200504039070101101000e549240d0001c2c0c02601c400c00034030079070070701f0140003034140c10800e19141401c5c140e800906050702c5440640f41080282d12003c190720000080109004c038002d46c00050354071390110411040c1c40d2030812001e6034024041c074400600d04129000c85a200b81d885000034042d03401c1902e0a2594030f0007800c0340001b90039921585034100380340844e8001d82c80580b011518507060030400290302e03c041e004000c8580100001c003031000b000b00048141c0d03801c200041c0b4003c0122030b0084030789090f4400910590302881100e10700c0c031601c480102c0d0103014006031044001244020405100d800d600c40402010f400c1401c5d500268070400410b10301000d1000300003810f640c2d100030860703440d40c5440c004e105400819174451504103a4400c0c00680c0d012407201c089034042e10348200521780f0203040d45014401e90740660030300c3c2000e050005040c0004943d082c0f03e2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 645381241 1250 645379991 645380009
    0xb0408031005100206011e0f0902211012031407050c040c0203090102030f033d06090302090a0504060225020a0b070305040603020c07050402030426180d05190c 70
    0x105035a0801d001c62404083c10503409600f1004c01032100c1030401c994454601140c8007001c442030fa440360b041e035071005039800104d5117a80000d00300750103901c4a1017400c074008400d0f041d4445441e0283c4803141a0405014085042c00c00b00845410b040c441e01c3d018030f06800415005544c2c00661410310781e20303040c0d80c0c0c00ca0b018034140066501914008410307601e054130b06070040d41c501140200c000d8455400203003482c1607086091003810402c5103030980030700403400318403010b0f158840b60040701c03240c070381164400707410846009401c0c001a200d600e80f2315007000000a010681d6110352400c000a40a00b0348680084401d0008070800800d403e005248560300954650319001e0b00d640003103038503105154001e03000c908100b0040181e184030798000c0c410301c00d410040d030300701c2a140c000160990740103541c1a91103802c001004007d0380e00c4001158412600350002a2600740c400c0f000545031003054807001c0c4149030151101040c40703000d202d0700441195840544072254072034034040c503801e0701d580610240 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 645382491 1250 645381241 645381271
    0x6140910030e0106051e0909120a120b0a0501090b031519030303050c091c080f0703050a0305070c03020c040c0c02031c081e010b030402031501060809010b0a0b1e04030b040803 77
    0x11824041b121420302c00c0341d5003452101c0c25a00003071003103100002e80011650301c2000c00141d1007940800140102400301c4e0b0b200c458001c00c41f441c20003034440740003032b5521030b960460b401c1001d0703a0000030271421289400f030200c1c1caa5441b0403d016400c030840c0ca1607508080d484880e0208070203450841d20a403403007520100030580744c00781180312502425490300d41181e21003c9078107103001c061015110203442021820b10307000001600c074505c2d802c902c104034046880460307003c0d2019010700034246e010038076240c00003e000c020344001350745070340152000340150703661019251040e228076052040316402404036880365940e2700840d60004a800040d00000301000042211002d00d4031a040101019800c020480d90030500c0c0d240c1d807644040c1049a16102d54000b403c140131085aa00740208100d031514581440c2c02ca0101c0c1c00e640003008818032401010720203000b00c40d0030a0a866010b07291880e8030740e122042d40c0c96046240320340e03000540312780380c40070402080080390f1004600c01c029009000d40 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 645383741 1250 645382491 645382499
    0x2030c0f07180917070c03080d0203010e010e060d060b030f030c030c07120b06040c0309020405070806100c1a04031704050c0a0e06100e030106170c041a010906140910030e0106 77
    0x1088540d04500204132918918211103d02d4000c0d01030700312540140512a03140b1390360394a0030b44591081004500c01c68010004119904240d103009006011501d001c040620b003200001e84000056100103050a5072040d0b07002146e1001c20012212242c070004503a44d82d030107080c000c1e03501d400c00508a003140c401c00703030082a07200d00c4541c44200e45d85d0011481034a61a0003007040050000080d440c4201a031320800100943d540307000710350050207540c49040f080d003060000e20007840b100c0444c41d4103210448501d500000da01d017226010721008480c40c440c1c0d540385d9240484814641c40000000e4041e01d000b88070038090082070851104104031542815980d4500120170301d03da040f94000d9200e0783d50702c24071501c0c6000343c051004000d8000d000140c459122029a60ba0725041c0e0320a5449030301a1400000600b03203849208041865200d8051003400010300007000000310380100070821056000e00c0700723140c0080c0d0945001c56001080260100c50488004000740710f28113800380c0a60030310368009 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 645384991 1250 645383741 645383789
    0x30501090b0d050a0f110d2d1a0a0f0906020306031b0d14070902040308190903030807032408030a1215060c0302070801020f03150406031106090d050303160207080f150702030c0f07 79
    0x801c1c03540c40249c078403c0c04c0c00311007d103070928001004110680c0c1c68454041900e58144a120b00300c9100c1ca60060f100d003403010a00d071401000c0e800185420342030600784c0309141d4030b082c6031025203684030304046540b1501c072a4107404c206c0b10307601103480c0500204011003000000d40203490000d06ca200100c40046180c4811074000e03a440c171014001c2508040442e1209220fa00000d0481c1210708034900a151054003501007598507038400c45141c1c0020800282c19a0b008210080c001c00d405002d000b040340c00460720510340003e10a032000e01c00e509003214201402400020001d042d07400007151608100f00d0702446a5100f212080b810301083c1c600405540362074811141901c2c1c0004501c482000d010040c4900307940031200482d8003024490741c80c00003440800c000c40c45842c0c05a2078140741030210704003a1600324a50441200e68000010322141c0391400280411317880310f00e00c4401665122080141c1c1075110780d242c00245405250b070301c460345220010f2000101d4044860325826408800350386 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 645386241 1250 645384991 645385073
    0x5060d292d0d0b01060207052209021503040c14010f020705040b040207050f15061e01030207110301090b09100e0715050405090403030501090b0d050a0f110d 69
    0x200da48841640304080200c540d4503500300c0c0e40c6044521048140514000151041c5280c9004403030b411828070050149580c140860340c010001600c004e001e101100c00700e1660340c50464211a01d0994038081c0c00190366686280c030222059a031306080d80c900b0281085190aa164010420007020703280d03691680354881d45045c0c21010b115409400a0350038501040040c2c0525030881c0c0c0c1c030940070f2240f000800c1e014010116400305050040c00002e408409007100410b0061040d40308a80084100d201284907000c003c6400c4024a00103079940c0003494012060006c5807038154040d03203000d5102042040504081c0e0184984100300e030200c5405100c65001c1d54603021800729031381c01210701042a913050304500c17400369906040c51403c254076000403801d5803108580a50000c1e4582004014080280c0300d03000b41c03008107542104d8a05e0f26511455a181c0112400074007010103041403605200d41d0b011500e0034550020600116194542456120b00c4d40c180d05c01c100034041440030709071120303044c000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 645387491 1250 645386241 645386321
    0x30c02220b120c01030e030c01020a080901060501030902090c090a0f0b030a0f0c021902060408010e100f060f03020f03120309010b09060f030706081005060a03091103160b0c0705060d 80
    0x8103881a00f050045005d000010010740491006010491b110700003070000c5e112050150340c81e002c89280140702e00d401e440240c2c1c04903051520781948a000b43e1070b00b6074115800b010dc00307002070f681c155074004240100243d034890780c160304203d40c1c0403490000038401075001c2d0716a1041480304102c049949000c441e4020020809640000030b00444c12035110f000c040351030300040c510ba0903d07650310003850030344100c200544116007001018a10300401031107500300c1c60001080801c05103081000350b002c000803502019208514148003085140d42c100300ca00c00c21640c0c452603a071030f4100b0044040c0a8012084030030306c00c000c02800542a800c00d010281c1c41004010010803c80e03181910580e01d079803016001c10f4804071040c0020030310307413146e1004101d81780090f6000100c0300c0c40f6080a0b6901c1c00c08240c6075119402c01c103244c40c20380c0810078460050b0307040304a889903200b00c5007031458a0138400b035112a030080000300d10729840f5800d9501104d042d4403900107a624003c00b03c444036440100440c2 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 645388741 1250 645387491 645387493
    0x6030303061311070c03050d1701090f02310911180112110403020a0608060907211e110304050d0813050f100c0207051c030c02220b12 59
    0x4002111440d2010500a90b03010003800001d02c01d01141d192000c560041c103080e2482d074018501001003080c1000108142035980c40e05000300c0260700b0040080c4013062140c0c410103a1140e240d038038010290b86c1100c600741c51101c0135002c05079948000ca40d820200301e403c078400016583c00050304503203502811a080c4101c0c64110b14022540e40500c0400c207002e0700860401000f8040c2c001800024807601200c4031081e05100d031120310354410130200040641083c0b0400070080144042a01c950305015004105801c11000703880181c03612940b003008040c0b000c01000d050240040300c40050041042c7c6440c0503020034807121000501d650300512041d58018200da00c010100ea43c01032090102640001541c2050114500980c8074617140c1010001c8510f02500910101c038500c503024070485985007514005064410f00d09000925030182901e42d512500321031000040406214a188203402e81e402080022a050f1490213aa00c1041080d402c152651030820114850302c2c0c194022981004510 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 645389991 1250 645388741 645388747
    0x50f0a0c30091401141303050a0c03021309030c11011e030b0f0405041e020f0618040506010801051311090405070504030302010509010216020f041e02090109440109080c010f05060303 80
    0x7040c0e640e466449100d5401c400035000c41b0120004038180000c500303190044000c148101c2c1036004102da000c55501510340405d00e060107480001c0d4010312121240c0350044001d681c800568401139078046031190ba0808251140c0340f100e4141d0b90164884294071009499042d9460b60100c00d1208641080d02c001d400206940b2070401c0c2030102c9241100f20900c09060f14816036240404981140c00c4030212140404400c1b0036001641001d00c10a54001404d00c3c140b101545840b0124881d01028800204001e480d07400c48070508005100f16200144c0142c020800c600d49118010142d401c1400120015420080807030b840380c0f8140240d4240140803540a4604810766007004a00d41d2a82c0007140c0054860038018032031141003200b0084508000e5003da41c4200c0300b0001000207549402030220b86d0301c901155025040b080400308400c4a01e011b02c0c01030340c54842c14808040103e8844482c5a60810b07101504102a10000d400611007920003030010844a003004410746d43d0881c0e0481e0136500c24 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 645391241 1250 645389991 645390017
    0x1e080109030215130204021c0e07030b1803040e0702060f16050d180f0b0a0e12070809010212030109091101020d0c02090c0405041404030906050f0a0c30091401 70
    0x210507040e8000708051300e088003240b031590115042e80c000c045810030301004015142952181d90003000c1015802030b0103094698199540d1010130a0007034a024101742030117100c0c03451700030100100ca0180c4403104580d41c99240c5000000c1d503444045a03549911410a4081004ec00030081042115100da0f00d07070904000c042e09607030004000b500040d4004554210b0054007040004603043c42e55805802c14070740c0c80c50140d200000b501c440c03500745e4481750f0003c0142c2c60560102411780d01c2c065849040169901943d100403441c101c5030004001c880500000001140d500640c0007400207032080d20000c0680901030016a1074140d0940c1c44070200c0c0e00e6000001c01450300700c1c0c1070780c1d02c00424201c440c00d00c1c1d2520003040072217190180034503145603400103110606030080c070164020402444c1061038050302c40b41420440c080c0a402e0410320091051030350800c1141d18042c030000003289860b0f070350800c80743c140703148070314051540501081342402d01007203401da942e010540c2d155043c6c4801705d40301c0038 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 645392491 1250 645391241 645391273
    0x50705070b030408040312020604020f0607110603100b04060f1b0503031b19030213050301090201090909020105070605070c060606110703151503030503011509050904140c09011e0801090302 83
    0x2041141c4c40d290401000c000240d01181650013090550b00078205031a040c818401078000a880c086c0c49082e041c001200040d141040c80c2441071f1083d00e210340c03652980350b01c80001c03c0040d0000080d04101050100e809640040700c4488008a0754a42d40a02203032000a2010b0020904c0500181c004200080d0000c0011250240b0008a805404e141c40e650000581440048040310320000c0d40014141c0343d030b00c4c40d83c0d4528001d444210001c11481149500203044041c0c0740c404d81c0100d0ba16402c0700030a680c040d0064504240e040001400940340c1040000c03d0100003001c12a41d1926040020071490701c211001320030140ea00000700007071821f40d1a000c1d2a840c1000040808586030b8a040344a5881345072050029031107074072069180e504010f50044585030b1206e0314020000d20802c00c005940d01d401206400c51303046000c103060100b403c1c60450a100c1061031309034100c01860000075944803960301410407040300186042d801900c400c50b0900f80d07210b22001400682c020810f40d46800d00d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 645393741 1250 645392491 645392497
    0xf01090b1318020a080708100203060a1505040b0a081806042d2901090506061606020d1b1d0d060c170c0901030f1b0f090503151501050705070b 63
    0x31420011070b500055034002202c40c8030580200c1c0c0d80c0d0304942001c000110081018912108075880c0550840c41d101000c01c90b5003110780b08020f00c44e0f6083c3c84000c1e116020310226005403400d407941a50b00c690140d8080d00d004000d80c2c100c80c15070001c46401c0c0c00d1030702c046036507400303568407101e40a00107005a80549044454030000d0150b80502c40c2000000340c07202c910b404030101620100d034502d0240180015002005902111541c0d00340b004228855581c003088400b02c00d14840170500d075076001c5c24100d0082c018140c80008251408030307862000f0140810100075813859584048440c05800c20b2140040e8bc800d40c01508801175440802c0011129040841c0740d003050718140750042e000031070b40c100d40302055a4080d42603400207901040c6503032500403981940f0740c0a5040c07180982c5200b00b007003044004c40340f00007041051015401d0f210303c42ca91280041c107005040340d8501e4841100e862510f0000d4441102e480341340781d04544594080c0c42520041904000548541850000f0f5070003d68 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 645394991 1250 645393741 645393761
    0xa0806070f050912011d07050306070203041509051905030d0302040506040512030f370203070b0c090d080301140108100314010902060309060f0c0408100e01020d0905060f01090b13 79
    0x4c40b11160412080d5402d109121200700041c58255000e0012030f241803c140283c1c0055010340c10145c10060510b030004121000c4640030104428413020004d0122141d4030b064020725804820311406038107205624540c2019520110280d0321075501d801d000754100d10031032141c039800580900040025107060301490082c6010351080d68a4500310304881c0005500070440140001043d90580020518021114036034403810115031038503194980c00030750b42e8010313440300614009100703000403d580c045000350340301502c01030110310075598a8030f0122080d8000740140002030080c0b581000c2c8940c403402e8498001d030092071742c0c00e0155041da16102142050000350000d603640b14424100162280c600a40c400e03140400034001c541045c400c00f200306540a40b00407401e08082c030090281c048042529148095150000500b921200031a01c0c0a07004081d0000341d0145051030480a02030049005482441140030714030711680c03100c00200071641400450b0390030000420090f91070314019400031000c4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 645396241 1250 645394991 645394999
    0x60f090f20030405072c1005030f03120c031012081e0301031202010e07090c021504061407021605010c0f0c0f1509120b07140c0c0a0806070f0509 64
    0x151965224840c001d2980d071a00031001c1500204100901005011100141400907161018010003541826126605a110302c001d004000086400c12045540e0200242406025076500c0c003808400181c581d0000d60803015603051005c00241540c195400300ca100d05013103002444001c0c248405400ca20b01d5002089039500001c2252582641c03240745040e800d0000c2401d586d54940c19442e20404000907240c461040d0382c14640c0d00000302801141d00383c10364044c54000118004070140032403524204082f1112100d4400060005101032a00301422454081b0018905500d91400403a0750755050500d50000074003607901801250311801d020f2004600403450360052842d0f039256040108031a501c18103075076030108000c1010f080c0c0b80030100107070b03041e6041c200c0f91030713281440f045910720610310020100040300340000ea245010b0821114900c1305402407030b071180306c614502c6580f0740e070320140701c0d2048024050000701540b0008556103d05555a240108100d2060054916812007903c20390b00c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 645397491 1250 645396241 645396251
    0x60c090b030c04050406090b090f1b0c010603020108090304121101110d08060a061409040207140709090c151d04110706090b0108030c150619060203030a050109060f090f 74
    0x1003100c0a0103035004403100080c0c540da8902d0541007001300e60f11a84201b01140c10001100400c0d1340340d80040768050740301801001c5a94801140901d10801c0b0340004405030004940403d800005600032360580e4402e880e0251240c60b03c3c0c0081d9501d0046218004456a4900d151800146612004071480406060000d4146450465141032004850368580001c103840200308203440c1c41d01c110340c014403c904200d841500d5162003000d031803040a049034040ca8000071080104110380e01c951800606403020790365125112116200500f200c59000e8400306400000410694100030010740c111069844540700a05103090302e45829040e1110340e64450342d600d410080c03520010006100e8144a900c0000d107410407468010780b81e14068000035030590082c8a1002e024000080c00344064000720f8452035650344100000d24025501c0201d00c0d5802c51844001414035000405180501040081800b09030703202c9404d00201c8290f0301c01c900110381000c2c3c007042414203a0303100400b82c085407500030030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 645398741 1250 645397491 645397499
    0xf150b06040602010c031a010207030201050705070504020c03030708010e1519080d0201020c0714100513090216020f100f0c08130b190e01020a110303070203070b1b0f0a060c09 77
    0x5903075001980508007503519400b41410403171345446a00303c00400c8051140d2000a1200000e44e80d0185010007414410002175480c140708080101d08000d01c0010015955440d0302c2c80c2d855120380041d1928000300b08030b400081080c41da25090944510819010b869941414008010320100030311104184c40305204004616600144051000702c03049400141c2c0d6001c4d500182440c04046904c15502412825940c244a0340c99240c1404e10b668949080d83e00e82003907802d130240001880c0d10a00d0400d01c002040c4051002d041070b40480d46008890000107104241c1c107001000740c91041080000c1d40c1e00d42e00c25030041c011814078555034080c4181500f005400030581e216007415411544c55207401042c00f00d0061001229903009101c0e0b49801403413403811a0010b03540e941050401000e980402c12807020607141081520318081d00182243e10701a039a40a5481e1035014048511480000712341143c00c0c2c0c07000168140301c0c402d40300c00926400e0b481d903c50100808818140310b0802c554070340001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 645399991 1250 645398741 645398749
    0x9061d040e010e0115050a0e040605060319210c0b07140705070905040506060613050904080d0218011e0e040e150103210f020a021201060f030f060c08040f150b 70
    0x1403075148000016076030341c9407403881818141d0340d06c45441000c040e030050065a0901c10030f560400c0e40320303c003c42c036a102e000000341004d108680d00c000d4001145580814013011441c0c0d41d0700c1c08410b103030103001d94070441002c44503521f0052015114039075100104c2d01192007003800b444080031070b00c60b003401d22a0b10f43d21103051a105600c040403164035071050006200f42402502e4100701c040320050b02d080318000310b0010300c054520426200e802c40800040901036103e0480e1007185580c0021581d0b20a015182035402c8182e00f80a0300245030451010704007065050780c600c42580c1500c0700d400d110310510801000e4455004564142c0c0a84264a0a00031408840601031031003030003540034254030841c24902c04004682100304104200d4040900d82d5004105090556010f998100c08211000051340c0944440c0d80644240100346000006001030700d182030303509510400081c044040c02d07150481c0c1a020503240900b812032501000000285946d01003001c9403c91080840c03482158000a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 645401241 1250 645399991 645400001
    0xa0f08070f230d050109050f060a060c0203030d050a0e010f0e0c04050c07060203070f021005010e0103030c020a080609070f05030307050c1c02041b020f011109130f111909061d040e01 80
    0x6036102901d1310014000645070b8010591302c0b034400d242c2c0e0001850a50700040c1174440900c600420b02c440121900e06540701441100d000c821091300c10b0280b0b0800d80580301c000d001456009005520f84000181c140e02d00340140601c1b9131070b0702e005101050500c820400140006440c140f4071030401c100c00c0380080c1c400c0c00071f58410719594541c60040a0440030117400d206402d020600303c03900d4440180969207100b0710a40c15281c05280842d81030700f09101082d0036820640001510f8032035001000b14901e00014000113a40301da00304a103d00390f0341c60a05550380101345004050707802c500c0360302c4001d082140d0034185420064407006210701c00c40c1c0218045034000401c5d20036145558075254042901000810704a14040c0000c20250114084071100d034000d010182d0711405802a0311002c168080c0c108400940130203004000400100e030320015030780c1c8880680c40b186500c040ca404226800342a02030221200c549030240d65010b100340524009156090340c0307511a69403800d0601c5460300b4420 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 645402491 1250 645401241 645401257
    0x2100c05060c03010305070605090102010b0d11010f090815060a1203030212160903110d0501060f060f09080715050c1b041a031e0712080a0f08070f23 66
    0xa5406510a90030010308100004025a03403502c410001000050301c0003842d402200c5503407600644400400300104c0c05000c40c0d00a00317501ca40080c0221082c0304120007603002c1c2000988030040c10410070541906d10b0ba400e442207041c15089801d1b1040800c40000d007042e44904002c3c80807802603102c8814884251100d001a0f0020340d000c2240c804c04400c0d818090b030040309030b00308180390803d2618010014041030000510031140100101b11381e403100c0c5c0081040b998408000c0c00f0007030310b03030011014100141c4128000507035444403020100e0b009065034015251381d0030241c4801307800c0910300200b2641d18507506d0704211080041080460041c0a1841c8610284600c2d20a620f4050100001d56044042c401340115039248486003550303001510350402d02014a03207550040400040509007890cd51040c81c803000c020f12a4001c000f41540200b040003081d464003840e4007a00001141c0340031040f5828000b0803500404140c03054040d03050188140c1e102280f0b80c2914032961204200c9400c0400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 645403741 1250 645402491 645402497
    0x7200306010603051b04291908060405060409170702150d0e0708060121110406030506070f080f071805040e0f06010b18060c01060b12060f10020601210210 68
    0x501c01c1c01000c2c2e00003603041110170f14030b103810141404035007402911200c01143d6101044005060318079110000c1d243c2040e61001b0f811034034070343d00c100134061680442c0c2d40c502c51441c20740001c0c060700e000d11408a8103500484a1890030158280b0340e46e1030760090b0350681e403101c1c10b0715030122002c41070380007800403020400c0301184c0b02d07800c052842e103081d01707503000701496800110051140d0400b20300e15550181c141c0070801060350340c0b070038450340100d030181c00a078215051071000b1040c80340000301c1c2c0d0f003d0011a543c5c01c104000500048410940a8071782c45094010f10000c50000382c03244001d400255962244848440d0307441000030700325458030300030510540102d8014144080c0038001c89005000004c440c0e071500ba51511203103040184580344c6445074002080106810500f54030400c050501d001641c0e9803150840d40001c03c0e002c3c100c44042c46844405109007441c21f101070314952101e615002407e469080c00000d1100e5803c42d1580c1c0840003820100c00301680d1079501c400d01091103a1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 645404991 1250 645403741 645403751
    0x32b0216020d0312050a061d0c0a05070c0f060f08090606030303040201030f0b0d0b090f030c25122301020901120f0908160b090607120b040b1e0f04090807200306010603 74
    0xc400010700041c07d580c031180300c84c0c03000410582728400c404035240000b441c5070595a514440c5841c0c440d010050f004407481035031042d008503a081c0c1101445c00c4400d103e4070b902c4c031581ea84c00041c0307641da0811903606405410500100d4010b500a4200001001d483c0ca0085000c400c03000210301b0032000d010080d80d00061b000c082c441c0400341405802e0041110b20041c1d480d00c1e007401c0c842c90760340f01c00c60b048440d440218900070b820000e0152014000e01500c0f003030114110402e040810381211120322407020500240e4404a468a0500c21520955010f031121500c42c1b001e030585000900400c0502c04020343c542c8031400005201c00300501c10054200d040510700c003451308000002d400c000b09000c4040e400312092054240e00300e0288040328084050102d4500b4040340440c001d00481c64401d41c02400341400b65a40b40e02c0b1044903404d021003030b1006150395020004100c1614421000980f043c1410080d410100d03810414500c44404c0d04020480f41000742000b091400109030f2142001070b80c4c1e9 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 645406241 1250 645404991 645404999
    0x371e15080720010b010e010306050114030601021f0e0c01030204080c0d080c0a050f0d261b041701050f070e04050606070b13050c030304050a15020c03032b0216020d0312050a06 77
    0x3041b8080c244400030318040100700e04050010741a0711401e4404100024040b0014030389a20820000c000300c130200c882180030010072460000503020464489816028041030710000d94428401d0b42d00302d4030703100d00500d03000c0810700034003880201030703401902c044104200c80b40c5038203010460f41420500c0780000342250000000d481d4148840300c0502ca04012001c0300e61404200800c4118400342602c894054251b00c50207070303c0001003241c502c40c00d22128007241c000740c403040407070038044494140e4000b400355030f844280111001200b16149008110282c08007615400c003940001e91046000c4c204a00e0079085440308108038204950000102c8202849d8000700081400002c9066000760000c506090800001582050660140e42a1150b410541418140c400c02c9408101140642076940c0c9030148000c0780c071003212560b0000380c080111341446601100358401c986068800d02800e0b503050105a080003000704080009404200052104c10708461381c9201c0c590040d512060002502850 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 645407491 1250 645406241 645406247
    0x4050a050610030204050609040c0b0a0504081603061a010813020414040b19050103080909270303011401020619050601022803030e0109050a02371e15080720010b01 72
    0x907c841e006120729420300002400d484120340946040000140e2a1100c0d80f008441c1d41c01258081c0c1c1031446105640141f41691800d04810340c0c0c081c150601c0910084910900c0c11546850303071500003035083e000100c42c1d01d01c2580c07201d42203100610109002c8041c4400c1981c2d10015070b800d45420512500380851420403680080320036500010900083d85540c0b60111070303000e8070506a000714a218000780311081d50006407000c41c2c00c09071510004100705541a0f03540d0b042401050f00301030380c0c181d6011596000003500340c4609691a4813000418280c2240c01c00303881d002c0c1245055228003500d480c010743e43ca0340e50303a0070382d15000900c4d14016411300f0000d096440b41140101113074076000d41c58010420100d88182c040c1e4050b11104940000070440304a215455520140b0240000410048102c03031246188101e9290f0550207a03201891180901314034480d11440711603070b4080810003612400340159581c040550b081c800190030748826082c00880501d2415000d50359030b4007082c185903030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 645408741 1250 645407491 645407501
    0x105221119020604030804020103050a0b220b18241002030d1512120516050601140108100918060606050901020607051c0e0a020604030302071a120a0504050a050610030204 75
    0x10710703100400d40e504144d02c015003d100081c00107070405450350005204500365422505804501a02c030303100da200b2608205100b0301000d005422200d00b41404007100c1e250089600c1c484000c28940e50010340c640b040504050700c005000e0b4241d5a100552183d0141c0ea20302440a150700190007460740d82071581070240803500e074944801040c502891081c480000e2030511048103030341c07108c0300554161301c0903c10b40300c9001342c14002041103100889242040301c0810802d04070f4110008412141080c900159111071044030344885180c000601000340380410b4100191403030942c10f550780e4020203501d85209954850300a5000300d9400030f2511901e5030304000290f409802803a0844c240114800c50299140024004003c11625a03000703103203070881401901b2516600401c41956280d0340d18010391124598801c564190800b400104240102c250440702d010f00407100c1c0c0700c06031356010b6401c401030802401c2512144541000440040e9040001502030b9803a0100c8403165813440c070410050761 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 645409991 1250 645408741 645408787
    0x150507020604260922060b1317150a0e030a2d0e10031119090801090f030c03020a0c2711030c1c09060518010209010801052211 56
    0x910030391002070007003c004054821489049503201d035a40c200340a208900380241160301c0e1444c1c509200041c0c800900da000f06060a2a0020081d2095407070040c0e100500c1010006811500000da0000c00c000c4103003151a40100401000250042000310b0a483d54000ca0080c00200b901513a070110295607143c400001a031540e0305420796888404c000070254001042c81c00e01442005042000d40c0d03009400101d1214a103104803a01e500c24410031075800d4a00420003030215000640118102106000b1880c0068020000d9001c2192542d0221071a80280300d0540460052403404d0700003860000898000744807000030b02800c181c0b0341c0401c5241301c00040f64540a2454076000025000500701036980c400c820945564941c0c000c241034203014985840340800d003915001c4080d0810005500060107102540c00ca0f40c910400407000754202c1c03044800d8036010444501c0104468a88091014888140103912100b40303200980e019003502c0c52024582d68600020078200d208441e5810f40305044 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 645411241 1250 645409991 645410033
    0x10e0405032b18110621041b0602072103170403201603171c050a0506040b0f09040312020a09030b070216060c1a04200a140607150507020604 62
    0xc49039a07000b101008881d406000780000f00c0c1141d06100c000c084444000031480c240c82c0c0c285801e161200148503041c11340e1800312238281000c6a030920004002e07007a00c2c047c4042c081440080c0c03c480c56820440802181080440c007030130807a0790303180c4003030758025803080d11451043c2840080d0f0070000941900030f600340d03600c111030314503800d950241c038101201d030403100e0f250764040210492603603446036115034000b00d1400440094100069480302d032062010701c1c400c10003501c370f06007017206880c4661107140c0d0120521041d0304081ca00805850742140c0f080c10514203580300240c4a6080e038005180000118803a20b0041050104001d00181c1c0140300d032024100701c0700031411003090080e00d802200700300000c02a1400c1004055200d9540340d050f5600c00c54014a444d103000b1031840c41c1c0b134280348046e4208103112709680c1412914a000c5e6468030720840080289030040c851641c000c1c0905403000c200c403080305601076400d0b219850140c0c1c5907038040c00452400c0c1c244400755038070036890050b031 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 645412491 1250 645411241 645411281
    0x60f040e030a03150305060106021b03030301050609130906050112020a0515160c0b04090e010e01060320060717040e0903090307030b091c09050a0f050603010e0405032b 74
    0xc0102000b00c0d010303110706081c009800303000d22440080421540e00020054400c6400116040e40c000030030300d4480100090021210325800245502d80c007080c89041e400890501201c2e08074944545066203452040e00000b4031100e5503210361064a81c01c4c0c1c01f9810305025400c61206600b00a000c00005e0b090649551a00240f481c19401107449041803282c2a245c0c00000201000b4029030a94001c050448410740c450b51039289043c0102078a000700c0c0c030103619080900803c41c40601a80c1c0c22640c100d080d5044141c4a2007000c02c400d50b01c1055264448002c014005c0040c4c4007100c01901c52480c03000280d00c8504041d07080c4444a40038090102650041c000c11704541e40c001541c10507a0b510070040c5001c1e80321064030501d4401002c8048481e030340c020103280700880d400001d441c2101c2003251609111542d501c0b00c100080791a0040a130003c1c1c0800050001b010002103081e0480d01c154100d9140c00c000d03405a111501e1205010610f80031003407040408085140110780c0742511800300300705 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 645413741 1250 645412491 645412511
    0x30203040209060d050703060903020d0806100f050d0e0106121b080a0816080a2f100b030f03030702060712050702150601030b030114040203070f0609140a03020d0b060f04 75
    0x20102c000182640e1140c040030600208209082c0b20b508010750f4420360500c1075013800d160207910b1320302d000c2c454000550a840004d5036071600e18403d00182040b500c0712098004211800c59259100790014192281c4941d80804503030803d2003020014001c00090243d040c403d8600440c11a04c8010f00025607800d0744418050300c4c501040d250455580072401030750b55480507a14900020401e80007804030500842c1c4002026040703500c1d515207201000c0c501e03190700d61180c02e103100c14040d1010380301c0341c0c0e1080c00503c241c18425030180300e15401c001e04441d101d45505c4411451607100f01c580000503004582800303110303074000c04511881841c0c1501440146007910000303503145c00e820012a442c0361100c0c040703102e07a4001d92001c05d070910050028480780c0c0d591010f0302507400044e90128000d1150000000b00e00e000c8420300c205441d115070303441c00b07514036101c19480044c201004403544000d1501c0000010f9490080d8032259910811504e90540303804c2c0c0800c0414400070080900590414100d00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 645414991 1250 645413741 645413749
    0xa060e030a0f11160801090c0510020d180b0415111209090415020406020106140f0a0e04080f12010302032b18031403070b0a0c0503161b0309090c0302030402 69
    0x890385203000d180c5020b040c680043c0061a040043d051350200004403940855404410341044200e41d0061121003502d680d02c4007400261820101c2803001a00700d403c03036100051142d0120301c4808424980441002d0301c1d04186003140e480356112201000440090801090304800c0312a020010000900400c400c10650016144516280f052161b03a50200240401010b0352210840091000045440381d468850181c02041d081c0903d4800400b45080000589400d00100001c11805048101101c0c584511140e10b02c134040c0c400ca503882414400701c03601494400140900c00f41d0950008142e500d107005060402101c00142201c1d00308410b83c4817030160120301d00510040040c90400d920395511003220800b6100c503040208051040c855041d1117001c0003020340070b2180517404440850b242c00b2074000455039945c55901c003084023480000e01c00d128080c005010810702d81424204041010f8402c143c500301e802d01240443e14a69042c4940070461040c0b031181c801d141030071841d40c10b140e0001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 645416241 1250 645414991 645415007
    0xa021b090c03061f020f161514121f0504020307021506030307080f03011e06080c070606170a05060907050a09090606051c1101030516031a120a060e030a 67
    0x240480c2000408180f258641c440c80342c498042c0c088001040402c071080003921a6260f160340a100c0c4505220000b46407401e80000086030740c040003101c60a02500019100c050a12040d400016010b00c0b007885001003140f15688610881c940881201d015050707012070144668200c94010317032041c81004200ca400060a000079100c260841d0501c0d9500d40020380f41d407190f0300b4010002c0c0340125074685e148131440051410307985544a030120f01c604146440c040311400c0d00c200d1001441d0000070504010f01e51000b00242d0740038001c0890b40030780361200e01c074403207144441c00b04180e030140042d5800d2100c1444802d030402e11107800b41060501e0100028101c2006001d0b240c40160345005000820070658400002440c1c00381048000300c003040581050300000b031906444416083c03541440c10341c03180c0316561044446850500c118262100b00310010b01252200d0030044c940f8903c0d070203640e130343e8043e1400380115100090420400619280c026900340c07049114013540b081c841c14038815044885 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 645417491 1250 645416241 645416251
    0x30f07030b0303130303050c0d0c050712081201120605180a080c1e070f06080c0403030e0d080c160e0105060a0507050c0619030c020d0801051e040e030a021b09 70
    0x114244071040006429480b0324414144494001c1000108050300302000d008004544000d540b20100300110541d280a29148004c1240d08000b1007840403a00c183c7c1d00c0d00410b40244045d50401c40d120500321444507080e00044100e51503c401c0b00100300c031500800d0b91102c0c00310007410402c81c401e0b010668400d043c10000705403007000f09100b14410010803000380303080302c03045102c00203048481405031a141316000c0ca0707210400c03c00e0301080d0a0300132648580184466901c4500c2c2a1445c0c4084403076040840580368024981e40055000c510424054070424841da0003908000b00c10314420700018050307030321800c894004400104501d690303800c20703a90b03003180700d0405a50314403240c60030706c5c10711001d014840d40c840d0010840d02c900c1001c200300c0a2218160761010805210103000580e6038070314500f001d0f00011340000c01403040b8102101c40c141c0c940405c50b00344191511500005050b82e82e01c00d04442c295101190803503200d5410000704055003203511051214003c00310203e1015100101 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 645418741 1250 645417491 645417497
    0x5090a09170d0228020f120a050a030b0307080714030f0c061c090b0604060902090a050105090a08150406050c1e090d1a010602011116062409021e030f07 67
    0x781c440c1220040b81c0483e086030b404c0301c0d002d80424005900c801007240c290400c04c001403003441e4904c42c0c1c449000a0743d2140d60a0041800d0800146a074219030b1540b289550004143c0c403840818030a031010414100681543d00c05465044c3c02c011844059040002d00d81d4030951018264003600813011414283c6510251070b0b0070307a1170032491031607881c03107207554081241d9501d0000580103200304074040c18047c450071581440880d03a59030f5503000384d008440320140c1c40184024108465030142c00200441d0401a020030801c5907a903044908150904801c544010715080030401000b580d40f1401d0f601035414011780b402e20b294506200a40e0000c0d03246440740360000524451303155103140f005c1c642150300c1101811994466035058162007c00e00c22540550300b03250900003540d031243c041d05c40b086404c0350881d10324a5507440d01c0014000340a07405041c0c141075105d84010301584180d0101805030440090b80c0c6030101549118100c542801c00d10080000b4401e1011100c40c04901681140c01c40c9 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 645419991 1250 645418741 645418747
    0xa09020604030f1a130210050a212003010306140903030a0906091202030912010b0312070611190e0a0b0304020607051018060b030307031e02032205090a0917 69
    0x1180044d51030520820100d075006103001044011119924801c0d2268420390300c142801c030100c501070302d05000b00040d50300420081d44041c030803a19400251303c040b24007034101080400100e4440d48075440e450080c510740010010040c0240b185500540809481d07401c4154800c2c601140e81c03a031280405007220070040e031100702d038005121060300f1605c621500b248154541e01040c140281d6a030303122090281c016051409140703003406041c812011044009005041c184a40210303041156129017411154a0b907200c038852001c0035190003030400002c0c000e4590800c480e1140c000f904a040d00c1f0001071086a0f809401e006180c1c00e607065941295040e51901c0d140d6620b450140e042072000b251200c543d919210301000501c0001105140c450300072082003041d16401c0c0113042d160300c01c10001034040340c06200d140b0001100101e103030000003000d00c1582e052280ca100c4090051298020341751b40c81920610902051514504294200000358000c100d24030141e56040c240010020721440580008 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 645421241 1250 645419991 645419993
    0x15040f151e0b0309100f02090405090708071202180112050f06060a030809040b0d0c1e05360903042d1406120906040605010605160b070c020301020a030b03060a09020604030f 76
    0x10410540e0a05e800c2800b4401c2c006e040e00648000d40107241003501c00d9007007034045412490007003445001d440e50403015044050910313119529a000e001e50482c2c200e5450803041021032803181882d4080d1134444220700703e00c00a800e2007440c0046144046805820201c1070000302c0d60341e041700070126036100030159201c10000d800900244011b24415030445003840c3d8542c20420700d56140015510154811720400154031400005030216001d016000b50580c41e141c41c11210304000811910304480c000f132001404401c02c5803480b50141c030540402d0f4008201449620f2501c1e001d95268002c0001001c6070301700d06a40da1010700c80710310440f1005412504440f003540c0310740084605101004005852030305004241d10b65408084600352403140c40c0c0400860030b6849078023102d180b01e1015100100f01e40c0e01d0b4a4400c2d8103040604804140a541c40d0180c1c01a00c2c00c0c0064110070965886c001410392416041c90b050007001814a00400d14100a0b0300045c1c2d00c04041e50250303034100d9807414075010f003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 645422491 1250 645421241 645421243
    0x3070813030302070812040c21080c1608030910030b0319060b0d15110901090315090f11031501060c06020f04081c1b0b06010815040f151e0b0309 64
    0x50440c050241c60300007501080c80c20340000306e18011803003840076443d05555034007001c9900200d651100c2c5800d0b006500c0c600442c6122029001c203186110650f020b070348040926654560303955020207850f40001c50072080ea4074145246450714542400c00f8000042c0803000a5155045101318640800c0300e00000030500c40070350b10a040320613001d401180b03180030350700707001410761501c00650050904001c0c0081407419002d081d01d60503081a100d0f000700e541155104041c00c45407102a41c0125542e8141801140b0b5a50901100e54018a8400d441c0000c0030305042c24a01840d00001421005100400206510003400c00100341c00510040e01c4014042e5840024800d40e0700c009510700c20100040c0101108070040701c540841e07134075031482c3d0170a0100d4500e8403e207160700203001e8a00000016a4550041e403006038001c0140d18030000001403200041c08031039581c500c11030161341d1800002d540449410b000d43c0075081ca03c101004210040c2d04502c5c40002e103005801c9803580c04008580b9800c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 645423741 1250 645422491 645422497
    0x180b0316031b0b0406170406141e0901020406020309280605030906090a1709040603021504060914010516050c0a0e1e160c020a03050f060604111c180b1306050601020303070813030302 80
    0x5d003c272654045081104003940502104a072000d4500c20301408110b01f400c05208960840b44150051070501008108000f4000d060014010320070400240e44000d99500c3c1702401c0c00b42ca1180c50f4941c680c2800780e01986004001445078903207511400d05440400c0d400c010300c0c0c3e12100403545d82c2c0d84c3e4044050109010388040d61000b900080f103241500c0502501d01c02134400d60380c007960388812056842c40442d030400100721180d8081942000034048622030300c013940c1300540c0280c04031004201d407603000c00c000c61103d80c000c0325074240703c60a00c89000344a18010245203007100d030300036050500000e040c0c80d0100191254082c0000e9202079021500c03518800002950000e080d1a0f910712178400058982e00e0031680144543d10380072840850500031404c4c0c60152103c0046034900700c00040802c0b0003440c15180030044c2c040c1d2000c080000130900fa030a00d106081641c0d409500e41e1451800e0301c296080a42480e055400910405c9200d960101e18164004c481141c807101105060038168002d00c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 645424991 1250 645423741 645423761
    0x60f0609060d09060e0d140f22090608011401090207030207051203071110050a1103130b120106090b07061113031406070801180b0316031b0b0406170406 67
    0x1000c03807140b01202e115406a2041030040800f40305141d88044003c1d1102504800c1002041c2001c0c400511b085072000030b009500d0642141903d0907070300d083c0700e070820750713240f00c0c110760407007881a09022085150003143d0041802c00020302c208240090f20b8504804140142c908140c2e0101303401091510070820540141005070030906103011a940581c0c882e40890400d40d042c3d168014040000e00f0803900801c1025003550380c031410040200d0382294030325a8007840c41d40301c1c801800b0184c4030109802c240c038018042050034a1340c5824080c403162820205900017410321414100c10018a01c0302421244600e80c0124001184100801084210300641028013042e0890800c00300401800920146194440340e040b0f540c56030f540303c0119040b00090081000310030301d00d506c0800f04840c6401030b0600040083c1629400d9801c18841e00345401940e206035801520a1021008590b60010361006883d900300313594507007810108003502844151030b4031208550b0200015003408220b038003404500d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 645426241 1250 645424991 645424999
    0x90b090a09050c073806030c06030903070303061a0a0f05070605191b0912020a030203150f09010c020706350105030c0603220c0806090d0905100206060f0609 69
    0x707080401d0014850313000f4501c100e503015443c0000d1000400d1400e50b841d1041c161001800503200b001059032400380c3c02030a99a010700c100004100282c3e42c0c08081c600c80d094110040d91074040c1814000c081d150356900c500e014000c80103c4e0141d10a01030201c841114050400030000c0072803a02c1156244517021028040300d1402e0248590030001901020721214580c90a10840c100005400041c005035a144008625908400c010060110345006070701d82c0000c00480c1480e55a401103400d004201d28075041014003c010014001c2c0d4003901182c04c01203001c0204031000c20494040e65840040c0540c40900105444c80da0f550749048207049100d60b11112181001c4288460300303e1441001c0c01241d101c0d010300d1750003101c10b0406030207481c4100417000c6c0d1504040d443c08031546a4205610041e210305c941d40101050f0900104000c03401071072040c00030a80002182c038010801340311a00400e1055605000a41140b41d000134255003091085036540075000004000481c0c0d8440e5100c03540d08 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 645427491 1250 645426241 645426251
    0x120212030f180a1d0105040e0c130b0901061422381608030703020c0307030c0c121505250207170604020d0b0901090c18110a090b090a09 60
    0x142c1e9820030480e1581000594110b0503598a0340c0384281c030f20b0200107441c41400c040000402c91450325401004241800d2000c1c2d03400721454002241c114406248111b01058880360031400c0e600307101036058010803203842d140f0f40d01e0110700c03a5408180b06032102e56207082401c2c1100080c456551090800034198451140a00c0b446401c1e42d9082d000060042c4c451280142c9094034483c01c014100c0c0c40390b11240b80c402801811985e511404ca400141c20481010340c00e00c21108100c40400041c040c40d8000e444c0c440c085501d40c6401704100100d500181011070780d210101000401904840c3c41140f1790150110b842d5854410041c0c040307079041c0c0e84502d02c2c29001044c2000540100b03c103070035036130b005400141c0190220303987c6940e85c07421344009401440c10204040450018800560001c0420f03001090302d40782502c41400e031850542081c081d80407030191004001c500352060040c4116a40141c41c200038080102803d00c400c40d10131314140e12400200101c4642d925407182004d01070303501d42006 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 645428741 1250 645427491 645427507
    0x19020a0e0a120308150a06270b0304110f09070e0d02100f02060a02040317130503010912020c040e0c061c0509010902010210140403110312042406120212030f 69
    0x1260742982c0c84190081268440420b80f604402c82d482202c440d0040c01680c4501d2514600300c3d22844460382d1607694501c2c01e02d51a031850201d80d0003200038042640025100d0625003484d0b2040c0082d40015446058003901e401c2d0503450b00b240303140e481440d900344941e50284c0d020200d0400303c00c200c2c009602c0310102d4100070845821030700d103440e0b0903026400c40e043c56a5000c0220108d20660101503e1003980c50749905d500741300329006100340100d014000307190076a40e401290035034415200031034a1341c4020001101480d410080d15182c000c1c121801d110b000c695401561311548102002400340c0400266041c0210340c90940c044100e690700410040351034101c01c5180240001001217006014200d2404851200c50090800d00e1100103026103441e1036540c0c0690390107002c400e0b80302650009005155500b000400742500c12802205440c031180681001101c4241c003442c031400060345090000d0264110881c85516110760542d10802003251078403c032803850048003500c5024510001d10b0700 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 645429991 1250 645428741 645428759
    0x90b04120609030e041104060f08010b0301170a06020c070e070527010509060c010c0206090619150e040609060b030d1202070f0507080c01090e06060931060e06030619020a0e0a 77
    0x400c23030700701341d80b14002d07181155012103110701300384903001c07908900388014401c44c0b20a080c00c4282010003403c4500008060f9200000d07070b0011032600380c4035000040200142006100016480105890b203180340640610080700320b600403c01c0c02a11030400613502c100307640100c08a0341c80c240d00500711511840d20000340c2d030182404140900060169101040c5c440000040141c0900f00da40d1201c500e040c0258a904020000c1441c0342d609590010300000310001c22183c40b602880c040c441c08a10044a81040402d4405484400c1d0280d40f1a03803c1558540d84200300c0045081d40200160360342c9154202100407450305070000d080c5005a11300011f41c04400100d40da010722081e00c42002c03044d61121040311102045455076001304040100f080c5601d0b201600d661010405268030b41c44c05000c20f101c58a4000340101d2a48190340c1e03800520884c0d020003081a03014904500525040c0b4017a004141698404130f04040d10903000300b11001c10701d02551501800610103009100840e503110201 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 645431241 1250 645429991 645429997
    0x20d1e031e020d0911120d0305070c140615190509060f0a0612110310053a03020f060601020307080d0e1c030b1806010f090e04080703090b04120609030e0411 69
    0x115105540344040320a00d05110383c030021504000f07805804851950030303045c0c02409d4000d20080812051040e0100054161520151040646001400c0701e02c1c00204021070140303d143d0180c405d000380c04d01c15a60040c00061402074030001d880900407521010b01190000750b11312841540062580c02c0810016400702c01084a10b88901d414272070340d40490144005440284c8002c0391080684200b0b0103141060880c44099440030403004407a268050126613294828000400f20a01d181c010541450b504110700d02460041d40050030484c108100041e42e648519003004110040110755060481c0c00d135409260f09800c45011b581d4000c01d44880310565041c002c043d000800c0c42d102e01c0d5483c0703040404803650b1780c120180080d240750701c2d800b0041d240348604c01c40000c1001a0ba200108080c85d01255060055104000b0261584101c0c503000d0032100b0b154200c03200401c1c0610041200d0781c002c0344100940354005500141251082c1011215121181031035900300381071110000c080c070310071801 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 645432491 1250 645431241 645431243
    0x216081213050705040515030d031a031b042d020406080f060901170708010e070503011b0206060d3305100315150e0403020607020d1e031e020d09 64
    0xc66541d5454405648100d03508010b00305502c524010700940c180b5922050b0850701e0819004a80002000020318000e818030340000000d03106d0500c01a90310b4031400c02419094110050415546102d403980118055055418815500d5040032294404c0c020385203440c60b00341da002c9150040c0d04101c000040e501a03c5070000242109000503041d20703004020500440b001440c901d0300b40d2a04120540d012003a8504035980c0c0134515001400040074880e0196485468025007460740c600070416003114540740010500440400c2e50580c4140c0c0410070703030342c0040100c40c0f020304446681420103815500700d100d1074001842100003401c229000d5400303110308040c060f06016581c2c45a0500040301c032184001000c119414120710a40d0310700b60803007599150b04c00e20088500d40e03a51410241e510044e00d06030007681180301449201c41d414422030102c050541044427000c05811800b100403004540c404007010303624180e0700e100c04000c3e00405001c00603082c0a5484509050041009000c11340e0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 645433741 1250 645432491 645432517
    0x10c0f0f17250e010e0402040308070b0601210501150906140d15180c02010b130e0309030109241e020a02100e01020c010605101e03060e0f0103031b0804090c03021608 73
    0xc43d0085e4a0a4000c40e001d980c0d021540908000039540c8040701410701400c2d550501060000324484524a610807072070741c851460011802d075240c030000e00f4000c9490308100d410030290803801c0c400a9001182000d021000c40600da40d2030900749489002484039429005002210000004141c10040c650341e0340e000c01d8010410450070540381c16800c9406407603030690042c6a4040d652000760056010070741822003482a070340380001410000382102c6064200311104d80c01000c0c0203101c080e480348039100c0400301201c00c000214a0b0020341c041940d1281026440c140c00080d0041c81c9407003840344490a0402c01c0c0e0502038103004040c058040e4000d14681d0b038040d842e06000040901e40841c081c0b48a18490b15244001d0a5504003034002070b1075410310b18203164075401c000820108828600b03200750032569130b02e241075045180040a000360b500c0401000300da2043c0391008168484111780403100201c200203115811283c0c240c0103405491442401400c034161060706002c2c080c2e006040e0119001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 645434991 1250 645433741 645433757
    0x40e060a0e0601121415120d080105011101020f0d140f04020f040f02130e06040c172a130f170c0105090d0c03140d08190507031d010c0f0f17250e01 65
    0x11043d50b5580d23a4110010002400c4040108102c0d40102070380d030792400780400090701e8803008001ca21079960019001c3d845407a51407601d40100a80744402c10f0308403040d8500c0c600142001e4002421136a5a504054801c90740c0780b0868600120315030445205030032425000c5401b56032001004102030003151114010350400c098403003114450081d081c100c20715460003480c1a05d0f04200520020003041200c400080040e02c2ca50011101d130002e040304100c000510380303420b8185450024900b40940c0050148807904000300ca02c854003040c103541c1100203180c103940b504031a0001070701034111418050b040c00745080e8040f00344018110500c0b010004130381103d072071451100f0126205141110100c03200000124515204201c035080250800c1d8640760100d5007003c1820100d1400760901c6208105a40d10218401a503030440f0320403204503082c0c24094a41d01c92001c0181c4504200c1d0034000445064000013044828041400c0551500702071800c42032950031003002e061100c3c0c505680b40450801 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 645436241 1250 645434991 645435019
    0x80405060601020c0a030b060d0519020f04050402210118050f16081c03020d050a0b0111030307090e0405070b0a18081908092103040e060a0e0601121415 67
    0x240c1d841c2010300c064030f46240300d450b5440740b87c007004000e8011540300300d040c00c104010400c1000000284046d03485108011981841003200940f0740300700c0316001c2ea09020421025035261980a100403498605444c1c0e04180d2240550042070403881f04104400b1005071070342030140000720a00822441c1080b2031040300d201040b03461242c0e0300d202d05411035101d03da10b410541c0c0441011201c41c280d0303007005420824210340e280c095840850b400d05c01581c0c2c072024981c4940c3d0158031915224001c902861850403c00002800c00415000d204140d81008000c80c003001810030056000300440c60704143c448940d0507008260103d88090302c240d1905940012500c000041401f140c09004501c0210800c0c059664000482c1c0001d81e8103a4031001c01a007104141803007560340d014a080c3c040c0515075860030100d02044203180a05824010501d0510901c41d1942144889420503000d0034500409008000c205004d40301581403d00d507031406206006151114000c40d10020608542d491080d42d09 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 645437491 1250 645436241 645436243
    0xe010207020907050f0405030105040f030f083102030a11120c01020a02121c090f0b13420801061b060e03090406080c040c050406020d051303020d0308040506060102 72
    0x96800301035400080080821561402038004001c1545210101803c1c941d031348000908641080302e0940704540446608820980d109040f105019011f007480200c0e0700304501c140b0403a00c0c440003102c1c2001b48041c107402103100e10800701083c00703a00400300d0b00160f20364074203501000c2d0b08408250099500a0540b20320a03404035035218141010303070042189007050b400b004030034482c3d020020114000e4011481d0521442803903c4112462030f1500000e1518101441105403131650005656243c20f209603404a0311041404003110440c03604a1a540b458000c0c0e0380110011004810a5150a10956444403109281c2c1c800550407910382e80e003140c0c1e92305000d90b5070041464814440d90078566100b00000d0301e07a0700c40a4175100040880b810b002032507012030200c43c091382080700164001d0901035001d1030903004140b503a1005160860400745400001f950b6100c00c00c2d41c220500402094100506020b072600000443d0000c1041c4142c0c0e29070700380606407034000d9805550740e00401c07001902c1940 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 645438741 1250 645437491 645437497
    0xa020f0709060914010b0702220207051b030109030909050903042c1b0909090f010f0e0c1009030605062e030c09051e13061e0801090c0b07020a08030c01020406030e0102 74
    0x710480c503d0307c5c0c071a03400c0201149c01042c01100c00c80072031a100c1191001c0d44051320b1050300ca80000c03c0c0040510107900059904403410600c00da04100d0070381e0020342d020131040100d44031000c2c04282602c0d0060401e007036001d00d070030980c0680301d00c000144225078840c6030030706404200307180010b403521500840055103240c0304a55009020401406005060070f0310300c40d620190740402d407181030f107110b02c00310f003540c149654030000e041d02d6040340d42c1500c2d000d20800c10b050008690b1020204002c82020340480441d100150046940c3c0c40081d40380c1e1550000d800d14098201c6800e01079041d980e07482501204c0ca100c044e0006460010041409802440030310144c42000f041c1e4101d03c1c1c16416010510000c04941c284c0002d48459440035502460040001a00c0b011031020200c0d00072207040000b0080a030700000c0207a040001a03c01308070044049030648600190207962040640045801c0c10455404401c01e8400042c0c04d07490800c066002d00140c0d4545e07036040c0010b2084019142c240c0c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 645439991 1250 645438741 645438749
    0x50c070c09060e0415060509011d0c0a0215070e0604060302030708090d1407050114040809030d021605330408070801060b09040203100b070b04020405060301051b0a020f070906091401 80
    0x10f00c01c5030105020075584486450b090401040101c0e40540310004500034803400e0f48203000001d0480d0040c054180c4540d00603a000407400006400e044900304000d503a4040e804070400c1501080340071620a511400c400c079104500a0320032070782e0729540d0380f00800940c01101c002d0000f44048000c103c01400c0800c40746502000c681d0342c3d80d10400c40800250040c2e020100803940c41d035131005070340011801c403140d541c0700f1401400c1c019100c600100034141002425891b06086400003601c04880620117490388080d2031082e43e50400e94031800e03854464400c64500f5180410350398842c2c405a00040f040107005132506c4078280c903001c66030342c0c200030300361040e07806400c514000902c4003210070704107036020315400b10b0002001035006030ba5140210b0281c2c00b004041c0c0d00c00d90720b00b042201b94141405003a4024006070001c00040c90030501c2500340160315900c406920b900000c00d03108c0c292007000380c01c0044d82c800c000d50b155180e4601c4a1001024584558540c0c94204200301699410304030b8064122 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 645441241 1250 645439991 645440009
    0x5040902010c063308071203050d11090303030f0402010e0117310506040218040b06010e01030e16150f0f0f0512040b10050603060f060d060801050c070c0906 69
    0x5041d159840802900c440103032000e03202c0d4001078050310550151440014035505050441301c243c2070000f82030614480e504002802102100820006948a4200c44030219180350028bc1c512800340c0031402c900c030340e1a801d9814400030040c00701c80190030b03401c54002c5d4400d881c0c0c10540c0c5804401074401244000120301c1006010002036100042d640a146441c1c84144601e0b4540c100480340101e1050140c0059542d64816000c000450400a501c0c0d440d042011400383c0c2d0310302d820b030364040f0030b4030000301034504016000d2a600107590007504403800c00704402044e608040b00303c003601c000021551080300c14404210180c141a6406500c00035580b8001d40c1c0c41107081c0781a00c40550b2142c1c03803488650104001085070000210142665500842c420300040541e0705100039680a4580107403c15849032804000b44907039540c89010041482d00151681d0303860320ba10308400c00013071106902c805625424401008003000c540c0008185803440fa1a18000d510f0300c807000c0b80106e9019001d05003903 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 645442491 1250 645441241 645441257
    0x605090d0f1205130218010602010b030a021003091113020a021b0a0e1315141008030a030c03020f0708030412090f0e131b06031a090403110a0b0705030601090504090201 74
    0x80c0310792500015032100080c1100c8600071113a0b400716880e1240c4182000202170940014030440e5030a020340084020202d00510340c15649800168450f043c000048040c5641e03030100b2810416010100b91110400078801d0800d4448404203d02a50041820b03100600440e031458000000c20700e2200221000504140c1c200f40c1000310440310810050081b00c0400320205403c400214000040100c0340340c03004012591200c410084c4180c06d4001e041109203100c0784c1c40510030114000162000d0b0080c0d8a000319104d800100154000c1c85840700380800598006281d8043c028410011402a88216031601e82c40c50213542c2215040c010b406040302c0000017034410080c0819424a064014803d1180b00e2000d001580d03e5100e010071070000c001e18510450410866585c16200b007050940340000c0e0103103440c80301c400044001500a000400340b000081003940c540e44100001d104881c2c4c850f02e0182d060410b03c6000c2d0140d0021180c0c1800220030403404119800c1a01404201c0c545c10f8503140d42c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 645443741 1250 645442491 645442517
    0x409060906030804210b160f0e010c0308070903230d05030c0f03060f04050f04020a06090b120a020f0c03040306051806041502090312070204150501090611030403060204030605090d0f 80
    0x204442da2000c03241c45e0441c07086000c00890f843d0b1150303038040c0c203044002c000480203225000c0e1240c0381c580120810302c82003502001c4243d80040e88646060350510301400c0c0d945e28414140c4d11160107800c0030b4040b01d01c0000078502c20703440c5d0b44401030007954042203e03100d20035000204c8841c40100c0b02020840c2092056040200e44a80550742041c402800070189103000c2020800311101119002c1a50300584140415130601980b1640513100c0c80c50402c16460806041d203020740b050440d510004040c0c200020154015907040c1c5103080800031460390f4400b860501d2035170301e400900040d5021803510700812140150710124000e00807560700079180c10340e520348601e14062041d41520031016020458588650340c28040401d00320448115107486800900502c000c88a2140302c11194240000c0c081c03105a030003121a404640b064072b0f0041c10b46880900c0c1070708602031a8001000d16001080200030000035400031441a000300c4200c070078405400c0b404942400c45c490355a0702048070400189 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 645444991 1250 645443741 645443759
    0xa03020307240906020306040e0303060a05091504020c28030e09070c050f0a0b1005150a050705060c0901180303050a0302090406080d020d110a030e010c060b040e030409060906030804 80
    0x400421a42c0000442880444054401d40701a614104c2d116940041044100d10b03261040340e010550b00d10040d804c600e00703900480d00d4100745010b0f1621411b8840d0005601e00c8908030385107100c501c0508295100d6190001c0d8940d9403105902003030301200004510402403441c011349400003078260342d69425080010083c01448500038013a8404c100303411200e40301088007000074600e09555040204510041403c1c40c10b52140c01910681c440860100204000d039107404910400d4041031404a40d03980c07031038006881911440030014000c1c05810100407420441d44003501088000382c80e00c07402515885480302c2c200d003d90000901007081030252071500c40c40795014080c00301025100148594503070060030328044000381c0b41e00050740300500079504954009920880002e5560090061300b0aa03940501b820b05001c03a028100300c0000941428446107400200315014050f10821104644200c155200c0d0b00500420358031034240000003643d42060302c903050407250042203460605040c810070f8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 645446241 1250 645444991 645445013
    0x1090c05070c150306091b110a0506040302010b0f04091a0a0213140a0b0406210204030f0b060a1e0504020a02010e0d1101050f091504030908070807090e0a03020307 72
    0x2140400c035051140000149904200c400500000d82c81c1d54405410504020f059030000e420041302c0609001c0612a6880450b41c85a07843c00a4141b0125002d00d010429203069102100507250384114030500c001d058044d0300004401d4810750303000d11041d40303202c140810b9800b0300800074031201000d55a14840946500c03801d40048190320050700c1d05503082c4200f00003003044d8000300301510f8589a0b4060920340030022000600c442d502041c01c2601d0503802410302c0221900c030006414412000c48403007000c5504440c09507600c07003a0038035100300c0c50a00345240502141d0aa02406260780003040000100c9211840018a42c009000031401c00c024807021b5005032080c00e06541d00c40c6210903035000d0500c1002104c54050340d490188071070382c642260039264040d2402c03c204041c44280442010082507044002c030a20884200a40380c900e02141c106100c0c0c1c0c01200c090191142c042800800480e0740812142c614600344a94942704031003580f25000010000d015a1040001300c00040c80b0240c2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 645447491 1250 645446241 645446261
    0xf032410050306091b0f19110a03050d0f05070302090906031c23190e041514241c05090c09071107060e180114040b0f060703090e01080c090109 63
    0x541003008a51172440007074100700d4000600d640003007001190403801c61014240d0380003a00e48134480300c0003041c082c3d454100404024080190000d0401c0c0e01e440e19401040c54030310011806c00052903c144014001d400c000301c0d83e0302c1411010049007d51a00103450070100c202490210050b400034042601d00b20742c02d50078540c0c0c0350026160303079024090440240401341c4043c051140d0147c0c42410081001c003802420ba440340d840c04c0064801003090031741e06000e075103400014100320b2030313008001207a1001010081001a0207401d004510801540290111400d500c285001d06903103500b510b800d50f84115004001580050f13400b03c9140351203011607804c000f0b24140502e454410180c12414030056412110201c2d5101c2d20403c0c40c0e003005459900d444071034602c905855414540580e03801400208450300ca1602c0d000070914655407410044414030005045c155075a0541c90041c0c442c520303c5c403e1035464085a00002606507000c02c400c540b5010003828024aa0b00b410304400080200580d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 645448741 1250 645447491 645447511
    0xf0d0902090114010207090c050306060a020a0b01030809040608070503150402061e070c080303100b130803031e060303040803030c1b2406030c01020c0f060f03241005030609 76
    0x260600141e01c4100c202800f0780810b40300d01e0b101101c0700700060320340031190744070b804418a0030741d0400d000d907403201c140c035003206088440341d9890011035402c80c81c00b60002ea024180e414441c000004001518000f09006a4291018402c0765a580391141d180d000a10a05416410060700c09030f08444214220b640184014130f91801c000303101894a0082d04588500801c0100001c0d82c08140418641004000d11203a40258514a0a000041d036101820300c00e9410940c008221030504d03c1000d51144080c002000403a074880c0350820484251030718180e01030745031503000c502184460402008442c15200c030040298616101c0b018403405540c882000b1921050809000d00100307141444030030181c0c0c000c183c0340040750300204003498802c103010b410240b095124000760038569070085680e40340e40202f11049006440c0517000b083c201e2042c50089000484008100300d500802c901e1144115038051056001e958401018021030030680c8103410003194050001844914101c90302aa200b48512 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 645449991 1250 645448741 645448751
    0xa0b0a0212091f050c1605100c080c0102220503010c1d061902030306040e010e1509011515020f0a02060712021c0306060215040803010614040510030605031e030f0d 72
    0x80c03c500d80514501910004000103900e2040d43c03802c21060030456141d030715541681e807074800001c1900030141c03946000d100500060300240024082960700800707100c4002c0d0358030601d00303651040c42c416528800e20340f1003000300045440d080503c01c0c41c0c80d09525403114100105482e40a954a03065a20042d5100728200b01481802030482d00c10003442d0700f0746d0019900e03410143e04200695445501007200340e2324080d103203907082500040d404403a8007854004840d0341c03a0300780700ea80502490340d807990307072403e6915000030028402810540310408640c240c44e2504004803d0a450b03c1850b1800395010006000e2031010030400c100c4680020b01d1401160700311a11020b43e44800100c1209000c08603581d44001c010040e014003c80c550840502c0e4040a0751405076149031143c0011700130300b07040140040701003041c16280d800311000b03007800412a601d80f4019001c01400f9041a001d040e000340180480c81d4a61007071082140380d6034810001550600c0c80d8103c3c10a81070b0080807480380e41a03212 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 645451241 1250 645449991 645450019
    0x3071415070c1206110f2d0a0c060605100c0b01060801080a080c1507030f0b2706010908061014030a120e010e1c03030c0203070503192c0a0b0a021209 66
    0x170001070492502d8600704e240c8404221020541c00300d500c98032582c61042c0100411780f201c200d0740882d500d10003642400c280c60800e41c10305c60000d08076500710301e811000c01c8000720303441a000300c8044040e52080402c0d00c02c50707807644402c9492075401e1264040c65484007410000041801c400340041d000090100d0390409145020000284000d59091020036900c4c088409454542d001c3c03100c44d00819148803d012000900621100240700c80c20f0141000142c0812070300da08c1961b45600500011003240c049082501900300d4845241c0b042c0d40d280c0d1300c100c003440c0e4a41030209212007003c1e000441075950240c4810b0980781256802ca1050420120340108c01640d9900040160002c41c01c01b24000c40040038980981201c240d2682c4206540c000c4c17100b54009200001200c0c1820070036148400b1a545009040e582d004900401d9603c11303070003448040041c4049410780810301c078101c0300011844d51711030380003101c0d1148040107401600310440100c10030301c0100040c40d0040c2c004d00064014004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 645452491 1250 645451241 645451271
    0xc071b290715050108010605151b0a17031009060303170411030304030807020f090f01090f020f07030c03020c0109060525080c03070b0a1404060c0e03071415070c1206 73
    0xc042e204490300c1c1c2e907500512007a20b0034071a5501611080e03c0b0709050440d060000c070b645005074501100f13540c054150a9414100900112850950009204d085904101009103443d04119503042e120b00c070880d8001031030112405510200c0e41c0603104e0104980c0c3d4203c004e103841000500a88422250080c4007095444c2007004200440c001c41c2d40c3c54480c9040d2041040100420000074811641e110070702c500c41c840e4401e03460440718800030001d8480c40b00c09480019001d103840310701d100080400d0110a050b040050051014072aa003034035034006103c0015a000c80c07440c018a000074405014240c030150b881c0c400019912000b40b4039484004840c0e50300ea805500941c0101c68540011075800200000e159250340c00c030780c4246092041c40702c0042d2200a241d0024406003019407a414006249402074045490340600502074900079a00c1d00c5e54807500034511309100d03010b01c54000980e03004412203c161002c031644240c403048264903020615445414950064810035a50486000d00c804 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 645453741 1250 645452491 645452513
    0x9120d0504060206011401020601050d030309020307140906300a05030a0915020d02100903120e0f15060a090908040b040609050a05010f2f01050c071b2907 68
    0x52940d94941c0c0c1c590510400070b04000060b1b00441c2d0094800a0442580e03070003040042c1910f40c11703a100c3c01201d0003410110090f00702040040d4144c010381d1301c041030b00390080c242c03a8040c3d60b0030340f42801e4540b121024060f25800c440080c690118960001560f41c00300c6690010000c40b8880840c0c1c0c4d401515150242181d000c2130a41d40801c0d000b2070208280f240d01c0025140143c0c50307002800c019901101d0103519401070b50201a10340765100c1c2c1505c2090b0050b0010280796651010401001043d40c81040d50b841940011041a20807084000543c03185020f8032032060310040c002d802d0b02d9142c14082d40243c218510304030f40382c0d001404041090641c100150008110998804401924041c1403000e41d40780768101030704200c1440311441080390800d12028134400340c80c903941d64403604a0700031140d0f15441e40c035404055083c82c060003103107034284001d0a60107005181ca102c03007410700d4403a82c801c01081d10600d0035001003011b44480070100000b4001c903003101c1003170b000d01e00800790343c42d050142 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 645454991 1250 645453741 645453763
    0x81f0515180a0501050901080a021512070c151a040c0c020d0309050f01080c071101050906160506010f0e1501020312010620011509020904061d0703050a02041203050912 74
    0x70a44080040304515402402e00600c0700b51750030039255040c4500e40340c80b0b82d2481d2029014003040959170066202d00b400b107031b031418015030003440103041c041c0c401840048080720131798940c5c0c2c00d40e4107962261414032488440508801201414008100502000e891070300508818004508a03150241e03e8081102405602c03a82d5500b481c41d00b007408015a0090301e560003410800b402c03040103064a003010803030300306980107503101c040310b079250004840b01d1090001d941e4110901003000504500d1a5100d03050b020300c00d40a84110b0b07238960081304400701c414480d1010307149201d004520001008200b83d600c060042c41524034050802c13446c4d80c1440c1003a40810009802d030380707001c44444a1148200c98105081000303102c0c1068004980d1074800c0180180012503a00091280d201e9440b81d01900c014601042c0c0300c903403000100c0c2d104421a1088483d040420300380000030341a41050701c2103605550150081c6207210302c10361000c131030070b030841d031580c6801088500790380c00301034402c1112031844 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 645456241 1250 645454991 645455029
    0x6090b040b010f1203030b0a0503071710020f04230915010201050a05060f122b1d0a03120c0203060a0501170c090f042307050406081f0515 61
    0xd0409140010500005078440010420015401c3c4142c80710421030015041e090301c0c000c01c8400950300000c54034441680496818490300c03400080840038034003041000c41214042e02c00700c101c46000f44082e0b2107400d140c2140b00c402088144a0100e0000e2518400f184080007401005a02e0300844e03c44a820756000c100509080848900741da0b09000f0950700440412050146080043c013040103440c2d4801c02c24400c03031020880030350300f4408100100c0e1400c118402d01c60000c0d0034a44000d082c2c0056008c1400244403244980824180c0030075902100c4c002a042440c902e01d5034803074103a254a064201010001e01001c04800350741d08100c00ca016112200e070010381e82d494101c00c8c4e00351000560403003800c0d07040a0780080b074907981e144595030b20070041c240d500000e640310329040b4984e10041c020405000c004074981b60100d140001c460b020381e401544c0800031781e61503c040603500d11f29012100b42c0e002031049940105002500140e401c82000048049000740110005044000d92540341c011 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 645457491 1250 645456241 645456263
    0x90912040303031e0209180901020f1b07060f090b0913020c0c010801140a15021e07030c06110d0c020f041404021e010f030207080d0e0a060c0f020c0415030609 70
    0x1a01e02139502e15880350900c4d01c000c526006680010031002041004101401045a4000b44075030000303404680c94a202042442d0f81e80700d1341c00035004510043c07810b0080e00d11a40303201040b0140505071440d41962180c6070300b443d942c9170141580003503108101058000009460740c00080c40c1600240100c01d16600103000f81c2008140010041d040c140d0210044011641c1140102d0320b44001c19002e44080d0400024150075400c0306030320740348003040c1800c480d8602c490901c43c2c4010100e414800e8a1088036090324042e07481c00c0c12583e0b2040c010070074806400240d00980201c0c0642508622107102404d20035000d100fa83c000b604032442d1540504007860b18004100461911081011400f03222100d50000b400d10440001c007034500349074281081c10b600140b10800c1c00080b10549624102144050203422202e0300f05070340f01c001007007044170780a0030190202030050042929421040c2e0513801000c00d00c40e05402c12000e0030b1007541c0801c0d040300341100400070a0507030290b504d140c0d0003403501c000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 645458741 1250 645457491 645457511
    0x2c0703020a180c1d1201060b07050d080a021c1a090a1406101b03140f0403060c08060915130c0302190302030606030c0309011401031407120209010509091204030303 72
    0x400d8802030b00191041212800c4e0000b050311004503000c5a6101c11303912007070854511300c01e4a0040c0b040d5000000003503400b142110400400244c0748454400030780d01c0142544a5605071026806405922040d0302da1018581c00e2448a587c807401800e0190712030201308904040100c0c840d0542914200020b85c0c0300d4200b0351864100702c1c00c0c0b030740244e8145e8141080d0892031000400c0083d00ca061207141d100c0c042c60b850180340c03207841e8100d81a43e0070b81500350ba80070640e114148a078050f22040311079a003401581500c443c06000a81d200c0c500240c4120301e16a2400c06c403241c4e08001c14125075014003807551040d000c110341c0c403d215a050035a180113030303101000c4007a58162214101100109801041001000e840d100c05698001344c0d08000140caa0700c54101c524054081c0c000c044014621000c0004103028088124500144501c010b0b81d4259450f031034807000754070015001a4000300c03d0001003201c4e08040c28040e50091a120980f100d42c200302c641001c20368066413042d00000d0310b40304108 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 645459991 1250 645458741 645458789
    0x201020c0f03090310020306060c0706050a08010501080f010e09030c0f0114010b07081e04030210020601050406081b0d03020f1b010314070219030e040624032c0703020a 74
    0x160800001c0c100440c02c3c100c1100000b940c030300303041e01c80202968000c00400c00c0c0f034443c0b03010350b4108190740003956401e5856550062141c0c01c008840e0000421a000015895010785500341c0560a40007050109a00b4540c6002c103611019040d544c003484100103e004056040c40f030800030803074200c0013103051903084022400d50607041e0048121980e04110307070030014094404030784046d8680d01c0d240074016681c85a50825019a274000b94200762444412042180c0c00308005050380d900f202c0411640d9202d40b402076442c403802c40c1524072101c0042c0d030a4103c0ca00341c0ca50b00c194921078030441d24101003480300581800b100c0c0c09021900642c000303c008c020341e0180100c04002c2c0141c07015032810702d00440000d69545c804d429912a210a0003090310502d841004010410f00000d0030900403141c0d69190804005440d0420503140b6111101d07854007503100f4000d207102c540542030b08070b080d02d800c0c20807804101081031000d00e01c2c1c03056000000050705c64400c030700c0003041555544d200d508201c941d40 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 645461241 1250 645459991 645460003
    0x120b0105130506100305040f0209160306090204080304050f120f061815010302061e03070e010306120c05060f090d151b0207120804410109030816020409030201020c 72
    0x307221181400104212902d0300391840c20b03d0440c0d031030f010a041e2510f0800252081407200302a41051004003000210342d03003050031014042440c0d80421949940c4e1030201c0c1240500e0080003801c0e003040000b0481c5280c0007195074044200208414210850344414134034201010052100c650448404c10803c600c401c60041d42460107103003e8000075440c07045d03402c0510300500000384600008241d02041e403148a40019015010114042d41c0c2e0501d103402402440400513001d000234184800440c0186910070050350785948440100020340c1400c08128164000710698005104284071001440c0d861945c0221902d000f5600c91652201d0240c05d40152885007141710340341406040c0200c45035a0004403202101c11a1994545175440c9203030031540d07881540d011105d00618005210f01d0030300950a504241c0e44000f40c111640012801c00702c20b8028400c1c51903001c10130019041012801c0c21008080c1c28020030300c1c90b0b001d030042c2e41c0090101d07a010801600182e5010a40201c031003410810 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 645462491 1250 645461241 645461269
    0x1305010f090315020d0906140115090e061c0602040f060e0319031101140f270309010c020d0807140f150402040905070305030d0c02100203070c110a120b0105 69
    0x201c140181107441d003810088240359018180d50b40050b500f02c0a070000e030301c04410580d00000a015014160a04110b1001e0070301944180450381c5444211041c00340560300c0890f404141c1000640d6203e01c100710298900041d9240c400d2110183c0100190185c802000030b840c614170350480c100c1c2003480090406d551626064003a9200006460329900884404108243d1501c0c0088003c0c9411074600e01411140da80c00c02d04400b180700f8040b441e04440041442100d82078003a001c40c100301d44251082d0b07100d004a281440c0c0041041c1440d0354402c0c075400300024005030140c0c030f12400355501c0420640c00f0300b5013941c22002043c94402c0c0b01740305010b000e40c0f64400b45d0044c51480300c03282010030110030140c80240f007569100c0d107907001c014080c042c4000a641000a60351520031524051000d000000d080c04014000e86030041e44000304c5200750390040f10310740d4401e840e00a0550340c041519010b440ca203a44140000400030300f151920f00c3c840a51803003039a444034294548021701512600c602c030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 645463741 1250 645462491 645462497
    0x1030c0c11031f0f150e04020d0615030c0e070c12050c1e010c0e1f030b030a1a150913060906150b094912030515090103020109180b061305010f 63
    0x30708002c0420303244c440d0f80d00148c040f81c0003a92460603107016401450488030100142e1000c2c0303400002e00c0644991b030000c803040315503041081d9560f00000c4400c1030440034024001c010502250b02010b11610181002400000c12a0031106500040c0900a14a103440303000c075a4480c0209050036a001185e550340c1070007694802c0c01a180042601408511a1510300803d40c4d184050320305681d042040c403010a40180101000804c590100300c1907031021100c552881c1a100b010403800e0400709040c610500f219600303030160b000c4954481001e40b0545030203551090320751103148190061510318030010010040c9541e5900c10301030521411400802c10b01c03801c82c1780c800c0400444440c1000344150103812003da614402060140004400091840079103180e4109000c150b0064042c1d1003c0e008040c044c4200c40c02104400130040d4011003400000c1c00900d40410400040c51b40590030301c0410258003002c40c20b1596000030440703981018404035403d085d403c008103c00d58008018130b460407003600d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 645464991 1250 645463741 645463781
    0x10207061d070e07050702060f04060207030b0c0a0c0f030519050a020d030e070b0f0c01050a06231005031e13060b0a24030209060d050103050c01030c0c11031f0f 71
    0x195218030f18010040180061100000d4000c0440d602c00048039a55045030194984454803128002e540d1b810301d000032208075078040007161000b2900b10030b0b00c0e203002640d59803101d4840544e542c0440c407440c0780340840c148501844040440d034006000903922140c223039111601e8200100b4000d290020b4020100d080c94944603400d00410750100d00e64040e42d174450317102640c2d0791644882c96150300c104940311038203520301018800c0c03004058200d10221140108060f07000034244004220b011181c1c0342e905e0b030050310204c0c0c0c17084c4580030b00d020710f5000b191850141031070101e511801a0100040764112043d0070b88244540030401144109440414140e54001c003460500300c40150890f482454a411001002c40001400e4440e80480b54a284041d06440e2034220b0400f80e60003034a401e010031a00303401844e41e126240c1d4031030b11440481e0b0701c09d5a941c01c1001041c0d15030404028248004c650140180c0302403400244403040840e007a81c01d80c5c40c0016074280d812400408a491040d15240c080280e2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 645466241 1250 645464991 645464999
    0x10c080307031a060406170c04181e06050609040f110a0c020a0614030a0f11040b131a040909050c1009080705010804150b010e040f091a36010207061d07 67
    0x2151f07030354403400183d440e0880c540384c00c860201c0c5d07070099a00812414090440c5010b50740e002c2d0700800c0613400055210010300c100b00c40c00b04140c1e5420f01586401107424041560549410741100d040002d404100103011010454200026030000103218040f424120b041411410a851a8401031241d0300d040c24588d4080500e00c3d50303910000e010145610b4452605003410300720b42d41b00c5074110305084040b40c0d90780d64510000705190817852102c80048801d00002440031044410106810314030b01c0000d140c1820821204020701241000381c0381407249141300c2c0410f0329012181180d00b01c1c5501c3e055002c42c6070003102407424001e078200c90b0400060a06100019a15140150804080c2000400c14040e0240100c50b040208510705a0040c1040e400c14044c503000d80c00005200e00643e043c4044160700300021503501c400380c03540101041104c00703114000e119000d00c08440d80803c040e004809600040e403500b684c005100a80780155540360700002c1c0c80100040c17460007811040680200b0b860 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 645467491 1250 645466241 645466247
    0x112050403021c05160f05010c020c0604050111100f0b0910060f26041b05040e0304030206160605010305030306090105010c02030a1209080109060b120327010c080307031a060406 78
    0x103403030b00761440c0000c43c0c809440c03050184041d40c50313013054401d8146041c916404c003083e180c038401c00c05894030752810f100d44c0c10f01480819001c2145c0da002d0989480c003441c000045400c1451205d1800a60140c1c454810503c042805082030b64269034074003080c0e50302100100008444054454841e132401140104407e40d005038041d486056142042c2884c0e40019445400e1039148400300c4600c0081c10041008000f48d41c00a03510b4240340303110300080d107500c0d0018001111420003200341144d00a1104000602e002c000800c1c6101c0e481030403a120a0320355881c003007610f00a070001c03a1140c00200c104070041c00c100030403c0c0141400d03c2d10202058481c0c002c00c1c0c881840401c0a400f41103914000c10b074041c080c001c58401000d050000304034484c21420020300410440e00c01d1841004034000d117810401000080d10a400b80052803030180c0707414590050b50100c400d0940c241403044504041001c40c04480141d440b8055a4801044503001c89202d00030283c40c20030035a02c2564144002e0000b41c1e8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 645468741 1250 645467491 645467503
    0x17090607020d020a1a0408070f051c02010b0105031902090a090c02010c0c15051018090b0105030d0915090b0f0306031515040b04020d02070c18091101030f0b04020414011205040302 79
    0x26901c45c280c1c02503110350400c20403d01c240c88000e040003500041f0b180400030000f900c2172915000c0040f0425444440d10124242c17445544058009007050001c25081803003084240b0007440c1076480180b030b21209501044d60983e841d80100020760380c90009041058080c06102000c40061800300f403401c000c1d646e400e000d515a501214072550f0b0303c0000424060075071100c03401801100440044a03071a41d00042c000e031507014003c0f03030707026441e10000840e820000791250714048580c5a400c08542001c9548000051400e902405c00c42480400101d21f0104c078002c14040c0304cad000c181e5a0742d00d000401d05240c1016502c003400701e00710210800401080c480107101040d2021117000c10403400c2c440c0010040d01070a000c1032f1801f0b100140c824200070820f07044200f101e0180c220345c1c2c1084021003c5408a491000b005010041112042c0c50150310030340c00000c06c5500100001150350002d40802c08036085600198490400e0082003407456803c40505140210106d5080c4450b1074a030750001d413100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 645469991 1250 645468741 645468773
    0x101407021204052805040f0e07090504050606060a1412010602010c020d051605031b07050901060203250218010b1305030a05030d02070201050712050301090b0d0308041217090607020d020a 82
    0x8105591200000a0410204001000010010301c581f10031000b10400420035101400200e10440750009190100d074000c55224541120250100c5d50314141480450307882121140d041003604440d49013a9406000603120030094190020515814140081d00711411a1091015036010b40c0c00c01529540c002e00311021034000118021100710180341a524501445512081c695036034140700004250010343d8000701c8000300c0b4044026641c0c0d9401340d8481c8a0440722413204070701e02050010008040e80e042a41d64030281485a5048418080c0102d4120a8200340320501001924800e181c0e4040c07244005070001b20081c19811a5903510317640e80b442031013401380c01c680d000315500c01507a004038103541c07200c5d410401c01d40d84403140744801003440e4000d0092102d05442c1c82200116410710090501c200303603054580510680b03030381d2100300c400d51391040c580003045421460790400e41d03101c0e01c00e640a000180b000f81080e061255000c1d0a004580b444c02d0215403040f4554004902a148010010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 645471241 1250 645469991 645470029
    0x30e0a0f080a030608101a01210c090321020105070906020303012102060705011b030b060a1124011403010c21090212161a07060b0310140702120405 65
    0x2d54400700c0e0650207040103900250050088060000750a021a00305090040341d100c100345004c42244010f68101000c0d5080041c518019040c005801070a80e00c03034405190746041c41240d072941c9540d8510000031540d14012403004441900401c10713024041c0c0c0703421007110b0400154060078100000c0d5640014481c1c40c41c2102c651740f6040241401a211f00c15051b006410a50341e03c0d0103080981c040c164019900c040114000381300c880f900d20038070810305040001425180f50809040049540c504802119645ca00030000c800b00c4002810404000034444003c0a01c440d40c54041000e044003003802c030040c001e904101c80005240c1e0310801d0030103e000c3c941d44d508900a8003680c030300024002828002e4002580074101010404c2c000f600141c1e0515040c08200318503121162052094101d00f188080c202040c0721102c00164140c100822099004d030031600d06119141c112010f80380c15601031012140d5844c14450f03166810b21250809035aa9a5071526041c502000b19410b1031a114060f000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 645472491 1250 645471241 645471247
    0x50709051e240403050d031116020103060509011412012c12033103080109110708030408070b130c050d05010e060106020c010e030a021318080304060903030e0a0f08 72
    0x200d40d664000b1441021041ea0810b640c12980741e10110682d200c0e02054034580f044000c2400d01c2807190140202c0b205080e1620f60810211080029204501c0c4004906040c1c03100340108207520754000700ea0090083c071741440681c42401d0217110400302c03403c030014000e0f41020100505510715a03034030070842002a944183c0c020100e603002c1c3c1080c050768941030b2a8003001090000504241c0c030503012220030303d485030581c40b80c1d511a00304070705064200200803c2007100100103a01840d440351298085c05240c4a281c04582d80d0f4100103070784200d5003180c03100d03404190b007001e10030310081c4980c0c400c85151081c44000c61648404013902d60ba4844c003441203400c081301d00c0801c1400e40140302d1000301041111110b507181d1300f02a440e08103004d98940069108408103145141c0069078188050700903107070095040c00500e11101070041e280030040440c0e843c03078202e400a800000114403440c091280000e4407482c43ca0700806850111401c4007440c0d001c40800c42c04150500c04400100340c0c8100c500d69 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 645473741 1250 645472491 645472549
    0xf0b1509060d0212010504050903030f040b0a1104090f050106050c0a1e150b0112140f070504030c080a0303050c07110409031107030c090e0f0d0c1505011805070905 72
    0x1e4180300c1d180491070920700104080c4104c010700c540080c16214211000d005503618502da0f150b41c0d0104454410500c4ca0840118000c9154a01c4858006000c010b0225603d24158442102c0d91720681c80520f01540d40e40c3c0d481540a0b46200386409030605140035403178050f54641355a594000c411001d0120080c0e140c40188002c0c800d94041052588408465180b0101c22101d200803c2501c154a01040700d00b0b0b00622400d12900c584551544070214044036a102c035403001c0c00d00b8100600100030700038100404004600d84e045032100501d0000002c0110442903c0c000b8142e403400341003401c207440c0902c0414001041c0140c28500c0348015140000c0c001f02c5402c08540210082030211428041c0c07410200900c0070744c000d080180c43e01180c05021003040010752a944642446400e5240d4100c0848945000e03c079202c131144650081441030071041804055100311007003a88070a02518480e0101418414180102988510310b030600702d22071480c180100705440400a0f42550121a40004203 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 645474991 1250 645473741 645473749
    0x19081c020a24051501030b04020a17060d1b09060b130302010e010e10020f060906040b040209042405091902062203080a051b0d050d0f0b030f01020d0f0b1509 69
    0x10030031082e891014000343c2480d03141e41d500c04242c0344015000a0521220b0742c50380c1454001c55031104441da0f80c41500b41c81c84060000d00c1c800142c4130541c829071047c205d601044000c1001111080390046401010346019500030031500740750b2112030741c00401e1110019021140e80d0700360443e90203082c8401c0c00304d000001212880c403502a003d521507024001c11400c9540040c240e609000010119030054a400500c581c3c1c0c0d040c01c40d40204448007041c005801410002c90054015214031a050160b0320400a0140f00184440c14542440d6654080207a401405c008059840403c0b4403000c8500200e0b8010996a00c914899226581c040c5d480d05101c60000c10740c40002103070442c9405445034112174008026038802d034012222460081444407400300041400914940c4507240c6514003420200c40d1b05c090560442080b00269a90440e41803d4800b40000c418060503000010f0f5101a603031000e904403944031100d00f281c00e00d007104029258550080c03404500d00314031801625500c10070001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 645476241 1250 645474991 645475043
    0x7050d0810421107141e06070f050a0c0905040b01060818030c0109020f15070b04060e0d0c0b150a0308132303070e16030504030e19081c020a 62
    0x4a0280300ca4660502c8081e80d00c45030fa00100c038480010340d03a050f0f640e10702c41c46040c900d00e00416844100741e0318104d189002c45840c0304450801401c00c5080119545803d04168803180040d9010340011607080d04100c8030648181c050110980200710030b003020745592505c003805004000c140002600401d644814003084080c00049010880c0e0b6610f0900c40807502038003030268200d0140c400107100814610304040512800b86401020a090003000e444001280710007038010341d190756549001d000e9841c0203110a40800803103803109410b8200c07500d032020030b070100240410304150000000881c4d543c1c904c50110200c03508170100f181c48031081111440100115400074040c1c00e0900c001c999078140da1010706101d81d0040701501d0440b60b49000310441e0540c1182d22400000310b00c000b024040307003c1c2d484150031034041d240c00300d050449840400e10031821b4800903000849042010400050302300302130006404620342c042c1c0000d442c10800307036582203650001406010800c45401d400b801070504 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 645477491 1250 645476241 645476339
    0x6300b06040b0c100b2209080708030a05090d02010c171e07120b060310090f0b0306070c060e0a030509060307030f0903050703032f0a020c030307050d0810 68
    0x201940d49920110305591448400d400043c95810140105500d03c1d1212040c0c0c0345045d20801e020085170304260846c0207090246084443c580700b0f00c07201000c078003000084c40c400d00c400000098039090002c01107151915010301002103a051007500020980d0105091800ba40c1380d031046092500c54030040c100c0035003408a60306075042c1354800c000e1202e910420b10f642d50300f0414010400e4501e410103105251104450204412107100d100b000b5202c1140d000300042c40d1080e5001480c2d0220000003402c10000b07981c15400100585225400d018041c8112210030701050001c4c28054525a0301500601900c07004600c80c0a0110015400b90f010780c1244220000428041164000720328002c0c240f80c11801c411b074000303031420003d08400390740000388410034001d100c0300186d8405800551841e952241c4160f000b1070143c1d0002c0b283c95202080079160a5205001800b040c000401004060703401c01045d404850008290400071050411003101c80d501d845400d6000c05080580f1141d040c00103024 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 645478741 1250 645477491 645477509
    0x20f0303040b06280e0a0207060f1e050105090109020a020a05070b03071e09030204020a02030705120726030c030a090209040c0603110f0d0b0409080403080406300b0604 74
    0x100410040c241c0c2c0d5551080004640c540c0a0790a0344841d422042101d05141000e1000c1e01d40034440708481c5210305a21004004c0058540040d940c4c40d08143c0e0120704010505c99181c9070301281c1d2880c401c000085800d282c1d0410010f03585880c000130100031062150390381e13180c0d0015004501da4424481c40c0c850b941c01400300c5241a6030b035881240c190380100e940b4000904c0321707c4046146040c80f04400c210010710303074a10444034115020440294040220b9a0640c80204076200020b0024030105000e50f503c1ca0f45113031a09198200894a0002d0a4030f008060032604400c8840c012200142ca8100f01203180c45516035907020721103c0140344441e00650b00a240c14200420045050440d5050754120b0740c0038050381164680d401b44038004c0700345104958400740a0a118071000d940000e6001da802040800d0082c115116a02180c0c0942c00c03d45100400140521640343c00460040c090012002c2c0000d5000c9840410b1150405c141204810a0384410a910643d03030f40e08183c9018059240d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 645479991 1250 645478741 645478747
    0x40e0a08030103020f040902090402010e0301061710060503010207080301030b1306050405010b010906020c100521070c032717070e15092505130b070804061b0c060f020f03 75
    0x42400c0d94240c00c2407004900c1440a070202c46640d0a26015600d0300c0f66000d00f10b00c015450b207500540303152990801e040e8056603225000030340016103800c103400c405402c5c0003500040304211030140958155400143c0030380c0c0100300020015840e9011a0304698100000800c02d0321014854014001c40388400380106080100b03000038444198800304013817009032183c04059584402c140d8842c4c1658500e40d81c000c4070001c417202140d005034010402e1101288084a020240010351007142b0002c3d42d407007000a040c402c1040405411255009003aa00c00070004200044500140e03441c0c04240140d0108041480024410800c00c1009901412000d001a03140b07180c040d00d44c102996144001900c18800c4a020a40c00461a1240c15620550490140c03a00d8018032003960f43d94049590352025003401c2030f0000750145203c024000d01c40c4544021a40c481c5448401800c26005005000354610800c0111001508a10400f0101d45090424142045003294180d050901072142c200d1384d40000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 645481241 1250 645479991 645479993
    0x1020c030a03022802071202010c02100903290c07081c0e1e03160201090e0c030a0c020f0c041104091103070306170d0c11041e050105010318060209040e0a 68
    0x1603006414a180d42c000b41e4101840d0011203003013280100724110016810010083c819a00204030104074240107042c04000020643c0c0840e04400551003110b00003503c4090901c200f00c106400042e1110500303601850720600c3c0304d680507180c800580b80446000d00010341c1020000c410094500041141d9a901602c2d0240c10311032000d07003148d88800c000d038002c4292080415170303690340740c15004503544000c60030b241301320002d0944070002c5c04041c0e0501c0716451000605000251015114850210781030340ca070b041161490342581c1d070500145040d50032101600c0017030750000424464610303044501194082441c00400310620694002d628050300300700f0000d90303a0420200a60080019070303810406a039540030038120300e80425180e00c065410400c00c40d03545034030a00504890354028080c01302041011f4000134101c0e0003800302d410354a008088002265070142c400d40d401403c00303080c14801c005049103010010f0300c6047c0b00409107a4003060044660b1078950056680c505410201c0e2814242 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 645482491 1250 645481241 645481247
    0xe06070809120724020c0304030503070b0105010e0108190f150f09140a0c090b0d0b0102160f030b090f070f1404091e050a0804151103040303081801020c030a 69
    0x821100e058191181003460a0b40c0b580c0c0d6812104034580120010114110080c3c2003a4940c03460200803d0060f000d014074144039600740011b000542c801c2c001569902c06600c0e00456070715050340003e0500c0300e0f064210000c0d0340c100c03110581c443c44030442580a0044004810000e00300400c00705119490202c822082418254000081d104226a80c884040e6a11800b0341550100340410400d036803181c01240308000715402841d8402d54500300740344c04030b454007041b010540050100300309894542901e503e4a50301441600070200062025004c10b60600408507400d50a6100081c5000c000e5000610180014030070f80001604060607121a250b840d43d00701502121405061009540103501c00c030719107440d210f41c900040d032110700b0070303451511420386012400090806031254082c107114400000c1c01400180003404035040d02020031885803070010050780644420008a500800003400425080031615912412204c3e6007816452940d04d4203001e8059008440390718400850384074046a0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 645483741 1250 645482491 645482507
    0xe130302010608010203090d14090d0602090f090412110f0303010b03010312020a05070501030b0f0415060e0d15050903070b0901020406080a140f0c0403020a090501050306060907210e0607 82
    0x4000e600920502d81c403444600d00300e100030b440c86d542952000440b004004e0150064150701d030a5212558105000c11011032845002c03802c04465441d80050022950701e0f0516400e10360841c01c0c0d425092074981030381c8220504511107412002e00103002c04d10032040c4005c10000b00207034402c200340d0b0f03120750707440a2017500394100b8003040380c80d04454400a00814030000398802403a82000082c00203514150040d0001c0c007101e00d1054102404142d400f0306074a60703000d480518010402132000e82850848020400109030120714407411051440402068940303011060b10781c0c4202d0002280d07190b400d091459031080803002046c084800040080c0940107602030301c00c86809495080940c0d54170f0401100300c50007411503840c041d10704000b045c10002c8440300580d000521010342864240c5170b80021702a05c00d503501011810391140011320084c102488804d0304500e06a40b54035460030304510162652400010600c1001d03411420913203078000b103401c192403105096007510344504050344c0061140d1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 645484991 1250 645483741 645483743
    0xe0f040207150b100806210a0c080708010b090f07170c070210050a0518030705030106080742020c1002010504050f07141e030f16050d02060f03100e13 66
    0xf442d0030a4680b4034207250300e02821500241d07940e00c0b200c1d542d00c000c00440010007000c03408401c440b060201f4203101d080292034541401742035250062031404080c0c1d840c100003504500b015034107040e800c415984401d506aa04119170b44a0f0100543c0e55840c1203580104051420fa0072a02e2a402c0c45003031940c0200a15406000340e03a0030007551525102555180f06803030030a800a6000c20006818000300c4151541d2940010103940340c2d00d40d02e00000382994034641080817140c1164404106d1940c1c00381c940b04451005d141c140700100520071103120b0000b604001030301080441000840070500c00d2028084d2048000c058601e400694400280205401c5508440d00d01c1141682c45d401d80002424508441c0407084d0b0b0000300b41e030142070008100e854540314460422542031185141e038288400c80d4003421540041c40c0d01603055600c0065991940e200501480d0211813210141e102c58048900c4a81007003000d83d625110141e00400a0391654030a4414101d46401e101407601004081135040e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 645486241 1250 645484991 645485033
    0x12d0608030901120209030a080d020a110d0e1207051804050c0118050d1718090c180405070509030703140f071202010e0307091a040f15060e0f040207 66
    0x15254210030765680b08200060780440e0055130b14440c1114607800400d050741c0d020b003c0d2100a079042e5524a5540c01042c15404071607004910030b54910750007032080c00c510300b1001c003c18209100c2800905020324101d4610b02a0a415100da4444881040b03010010b14018040c225000307002c0c010546a03040948084a150103009078000c02e9611883c154032035030303041c1c040303800707180e840c00040011076600d80104440550600d04600b0342e0480a03400f03400b50341700883d1915040400321080040c9000000d24001e902c12040c07000b045049640340c0da011540b207003038600003115202c03008182c50a002d00101030351716228040b404000c01c5081d880075851251500c0443c0e80601d0701c0d0381d945450759810b0180c07180020656007040c3c003641c81031002d0002d0701303006801c0d110b40e25207854000059444440811240d02203510040d4030718140ba01c501040011281010064a43c003290f07003503a4842e03180320718810401c6002c209a82c0b0741e1100c0d2503410040004200b10355804051500520040083c0420790b90 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 645487491 1250 645486241 645486251
    0x607290705181e060a03060e090309030f0304120305030601030e012412080304080906070803070f090b04030317190e1f021309020d02040302041e0f02042105012d 71
    0x15040c41003c0c00310100314100d10540e031680303100a00540e600302485510400d070b214000010134405800c0414081c40c003200286035260601c03000d1500d40046980040690b0344100070070071040005281c2c07e1807155051030031982e0707074a078400120054440107030b900c401d9520300b115008445401500103c0e1081c0d041d40c81c414095601c06844203c4650a40040c007481420000074001a0242c40200201080201805c3c1455901d445003007503a002228a900440e0308803001c440800c0e040081306000340600140e452609040d40c3e030003400f11100e001120750082100b8046031090080345c200c206d03800c1801c4010040c100c1e40c501825610015034407111601600d503081d9034103800150080340c4001802c212003d0703400f85024200e20096008058040c4416400d2001100694407400b841e18011030b8440248009800c44120004845003c1807114025204000404c2450102c0c0c040d108803442495040284440c1c0b814050302600d02410720720042254809040c60800601c27400118a00201c101000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 645488741 1250 645487491 645487537
    0xb0f21010c0509180604090b0f04060e010b011d010c08030c0a0e03010603080a1407050106030b190b010e0f04020c01050c031e040f1e060f1a040b0607290705 69
    0x2a081c0b0032100481d8204c1da000310700f0311340d1001c03202d890340e08000060310025030141503489800b801002500c0021140004806020520155000f80c0d005244504002c0007505420700c0013130281d182400031b15803000307030f9203c400001e68024046420080e8004030f0650340c0e807820885c8803429901182c08800891100d0540c410741d810148280410b0729802081c503441c0003120103050310504000f0030f04103481002003100d000003c0c130a0040c2d90040d41714108001050400098a8031103a82c1c42984944d01c40c41d04019610a0381e012024080c080c20a80c3c80d140001d200d038012070f029208045000d0406d40c200024041f0220150009620449203100300902420a0b4000c40004036410758000d412000c1c0100d105000c5181c025000c13890104c5400c2c0301032640e000c2c6d65104107aa0b0001a42040b440e0340700410004c0030741803904d07005070f00c000700c030100311010300600014243e005940026001003010a078102c440c466490700e07200c4185402211400e540b408100040182e0b1020001110030010281c0040c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 645489991 1250 645488741 645488747
    0x61814040b100f140301080a031b050f070e15030706080c0c06010f05120a050309040c120903120b0a0302030613021801030f0303060f0501050703031e060603050901050610120b0f21010c 81
    0x41d06035808000585548d4007685c90495141003403c44102c06001d11498007030000b002040b10201d040001c801170000140f03420142c80f54484002d01c071a8094050603107030f0246940200e10402950740500784010541c503140a000b40f030303006540446056124003000441e000fa00300328840d0882e00201da81d10116206030942a40300c13100c030301004040341e0040c4042051403070036030854a03000c507603807600040201c0070000d03c1c425078000d0321060340864420076500500440600524500210030b40e80b02c1e80540c03079503001c240c3e40c031401081c0044101d420005d1030219130310140303132440808501400384421350b12800c1001e45040a000224046454140005100b420715203441045820507121181440000e0700c0980182984004801440c3c06814003a09001008c1c0301e0780c3c000d0504d82d600001c1c1c81ca0325600e80303400c5660140156225900c800280305100fa4840d41100c09804994804540c0080880c0403600406064014550001d0885016140b1001764000c4a00c1e00174580001d0000d41420841a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 645491241 1250 645489991 645489997
    0x91b081506041d0a09080301090507120501090c11010e190c03020a030309090b09010e0f13060e07170c030718020910030c02150405070501030c02070b0c070e01061814040b100f14 78
    0x200141007d000410000c01c6075445a940f0100e10b0a148001c10f00e801c400200310ba100741c004400321030b03a0b00540c0842540c4410074850b526036210003041006040c404040da07400d0707a640c005441c203c0c1b4a40c2070701040721501c042001154003802007168903442e1700d0003501c0300d8018000c5080652174030351100710500d01074110a0403203441c43c4100000b502d4980c0302c4103100c24004c0c10880c00b80c03c4001e00c000007841c24452154071028170b00283c81c80c0382c10008092001c0c12520403070052070b40b01a40f440220b5074040f9403581214445801071480c1e40a05100b43c01070700418244581c0035101c12840003003280c06401050000ca582d03425100311500301c6501e4001004140c40c00392580d030100340244010b5020394000c031803451043c01124480d660300c01e626151548903810440351504200c00401401da01c0486550140c129400c04010240e5105d0120742400708911980512180030154070000e6111a03100e884d1850002d4032210841c42107803005446890708001400010700c4411281081b400300c80b0075 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 645492491 1250 645491241 645491243
    0xb0f0c0304030509060c0a0605060f0a030503090f130e0307020f030102070f060b0a0801062c01080c0f06090415080d03060305030715140109060609091b081506041d0a09 74
    0x24034215101d50301d080b9815044551040c1d04108108148101c54804124503800c2c14402d10001c50913151020a0200c07642c521a0346134010868000140001080031066500c04442030303c2100d0410000c1c00002c5204c00c05115598800d80f52150003000c0b160044001c0101c07900a81d0245808940030040c0f501f02e10500710064000f40b2000c0c030840002e012504802c6034848010045100c45459030040d40c00c65699030301c20181e46041e4445841c001c0481c540c82240c80c10240000d501c07640c58030b25a00d0721400c40c4110580b04040028000401e0b5440e5001d450002d80050802c012a82a01c82000c0f100816070040712004d00c14a0f080801c000e21038090501a0390b4080301440c03d194090780c031300044029000080d041c82c2e480e40902121507203a190440d0003000b50b0340020801925003036000d0010f580a400580c400d90501d007445e4070080941c0741010501d4101c0c60b03c41d8081e0b0720b0142c0b240d860f807070411030658003810000b0b000901070341c56000f00c144a000861103007842c0d2034040200c400c8a44c2d04030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 645493741 1250 645492491 645492511
    0x1401140904020d02010306090c020a1703091903021c030e010b10120207060228090905070903081c0c030207020108061c1205091009030302060603060c1806090d0f0b0f 73
    0x600600b04141c2d0300240d40d2041c100485c29546400100d0706449c031054010006034803c40c4c0344404c0c003000d50f09080110851158262441c20709c0c1c0d0405840b00c6403543c030420110010f03441001054401c00c010480f0700711070b0085000f10211004000e000d0050003036092025801d207031a1800c189407402e205c0040f482c09840b0343d030450712842d03ca0b4000e50410303d010394101d5428840c01311521800904000607000103140014448501c0300b0242003040d158004401032840c00c000c0280454004800c1d070150f90b00009695142c04503401c203407080d2603541d07200070405414140c0034400d281e01074001d001802e1007600e800b42c10f9a01c9006105003c019207916004500e01212001d000c10031441c50741c2402074031860854507281002d001708502d88000d10180700003d003028030800c1030550611a03583c019004902034540c5007846502040386000d200300c240c900703401440c1c1e051129030303030b44084071160071b40982242020402e6040001e80e20705a8401611400d0785c0710000340b000b40f00740d1182031041031086 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 645494991 1250 645493741 645493759
    0x20f060906150f0607050105040c090603080708070f020a06180611030a0315080118020f0301020702011d030106080a0807060c08010b07120e06120a0e030f030f0603070b0706140114 79
    0x3100850440b41c1074140c00e401442c0034440c02403544a840041242900413000410507007041d00c1c005950551550140c02e071300c0e107428810301c001342c506000c48044075085040c0303a4a43d82241005542c0c02ea882038000e6220040c0e0100040d0590403003541e00300303081641f4005c20401d40c1c81c20203480d0764802d040d06004540080021016040c0240d01503485800c56041f0003006c1500c0d010350030300316907403ca400300d26002040601002c40c80c200580560142050380290300341881c0781d0010b444030300c2c0da4014058052040200d040c0c40e072000d512070002403916200325401041141800115507201ca1010307039a05080c02005070340740f40a80065412074071080212490318502d0b86440300c107104030402001c02c000500300b590b07160790344a002030030348000134140259582c10400c20a0080700c0582d05200400c0e0070600801100c1070001f801d882d403200100640e00351507075603800042e0030324801d500f2280c1003e1b000700c1e4071001c0c4015503101e41081900500711030010f03600c03049001d891444241d21154000a04 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 645496241 1250 645494991 645495001
    0x1090e04060204031e020406050a0b0a030504081c021207030506060f130902030106050a08011a0921121201050109031722081005010906121e020a0f06020f060906 71
    0x480101503025015840050600740c4a0341d5003036500e000681c2807003110801081e04025403410344034100040030308542c034034012840c114107882e0034080c0e8000761050668071800201403002c28811900846c1d181c075440710b1007514680d5004000c0d00141d084c1c0d40d0300412000000c207000c0c0244201405000000d102c0c1d410007041c0c1006039400d07400310010125941d4840c200041008043c006103000c0c044507150191a40c82030200140040c9050b400b40301c2081d04420181c0c4482000300454124020585010080c1c05000c50030318402c541010b00d580c094818424100d84000a0a004c1c00303d11042850b9648583d80e13a100444107110b6602001c0c2500c034416110300750b0f64900b50014035a002c42c840148000c501c1040d0310ba0039100050344058a903800004c481c24805600d071041c5400740881000c10046182400150807401040c110000c02c903c007191032210000b40300d0800e1000095000f0030044580b900c0714060030100515106000152041031403014030322601003540351082c42082c00824499441d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 645497491 1250 645496241 645496259
    0x15030c0e181e060703140105040e0a0c03140d02030306010807110a02031c1103030907031202030d020d140603063d080c151c0207060b040219030506030c0109 69
    0x9854400010000a101e650484041c065001c100d10440c0c12662500d055074001410410014441000c045c13400310b1900380301780c0342c084081c1519425034002594002105240d0315000018802074504008000008100208140c408216101440c20f44501c01c290707241c1a03a0700e000a80300903012400d2000000e810074441c200c2c030601d0680d1802254810b88890b00801d007050364805041440d00b20107141c0591040d00034402c00344191042d00250710314600203580a8a07103480c2d020052003e4071080100020034420000d90300a412404011550365244d1002c0c18018000b807110080300698090020f80301c1d18000c50450b109000e9100c042c08001101506210760112071152480d01100901c80f00001083c500608000391100c40000c24007104000100440e01082e0f04e000c040b240c40400c81d080c49410021030703950a800f01402d0150b11443e0602c0c145c0083c0240d950400c3d001071000c180c0d031040114200e0100ca03102d0b06600c0c00c0025031166000d0589a0b0302401c8494081000d4800801072407903 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 645498741 1250 645497491 645497519
    0x2040b0d200414041119030f1b0e16020d0f081302040e010f090c050901051f0c06090b04060c0302090d02011b141606030911240c03070615030c 63
    0xa00074800030700d08520b004a0080c41e40156415100c0a6a160a05060341030410080030f000d00c0d102654003038645141d032540c0246072548c10080626000c01e00c00400e820000140e800907086030f458100051601d620413603548000004008018864001c40c0810103014000d0110140900d030340700f1100b42c2ea45a5452051a002003040341c02c140d46054800810600b031042412003c0d04400101f400c1d00d060600310031092054001600c0b86c0d04c0308004010382e0703490307100400c08a44140c0c0408021a0300e40c90650f480c0d6040d07100a03015604020f07070701042140c0a2a00d5110307510031a0200004e00a00f1412004c9025400380c140e000740c80c0c0091003002d0b6000d0100000c8080c1c811403940d89004180da603800d0b1165101300240981e40c0807607808280f18007010401d03005042280703010094604075433078011114080d004d1107401000e28076a0102071a10b4450200354603440100c140b83e0b582010b400c01c555980c411001618403602d0030500c41451040c946c4283c0480ea00a001008014207010006c00c1c0d0071 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 645499991 1250 645498741 645498803
    0x2c0622060807032f0a2f0709050f060d060b03030706021213050316080d18021c030207030b0c0712021006090605030a0206091210231311010203120f0402040b0d 70
    0x7a000d088580d0911344051145030704070307981117042c581e4001031103561a284003a002072423164140010041800c103201462a40020104d87c2c0210389401070900390010803901042c190103000c00a5403606002c01c0341c004103c203602d81302400489580e110113450313a24407056002405904104107091148000c2c0310740036074590040f0f008602d409403030b8502c0001c43e0403034080f103040c0d20b0031540070303000758603100f41d01d20300703545420450b8011004079540080d11403060f80402002c20b443e64001c18440c8002c801a500c645600a00900c0341d4035080c03801070b540300440c0c000640694109440400c000d0068040d28007202c602400030300f02040d00d40d080180d55008641c160350041c50027449900c900204224210013507800c18400661300ca4205c40d0031b40c00c40032241941e07494600303400a100f4810710101d440b001c2241c01c09804000d41d02c0c0000100c0c29482401000b0b090088000b0a0155850160080a0046108407030070044005004184082580044000780c03241030031b100c0c43d0809a01a4000724018 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 645501241 1250 645499991 645499997
    0x10801050103150509180c0114070605070c0203150a11040302090412051303080c0618030a1d0d030305061311040605030601020106090207080306012c0622060807032f0a 74
    0x6944480108542c4101181c500302c0020b01741d406d003684050706021b0b0843c070300d01c28640a0448802492004140e210f142e100801d1680e503031001a80c0940314084a600e00d503030007019607a140c10307406052101000192035641801c1e1422007030120340c5032004100e40441340d0181c011800e9a480380c890043c0700c80038103948000e10108002c040104900b94281602851148144036202c6886c102035500d4840b0040240d68201480705040500510000640754034031094a010700ca0000d450703c000440041043d245500a408a401041015015045248210426a042000206906141c0c001c0e100e400700c80d007109a400b040107020382c9201e14010b650025060002007292a83c840d240002c80e44021019299200088148070056a00406150820703440e1107610440307107413204030622020f14040006104450000e5241c052a11050001c154060f0000385030780304540c2ca1001801e004011203600002a103003003007082820460074840100c03001d41ca404003000328800340700079080d948010444018 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 645502491 1250 645501241 645501281
    0x60303030b10020606221d071401080c04030f020f190e0f0402092707030602030a0b01020d020319090302040203040f0201021c020c130e070f1a250c080a0818010e010801050103 77
    0x301f0401e04101d04510346018005140c110f141c40701825204408503011030401403440d040c000b0f00e000e54001e9030f05507500540c21035070300d0f5200c2c1700203603001800e076025075041070240382e44119420807241d50404550a260340c046d01c6903100003031445185801c9800a60140615010900f04c12600b0b13055102141811300c0d141500e80d82480c010701e440c40c3c81d401203c1e42030700041000000550750192034180982030000f0010718614800103510380c000c040100d494010380b0b07498040000d11038582c0800940d00a0070441d41c070b080605000c2120070380d0381402d0f8090301c12643c52003c10380b0407030365082c0c3c411183c1c0e024040900c1044100000140220a0110f400b81c40310700030a41e58005005d100010320502960702101480c2c01001214100c0b440540c2201da041804500038400e410310b951130000a80405c0c05800340c5452408620b081104d401020091023801d10380c1c8104000d080c000c0411000c07184054400701c4840c001140c80c0700340e481000740001c000c10300420555020b42c02803603c0359400c00320169 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 645503597 1106 645502491 645502511
    0x60e06040c0e06010c020a0b0306042d09030c051605010f03060b0306060304081c09060510030f02090604020d090b100b0a0f0f0909060303030b1002060622 68
    0x403201002c0b20020309281c3c810102c0480040d4001e01c0094425214113141d07106410485090f40100d14000c0501400d0342c2006038441d0031084903008074003243c94182800060312100d4002c800380900e80f8451340004005210141e12441e0400e10840402c7c82c0c480014086d00c1c0e0740706800c5c1803624141040c001e005510b01126070280d0b007038a085589440d6450020810310800000e01e15103000d820360551850055004500c00b140543c001380305a48480d021040c0744a024440201128076020840c001814031000e81544140024401410040d0085280042d20030b1700408a80c603500650801a8903482006490b010380640031409040021070700b406820156807041c00b10130302102136800300c5202c1c0305000310405000b1a481c14081d040d40e07840e010300a400c600080074403d040c00c80301c170009180300007000c52040d1802401c50400c401140e401101c1d841c0307074100f248842910303a40054 = true := by decide +kernel

theorem cover : BRFrame.Cov 645323741 645503597 := by
  have h0 := BRFrame.cov_init 645323741
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 645323741 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 645323741 ≤ n) (h2 : n < 645503597) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
