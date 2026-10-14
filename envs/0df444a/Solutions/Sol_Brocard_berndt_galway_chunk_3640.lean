-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3640
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:15:29.029285+00:00
-- url     : https://prove2.me/submissions/0d040e70-bccb-4ec6-8eec-4a939a7e8530

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 654496402 ≤ n < 654676258 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 654497652 1250 654496402 654496429
    0x12020d02040e0f04050f030307050904051009050c1c09020d1b120609030e01020f1b0d1509020a060e030d050714060f0601030b0411040902070327050117070e 69
    0x20040c106078481d16444030004040e034041d40402550800c01040140c20030004000c140303424007460550815007000703466405800c4000d40700d203840c0c030006541400c0b150b40c0c0d0001044103d17428040390428983c4028164001d420b1111014075152443d00c588041d806500400ca0f0701400c54916603039079854102a103000c0240b00c4803442001000010a254441e00300e944c01405400009140c2195140144c0109002c0da11503040d50442c005c0444135603004140c00e241c910360111030480004414002582c0304928440041c2942d000070360382c604c4c036002a800801070a100b034134100d041c01e0303c0b000d0582d00500302040b020fa05600440d0303048501c61051024101c518408d09103141001001c5400904050048880f84c00c240e03604400c0017010740e4540160000d14006541c20010070000c10701d540d409200d54044d40b0011074001641104042c41a0709605074020300c4100a180c201c0d00109015070700600340f00f0b1900255001848800e2045580102401500503880b00c40c01c440c1c04005000d1840407054 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 654498902 1250 654497652 654497677
    0x9032307090603030302041508090606060d1514150c0607050702010e09090d0806122d0f0705030d0f0e01031d0304030b0f0f0108120c0106030f0f03030605101202 71
    0x41000603818914000c2d800a1442500d0245e05c903800e1a007154010842c40d40d8800c2084400c0c400e0100001002c40c00540040069410a82d910304c903041c1000580700f000074640d18428a8440000c224208104008103c0340840c2c4d00090300d07203098581c4a80d070183c00c4c0c0c2d070707040d5420290225040b640100002c0030440c4c03040c1440416040c103040040c038481d104545001c481c4d000f010009810350743c040c02896001e24100c0305251aa18040111544c481e0b0007811a0702c460f8001204a104012803145c01c0d803c0500c0714229075000000220850300e880240c895607010307100e10f0741410707840390083c01035000840a5541c2d4240c03640d0810011009070405100c80d1841c90407042c21000d0cd03c0d820302c000d002841c0518500041c600342140c80400c051002044000a44482d81c01809556408100a440000c00c03118054640b40c44503400c6005210300d9200a10b080e13142440c0404108403500340c0c2c01d015009407420822540c0d03503014000c2c81c20305000f10300c1c000b070100000c0c0406020140e0241004840e5803 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 654500152 1250 654498902 654498913
    0xa121a04050c0604080c03060c16030305130f030c110406060f0c020109030510090c120f0311070513050a0b0405060108010b07051009051f1e0506030a2102070501090323 74
    0x7240403c055900076080045903400c030a45035002d44c102040442d0304240d418148610b040302e110840c52031629400401020151940c0c003003a95584581c40003804030f6000703441102044c4251501501041d079454084035820005d060b401d000703240c43d20030401261040e88491900507806070080396110f01d80038040741032210304500480400e1007004216040f0380c00000004d0310721418200354220440781e51100e5109210081c4140c0020303560480d1622642d4136003004000044180019810040650800e9400001809007a5080c080c3c0b5040180102e10449040003032202001c144000e5510803120980070030305240040001f241c401004082050068081d00d420b1503031908607000396015504180d0760341e03110aa15212848140e1035016500061340070820070904040d01424002c2413156a40500e590703680000703901601c091241c041e03000c0d0f01180d0602c0285902c0e07484004040094032000042c492000049070550068141c1c10a40790442d0000009601c01410602c1560002500c5112030054 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 654501402 1250 654500152 654500173
    0x9060901031e0c090803030c2a060a09170702010c02090910090836010c0c0506030a06090c02030f12060d02061611040516120b18060a121a0405 63
    0x1441031001c0054a0000218500e0f460b000700070988400c40e04644000e400810a03c522604010211a80640c541409000c81c1c8a5034000b0000e00341d015413418150b0058004104018070a54000c000c1c0034810300c0850305a4400301040501c60141c01d4000380407554901c0d02d0005840d0081c43d25501140a00032584218100b41d4450142c80b10100304580c80240491101e41d00000036146203c0d40314004880b120015103081c80081c420000c1170b07014103116640c80340805105640020002a11b401340085d035036030408545604c011300452143c01340003450b000391000300c14400f1003201c400c400a82d1b000d03410683d0040064500321009170000754041000b007954801600c520001c1c00030b41d0b901c00031011050115041041c0c82e4902d610910340309a01d4071080005695032000425420310003480c4c105c0080c050508a440140124400c2c40c0d070040c035180001c610234144082152094209032004c01c41c0c20740c1c500300b1821007140d0200041c010751004000380c041400303400a0300d07030080c01002126a5441c1c0c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 654502652 1250 654501402 654501431
    0x309020121021c0501140102010b03060c0705030f0a120605060a02071406041a13090b06030f27031c0209220f090b010611070305030418020403020a0b12010e06060906090103 76
    0x482d81c0f03035a00c000d030700c541c01000420046480321050000078002440050140310001e5110600184171880c0c03504042030b41b0741072090410640b401d101c21880d02e035035182c20711a00074003018611503c41000c1c41c2405008103140c2005004d4489181c51900240031090410741070507440440c0000813500414103120004c2c4a090f4100d0340040c074044000c005039105070451f210086064a1382110000c075081c41c1c0e960b03080341c66080440350300500f01180030309581c0f01d207507c0840041d41500301900049601d501020016001720080c601c00031001d02240340c1588180f1b080d4160301540701650741c0300341c81d600342c070000122070304201001c10700003400000c03098002c0a01404691040e8000c1c1c81014208005100740354000c0d489040070f044200040c0f91091450f95501c2da40d10640c01920100c020010402940c54800e405903400340d94024041c070041034541d00c4004176500400041520042018000a01a215052042d00542001e00614508a41e034070a102440e44051308290401d6521000b001c02c203038 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 654503902 1250 654502652 654502687
    0x210020120090111030a080708090601050a060806010201020909070801061d0f061e18131a130b03030708030a0606090f090207230703060b0613090b061603050d0507030902012102 78
    0x101b0b6203c1450718184041c00500154009181080543c080e000500c6280d442842440480b103051400d00350356900c5900403400f9016285000d03821508100600000a81196000e4140c0c3c689036500d640152041e01181d010540d0b459100384c02000c1a42a1801400d01c0700c02048002c440072410ba40b403004031043e084650703015100d407049101c0301d0448108140390001c0217055688180d04103002c40300c0c810900c0103200012a52241c801d003190041c1881501c00380d004620381800003800e5903101e1049003071102e00b550003202d569804915107400851054014058a410b89402403c5041c03041c2c02d091911000394454901600d0304000b0f5910030120320109210483c8011094000d03111852541c904070342510941503086108400600c82802120620035007441117821081010074101d6005c4042211440f0304400ca40c5540c2741d40002078141500a0010003040e452040100b0413075a90503421001c540f1847c40003400101c4101c1e0241da005090a07461060102c2c02c4001403405205c0c11820031b600 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 654505152 1250 654503902 654503917
    0x6091104140105061b2e090201020c01210e0102030406051308030c0c120c011d0c0d0b040c150c0b07020c130b01021c0201091104060b2512080103021002012009011103 73
    0x550030103c4030540d02021006c00c4240c041d540000f4460305500c0d60010752103e6201485504000c40d4031240406410764402c02d01c0c42038140320081000903c0c200e0030902035801140d054404906100106110350814660020304640003180309095484103405030380143e000800d58601c0d44284045803a185181d403005000c4142e07560300002c0c00c1900c13114011a000b15001a00c58650004500c0340b00036110406486c010703551000c0c0f1500155542d1030031305003000f5035400000310410100b03200700100d1380000000764014044c000b5200f240e51014820ad9131001c000801035000441c0101d40300d11110240c00002c0c1c2c00d44140142c51615100202c1018201660418500181e440302001400c1c000c0c000503003081c681060f981800180d041403030368003080c468500001100c00180c5020421396440342442031a00c1d502c28103161102d81d61039801011000300303008c10707131182000e0715010841c00d005225010f0039016203480c2d8949110700d0445103c094004a03402d40c144141403844404900050004000b02c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 654506402 1250 654505152 654505183
    0x8030304143310060207092004090e0f010902010518040b03060a060f060e0a0b070f080304081b010b030607110a0c0b1201050d0308060616020d06091104140105061b 72
    0x20b0350385a490000211000b5003d034551800c2007805100c510703408100f04007503405419000c501990b12031802d4010301d4003030000112151000c01d0210309281d0f5600702a01c001b03291001c4500c6031a0711010075080340e600d140024080762040004100c0c40049040280c280040144002403010383e20006c20f0500030111219041320f55030329403d010400510b411400075044501c2c2c030310410706088001c504c4400180c00b03800400d4601180300740030402000b9038510110b50009905440c0d0806240074011508171058200c903903a4201600c440541c01440380704030002d8000e0050040c1e841d003001c10759040c206171044102c140100030204011444140d0501d008141d8858050769801480800404103103040e0031852103405a4401c40010aa120b2892a00114110380a65484501c1e40d9910500006580b0003074001c42d000d540300781800f0a55000c109020702403403a07812141340481c2000101d55018114000f000b0b441c00061115040107005010291790380304000c02182c19074981c40703140500080d200482c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 654507652 1250 654506402 654506473
    0x1e03050d0206091b0d1b180207060c08060105070605070306080307050604050c18070f12090b090c091b090409081902071203090e090a06060f0914010803030414 70
    0x516101000110440d1044000500d1071640440000e032041752890320107040c40318500c441d81032001c09921440001c12008158460710742e0440e41e11030280d040a48280d07003140ca00740398100b046008925052085405075907007841c11401e07590f000b0007030001a15440800d41d5642000c501040208020300c610703406000144071915052902c503240040c11202c00f0700a11000b0303201d135030308041c846080f5004042c2e030510040090940308200c41c2d2640082c0c0c44405036013009401070500000c041d045001d80461400e5851822411081c0200e50344140c0d141d04031001e070544070520440c144005040c1c04d81000300007003103c00391521920340320381000902c000441c418001d00f048254042007820014249850705003545103a40e1006000030703042e0b101c0c204030051f0340400299412024000c24003d40d070700c07600070003455850b801c1c481d03040e4a080c0203807546a80f40c451400c1c078200b81050294101d406850081d8a5a5203d0741d45007601c0300ea400082c140d40c420203640c4010102c212210021407041180440d8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 654508902 1250 654507652 654507661
    0x70314190e01050c04140f01020d050d110a0504090b0d02280e011d01060305090c01030c3b040e0c0114040801050403050711090603210708030901240608011e03050d0206 74
    0x405400451b50600c900090380c842492641c000c102e042071500f10341061600c9044600c40000a040703174440b5120004000160003c1464108010f4003e481180030104117851aa8040c030030000000c00000e5400382103151601c03100300c03454040411422a180c981903c0964412a00400c0b0201b0303007103020507a21410742801003000007003170340d0f00401080c40c0501c80c904103100000e807a0301c0d0003a5074904064551115003034a5000300c8140040c00c164840c80e100000c80b15201700d43c0c001c40108805003841003c18038a03082e143c140034480001100700050300c21071100e0030064441008500b0006d080e0101403000160045003031041d54895402a102d066844d02c5034604a50350b0b40300c04003224030841c4001c040c02034980300002c440d09480111304440e401c2c0440b02005032841e00070b0803002090f0305400801c00600c51019040754481c58001c40f8060780c2e1700f02204041902a0982c024a0000745000c4010804144071010300e0b000070407080780c140f0b5819102d85030242413090340754070f00c00580d02110602 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 654510152 1250 654508902 654508919
    0x11060c2a09091207020402030a1b0c02090117030d0f11070f03020c0d11010c02040209040c0c0b01050108010b030c030402040b0901090b0a1a34140105070314190e01050c04 75
    0x50b6000c81d40001a020b1030411002101290007401c2d4080d006650100000704a450b295100c0d14112650348064404003a0f00b40000301030b0401180100e00a160340d100002ea42540412603250840e890740c003030342c01c1c4514500e03010001c2c500c803400c0217081500c0d0045600c0392551000107081c0a07018034002007200340d81d41030182c42c0c1040c94040d41e01880d14000d829022402000704e0100b40182460100304070101800081c0181c00f031200640d038814500041c1e1805d580e004080000c541d40302d0101c04030160fa0312001034030544824400c102003076008000143d443c80000c0025580b01740b00410005528000d08081460004241c11400080c1d548200c0703012107140910141c00142010051210709540414411585008138001503240340c40360700c0c019041100780b10800049c0c000700140401184294108000d44251400c0d80309015480c04c00032034500792003170007100c425078422102d0341c509403074040a030200c0c4242c001110746407645e144c180d11100c45003801480d0050815602d115240c1d030804110 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 654511402 1250 654510152 654510169
    0x120a0215070318050d080703020c0603100501080f0606041a040e041109060f1c08210117060112030e0d0b070503101e0b0912120a0e040911060c2a 64
    0xb4014244000c89003000380d03170f850242c0842c038664844a0740b03407148030f2480c081c1d20301031071b01035510383c000008000c0000345003114400b02c00715a400d90f240140c64a0303a8407514103082042e5013183e0400c0003000180101c0030b03109442d0304082c2d00d0b04e40c075502e419a075143d410744148007903a00f2134150400c501014a50320301212400e402c518126002e195160520001a07041010140400540c845000e03030742003404648010f48031003400d031402c0c45152250300840004040000d006a0314401005036420462100014080341640e042c0d00310300301498000d0b01d0a4030303420058002e140d4440404100c0c1c2c0300103000c01c5d10340d90050f00c1a8554a4483c10300c140341034031038880707904017000040ca9000d5070001064159000d40c1105c8040e031005941d60141008074440c0110340d1a100110701c070300c207400c1d20501000070081c1081c2069986401a101042d41000f080d03c01c60300d80130b410480d038180c0310350720b82c03400900030610b40326020300319048ca03401500d4503110702e40d10615880d07038684070720911400c0f420300000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 654512652 1250 654511402 654511427
    0x1407080604030c02040b19090506010e0301020d050106200d03090f060c0c050d03110f0f070507030b1005100f0f030b030d080a0e1507030c02191401061403030702120a02150703 77
    0x803c3c04102c0701101f482d800307680c40ca00c10303d10f4680d110320200703102d40d008a5840d030384528094000d543d10031102c0c0c08680500303030a106031000600e0240c0c8880c00790036000d1f142c0c5170242e0900b02424140880040850190240e400240e0b80d01c540d07042d400d80014440d2154080520b05622855500e4680c2d080c41c030f04040704994810700340b60802a844820f0044c0800300c611000e080301e000d40d2201d070f0003100c00302e49004010004200c0d22480d42e0120a2048543c0020700c6005403d031200e41503a200d00a00c204280d80c0110741000c0361541e595110158060546001800b50515002071100700500001e0719004402314200e0100d9404c40901000d410180520f030080b0441030000c0002c0300c10704446403803c1400914407010160390b65040392040e4401d002401218804520300e2050f52a6403c0c40703800f84490500d0702c2c407503610388140002c140305d00c10841d4222000042c080c608010103902401242c050002c2c441c8040e00961884500690354074862400307241052032141e44400b9189000b07091100c101c107 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 654513902 1250 654512652 654512659
    0x61e06120309080f0a03030905030702090108060108060901150605161e0204050c0406140307140f0a1d0108070309050703050a06151436010810110403020901031407080604030c02040b 80
    0x2e0140300b84c0d002405884055061400095040341410031500798003d841000b58405c0e00c240001583c8140010102d069aa501e400d07200700b40c80e0300b240e007801c8a040c590000110740c5060790401640d4011009011000d00c036542032400c00100f07656000e040f402005440612051080040040d401c05218450748003045400310740c505814424060329042c6d080e040614942070000001e9505440b540408a6404c114a503554841480d1117a010f0650095136114000a0f82c103c0c17201000700c840c50006c3c5c5500ea042c0c488180545030210120040e02581109840d281f1481e000000014020071508040c03501449000400d003a043c05c40301100000c40e40481d51820f450031051207641d0301c89e0501d20110540148144e0300000f4070103440f492460070b4a465005a813850000114001c02060013515440d03d00402c0008106c8030340250000e0003607000c081e400075141001800020401a0500c624a0000c07040391409561034040b17038605001200c007100025803c1500c1021400d00d4000c000940c64202c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 654515152 1250 654513902 654513913
    0x12060108210915070c030f1403130915030804030506100e0702060703052508101502070b0702011404030f06051e160e0612180d0c061e0612030908 64
    0x45140480d58002c0c29101e620814405200d0a22900314900301c8604a074440d21101302c4d10b81da42801c0000c4290300e1300503030304c1c08605041c80d28108004000c070341030164545111040300c0c0c2440d410000500400840003004501e0bc1c01c040007060505010f0303c01944144018513051605240484644a80342c4c0714010b00350503241444403854004c140d041d03201e00149800201c990f2801500c4c20b80380e5200030b21000c000030101500440a40c4145141e100703d180203022001c0300d079034140e10003010060608070401600120820b200700c8a05200030444940140760035140e40d2031a080141c1a81e115605c11a02060306c88014020003440e8010750f03500c1016510100c41c0390690b008054140140241420120b02886980f40350250003030302581255074010b0030490305c40c484083c0d0303400015000e8624103010301c410381030b503022400d0025001880d010140e45540305008541d0b28103000e400c000c00c0ba888a40c142c440303400031582caa446280c0040400340154140340840d4103029103118901e0b08403c442c0c1c0c120 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 654516402 1250 654515152 654515203
    0x603060806041b050603040b251b0204060b120405101a01031d0d260105061207020304180f0509060601050f0c070302030d020102270a06110a0212060108 67
    0x228a030781d40180c100540600c000404402c0e403185604507000f09a1002000c0f06103c284034140214a116801d004561851003121080740340070700c40c2c90690040041c1220351400341c0601c04034002d0949500c041c201142d0306803540f200c1030040d0009800d80c024946550100b205210b010403052a500d550248100103c280c0c2416545c80b408a080045041c10344820300c0c1100740c41750003001056011004140d0341c0c045060a0000c0114012400d01302071403105140c00700010f00c0101083e4100c520081105250082c000c1c440d010f408001490320082d800103010005100c40c0781407207940c01000c09140011000020541081101c0f07002d4071242d0580d0004003002280d981003000c607042c0c40d20000707101d0f4503041c6900d4004d2800051340c00094060140b1180518419015009010041b07608108450140d03503440b103640c0030425180701e035070740582565400c12842c0e01900080c003904500c41d0a03581c000e01070f6000315100c44220502d0000b140e02000042224160a200c2441c25561119485900080 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 654517652 1250 654516402 654516419
    0x50304091e140105220e0c2b02010c030203040905010608041217060f13061403010b060c03030f071b030c0b010503070303090b2d0304120c0803040b04140f0c0307060306 74
    0x405004141c01580360214465078650843d540c04001d10381e80b031080c08510810120151501f1341c5684550003903011080c80d02d0400082003d21005104c0618001040c00c401c0d0011114540211426020360004105c003003040c665074005d040c040d200a441e0351846041ca0710b855450400c1c000030340d80030440d480303015400800b10060281d402400031110b00d0015503121000940ca60043c40a407110300f0700c0c003880060702c800b403a02c07012000c0d6421402088110514828021030b84030b612800f0074203030002c00000b03052000d40003441d60085001e10303141460100b03d08003112100c003c002d082e00425025189882003080083d101750241c2016006406460710315500038007084a01d0248522030480840c00c24025401040d03184050340000d400c0341800b001c8903000301110791050304d058600080016903680500e028450900419a015985d00e00d559038603100c40c01d4030500540129980d8114800741410001d080110303001003419035000d02092282c103c00c040c03514030710368001020301d400d040e020000680e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 654518902 1250 654517652 654517691
    0x206060d151e0605030a0f0b0901020409020f07110f010504030f1a16020f01050601080420090a0e07080d02120a030b1302030105031e1b0d050304091e 66
    0x410a031201440216503290141c00341030740394030010340d061801c0c42c07241c510300c0030002030030307004031007000810440b501c030300500d9218502c1c00f10241c4084000c588100019881d8001c0540c085602c40c001402c1c15140c2c01c0c4001079a00c0520007003d0301c4404640c82007405000b60480442e568101e94843e60300c8070b0440082c04034096032101610019031b8804150601c01c1200c1c5e5001c6011441c0c4007500289001801103a6000803502c140b4014032841e03458030114901481420b02401058403200d480790f85580d29240c4c105402030451700c1c14400c00400c042030383c403201803d501860300d1b14001709020501621030b41c50122154880303e403070340c8001074070440682c021503100c803110602442c40b035075400c5070700040c0d000d841d41395845078119555000905449000b40d0156059520031010b49888280300c168019142986070104080390b003080c58280c3c655812a01420324400020b0701e020130aa409480d40c81c1141c0055228130300092b1205004c01100314580540c100c90302c400300b030403c0345444c184a200140e4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 654520152 1250 654518902 654518911
    0x120a080301060e090a0e0c0d03180f08060f0c04031212060639120908070803041d16030507090e04050c03011d0a020409230106050406090204030f1104091b0e0f04030206 74
    0x7601c1201644040c98418180b43c02d121107000002d4442b1a9170b52141540d45071544151030207401194041008640e660030030310700481c49400030504250a42c0c450580002d080c2105030184910340f0180008074089001e440f00419164407256509040d41758108100c04000c0d4402489200114980b180820701010781030541d604180441b0482e288114184c4880000b5008402588259a800258240000010302c140c0b440359440d800490200141400320210503143d05426615840710030400c0e6210b0781c41642c2c026405d103800c0300d1040e602c0c05170310310240c0d00f40c0302520150040c034000d801909007400742c0c0d9000000c9141d030210800e0000802d0703403110401a8000c3c480c035140e0034282c1c140550807044040b550000340320140d144000303002060003000c0c203119140c00340c4c3c10090005502d1360031780b0036241281c0d04240c0340301c4c0460241d40c0e94408080c3c00e02c1c4680d4041d6035816114041029010081c0307403a10901000692035081c0342020004d584024080c0345902d014004000c00aa4040350280c3c22 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 654521402 1250 654520152 654520159
    0xb10050913180f0506092a01230703030f0b1c060e0c090f0402042d0e0715081b130e06011218030801090515120a080301060e090a0e0c 59
    0x1800800e003002d4003078a00c81000604805501c0b102d1a06100c00420f000d4000c4c05488100d94000140268600f00f16081c600a0480300e000c104084066500444801c09034084848440c2c0d90407070025025a0540c00040050380069501c45503081151450301c00c0620103481202c1c1904e40a105585800780fa007860030008001a0b1240e00b000044d9100300100c11503ea001042000245800007901e210380038100e0341030784140e04000303402c003014003c800d1020340c051a00005140b1800c0300400d48014190070041c00182d031082c003d0000e0341409d00d542600614149549440c040c0c01c00554400002d8900e40070030400380001c1250310b06501d0f901108404842108030000d941d0b6980c0340c0141c4409605210a101c1e0074103014900840d02c8444a41c004498802e44488031580d1300d40c805a000c0710300444020307041807800c42144d00785140c00060b05045007002c5c1c0071114201010b40d0703143c1058000b0391251011406030004418203160101901360301090310b081c01c214000715401116594210308800501 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 654522652 1250 654521402 654521411
    0x20909010513140f160801031e050a0b040309030b1b041a1b0c13020906030a180503040609060305090d0e130f0221091c0e04020408100b10050913 64
    0x80982d80c2c2c00880c00c01c0303820014481545440c520340d0b038071650102c40d00c45480400315010b0541074007446c0070300d05803030b00820640031100030a0035030325130305d09201c03001c5d41d41d4402d4000c00310000d0b034500f003414440c920aa031014100f0b03146240a41c901c140c00703400c01c1d20f001d626038511180c01d03003014291001c40da0300701c0401c01021082c1c0f80d84140d40c0301d20b41a0416105084103007590300d200c00110aa01c541e015a50b2541940803c402c840882c05107010081d808041080032038248405034011f0b0803c1500261400790720440c0760f9403203240da03200d035103ca00440c004a4007086203030707014807075603500c02c01c00c2001d004420301c6900020144a150100d03203100b60402140381c4802d1565510000d00003a8815003150741d00c0410036403110101600e80e8001400c8400000a0202070020600011980c81c103c0d40d40d40c2c0007031095040d12260702c02040507400644c28000006c45203000c100180402d020a140002d1030110f61f0107000c0030f04d200244c45418040104480c064649034540031071003600d0f0310350740043c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 654523902 1250 654522652 654522679
    0x70b060a1215110705010b030d03090b1906080f07301202011506030e070b040803041202041e0c0e040203161b050601030c09150b0d1505120309040f0209090105 70
    0x40007850f801d41601140356001c5040f10800c201503210800c1c541c1c04804036400b0b1510440100c0c140c0b04643c40c0100b0b20364100d00828076070711020001841d090b105a501060039521034101030b2070080b000380005050340c4212000c2041901031011141c1e50f45107111840d03070150741182d40114100414400602d41442103039000b907818402c4d4454050310304042904d4201d203a507100e00401a00142502440da4014070f130002a5030810795044400b201c40380c5010314109840c0003000200400c001e0800d0760059100d0358402c003181508609a6400144441f0010321001c000000030680500881d030300b80114410820700c00108081d40000c1d845111038a45044a400c5140c80241000040c90300149184031341f40000c000c10514110341002d4500c0840304020840311040f85c1019a0700030f200742d840d84103080000c1c68016080d038008401c3c4d0360500440303a440c10307980c00114201000c00c1c0301c03464550b0408110260a40f40a0090310711041050406605002450b00040c2e13074082d0611945c2c1c40340c1c00313480e42d20 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 654525152 1250 654523902 654523943
    0x1517061611120d0906050f0709060c1b0e0114040507050d18050d0e0108090114010506090d1202030c010f0905151f0b04060306090c0e0f060706090503070b060a12 71
    0xc040020345040b0701e50f1500c1401d42800050041e00074111151403d0000046140f0440411079105540581e51060f20514116041d10082d088000540b000e850800d45485080d262222110091580d1440148298541082c10040341d10a45005201d10304240620040701e030b2003001c0c0c40111003055000110700018184c081041940b100c00105280502d0056280c6160031101d5440000420307200c5c06032030703501d40c0c00680c05c0780d0700e200c032000402c103600c0c0c018041c0c1d0901d070018001da40400342000d5200340302500e0780c40c03266081050741e40c0140d01c00180d031a00e0300300030700071000c0e034024105091041078055580d075030316500b084086008500c3d09000150031303030009003214400d0b803400d45004034419032140d181d05600d511030f0050901007400d0081c00904111107115448024210b5030350002d46d1803c00381000407800d03104070041d5000c0000e02c289804100700b80310b03c80c01c0e2441030b0000c540d6a070241c503081d990b03058002c2040c0d20030001018204400a41c000304162903580c000c444501c55628520403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 654526402 1250 654525152 654525163
    0x1170601021911121f0f0617010c030b0607020303071502070212010c14031510050d06090f051609060305040206120103230607050d02070204020c011517061611 70
    0xc9032405031601c07900034103026080c81d401d50078020641310f110740c00c1c4103410b0095407081c107036204100307400c41d031010a10348140660061b400b5030400a004150643e469145080c11804484684400d0b55600108000580c01d403107440c1c1810400d550b014200642900002d07201d00401e04060300003c3d042c002d981100e0340c0c660455010b9075000700140740f00710641d98101d000701402c3e0f11107004a5880ea10b010416442d120070340f2f1007130441c041c505a00c1400001801880000a280d240a100c800c1c00360f1441d650341405050003804000300001000d445100300f202c165480604910702c1122a0382c0c072000000d174001d11041c00d0700c02c1420041a46d4503a0720100f09039108078000050341460180c0080b04010340f90700f100000ca004800c5010349904081c0505442e800c003501e842c0c002c00c4080200c3d00640c0107540140c4900e45c00140010b0400d844081c446094806900184c0d000b4a04903e0074003a48545c441c84201034914040209518940311026020746801c00b00c00400740183e0608201034003804108 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 654527652 1250 654526402 654526423
    0x20904121e2003070f080a1b120e12060a0b03100209010203040e1003120504060807030c0e12071a030403110606010e0402031807140406050906090703020a0908010c170a0b0117060102 80
    0x1002507051561300700381045410018455001403030020100c00000b00101c0d5000806800c480c502d40e039099101c0041e100e00c40c3c075080b159008185000642f001104c1402602d22443c02c041000c42c0d4800804101824500003170304002015205000c0078001d44d0380001640c040d600b00110341a0141c45a01c1d88a80d410101e900003040107019480842c0c040c1d40c01b00180080302c00364bc076409010380342c0c80019405d643c0c124603c500000c0707c15034400480c0c5048041c1c8001c09071103e041e40c20064813040035401020504851301d1501c1400018001016445140704194840d80400303048a0b00b0715000003001002598121071155802001181c040960039120030f551407040ca0407602600d9452005c14020001c001e22a03204a103001070001e1141021845103205a000070050303412580e0340c010980c0250460100c007001c22103030300c4012941e480c4c01d01c40d540940d0070507101d1a001e42404090740d884940018136000e50b0034240b00141e150ba980042100141141c0d103068220b16903aa400102d2800e0030114 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 654528902 1250 654527652 654527663
    0x4091d0d030902010311072f090f060102070602060906010521010c030c080112030e0907050412051006090606020c010f1e0e1e030307080313020904121e200307 70
    0x20314900000d4055000034403440c800e807000d00c543d1444200500b0a4003980c00c000d0040301d50300901510307032420480e00f0506041e4404030031541d02d01d98004a100080111030b14020b0020070b409116980d83c04002c03803001844030f440105020b1400d800429101c41062280134096015640b11914084c2010003042d00d00c0084c400800c42d250703080b90000c0241c217460050901084100c4008500365014603211640070f50140c40ea001c0c41c0082380144510110010721500811005020205412070041c08050003035000d0300040c104200451100d00c1150a0baa0103000b5952501c0420403102d030300452000d03600d200908014040c40c014603400c4e501c40e6113461110700030549001900014a42200750302e009a0303002c0c2c132030f000035254585500900307055100784680e26600c18020180041d2140300150b17803200e5400d41c035014040d91540800c0d120141a1000c0b59444513112444800540c01924840c520800d8040030b1402110140060481265803810039603603141050800c0a01c441007080780c40c03130396000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 654530152 1250 654528902 654528913
    0x20a0f0f092412020a1d06070206030c12100e360d0e0a03080421020301090303050702190804060f0302040b03132913050c0915040b0303030c04091d 65
    0xc1030b5808058200725480c0d0040342c480d088188800025100340c41c80900355480b030003480c000c1d010814101c072115038249580f000081004500503200c07640554081d400f014102e540752a600ca6500c041500c0042028030344c1c2d80c0b03049040268240201d0090b130800c400206809142254071a00c500c4203004001d44100c0f00a284003000410b0f0002801c58000134481c0e403924400a220b0b020403803e0709403884040d210540503c028050904a285c16099082e010b09044000481e640d01103030a4508517401a0f020964600c104000180c0512401203166080043c004e592811a510307203034140528010031041001c0c2c281d502c0307103a6000b43d04035030240401250450701c078903040003402d0201000010072104602c144d2421b55841100300b001e2070400040704c5c080182c07584c4259107004040d2942c2400d44e854458025524450744818401d1401500b260010038101d505c00c0c0c1c10311054548220318540250b0040080110f203246650644003581d070006800700f00100c081c80c3d6540e46920b02c032016401030240 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 654531402 1250 654530152 654530189
    0x60e091b031504111009051002121b070e090606010914030714040603050f060103052808070c03020423070504050f09130503030a0c0806040b0d0b040312060306060f0504020a0f0f09 79
    0x841d403c07c4407811100c06d00c6124052404030b1700c4002c16105040c1c0502c0c140990541300f207070400030070000354a4400729030380c41c1c0e5103030507151444e030003a034409001c0d0b04594180900b55900c1517101c4050800c0000e45000590414080303543c50700240b10f0b514108210300c400715810750320394001c04001c40d0000c0845090314003180b4169285d003400e03c17080303030140714806a40c4c5289600d049002106100c2031581c8512041c10f84490310b181d4810030082362509600703400800182d86078820a1241d82c0d0412080ca190150f0704c8a4150402c405040401444014842007002d555411003501130100b0660350340089071161580e1112011122000600c14000482003004001c1c1c03a52040d070b6103055070350700c40005440e8807003480300700c90301c1030802900020072805e40404561000c40c2190401c0c407034681404034102d000e07454800c8481c141c00032940d854a64008100034807408161a0203890300b250304514003a610782002c0d089041c00d03604513040c008690602c09600c0d0150007910700400d00b401c0d949110540 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 654532652 1250 654531402 654531407
    0x906040801270b0c0901031103011e0611120f0906030c0c010b0109060c02120c1011060109060f1806050418050f06101710060e091b0315041110 63
    0x545641d45050b0b11460115114414000101241c1c20440801403601c0704040413580781d00441d091414140c440055107d4114000c008500a0a45104040440c07003241c0f07502004460690018041100c50440c1340c0640c0000710b00d85102e040907000039035541e2000808060a4098604c0c2075911041c08020040c40440c41c0b0005c00003da500c0008011001142d401920b00004501072100000c0150865000500301055150580c001c4c01045400e01440040005d07458290340d02c14400040e9120b60024070030340100001c0d030240c025414148400c604006056940140610072188000d00412710a00c0c80c1c0c00581c010781c05004003038424030034000c00c0e02a0300e1065012603c00c03115803003460038110800c4004103210b0700409482c400018154070706008400386082882c0703038003580d02503405048003e015900c18440140303811f04812400e45004075000742024140002c1075611030302d0062041c2c081c1d034042900ca030034101042e5007408640300c070f050038603500000d004100c0d0410000ca142440480c1c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 654533902 1250 654532652 654532661
    0x70b07021203040602240c0301060f0c0212070614040b030a0b1201050408070c060c021e03070506030f0106020c1e04090602040b1c0c0c0f17071b060305280f020906040801 75
    0x16441121b10380c01c2c1040e0130440f240070702d08603405490000f0a00060090740c0c4150020b480d062201e00c0c14000c084444d40000e56850369a0072200581e40c442403042003042c4d0041c045201e4446e04100a6090034500341680000d0f1200600c83e5921079690348010016981d4503a0882c066100500204602e1620386011201544510000c1d0740ca180da050000821078070448841c0900c1e03a0103050000141d0705060500040804826401e80c540120040810345848110245208806102c1c00050a5240001c085e05105511728030b04c0c020824282e0342c9003002d2039103d4080b1461001d07a8002108040e50510300024080c0d608544c4c81c800000504c0030701d030403960070800410302080c4030030000c41d0300c0210150b0b020744003540005d100001d00b22102d40854101c8202c92650b04040404501d8440300f0b6481d1460881da03041c160064401c0c0000030b201059040c41081c1e880802c1c103e400d000c801100950030108400e110344e5061403034840b42880c00c894003c1c4c060350355448002e40943d440e00d850b84c00c0d03035002c2c2 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 654535152 1250 654533902 654533923
    0x161421040911090d030e04110703021506010e01021c02030f22060f172d090d0801030b0f1b0c0f28031d030312180f070b07021203040602 60
    0x141c0c00d140202c0d110344012002c540c00c4200050010042d01090343e01502d0542c80c44400e141c0c40ba030350f826401c1c4013110001c01411401d10036409440c02078509030145c008220060324650401001903d0448180d800003501e01d2228160000c8a11030005040c2c100c0c07561223078406007410900d0205032140d8407003440b00100d600041511041d0849904c524003120b00c1141000c0300c1000502401401211555800c603d98210803000d10b5a020300300c4e84001c4405c142c0f010300e0f454282c6001c0f0410440d05013010700c584880c0c0081d500c0c100745154955222034504070805400b401e80890380d000403c0c164014800e140d062050304910440c0c4454405048507100c7e0f030303009049500e60103195070003c43d0804c0b19801d07048020303800390b80c2842102c45480c102d8480da401007685002814800351450301e0343d400c201801030000a643e403250180f401d00c80c07141002002f401c11296550203841584141d00d40850400140e460460023151242114000a02010804405400b59000c0042e0100d0082d44c0840d40206a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 654536402 1250 654535152 654535169
    0xc081b0102100c02030f0906130f05120f060f060102150403030203100501030506030a03030b01140c010506010f08040b07080c0f1b0601120c120f060e0c130216142104 73
    0x2d40a210b56440c054881000d004001a0010000800500209005070a0000300600750906008480245a072050342d26081002d0300307960342900700005e26011a8580d094416074001d440301401101c00a0f0f65030f42e01034006120070b2142800901e141e4801c00c032801099041c01c0c81c01920341050304024000754406d03101d4280c0e45582080100f03440d402405158040c02019004001804039510100e0040c03131030104a60403c840d81420210003c01c1c54041d00040100700c00007d11418958009010448403241000a000c494070412003c1800004000e07032043c0d050800a1940e40ca02020545921a60708605443e001c08522182c155002d8900349121100b50130031070750981d0b21b5540e141d150003500b400c010000ca01c28901400000c500b0003608200d1882800c448a40d08444e40e540c20503a640c843c07100c49030354041140e204841c42c240980c450100304510046252281114002d05140e501d004094540b17114082c10180901c41042000c0b10b140100c88649080800b054005209902c03170f2086084 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 654537652 1250 654536402 654536413
    0x6031302120c0109181b12180b130302070503010c020a0b0903031303050f040902180a0915050d0203120a09060905010f050d091119050a0e01050603130c081b0102 71
    0x4001c0300003144490414140c4496988901e003500f250b42a030210403550041d25264000103184244000c41c0a8001400d078640200301c00c14a0701c44411036038880c0303e041d0680203c111440200d000c00310302076080556240d03109608065800c0c06c0c0d141c4038550380031030b40561038001680c08242e401302c0c4107110140701c0e0b02e540605407a003100b039aa407800142c2e105801c03502004172440020780100c00400c120822000200d0400d6a9107904004a8000d58502d110313910001c00e455440e461310450200251940c144208101d11b50807503981d008040c23030700500340a0f0703a048400c0b4080d0f5904021000c0300040c6609401d075a0030000030f0040c000c90f11886018040b034039419000c074056009003442d568046460380c403e401c0c45c500c80302000c05407203290310580704000c0c8540031a400e07854410188038200100d00030442c126280c038043c8126a0000d0780070017903126205005004d6903807074004982d00102440ba04a0030580d05e81403840c1042e00541c08090700b840383d8201110460100000400d4040d0240c09446 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 654538902 1250 654537652 654537679
    0x3020901050931020310050a0b010201060f1406040504090602090909010c02030a080c070606080610080a080304061e060f0e0c0a080c0f071a0603120c07060e040b06031302 75
    0x2491074816142ca80700004403c2001d8011141e6403140041c41903908492002c000c19a000b20342400421a14030080039111420400c1c4032039107001d62500e896082c0b00800c240c520b0114412090030705402400c4001e03a034158014260fa50720810740d03001c0c21001f441085182080d02c2c091000794020344500c0d000310318650000399500810300c240014031815030040e5180c4442c02408603209a00144240d203d40310070306c4060003148043c4103180143c801080140241d0030100e4600020341d02c642e10075406540308a0801001403080000d403600700d5407000c1d000c100c2800711404ca0040358280090110714a181200c001000360490581408991090082c000140c0380c40101a046100710030001c00458030032404a540c0210300001030a41140e00c00c58541424016615000c1c800000c9810b401c8815907202444201e00c0c080c415100c009c0350104d11740c0d00c1c01d46d094032401d840f410701d4441d00080c000c091105401c541c0b920f0300101c0e907400c8000c0490303581e8500703415400c015040c064010b034005c501300c5504a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 654540152 1250 654538902 654538909
    0x6050c03010308120a09081606060522020f19020c010f050c03030615190903140303010815060f06030106120608031e0c150c0301092301030f0f0503130302090105 71
    0x1241030303e0f04520860300e850780340410310032040b40144c0400c2119945540101c0800c2000c0701a01e40c504a0141c8654003000500304101a500c8940001b4466103205000e00c5001c5200341a10802c015407060243e22032000c03011003040e40c01816030b00d941c60100034030510091503000c610809030b003078240c0381c03510f1111200c00c00b11071600030316080c05001d901c00c2000c5221817034817600c0102d01c1c4202ca0b012a203080c5030074070f5454014168004078801708182000610400040b150750101c3c3d03481d07040085085602d040340099560612004c0100d01d14203240c0425815291032161f4406054003a001c3c1b0f5036941c1d10040140082080130011034034600e0807401080000e030110803124805d21007000f800010306002107103040341d489010180c81c0c0c0d1240d5180d1a224088060300035100c0d04a01d9120703600c0b50b16020900050b9a00d0041c2050042c45004036120031101b1661319074103503608140e0303024007400246020082491303640c2002e0421300c408281d0b01c91080c03141c1c1020f002da0b413082c0e900082a0340c0e01e0003403 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 654541402 1250 654540152 654540157
    0x118080d050c0f0703080a06170a0506090a0203031e0d0501061d030c0306061302070606060906080c0c0a030c0807050610180603020d0f0515070818060603061f05120102040306050c 79
    0x69460759104024042c04a4400c4c42121f80202091400054a0b50b507540d10000b6500c60280b45006038101580600c10300c203003480702e541d000503c00051300e0b020110380e0009450b8441c6164004086160032000020410700c0030a0b18215500604100544d50711410040c14048113120510b10384036501000e070440c0d0038045400400c10001400070001a150f0508111180400c0d01050401990030300180c0e01003400343c002c46c4020841625002001420120000c24028005001c018a05810090441e050700001449030401d60545007a000c00c01d0603103000c071803074403941c4c4002d0160b100b604280401612200184d4040726050082c02000b00180c072004000d0f20054130000c0c0d48041e143c60701101040c0b82030240c400061041041d10f00410440310b26040c58103040d65410700040c061010488440c660314552052032511200506030303440e00720006540c6410050850340400b003001c03900846076076113204002c040c25006002c1c0221040002d58603000b90081d200a4a080307080c04081941c03d07045030308 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 654542652 1250 654541402 654541417
    0x2709011512050a0e010f090203010b0108010f0311061204110906180a090206040b0a1d04183c1211030f070309120b060f0609011b02030118080d050c 65
    0x407220312010218116400a0000401508002d42c480400a1443c01d082c407a406181e048084001039a60440c01458211080400c690381030014800c014083d6200c001c0b150421607a120b00a1850305425801244540c000c2101d145158131424040c003041222010081516483c15038840101b90380d08001c00010000c0040c070904066901808122109410f40000b0034050000e04001d00d41503940403881101c0d8884140480054003a03580644158108200200300171030840d014000300c1005050a041d80f004e031240100303420752001c0099038024038000821100c4000620042d045018449100001c2c00566021180d403135a038211420b030780d40207106c1c41ca19a00c82c0e5004500700064003040107080d91100300203505000c41b4810024101c0080700000741000d200b00e07aa02110f040c06424004a015812071080c4100ca0920110304c0c5660b02c5510000c1703424590000224001311800441d0040c03100d40302481e0200c041c201d0350814001c004c00109100c0740304000400080d52003404240d4240140903 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 654543902 1250 654542652 654542657
    0x2030a1b0f0504060e03070806070206070f0c2a082d07060f08090f07090902030d170601051b01020315130608030904021c0606020d03240b0c0327090115 67
    0x8418418148540c8030380e4407001020b01181c7e402d984403110a8546042200e694006038403910400048a601040a01c0c04031014149000d02c4815940c401134815440e02601106440070f10302604260300003022340700141780c2007050318104902c2c00a05060800c50b80c003030004207201d40b41d50003141880040d1070f80440380c442d5074456108805080c00c0380c030000040c010840a2184001200610600703200b02c0d40100b040e0700c40003e540e01d6510516042200b10700c5054284490340401025540b000c2810560140092820030b98902003500c101140624070750001e1039561000c02041030400320448001e041000443e16419801ca1801d07005040d5642c50140d0480d079041400850451300b055006020441400741501c02080b0400c40034100b02c4541e42e1082005900c40c0000c0c1040750303003502c1040400341d5010303081e8481c1c403000c0d00c0002c0c1c1003801c1d201e100383c1445d00088c03e1000490a1094640003101c80071180c0311450050100e10918090488080c8194030090002500f5081c4442c6c030341103d450b58 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 654545152 1250 654543902 654543907
    0x10140904060203091006081f090c1502010e0109050114010b03010b0906030703020421021908061609151e0306051003050901150905040c0503061b0a020c0402030a1b0f05 74
    0xa0307495201075080a010700c00d80c1e2007018096814061140070340740290181d80001d00800070004254490040e02035464440c040c6007200c2c601c041515003000805844040c4030008900d104600b00301d006040b080320034806940390420b098200310f4103411142c0050500d148501d242d03602c41084005512081c4038800c0240c8007009020070909180b00a1079010780141801030810799a00c2140410020054400c0760710b420280c440030452601020307a0101014041d002c40e000d50078840d00315a1040c01409601c01e01c0d40108618076028401c034468009451200c103191088a2031030406401e4403a5515400711150070007000d00c9815110f4443c0b082205c500a090244003e0181e20950040070041c104518654881075940181c41c64140014001d00750303070a0000d024600303030900360001882900701511a410900a2103062640080c10441003c00048103903a170301c207000d905078035080c8400e90140c1c002d4004020450411a10f9001d407441400c0c0e58801c1000e200f40000031036100059804110101d04107 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 654546402 1250 654545152 654545161
    0x15050105030c030714010c080304060b0301050f01060f1202040b0a0807020c04150506130f0b0a12050708010605030a060905040c05010e0102070e360105071b0b1504091208101409 78
    0x5c46095500ca9010304004032540e0840e1140070550f402220261a03042d181c021141090509114039079208044003500d80055060440050002d041180000d0420580703848003c40d2000d6135045070000e082882c1c4c0c09075600360788240034107050422500d43c80540030341c00500071542024000c880290074a21002071a1604041c204003554025405a104251240c480403030200021402c2c03401070704540c0300c7c03291510031400009181d4844e061a51820500308004e2242140d0403110960546007941407954036942ca030741c0103138024149a44456116030600d001e0109001c0720b08800800c0c3c4030207a84a0100d81c80c08801aa5078013500d1140040c83c40300d440010784c00092071200c0020566212401c44400d0402c004840c410100800c81c481280c0d41d244203204c0780c1500614034080550880030450f03682c00841e200c494034540020842c00000c0d09035400070a2070f96840d4000318015512040c401c40011582e08010041c0c0030844007014814a00d00022a182c400c030f001c04c0aa1990042518505070744 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 654547652 1250 654546402 654546419
    0x1113020d0213052103390304090614030303270124060815040b010306080303040624080a0303200304050a120212040911040f0b03071416020f150715050105030c0307 72
    0x1521b0051100c1c41e00d03c0e40e24020019603800b500c00f0148510096488500b4246100200c6403254000c404080103144050b40586000c0f00341c82c0d10021401c0f01103191041301e4000040701a070076810304d8240d4a080c0542024a0917000c40043c118203050180c0e1100307807581e00c1641c005609650b40103070740508a20306c00d5246425080300c0c1c2001c106241c08a989940d501c080303860340d08241c6040f40c2c440d031104503140e0051582c0c032144c1d08401755500013910803460b00a14079100c3c201c40c6000350405032152075500c040c030fa594034401e000d038180c4040c1954a180504240c0e450308c080342c000300d80100e5801012601e051002914a403019202c01002d0f241518201035503000701908100d0b41d12030b41040c0700000f0304100b104038600003040069049a52441c0140c0003c0c40603000188460484406008041090312240c141c2104a5030694070840119002000074495104503000d100d940103001940008200110440d88408149081c041c4040c3e4bc0314020152600c4289041d00d415a00ca0001000a0003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 654548902 1250 654547652 654547687
    0x206061002190201121104091812030905031e0c010c110705090a15080d0201062108030703110a02010c140430021e030c010c1113020d0213052103 64
    0x3c0c0305043c0394100507442c503d20001da0701245002c000c201300c04107081140e403016006880407124460081680108103958950076070004000034002c05548100000070072104100f140c40c04040c80c802641c070154203061080c02030b40540e004400e20750a00e50b9440f6114000c5060b1115800180041c01071642403800b40001164010035005c4400e4480c40800f01494180e803031180600403c001034660b0300003041c1e0190964030180d1003014840200d4142068800c00b8014a02103107612807101961390b140e50000f200131340300d079443c030603116803000941c494001d8055228000015094440030100015414241c066008511800780c60a41080c00000c0540c1a9106500400050b0146189260090f0046500889040c90303103100d04070ba11f60902018607042150308505002480c0a4800220340c1e42e61592040000d07070000d024003010082c0a1001340141c0503161a800100030842d1542d1807501d0045241d0410301ca2a1b01626842e442d032840405010318201c4c109031080001c0d0310f02000400c04072030f042d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 654550152 1250 654548902 654548953
    0x130302130506011e0909060e04030815090402040f0219033903050402150c0105010e06040219052508031e1005011805100914060a0903060b040603120c030206061002 72
    0x1300c45ca440204400450b480742101412401924030b14620f4103240107000d0b650042d0010380468581149078817296a0030310b84640c0594144c0300402c48481024040c0082c0c015a14140074406890380c03030248480e03040d0301004651030340d03d109449400702c1c1c0c8221f80c52100c00c80e41d4040162a070a05022a55000e0707000a03800070301c0070700004417061b841e07810340e440c5810008605043c0d94441004001122840c017503180c0080044404504c0c0ca4010090a40030001401040d014404081030080d500805035559800464501000d0424000a490401510b60046806241d00794600864aa2046540003258450b111181c407155125051800565003044c21301020306504040390008604c54891910002207001a9261014440d00f461081c8000c048000040e9000d403e00780010041503500000d888200c0c0d0b0005000500c800c0d514000c01c002e800740d901b025001c55411400600440d81c040d01c01c0510a0190707090b900e140d1183c6c0f00300b0241103501420140140d0041e513004420301240c005014a4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 654551402 1250 654550152 654550157
    0x6140a1b051b070b0309010f0b01211e0c0915080c120a0f09051c02121b01090501020a1706010806090c0a030b1309050c04150e1902130302130506011e 66
    0x1096a4022184a50748221000c0b02c5a235102c81142d25081c009029502030030b002400c1000c01c458403c80245403c0d24002c00326034009889200d151a810a0108800c03052103180d0700c1800303000440d890182c05000103104400c9030013816081802664441c69945004039400d4409600d40f46103840079272020500a04214180c0d80d80d003c0c401095207040c8200303480b0610402c05402e10300d1240000c60100e8883e400c01d402990440403912800040e05012550300461311040c1440c00d4803a4006d440c01010181d50003000e0358800200742c0310854004040240803800c0e4503444407030b80d64603001184e0741c03a800d403442070700601c9100214a00c414000068468900c031440c1c0011003001103800251550080c04c14400002c0d5a0440035003448800d0120441c0d2000c152401d00c90310b000c08014004482c01c7e03109800522810102141461426008005030600f038580199180d000c24a41d440700115240300480c4101c0c840c640c1889a80c4050094510940c3c05840d08161400301c2c0741040680c0e00d030071016404 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 654552652 1250 654551402 654551413
    0x140c03040314011b030501080609060903160303060302030609010623010c020103091109040c15020f030910140c060a0c02160e0c04030203010203010e04060c0512011a0706140a1b051b 80
    0x30300c01384580480001d4811079801107155403502103040d09004020740307411250380001d41000520b540000441c0c911020700c40f0042c0b4101c80034103085000b4007140d04000e50502a0500b030002152054110605569036102ca07500c28607810075450441c5107862a2140c0032990070344201d8055030081c2d10920042c0c0c06a44c01c0f03a0703a00540c0c2c0000301508401c03603044407004405441840070750324040707145022004600044c85075102c172091455481c05141c0381c1d1442829510b90480200303201d50807205181020b94503181d220000380e155a912000b00303d03140035501d8607080020010501c0002c1d0000c0003640b0301e140010f84c0c2d081501c0608000401001040b441c8003c01c40000183c074248000c50007011406009200c43c2031601d048000c2d500c0c45002c9000b0003d00b804030744101e0070018207d078110707850100359451100950a90b83e4040c0107104000d0621440d226403440002001c3c0400c3d8400c50b49079508106449401802080c03090244104500050040c00741801d54440b01c0b58003000c80480c070302120f4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 654553902 1250 654552652 654552671
    0xb0703020d0f2a090b09190e040b07020610350f010207020306060d02062502120a1412090607140106060f08060405040308130f02041803140c0304031401 67
    0x30141e49246030441e000815440265000ca100f4000c62032080805182c841c0c5400e01d46041441e440c0519140c05204024010608503c2402c1d8140f42d0024031090410300715900e00340c01d00d0305400c9400c83e40c460160203000001040d50103c0d210305407e82c0d0340c80140b014a480809002000c00045142d842c8035200700180b0030107009820041e10040ca00008000740c0e9030070701c5e4414181050005002c0348d00551442e1030744401a510501501c500800409003890700708513004407030210a031803401c0a500401041d10b10010040c001c00c0001c09a4006c482010b41c4a0564400c07665442c403050f01c40c400c020043c007101001d0300e000e400500d47c0038042d12039a004045246000e07800c4414a82c00840440e200c076a42c8401113400072030070707903228030101c2c2d00704030b14980380d1006815050000c00013840100354580c0e074030030803414400c0c50040640290080041000c800318030700d01c01e41000005d070003050b07415104ac003030500100115100e40031070201442c101441d56580c51000000880c0818030340d500c8100c00c8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 654555152 1250 654553902 654553931
    0x403170414180a23192715091707061d06060d02030f0f011413021e0d0506070905030c0f100503040f061104050a05030309090106050c0106080307110f010c0b0703020d 73
    0x1805503a4410b0070300c9803142005d204c0000c031091522101c022808090014141d200ba0b601100b044c9a00a902c000742d040c03100000c0d100520803880020044004c0900b001c850404080c007400c08540310b060204100c860405200004808180c46050181d0203600002c000e428441c0540311640e201030212803448048610340d174185600b074207094200b603566072552500c0301c980c01411504502100c0c1004080903254000c9405030420311041c40011680e00b0404c2d0250f1a0020006085a00041940c415052a040060002880d442114031030310a02c009030081d450701c031009035206a8010018103c03500c21072010396007a00010800c1e501411003203882c401103526030240e101480140f440551b5200d0800d01000032028450700124007d0f4001e201c8450940c0751000d1103030642f48503090013030b10b43c5880f1050078090461908009103074000864601c003003210b0029220004a03040710340c5042d03510403000448403500035130000341c084468180444c03c0c070b600943c010111030424240c0400e5412440369032 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 654556402 1250 654555152 654555221
    0x3020f3309130902010e0a0b12060d0f060e0709061d07170906010e10141e060711120303090a030503060d060504030c050d0807020c04020d020403170414180a 69
    0x10b680c200d0382c407041103004540c0e0002014001c03000803109010504d0070003c10042c28041c0301d246030703516a00540402c04c140d40b170301115214151300804005d100b0102d480c207078020b40403c40000440e0f21400801241040240c06080b040e1030f02050500001c044081721716888a00103001c0d0010300000983c1092415122070550f4032840f01d98004001c154901007181c0000d1400401c03843e038002c07502500b8001004601155156417000f100c0d881e00b900c091410f4480841aa4010365a000302d0004456081000600d42d490080c9012101c030176401c00313030038582a280d220456200400d0b4016480780030010b4040c01c0616004000546005040e5031103664240880d4416203081d0701141c00e0344544810000200103803d810500da00d040f428508200d08040e5445081d01c000ca841550085610035002c944c0798150313070041d504100500c0f54000d48a10360075980c0d00601409e0f504180e80d0503208000d0034005140c2406c0420202c040d001c030364072400c090740200b92451080d601c0310048000066220310701d402 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 654557652 1250 654556402 654556429
    0x204051e0a0302062a03090609010e0102070513150f060e0108041407230a0609050114130b0c0f010b01053408090406080613030c1b03060603020f3309 66
    0x5800017120a10020300c0026024811540b62980100100340c00b45d2161020350303c0c401c00c2030905035440ba05480050781810b001c1e401c510f800c08801da003890301c01d61040c0c000380044141c041900b50b0030764450001a1951905010340000320707440d17864401d8075504c82d42c03482d50f0103406520068030301e113114414a4203281c21a88080c0c0000d651501e96000b00d110903010a9020300c0490b0102c5146140c104050886812441200c0c1480481c07085090054030702c1089481c1011010100c0c01038030344411001810360441840c0140620820502500504052081002c5030030141c640358105440c5007200c200703581c3d03da5841041c141c034040390200b81648443c1400c4500d445548000e4591740004144400ca801c580e108507455801941800082443e0300d603802411605485e001c601071000e41081800060035000c0010880300b05900003080c0100d5501510540b482201d0304034040b030529040111914800c0e000d20109407800c4601a618040001c0e10a44084101052800c10700b41c5400143e0f10b00318041d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 654558902 1250 654557652 654557677
    0x30b040b1f060f14030f06040c02010216050f0d020601060e040b150d0b0913020a030f050a02030732030615120312010e0603011b0302070f020909030c0609010204051e0a030206 77
    0x202501002a040044034041c1513180461604518010103c82280e4001401c00d602865850762980e104a00c07e40403640c10b40d80b6142d181c41d43c80c01d1480c28070f60b00e0030440105a40e9005044035110034030700c00b09225048840c0d0b035581d0500c00604030100001081005801540841580000c8240c5501000a4054006001c1c80043d0201d91002400754080006000142607540e44011400581c1e40807105001e8035040489200c0c03000f000e1812602c1d0107958540658580301b5000d000400840c00300c42c50b88400464038240b000440c0e5810424031404031185160790540241c0c00007501e80040a00345c0285000060201c54425200c0c52454116440b103850480840414401407001b51120322065420181c254000c000c0840800038843c02d41300b07a61050001c064000503658140410142100080307034005100e075480341444800d01e5078036030003050300150f240500c20008081c014184266400c80c0d0010b055442036000d455178030201030340a040c216901c41d101c81c1011000d40c441c0805050a402c900 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 654560152 1250 654558902 654558917
    0xc030f15070507141f0e12030a0b0d050a060c05090d020f01021f091a0127020c012316020606010c08040e040311070f050607080d09141015030b040b1f06 67
    0x80078074440040b2850f60003005402c08400b0800500002841c0004087d0180c800e500d9441d2407102001400004544a6011034648000000d0020100d552014188240006c1164844c48031081d103090203050b6555601c001107041100140c00c5c214604070004105205607080d514815150941c03103142e1040b00000302d50344140c15000c00400045955110503210204200d0790f02d002d203821280c8603615030454003940d00740805003d0501d1501503444e0301d591a4001e01c40950000b4181007030007201014420b40d51280300200326800c0c0106282464003c039076014240c159511401592244031098007114210004c20000400e00030300012107024034866a030b24400c80c41074078001454185503030092481c0307070261402041705036504030072100c0e1240c7c42401c850f22411810441002003117580c0e0b0150640180c4480d0350104a00450402014680c0c1c0b00c08000a906042d008001c40c202b9000051444c3c5840003c24081130f02006850352080880403544011b4007419501c540c00d5416600203030120707400c0d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 654561402 1250 654560152 654560173
    0x312060310060920040e07050a0507080a0305190b010c0303020c0a0b270f0a061d010c12051303021f1b081509060d031809020c06090c030f1507050714 66
    0x110389004002004440c1440c10242080d159513001c6e540503000100340308001034038102c00d074098004e4412054101441c01e44606502201030060a002c031202406040010b501403204030441c40780408108040e0b4404e8108007071076409800035071000a01d40d82c0740c0304a113154400075a01540f82e52140307440c00302908240c11004a81c1c00c600b800d2841c440d0040e00000c606034070001000580307441c0c058008001090b45036180c9120442d5401c0072001d26029424010011301064001401c402d080b170721904100603603501c42a00c6040003074440e01c02801608640c0d02030320700341c814203031088000d03000300d20010300141c00c0b040400b081d080749182000030a403201c08000b45021020140003a00c1d00a482d840c8851500f600020111492250010240304881580c09000b0005840c1240600303410f050031903982100300d201940d603030030884000d5203500c15600748425a00300030690111007003038a8001c0103078221074110003d140d04010311038820405d00f4000300e0b01083c041c14996802c98650700117020300300303032 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 654562652 1250 654561402 654561431
    0x51302090f0901060c1b090c030209030705040b060d0e0312041a010806250207080f07030b0a270f0203011d060709050102032a011b02070f0803120603100609 69
    0x554181d5220300181001001110740009014856039400740c00303079824099200080803498082e41100b20001d28100c00c00700440e030168002c2c00110701c00c071304070b619866a400400082c0c1300c181295540141c1c042c03010751010b40454000051101080f4250b03410a544042142c110b620102e60550340d01c29608400c2c5910b401060040d809400c44801a100928255289007642e0400301e5840d071800106180010030740d40f0a0004801804a0310180c4006022005034113540d42d01034002640d1342030b498004101c5aa03010301c00c0c1e40710f60780510f0f0404c080e041140c0100c1d00501c0303404001e49403001049040e40050340c1c2841030018039100050105400101c0054080c40c0a0004011009001038401c05100d660b030008140e03441003440300c0451481002c03211107000000800c2c80015810343c24291006206a09400040c09401030b030380c2154210f55075618009100e444911a9001d030f4dc00411a15090401841d00280e000c030020b81250280c0c004100002c0440f0002e034010700d05140e9603003c03010700300c5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 654563902 1250 654562652 654562669
    0x7120c0c091523100e04110306030d0e130c03060e070e01021c0306031b0828020d03090e0f150d08030f090703080a020d090f0b2205130209 61
    0x504031410400c4450800c640301c00c142c101c0c000da0441c40c188100d0002d24040d03d4180034080e01d00079051224240c4158406001c0001e01076820f8030a90070003205244020990090700d100f008014010030005078003820503248403412004d6150010412500204d001c01c050082c0300380d109050703070001070031494802c12403155000944000c040000d03042c00500c0c1c0f41e034002040d03c0003560303440c2001d800c03081089040d4020159030780300401080340511040710303084408810310304495451060350f00701e00e25005500404e00084102442e41300c3c0103a01c04d00507050848080030740920904042c8825a00e880b1581149142200d6020b804401038081114040e8106000c00c42c800741924802c80d1000d19654650107404001d00d00242c1508580000e5041f40c0c040000300015600141043da4031064100000e4441144410000125403103140016501d00300742c0c40350f0308803401d0b8080141043c3c1600e2002990700d0400b5061112081c41070804911a40c80c1141003094210789070006a40e40040b00c1407000e000b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 654565152 1250 654563902 654563909
    0x31e0910030b090f06120a0f29010909050127030906050a1b06090b101401022407020f030a0302040e150f060a0c08030406091e111507120c0c 62
    0x5051046100e02c075121004055000792503a14921501d945401c040341e00108481e2034414184200c0b49600280700d858090104001e000d512801d51400c03400d107440ba0070803450341120b140c4d0348240c801002050002e038020b03003504d442207001241500030160f202c600b8502000c80180108013881158041680102c0103d00906030703403d001c1d040001c042400b602d4004c0c00c1407160303034080c14420088208007031584602016940000160114141206181a400b0a40c090090301034030814210740158000160b42407400101443d0300161180355a902080340c50140130701043d4442c202074066680c0c0c0900c06400034403405da9005890300d14101c418015040090104005040e64118004060300d0b030711040f00c501c000c161a2543d4940000c0c40441d64400140d5000d0040c090100c1484100201c6410004507240103411000140621103032143d620290810300030300900040c40207036003a0801302c80840304010220034035400c060040e1100440b0300003e800c81800145c41d64101020844d083e202034024 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 654566402 1250 654565152 654565157
    0x6110c030706110705030109080702030708030304150c20061b0c0c09072006010612180201210608070501110304030b070509063a0c080f09031e0910 65
    0x2041410004a61121201d0141104011024214152000c001c110203801000081c00030040d00d95141040c9595401c203800483c480e0080324800600c4140000c10b907405580c00c00c0400d23110080001076600141203915014041c0501000300d40c034400d900c4140400200c0865014101629007022000000c2042c12556110840d040c4001941c098001441200b0350304251100d610b0b42d00c0f51401602e50010a40e5101082607c20b8181c80c14904041000c504a03081925031465801000d03010905413000d80210a14081c1100e03244009984a2004041d1301094a480180d044601c40c2c00001904d24540200303885d03600210382001a56070101202c0740d03004086000c0c41c105411036035196500a401380c40c2d031040004c045410a600c1d80c0d40c0c42214008620041da550200710303c0d840c20b00110590354064009032003031190225200310103000b9000c840b000340d42d82420707594824045040c6c07403c01800315480303480b0500c01c14900c0240300042d0015020f0080e64545c0b030700e66400820208400c5003080d1000c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 654567652 1250 654566402 654566413
    0xa090b0405151014040903030b030a05030705010b0904080d15090f091a01050102060a0b040f0c020a060c090b0702090a0e060f090c0312180d0222240608040f0b010b040611 75
    0x328140c01031311004000441c1c01103998841030070210003402054034410f43c140902102e10ac10404000f004200103407089000340200c192440400a800c0ba0466014111640030066943c050132582c1c0f08102428060b041044100e440e20225400c60303140c107000c01d4105541f4003d2000340301c04408a074000460100c012421503041c000000e4443c0c1010b8840d040494555100b02d2040d66540c00089100c1c010150400c02c941c002d010096550a081c072040d00c0492403c031403074031460701c078880400035500000350300d6150074130030381c00d100301350200408812190703940e59403005a00f2010b10040d070003a19a02c20911040c01c03d103a50300d00382091400464801c0d40681c09440303014510100f40d0385e2980a4000032601c020b0343c1c0000c07801d600f10340d010084d8890341d800c802c030002d80001c0403400800b0000c21000c0010444454a43d105028a4002d808025040c1d5404110f40b074401c5035980d0740240b01e00a8880d4030101a5540d08840b40300381c01040007100003043c18080c99911403802c00320305400000400303 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 654568902 1250 654567652 654567659
    0x120302030a080a1b030207030f020c030304051009050d0c0812030f01060e030312090607030c0e090c1e031303081f030206030a06180905160f06080a090b04051510 71
    0x95a034031641c9140710501070214001641854150710107001a80304500309a040c820f00b00c2d00400940c441141200030441d2a201001c1c22480000c091006a001031f005615040c180700c1007001c10700c0d0f0b580c0c0740c40802050500c00301f2241c4440451031003040c4280058151103040c0010325083c04280108407041140500422030b030a5101e00e04141154001e0a2120148002d039000c281148034181c00710440200140078400c00c1000021860720803601c954080181800c403000c1191040342c0724040c541d00652990103e01c660130b0140051520310708a2aa40c481c120465a01d07005130b80040b100843c03010340a034801001d154001b840a540003146d02280c0c06403c0b0785501240c441c0c0203601000c0d001c1d40c408000200031807040c4e400017000d40074461a020601607106110806000c0943e801ca61500515000303100720070047c0810410703201000701c062045070800d1800c0740c070303410700401081d923003900c402101d03011a031056040c600030f9020b28042c0c6a0514855100506000050700514001c0010103040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 654570152 1250 654568902 654568907
    0xc07030806190503030315010305150306190902030a080a030f181211030d0b0f040e10020c0717032d09061606061d090c06040b0d060807090905071203 66
    0x3280d21403011240582035a041d01e200818445898000e650944000028861500580801181c2c0e104090780c05020302c2d80d030760b4814503070414560701c021b4260f0311410201e03000c1c0340c0c0c05000c80811301140000003011521500028901071950b8001d44201704001808403034035526000301c4084100083d002c0c04402425015404880b5049101a050340384040d01e6482441c801e070002c2030030340c5c512400c0303c0e154840464070b40d004011030640144111001d80c2090560b00709070081c2c05400c1c1070f580c0078180d804001c0c640000070303501207900e0814500410740701144007100410b000441000da94003c40c0c07900c0b080300b2841c003030703001c402c0d170035003003280b08408017081880c44c141141d54802040d038055031039a5406031411514a02d00701d00411907400c10801150b003109031140040c40000100400c0c2503500d960395010b40f1900002c41035600600c1c20441440300c0b5840d030008101d10000e20304005900c590b50542c0300d003004529088a00d0a85c3c9440055081c00030401082c00980280c00c0002014019940c0c003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 654571402 1250 654570152 654570167
    0x10605041409061801090f200a110a05010c031e090803060f060403050105042616020603091c03050105031e070317040f091b030903090b030c0c0a06090b0c0703 70
    0x940c402c1001400151203520f0321035481d507840c980c4050b0301c0d80c1961518205805001c0300081303540054a458022504215400d0b402c0d2804145000042c4c83e2210000046501c200f12240103140c030700c2441000c074001003091041d15103007144c5a0780000c640459804044424160b00a0000102e0034550320f1000b02c0d003d1400c494000f50301f1036181004000e1030000c11011302580d070000e0542d521708800c01c004e10030a00b00c0c8104258a100c2e42c6414900c2c100d07014156030180541038068200c070b078141d80005040110003981c102a0301800c407a40b030f000e03001c554001203441410140005e80c440e00100920f0070100101b2148050300c040c800c603040a9008625503d4a88ac40041c0034000c508a41c0c040c84801d02c4222009061000300380d010780d03515070303034500090030380c0030025000600070421985050340309106040486505540ba101c96614004248a460b000602680403100d81002483d01100c41042110b88561080030041501c200c3c0741420340284200801007081e04e0000c1208400081e4020f00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 654572652 1250 654571402 654571439
    0x2010207091a0312120619090911030303090a050c030f062208040311130c0516050118030905030d020105100b0a0c02091e1605090904050f0604030804060501060504 72
    0x307000908410301901500250038107030805805006000b1074240c4070001d00c005000b000c000104403030760340d00d800090203c0300855a00c01d44503049a884e084c440c10310207400040d80c450090781071a2911b400e8200190550b8000d90301032200303a01c10b400b00c0e030412030140810000b2801c22005895001c844200081c1ca64500800703040c2e080101c000c13001c0e2501c500c0003031100c500e81c02801d0242c4554803480c01c03020003001c109106200e02500031b40701013451454011350a80b8070700c60f44c0b414101450201c190400c84c124900842c2c01d03540390902c2e0021081c45034000010780c3d0080e907440c03a1007458201032504024800395111300b1641440200701420726108008021500c08440840e950034200a048400f60004600203500003a05024001454030ba0b2482451824004010318966100c62034564210324140c01e0300b00110b40140305030b48072458036503075690b03109014009132080c01003d5103481e030415004941c103c0103e28041d007444180070940c0b050718090405414030300e203001c1c20400ca03102c3c064034103407 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 654573902 1250 654572652 654572669
    0x40b1b0d052212030503010e0c04030807030c0c08012f0c06060d1b0b19170105150702040204060c03120501080c0d05030d050103030e040b0306040209040623040501090303061202010207 81
    0x749021420340440c5041002071142c2201d428019200313140042c80e640c002c0c401c54484900120105101c01c6403841107800b00c90f807102c0c480d0f1030300250755001d8034061649a0300303503000d000d00080010030304c00c2030040d413401e4172860400051000c030003010200b0101c0107900e49050031000744880034200c0d100042c00d6400000480d040c0d01110000e240000146092410442c070314486400000b69030038105020b00141030607610300ea1807201081c0c5040381c040c840e14107007102c2c8805400040041d41400112802d1020b42d05840c2407030a0a940c0115041e64099071000000400300c811030700c18554070803070380035039001c1c001014032081d49030041a43d85c5038030850840f031040700705203586410000300b00201d5800d0b41c8100002d00003580c1d00d06002e4000320000043d0b600a50400c0383c280d0681c0b9010420500c40c1e03a00030031101803a222501d0b82d01c0240303441520f140600c041c520741040342a10704001c0d28410380c840c000114804845140090a039071595105412184042542800503130f004130340581601c5005 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 654575152 1250 654573902 654573937
    0xc12040f0e06031f1b0503040308070f020102071b0509060d080909180a03090513020a080a020c0307052b050a08370203010906080304050d1104020f040b1b0d05 70
    0x10000b401c2801c01c24049050000c01340544ca00380b00180c010f052103082d8252030602c0b00314500000c0c0c515100444c2c00070f0000b0611400605003034060a403003110503400d80f00041c1452b466940715100d032040c100c080d150741c890a15003000341e49881001c01d40c1c020415035032821004015958013819001d814051442a014000000c58a262500c6401c1001c002001103550501c907504001d420a03003a4000c00e4012231040700c0c08840d810480c001c44646850959840c0d50383c0e40c071810803070000d41205080c28094042000300001044003000105442d002010b00300c10040340c10054a281601140080d809001040c40290704694210a1040c1e00c405046802403040001c0c6441c05c4411601706a03070201a52244100c4880007a51741c06107050307910303401080010b075841e004815601d0240d403088540c40501c454220300010a800402003403c240580050300b0401559441111030700180c011504115020400d00c0341490480b03060b001c00d4081201600c3d100c0c1c589500102a031085030410521807018 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 654576402 1250 654575152 654575161
    0x712080703050f1602090a0605011407020a0e0c0c10290a090507030b0f091303050c070510030905060a05011802090a05100906140901050d0b0303130b0c12040f0e 71
    0x1d0b000b151140c5400050040d61030b5449562540c03050711304a4240d0140ca991000103400d0681c0c0d00c208415a50161600384200e100d1082a02055110001c2241c0000d08034000150f046d000b441c10314014022a407010380c81710584131907146045801619440064145400c0c201141500040e50310b0121500e440c061900d84200007103122103041e50300c00c503406480c0c01d04101b24158998011042821700300e80291723881e82032008000419209540003944014030280c0180000d018900070a1880456030a0381c40d030380d65039800103041c060b10400c51703c0401c1d1036092a500b008014820b01c0e80c48182400704000e507504005604242c20542c0300c603915040da0000e418151035a0300038000d4001c00c00208404c0340350007103000040ca031102c584182d2001c51240011003280310307d00415031340255010307941d103410136904100305000b4047c0c0c45241509404100402c2864140c040403210141c9404031960360b842c0e00c1000203514154080c0c2e55210301000c02d005c1071164201c00da0078002280c04e1038a941d0300d26140c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 654577652 1250 654576402 654576407
    0x191101020c0609030a09080a0b0703020903070e0903030a140f04021504030c091d07030803151816091406121f230402030412030903020309100905120712080703 70
    0x81d0300540382152241504200745080008020300c500780389961800380c0550340300301c4241c0c2d075221680d0060030169058000340300c042c0300b0b501414120b00010200c1c1d0207296100020940d41d1001e030703256911600000304202d2181d150b400703900d60703807500c407550340e5503502c3c004450198070340b40940005d01c903410004c0c0f41c80030168214255800380d0b4020000d070900d9a60382504200515246600840f0054292510403080300c0110b8440d044070b0b04941c1092950f40c0c3c0726024000380c01c981c401a580f02d86004c8103030b01d200ca21003076124407a9480051201f0300c06403104000c0c100c0f41d07540d4400300f0300103414440b8200680f03406099a103040b003c3d00500b40f191722036041402c2640c3c0140e0305107a108850f1540010740300e141000261002c1043c1d0101c107040c150550900c02030348011100603002c0070301c41d0001c460383c61080d0300600310503020780306803030030481074800145030255810300b0304001502c4083c1c10302a521b4906261103036015120010a980c500e054035107100340c4a03030365001c0e00800020441030107160 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 654578902 1250 654577652 654577657
    0xc03080402040608160515030712052805090105180d0305191b030b0a030803160e060d0e12040303140c1915050a1e0f0902060c01140c19110102 63
    0x804d80150f82d0484104000280030030351500c200751041c0030a4081c400b0801c4000d0490780283c030955030f100c4202d00c1d80c0c1c510780050b00000d02134105901c010780200c140c1500103604089101003c01000c121420481c28003800d60380d016000082031002040c43c5031070a80009001d01c44640d050038040350541d101b102400d010b03100100c2c0c0b0700840b0b09000c041000d20343d04180b0b80000c0d040e961001c1148160b940c042c41032008043c04000c103080c0c02040420040d100c05c140789a52408141380400c46281b805005c2603050708280c6828000a846070420300700c2e424140242e0002600b080390f12410b00d0315503140282030409840a201c51620300240713461108009005c00010f0001012120404041d42d10b0140b0468504140341c680c26840c000200707034515080e0189820398410005001c10304801143e04900421110a143d10001d56403101c10340140c641c9009030613549003007000000c000300c2c1e1800704028004014100012040d04115078907200c0d0100001a040c42160715103104041500c440407402032 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 654580152 1250 654578902 654578909
    0x10e060d0305160807050706020d08150d0c0b0d0608030c0c0f150c0a0605070206092107150606030608061009110909280c120209040b100305060103050601050a0c030804020406 77
    0x810444403c4014482035030002c180039031080007222041c40e6652000ca03200e07214a1401000100c1520100b641c0030705140480501840040075500c4600844e901e41145084907400550141c10210b80c0e59110307492489858028507051014600d4030381007050254441501d090000d206101c0e01c0a0011252680e80c0425840e0346440079450303031a40e40d180c3c003c1e40c800325003104030bc1541c00c02000440b084d10100e8aa400342240500521852011a804000b28108034442c0c21a841c0d060059501240406113840c039624142c20b80014000e00b041401010f46849401c10ba8490f44139030107000311521140c940c441240c0d92040300040c521448030718010a407144230041c55004072000107200e0034442e5100c08000c0c442a0b8140d140703010000950710740941d04916409000300d01403440c980c0c50140c56400600e2003800040c000104501e0103000111404603a40b0742e83c0002341d42d64100840d558140c490141c20003002d081c500e0801d940f400b001849085104001010400074a02250440d1a15001800607 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 654581402 1250 654580152 654580177
    0xf01030606202415040b0d15020c07031119030f0b040804120305090901060f0f20010204030305030f010e011a070f080c0c15030f06150409050703090614010e060d0305 73
    0x5203c0401e09100c43c0c4070255003c2082140d0400c2e40c03111460544990405800c2c0034004115401468441d09000d0a80074416480c0381e03000c00ca841600c220a210f0030000d140305a048510100c0e078001807080000401d4885001d10b0f20312501403010540700c0000c0780c40303541e201524140b1565546071003481c3c1e00403580001d02d10f010082c003120802d074228001c1c06602405940c00e600e00d82e41c030034007200c0c5a8512801c00003c202141b002010051040f0700208440c0c1041100d40182c0c4a0300c9001070881e40f26620a4000030404018041101e0f04503041c203004040e503218410035035040940400c1c1c03003101e0f075400e0040c8200016a04040001c800d0074400c5090b0400c1e0711503183c0301e2803940a07031100d9240e01000e1284a881c0c041e800d034003d081040d2405100362810440c00c51307890078184107200c81078840d400c4001000b8400002e1482c000c0c05050302c6881c06640100d201c1d031241c41d010702500e180314200350122a01034018070401e002054800da1101d400c0341e910303105403050b0500f91010310980c80f880d80d1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 654582652 1250 654581402 654581443
    0x7140714031216031a01050a0c0203070306021309050403120902130905060618150f060d020309010f0501080c0d12051e030414190b041406150f0103060620 68
    0xc21a08440003144982c00300300c80343c40242403454013141101c02c90241c001c00a03281c058449855440b0300042d140382c01703a80c00c2917a1005504c0c0c0001e464410f09620440d516600021b40200c3c400030700c180500201a22441802103090035907000d44800310540340b01000a64030444031b03095559040880454520154081016008a0170f102d03850300e0045540e1405035101151040b240d1101e1440369100c5d10b400d42018a212140754104108002d881c100300c0c9c0c1c44102070100c8400002d130b5100560040700d64600014500140b4024101926416802021107801522101c1c64a444d5190581c4409a10001448a841500c40150384034000c0c0e1803190030945464054070b8003c2100c02c02540104e020b070b0340400310301202691403070303a0710002d03c4130b052a07404c00110400011409120304d5003092103444540048080048460315201c400c480c4049618004000140c0302d0514034101842c404003032a090129a08003500980324000510741061140b0030100004c10303401d002d1103009040050240c80f440c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 654583902 1250 654582652 654582667
    0x209060a09080f070f0506030a0b0303180102010b010f0221040f1e0b0702032e0c030515040509150415021219140406090c0305010c0c0b0901050714071403 68
    0x18603420203401621007074420002c422500350f4002030040c04882e80d61140701d82407800c10052105a0304058090039465860b070862008556083c0040c2c100500107001203030004003210002030a64404c140880d0600c8034604a410145d64041035985076010940c520300013141e40450b00615a1003203030312003020782042d00710105a2a20414841700a28440344805130166212400441940304002000354584d1041d000d02589054000801d00d5000340101800390b201800c03400310041e50f0444220400203030744d48c401c02041111031000d240f030099090304c08010a2416200c1c80340d481c180071609549001c81d0000040801500711100c05002d00d40030015903d0700318081504603440020785054010b0f84d041e60541200a2551040c0c17030b46403100b00b030071003003588581d100c2000070440101d056441c1c10301c00d800880801c600b405001290b01d074903600c0749481d8041e030419040703c3e10094091002039041c0420300c00520f9000c042240c4813030b88441c266907200440d1400c20328086449620503600c0c00082000b2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 654585152 1250 654583902 654583907
    0x3020c070305070f081002030610080415050103230111032e030605190b060a0f0e100801180506031c0215070306051c0f110a0308040801330b0d0209060a 67
    0x513080300c4030181102c202900c5200050260b006c200d07503490300804140b682454441c0300c3c0c40c1c0f484d006402044402d0801c0074074001901681c500341c0044c2c908402c1c40d100c0c07858001c0c04000d0015000100c000030030000b10310b4611905c19104c086c01c0d054461440d00038503e0b2264404260035400b0040c20a0b07030181559920744240a054100d0364445a280001c207442e81041c01800740c00290080208038030f26250300c400003a01d110280e1307502d1004004060107003030005e13260100183c900303140383d446d2000150724040c2d81e8400c00c3c00340d08007429994100800c1c440e0326103001aa41d144401d01e00c900300b4488140e8901240b40c641202440c0ca065030b00b0400b4480d8558141e8802015180d080d9204600400f00c006480309203464440c004202d060303440502004600003101101d45d0b140f0081100754099035a4550b2060740d04a80c21400c004e035512500354604034100c4180381da5000940c5c2d0504880c0d1141c411003c441001e500c1044284040001c801041c00510780c1100d0414038020582900c504860000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 654586402 1250 654585152 654585179
    0x405061801080c0c0a17040305030d0504051e0c040b0f0a0f2103170703060801090303140f041e06200d0609150501030905030904230f130303020c07030507 68
    0x112030200300c0c0c94000c280c3c02d001e60b00c2150b0031131010f040101200c1e041035940d860a01c80e00707501c003411610103200100004a06100403c080555020003040904080c10301600b01800b000e606440840c0f401c030040e01c4101c0204115440d004200c900181403035008021401c0c030f000140788580d1012600a0200e280380e5010b408905030780400444035564003000900200c815003245000d00031618220980e54001c118007403140d07028215140101d00d0513681c03100ca80c05d555000c80214042910303600d08054400c180c1c0441640100c410300440541d0410352075100c01011228070020b0500d0800c4142130501140d6005034640c2d41d4901501c0e488200296801900c681101c07403142c030317068206100022100c03140c1c095440c0a400c0405c107a401185400015001085c094204640c0c600040c80f0b400742039501e88c42120740c2101c1b07103030b405e0184a804180300e01c810740d002020982080118018000c10070540c040303189049a142c140165960061295180360100070341c002400351041e40000304682000320305 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 654587652 1250 654586402 654586447
    0x7020a111c1202010b06160609260a0e24030703091a04060b030c031e0a0615030210031415030f01050115090501020109020916050c030c0102040e0c07110f0402040506 73
    0x20404178502c60200901e900c40c80c1001d984020f50140c049001c0f94945e400f8010301031150300300d1301c50b00380d22031302501d82d2200111802450060202d401e8401d50f8209208a8041c481110410007000e0740c04200d00c128900c440c0308c040c01c0103001c40014021802644000d180c59001004801c0a401c4e8440940d40705804940840c4c60701e041c80c2103030f2140d00700090401c802c808000c014010001d00c1882140400044918012640c400d0b402c14901194041c400e51002a05d441d102c035003624154014081c8020364590340004040c64041c001c1001e005203089680c0041f5010702c8903000c0c0e00140c00280c6440350301c04002100303503c0c050000400043c001504800300c07100d80c6505c13055940d0340c801a422100d0740c0380d000c0e4021181030b00048a00e03034012850700f480e84080c14414100300071040702902d55041401c1500c9180c0d4001000d000340340701c6403040c540c01201380c0c40c103a180c40b40d0740e502c1013a94410b0480f0306000e00319108000c0007d581d0b0740c040c0c0300075140180c01035844555034105001c4802e44a00c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 654588902 1250 654587652 654587657
    0x30a02090a09020403200d1109060f180f060a06080106030f091406100504020412060f021209030a0206161d041e0510090912050705070302090705030f0108030307020a111c12 76
    0x107086c641d0610400c640091500a404500100c0c0143c09100a06030020f280c0c9034071031420035000c041556040854095260780b203180d0521894800c54600301980080c1c5640d1065044c0b0804020325940200114190f038484e18002c1a00a014821340307010b03211a403402050301082070390800300d852000031071900c1244481480c00c4880d560b0424402244180d0207403090381c2c1c03d01e1540c40c001c03d442e82c01c191801034284034018078040100068840e40309051351545031641000584074042603041000a4001b01c07021a10841d50404000c05440b0300c0400000006107460110709a00070f03910365010010007004084000041050640110b00038401140c0c50001012250310214a008041c80350700c1c0c800e540400d08c000c02050000040e0380d280c002403801c0f05d003072140a20100042c5c60f144103040c01008580c94042d1242000302345941c69100c160407041b07069000b4010803540aa00280c1c00004a0b040354501c06841401ca000c44e4604003418185228107103c0049041006400c04100f600e948559 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 654590152 1250 654588902 654588953
    0x20a062f09030a030315090509070e0718030b072a0302010609020705070303050304110312030403120b150f040e040f0309060207060c2907020706020f060c030a02090a09020403 77
    0x310a00000d4091042019015400501c510b80024001c1d40400100c4000d402e80c00b6031030340d4420200050b01e00465140c850794205030403c000004411144c00d402401c242032108076404d09494440c403903040f9100140c040205034000c00c0300390b07014045078030001c12101c030226020041e03000c2d103100b041c503500d0f01100150f207486c3c070020b161006031013900c83c0c082c5d010000c1c0c01c9145c40e5440c1100d00390030103001502c122842a00410b42c941d01089070300050198414415100d19280c14040d000528132142c00b03880b1030034210300f40c03242d0741c9880f69002030382d200401d00d0781c582c801003000d48140d0180740c12007501c0b80c3e802010b10003840041180c21010510a6030345950a54903000b007203071110600d1151a021441700e12410000600350f505104051044200002d401424035013403001050041d0f60303090260300100740501040d43c0c180106a1941aa0001080241405290310416100040500c04d000b90701144028980c0c7e902100c1000510000a013952100d80340e052003500c407040d85064481d00c042c0c2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 654591402 1250 654590152 654590231
    0x708160f141e0705091008070e060411120a020d06031b0527130f060207030806040b010309030c0f05191209090501060e0d030302040f0f0e0702012901020a06 69
    0x2907140b00302225600310103000c000e407404007408800b82014007207041d450180c050100d0001010015900103051006000c0078608040e41030104480362810006e040700d10070002c10070f18441d2018110b80260001c0c00040e40c0d000d42c400c040004100300c2d04003d01c3c44a00080e071407503a50406458500341c6070308961410042407030065599041102a0718507c0140081000405c803075521781d4035a00c190301900300028070418640d201802c9034084a011004142c4030300c140700e55820140b166050140c020b00f410441103071a03071001781a40e5041900280b002d801d0405000c20084c003400300d084080c65411f207030103441e50075240100b0781d1442c050008001900301031000070a620036000b558106d45031501e407130403010546014428014040344058041c550200000515414581c090706c0003060680c40310058a4100a0070701c070b02c4031024017100c00310380c1031082c440614100418800d0802c0321100c4000d10381815180140e080405c0c400f005444645816036000b03640c200d298078880004001030500303010240 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 654592652 1250 654591402 654591433
    0x140f0a050121061b1206060503091b0604080d02060f0f040201050f0c0115090207030e060a050316110115080c031204060509030f16081b060708160f14 66
    0x10248159040e601c50254160b601032410504100c0d0075006880100c0c1c104031481101d0040e0391030312651400501d002680d0340703d50000d031250304040d1456241c010710b14103205005d6960b92551402070124608604840d44403a079134a02101c0c020450700d420f592090b805050042d464250403100541c0c03626032100040c00300d194480b031036407181c1c3e8161555414508800c180010a0b080040c840780190340c0c1d01003000d950804101a580209000c010150741c0e1031041c50002d210320b80451189000f850107012a40300141c110f410340c1d52250312001964071099002e841264440c10412a500c0d070307075180502881d10190b0030030030070080e10002c0c01210075a4103040c0506544e08020010403004007800d11050140d00d201d20000c00f54464020f044030300c564904800c00e800c05611145190080722280320811091006101070201094550300b15500040500081051889001c0005100b4500011005c0c0950f400e203e0007628207030800d01d034840c0000940741c04c01046101d400065550312030000c070b0704140103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 654593902 1250 654592652 654592661
    0x10031a04050604290412020706030204080604060207020105041206021218060a02030a06050307080a05190f0206090414130b09010903050403061a0904050d1d0d0222140f0a 75
    0x158014000d000e150380f02e0311050000c0080e602c844002221620701032828200c4501d14034010790080c03009000ba80c031810030103403500803ea840390040c9030062100300050400030600741c0d40260400d60144e40c80c07005200483e00380c441ca410002c948541d40100c0d20501240d03a015081c2403d40b0709035109a501e40e520358000b241c0e0031440728011a407005000aa12640c2a00a590013080d07440340480c0d80d90305c03400000d0414581303230003002c5141d200500031410300108110802c261086400f0301550102c01d81c0f64140300c1e80d041c120290088100003101c1c04181c40343c2c2d020f000c58040500c02c101d954100034200b96500d043c030340401d132000c800c03010104071108818850ba00045a00da20f50038940340c5956100c81c090400703d08180102d8650414000440d1a0b00100238411446213014240c0c00302d5030a0f0150140d440c68175500981c824012a850050b241c035220003a0b41a0100c807080304210b40c412150541ca54040310820f006030130002000b101030810f010550044144a40c0825a50303200e0540d41c04aa = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 654595152 1250 654593902 654593911
    0xc090108060601030b150a1101140103030207031412030403020c090603010605061606060b0a0203130e040314280e04060504050c1207180e040212010e030301090209040e010510031a 79
    0x1508841d010070482e60096001204918000d000c0188004860042140d135811442c60800400c125005030b2010035420b00c80c04441c0780c50400400c9065046407070080d550f004900004001909440f010000746804201101110151140181e600d10301890003d490b0781d0744454160042e04100003080051130180aa081500c2c006413030181481c110f00829140502844d005a030425594203002c261005040001c00c210050f5400650703492001c8204107030401100e511912003088841c0034040003070b03840000240290300701c0c1c05050b280c41d00074400022241c0c13000e198402401e92007204003250340d0490300103645d45008450400a666840086c0410303214219505601030008011a400001c0f802032140e030031501900e0038020122007260442d042d95602d8100d034000c5051b10040100f1403074045a04052900036100a00c400602800c1c01c3d5964007060043c055000d801049100f16a03d070740d4002000720101c10001e11040c01e0040520095152500058500400843c1e01040061107250100d015 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 654596402 1250 654595152 654595169
    0x1020f0624040f11070c08120904050a15090501142b030903060906140a230606130e150d1214040905070306080d2a020a0e0702030c0c0901 61
    0x80c0603199440700d48089184100c1d038003559070f00300489860307100d200e2158950104e503581a500c1c415424401450060b90b40039400c5035100c4a2078254481c2101c041c0c0b410084261404146510341e00380d1503000c1e0400b1002d0542d00007602c0c00001d00512141c06ca981200e801a0000262420708428465070b1055162406010141c52051074103100e24141e0b00302045000303140003809541c03643d80f54400d036011181c041c1c500507115400c1440040f4059001c50b0006420401006490250501c401c1c2a0b101d0000010076099040000740d1036803103640441d641c24000010710f09071143c88809a00420a0a175021901100f0702c00300e82d103203410601806102e041d08556500100b084481044508500c0c1208503510a54184000120644540aa41c1c05841c854038041340d072508140c401440d000382a694003040000149010040015080d10f070a800b894101c0811a03640a42c008908031203071a074803c0741504c0380d40042200341907000c00948020000c08081e900c490b2180000c100c0c00d007c003801102207 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 654597652 1250 654596402 654596431
    0x19110c06040312050f22050a031109040201031b05301918030c0b0a050c1215030d1824030e010f0c050414060c0304052107060e01020f06 60
    0x2044550400d200903d15624129140081c654030210303860b003207a102c0e094548541e8a60078421401b8641c00d0b000380c44281c540340109443d507291001200001007100b40a10b0020001c242564400c0e0044181402c1c580300385621214014402032055001c04d060489100c0e0302000040c1111080c61007a403991030702c0e0102281a1100144024280340f0303d100315281e980ea03a080c01c2c1c0d0b56010401d0107201070340643c803990002c4071941003c90040000804140c24149010204020b05036040c0a41701c0500e107042d0081a90780c1c40362041c00d554420000c4140d8588604a0f400050381d510042c1c00018120685181c1c0f4059a00d180b060b5014040088482056034801c1c85030000a00c00d80c840785c01d4480050000c0b0b0224600c040403411946507024860002e0400035060045021001138000094001d942451030615205ea4980d101c1c0214050303188103004132451404845400d41407406422081c1055501c2a6a20300c1c4c09010703090b00951050150103040701c0c00811150203d40c0341c0c801c04a540381302d01d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 654598902 1250 654597652 654597659
    0x180a0b0f03090106030b0c030a0c09081b0310111309090f0f03020c0a03060b0312090303030f07090b04080d030e06250201150f08010e0d02101d0319110c0604 69
    0x106810050420442d59618a40040440d41041a4902903c03017249001d0b85c906200d250b50042c0c918140c1000c1c03d10148002c100404100018006035141c01c981d00340716400c42c000002030401c0140c0d45180d01c0c1d030303040035101e444200741031006007081805000208105603840b8000c074155038400d0000360aa441040c905c2001c1502e414841ca5424031a01c1070f200040c1c1c0300f6001074019522900262038440c3e03a01c03241c170100c0c1410400708004001409d5503e041030002c1001940d00c1c8001880f07440c07100b010702c003c6000540600c5801d80a05407103100340d83c8035500e494415560301c0110514000280c1402c201042444011078128001c0c140700186070565415095074046803814100404215981e51241e14501c1241c040d007500075103840c10400d03030070302e01d002440780c03c0d6844000501c1c220f8010300c041d1a0076035000901c00e40316646070480842c007243c4050b4108050f2102d02211581c1d4000001d0b4086046c20a80644031349002648401c0d00302c44210450300d0b41c9640b141c1c0c0740b0343c010780c0402090 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 654600152 1250 654598902 654598927
    0x2a190f0e06131509030512130b2a060402133b0109030801180618050c040f08061803040b070303050a06091b020714060406030c030906020a05180a0b 65
    0x9040160340719000b281002e9584494546008140c100c0b800007504c840310502c1089400d00585030341166541c0243d05001e240403054800c0403c912072900c00110000c1d800b098110810380200b8130401c01e00c1030031003074504500d420707441301c00445040780314400070541c40361003803094452845860444d5400d4200c4c5001c802d250288000181c080001e020100140d0304c0e4860000d00403056520710a1356442000d51501c4682c000b0b190010003110640d500b400d009100310403007a450282c084202c0b00000c101a140d480200610340318903000490310800d145400f04485000203021030044000e03501000241c1120400d40b91280542c0c020402e4042c010401640800e1003504456080408107030001032055070380c6090022030340070480051000d0f00c4420780030b0a0030340500511004103040750300c00299818410000b0140d205902980082c1640d0703090b188501482a40310f00821035000b1800c540d9100120b41c094100e40201c019a102c910001c0400340560a0084c058011a0042e001c400d0030002c00300980d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 654601402 1250 654600152 654600157
    0x31606092705040201021005091f0506010509010c110a060503180d1b06110712020d0c020a060c2604090c02030c0601031e08030a0b0405060d020906092a190f0e06 71
    0x917411403141c0100102d901a4520950780240701d040d004001c03c500380b0010a02040c03450800c0c03421203141c04c0c1089000d03600807049800c1040240703050f2144140d140f030503c0f120800341000c0d6410080c1000c010410b41d80140055015480302c04030fa1f5031031310943c69003e9552110207410000a0b0b10200310101c6030403481e0b64100128485e52010505602819507410305410900c41940c1c0e10f00e19500300703084241c041c0490310390031f84145050010404640c0108031011610300c201c104000035011210f0500c41c461b108501d00002c1035864040300c0803142c200b807049404c51701465543e5850160190403031400041101c40c0c03174800350081c002580c60758540029141d9411000101e011807103c00c8070005d00c032040203500c1418212400607034060b13400184030440394003c000300d0282c0782011601016940c0e18402a511810440300b54119941d2150011800403403811034065495440038440c0c410540c00b4081c1c03071071284e400c050032810a41020103c0d5640b4204030000007140350000c1000381814107000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 654602652 1250 654601402 654601411
    0x1409030a140703141c230906070f0605100506131e03080309030310141c03091208030a0e150c13030f0f05070608010b09091005031606092705 62
    0x195000907030b81e921001380284000324081a280c016803071048900c04801c590111031307106860440c00b03c5060301140500b6112617482000081c03c0402c00e4015640d40c0070885440c00c1e4490b209400000392803510002422058031500030030505844007080c20b090032804e590407188214140c984052034460215034540c440b5040b12041180f030b45021020070000d100840c01010b000f40195035034504a4545001c5100c60303048102c030303804030f000305d50301316902e17001d41c18441184045103010258561a00380c0d9566100d89c0207203520040207420109010158018600c1a8030000e8140500100d4001030758030780c020708080c48024000c05d00400d5001d2000c20180c00081d51001e007000702c10340c403a2a000300300c0a62140c00c0710181801c41c0301004010081c0002c000a18036030400005ea541032a21013240303805031002880c02800304c600050b841c8540b1260034401040701405030b8200c4003410000030071070282801030501103601c80800154901042c4507050348410f00526242040e003030150003601400000c0c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 654603902 1250 654602652 654602693
    0xa020d02150a1d01020304060509010806040f06090b030c0901030308010b031306060e150f1005071104020d0903170906070305090c0316140d020d0f0203030421031409030a 75
    0x1049010400c4071000a00c100c2c00c0940700c04603040d0784903c050381c824402e08900d034110740043c0410042c01e90480142c4250354000d08007450507a440c54040750041c6000240702101608102d0b000801c8a169070041007510b03011380695400c51155001e2043d0030100f84002000550100010490440f207000559000018100c0c1200141c0035502c0350b105980c1250001d0341740c0314201081c041c1680c500c08080c1c040c40340a54619204114207030005031646d51440c0014113100b000180c440400c012035800ea501031100520454550401c50a418000c25078014101c01082401500140071032001c0c5945119452031801480e41d5a00e1003800c030041e010240039050940310345e803801d220998050200180e804000d1514404641c03401e5101449000308002c001d010f40600580a400358481900300a0000d80041a00c009100709102280c83e40c031840d03100004941c1c120740d00b20301c0311002c44a4080c61501039a10700154040d050344000183c4942850076905911845180c0c001482815050100e103d0b940e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 654605152 1250 654603902 654603919
    0x61503040c09091712071106040b24030304030f061d061504020d0c02103b0705030d110706090506031611070b0d06060e1011120c0109020a090c020a020d02 68
    0xea0084c0d0150844250054070304100d0040124550380241a000c0f0351904500078105410940c03204502414054039101d000011802c10411808082c01001c02480c000780c02c0b40d41e9603690f41440c00c0568a208411103800d410000ea0080b8100440c0d80c54020300304d04406001551125040d041244200c40e550316040750b000e010b142c0c1d00e2200ea01c51001c040300150080c100a400c4040c180d0100c900e21075040c0240841c800821100341d04190800c0d98000074034007050000d010b6403510614100965200952500c2800316254081d036020003603014040404040b1900c194403400c0c140da40720458094aa00032405000060342002c40046004090b0801c1c203141d6150140182c450f8242450342c1c0240b41408400030b12000102c0711441410001d0000d403070118100120017000501c49141300780810100800210048038840b81400515040030b0404000c503034613101c01600c54042d00c0c1000059109001c0944001007c3c4590702400754609610380c0074120300c9a00f60308102003c020b800e0305036000040d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 654606402 1250 654605152 654605183
    0x30207050d12110d0902100203161704030b28051302061b06090a0b1305030403021e0d23010605060405060c100212041b0302011418030a0b061503040c0909 68
    0x2808004c003c0d603481c1020200d0341a5440c018030242e40030f03078500803013154000c11621441c829600e04450106034444550000b4550030111510302e4012a000039201b01e9800e0b0030b00c40402c0d000e003290007001d015200c66003141c0f0081c1c201e00c0102c80c1e08495004007a0b145607030030001441c21100034424075243c80c5000701d0080240402d94500202107030110425404800c42d01c003441110300d489a80072600030280392008001c1d9481d25143d000f00c0c8802400f07651850302c06610b1215600b07901c003900c54042d24115412019003003c0412803d1086490380005012610400c4e180c018050041958805010145824507140c103000040d84603040e10b698502503e4800f01c00d40c9501d0000303115582501c0400613140c2041d080c6003e5900400310283c5280403041c2d41040141d03003103014090703000760000d15107440349030440003070200b0711070600c071198180503208686040040481c191b41c0103840031f807a0100714502060001c00144400c0c1d4001e0b04401b0485004c00c44004d043c1c218440a511444690195040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 654607652 1250 654606402 654606431
    0x50915060102150103200603131403071a1023010f0909060b04090c0503150409111305010906090b010507021009031e170703080a09081e0910030207050d12 68
    0xc1c0c00480b0450040d040714070301b00c43d140040c0c0940a0007111614550b0501d0506080207001c8000010f001540302d850341c0b00c02c000107009940d2240d402c941800100c1540281d45125180300311501d0304074044966001c141d01049088881a02e06007103031803910804200015140070000c011a00200b04030450b001c02d69616602940000340189030b0f065490724201940d01c000e4918814490301000018001c120f101d142101c0b2000b0848819140004d29080f035041c44401641a800e0403a0464030500d040c2d0151482580800c0c1200e1070481d0030030109458502142c04e941031b21403164009070f0144699409132a00d400000c07408005420310300d0800317030f627070340c60710382c0205204c103c401c41e41d5030280044140200550390282e10080840c41501d07000241c1e40c041c00811014100e000c0b296914040308040100b500d0071114100d1003284100c1107840011034550883d400844054081c00303040d4106c0a0300341c041d00170368050b179501a010f801081d0800d94200c1e0000d00942d100d142c1c035a1581d401c0344020740d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 654608902 1250 654607652 654607693
    0xa080726060402040b0a030f140c0417490f120b0d050a0c08210c0a0503030c22060804120210020706020901030b0a030804060f030b040c020c03070603050915060102 72
    0x200c031030721f000c200c001c0402c60003030032101c40c0000c800c0d00c0340716101000a50f1452404807809d4078848a0754140280c210041c0b01e26046020030714803031168021403254480e40030402c08a0411807000101100742540d41c00b42800b40c02c1c9540c5000c041181d54800e100c840c2d001d181900c550078000301000a04081110000712900550041503840c5d400908100c002c2c41a0419031034082c3c003584000f07000d56641c0d8240302000c00040001490b00500201d4554000002444625600c40e00a0210782d240d0800c841d22100c6c44d440310107261103010320b82007101c403001d840110302c0d0100d0f071498403000f995580e00d0310740907101c2403d40316020440c0119004115208128400781031140d0041c040140ca9903140d00014040703c14080300d90b44600305002d01000020200b10840e13080c0e40c0d26140c244080c0740e0703080e8160094024003180650003400d041980741c07007a500240034003142d03000302c08844842d50b403010194116602a40c0c013140c00c3d003100c8410041205400c4542d41c1102e810710442e40c0424255056030a00c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 654610152 1250 654608902 654608917
    0xd03140c10050c09090f071d0303091809010b2d28060f021b040f14040501090b010b0c150402010c0605090607080a1401141908030a080726060402040b 66
    0x3c440100d8551824103180300001d0780400c0981c003850040c1480e26000e0b1006504401d044a0000706007001c0185441c1403050310300241c0040c05000459000460040c08a0f0b0202d50303030140c0790300c1c000c021490351600451071003075010b1000085014104520045401261180565822804400c0c42007091042003850a00b991030600241d040b550504e0b100400008820300003000b150300000310070907901048000034600349421070b40019602940507018014159029000c1c0f1000c0c4c0d00360401c01884810340050300b201d4820010100642c0c2c80300c111043c94082c0c4281c841c0f040e84503100d4143c0010400a03002c0e0024014184201c0d0100a0350b1100240c2d070007266000c100c9d801c102c06100d0000c0d0000111500a42c0001d0240205a640314801e4208a4140304081d103520046101305015282c0314981601600b9520b280922141ca90160644da07502000712800020110400102201d1040400c80416000c24ac0d06504030880c2071054454408050000e55200d9420003000031071030448802000603 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 654611402 1250 654610152 654610171
    0x604050402191e050a0501081948050313060603060f020901021c0c0b1008031306080c12010b0714030406030c1107032d0c09020403110d03140c1005 65
    0x5a00f0811201100710764a80c04103005148081c1c0622140ea040342d5025030280220407018240340300600302e5409402a07210f01044101c5041e94662100984183c0070b80d001404042c0143c01d08000d100802ea020075408201c00050381071000c6003900740ca13202a6a4040c2c0a0035010031000d460341ca034042110011404d0b1903030640e00082501481d601440002091011001e41c41c140e2584000301410f0307a0f100d441c5c000c2c0700c8490500040c8a00c2e11a070301e10300162a0038411a41c40f498120000e034145030240c0100e1003c02d5034100014a0107903e90f0854408082504006443d640b030894a401c15800040044512220766441a256440d041010304002e009994011407400721484029100c4551100c0c80301c40313600400301c280701181c040042280410f100c2904010300320783c4c641c01038180c84000c3d1030080c540881044005140412a00076000f5207000302d0b02c44200141040c00c121450b1101d40300200451500e840c0d0903481440702015080400c0300d036065600ba403030540c1590045030f04c111404190f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 654612652 1250 654611402 654611429
    0x303070c14030313110f011e0915020307051b030d0309050a1a010603181208130c0b03070318111c0606120b0903072103020d1b030c0201090803060405040219 69
    0x5005444d40e0185c00300c0c5090b25185110007218000802c0746000701407006001c00d0b200f00340d01c00307c0c0c441c01c400001840e0000d82076400300d1107003600940380c1e4400101561f0510a0060029901c2c1035201d00c0e159464009004140b1002121020740107000441c20544d03241c0034940010010501050020500c2c80300028880c1e8190306110024048039403503503049225442181e141c1e0001a404060b50586a0643c104500075603034644003010302c03010f004001011810302c998001100c0340064090341c040c541c0f903102400010341c2c02c2002c0c01c140c4404d032400340195205400444060404001c14818080c8051018044006680703c000581d107081c1c1c040d11194500c2c1c2c0c3e07414240602d4520b05130b080204140554a03040041e111b2000043e0b075160803004000c0c9148440d103460340658116016682050014448120141640e418550b1b08032034800110341408000700f11248184559500c00340d102121a046403036980a120090100400480e040310203da0381c5060030070140e42d15002450102002107 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 654613902 1250 654612652 654612691
    0x10c02010e0f0109110d02061c02030604180b1503012003150a050a1a160501050402010f080c120405031201032f010c030c050a02090702030405011404080303070c140303 74
    0x1d2400c0e00b0794071142250b034504220000007403c044481405000100d60285000f41d40340001a19442014101c840d4800021141039190006401443c860300c07084404100351710b8400d81c1000c80040b2424000d00e24034600e400200148000b04c0341541f0700c40060000113101400e07065400000141107180955000044100202d00360b64840e400b0020f44280d58425495161402064031007031180a044078001c603044031101c02c0c502140544080c046a202d52181107500383c204107008210a03039061380094443c02602c030015001e5034059004683c4030028a180000110f00c0c030400c4080580215007601040014000c2c44009000c01170103140200310781c140908603c140d601034030b21039000b11452103070301443c01c02081c0c0c0c00100c6542c40b2030301400e20303d140794039500c2c0042c140001224000d600c4400b02c424459001d9001009c5d2051300c20a0300c58041d07032461a04168124007941c462080e8650003080015840c5104080315440a80300d1100e0b14208142e0f140d80302d08580040f5191400c6008144425 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 654615152 1250 654613902 654613931
    0x513120315080f120a030f020d0603060c08160e12070e0115030b220b0d03030605041104080a0f0317010902131d0403110f0604120e030d08060d060e010c0201 69
    0x10004140b040b00400c0c1020b0000081c82e110f00d41c1030302020300d00c0f9000c28992400e50280d0080d40816a502800310340e1290f03076001000c010005404203031902d619002d03030900d040740101a2540161f450b00c0341d400840c146040d007110751240418242e40c01c89128034441d10f4104080140301c000e4400100c0001c103560401404100c1940c0d502d8021040500741540c1100c203468000c040000c10b201f81c48210800711150501e04017801c01d010004d50480c80075106101459850b500072420740d5400c0b2411322400c81d80f40c11042541c040c0d03000f801d005810819480b40042d0368914013820032071003801c0106aa002e0003680345003600003603204441d00390b0009400321040c0c0c141c000c82c40180c031100e5204418031581100310340013090014030040502c8850003501c10714800c1003229400e017a403440d003250b91b2441c0a10f4078036851040d241042010911801c1622414034001c12005e002c4503080d512803070643c1e030385c1c1304005d41e200f4000720650799140c1c0c45d004840c04c10030030b01903218801c0f130b03e070000319240c0301c12a02c0303 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 654616402 1250 654615152 654615191
    0x515010e09060f04120e03100905060601210203151309030e01031406010f110a230712060203070e09011202090a0605060d1104090203010e040b090307030c030305131203 74
    0x8a440340c00420400483c41c12200d03803c0d070425004030400700500401e110a9030b10154810306c0341d40c544100540c245080e41160024000c0702c4c400d006031021612101d00654801003454950710740c8400784c9008168641d490b9015641c8180d05043d0308260304042d00114203940f00182c20fa4400c952150b2064040c5508001e507036840d00000e2804119070038005000040e1b0030000381840b030401a9103c4910283e82c8507a4040c09041c95400035a44980281e1400000c00020020702a40d000400c4116200500001c65444110790010100440740d628980d2241c00941c4018051424840254007003039003511510385850103041000c0072009500d48900400000541c0105032007009814000144003540340c4100f501d00c0060b0414011456a2a15512a400d80515084090100c0c40800005101aa403645c12402140204448400350702d41d66440c90700c0f4458031002401103158040400300080c421391040354013412510035100708190f155181c0b901441c01d24045030000f501c4406500c0740c01c0c0308405 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 654617652 1250 654616402 654616411
    0x51c0804082a0f040b0f0a08010b040609020406090501081801140925120507030b0c030610090608010506030a0f1b020706030b330406030f0b0105070209061201090515010e 75
    0xb1101907070040001480b205001400c40e8002c3e03866104400460712112a00d40d01e030580203015009454841707002078020504041114408d9040034800500002140701300d409885282d13a400108500703220041d640d030000a0082040106900d4410400d04401c2c4204d070a4182030000108587c00c014404910380192380c102c886214150042c5801c0030340c0050451411152248603421012105003003213801c10138103500190280250903f0491881c2e0341c0300045224103022124180da5034858082110f00f110305016080101e0307051401881313035180c8174001e10740c00500003002140c102000d04240c003d84801c1220804980851305103242c8075030301802900064180e5180401c00b009003000058030101d2141070038070800d01d1100d0146101c40c01080c0000b541340090000c0d560707855460788002d00803d05140d5000c80d080c0740c2901502a58840c008544044d6001881c140094a4060401000c100e0703040030302d4115940d401e04c080010f6401e00020300c044907219100000c56240858a22802400a0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 654618902 1250 654617652 654617713
    0x3050d1805010509100305060301022208070b0304150b04020f070303061a0c060a0f14040f0b0a0212180c030a08030a051003120507061112070e010f09051c080408 71
    0xb014404c90344802c6480640412a860045015104c81d00800d00910070303c00d4100080300356070221400031401008140454000200f02c030807042c3e60b40c1495180b4082030b14014a06e08208247c5600c005140c1c00c14076a0a1008000500d4205c8901d055001644407810407000f02c1d071070758410002c01c44540c91002180c4443e0480703038134242c503c0210a44804004040841c141d903180c021202c0c20441c3c0e4010050b03c22841054070681c00c06040040b003139090000b04480240032000050002d0720780d40261880805204804030040d258810700c0b10441080441030302441c8505003c03584907541c00c0202002e100d000d00040340e941d05240040700c09440d13004080d10360b070b1229001704000050014100c042ea901d130320702d845a21081c2070300d400e5006d0b11581841c11000f000225841140c5055005094050a07075074540c2e03024600c00d5801035410440380000b04000c50006641049182401c02d20b415481007104941800300c0c0b183d80e41c3c1b0020342c015800010055100008171000c202018424180e81350016 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 654620152 1250 654618902 654618907
    0x301050105010908030d020f0d0608031905070c0b03060114041403070b2d0706050403032903190c0f030507030506090a021c080c0111090f0108060904060b010903050d18050105 77
    0x4e10b105550744188883c1803042a07000a000f03e02d5000b000c2a1151f00c4040c0c001400080d03910f0780401e5a03504250260404001030f0030b0311600950043c4101ea105950122880000794500004807006401c001d01043c144000307102d880080248076002007000e011a40103840c1c482c0408007d040c0742c400d0341d8000f030380040d104001551109802e1041c1040501250406460440c0c050082c1a503501808800424450508083c00300301905900214120360303180e00d4141c40c000c007881c000c07000041c1c81201c550301074002818100d491a030032461781200600801a00e4041c50342c540322054209640c2d80705072100d80200345d003881084030510015030049103c80081034140859000500d000c100e07001c5404581c0400100da07000c1103407500580d810071400740000c2100303003a0032498000d03a91040d40e98030310540311240c22071003a42c028034206020381c0300540340b6001640c3c1c03540c131040100302206419060041c0d00c90004006002007100b0112034159036544100c1c80c1142c0581c00c10b02c80f95030041d60500000b03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 654621402 1250 654620152 654620159
    0x1201050103050d0917102f0307120c0806060a020f16031704210f0b0403090503060601091d1e010b07030f050405130f110c0a11030f070303030c020c0a080c03010501050109 75
    0x191b44462a00d600701c0014042d4090120407201d0315a414148440f601000e00701c0d050b24000d41c040e610928650700c49101549042e0314120481c1c0b2003100f800041514000442d45a04180e0301a1220008500454414103401c983c0103241c0b01c2003101040100905403000c2c820400c12041d18110080701c0c4000c0e50400e81050100200d5040e481441507003003520300d020070148041118484c047d103410522200d06400c05040c000c018440e14010b00e80a8030942011502c01c1d442840c998003280c8414202080b24000b4914840481d040584010b101440d261900721b140d4100c403001a0083c4646240280d413140c1b0382c81e0203050105c40c02501d0050000601c420000c54964110302650301001b410009812070740b91440710018401907400c02101b01c4041075031512608009440d015290003904129886004101019642c111840c144401c98010100070400280280c1081c44130001c540140d4a1040c1c2241c04a0b10051850703000300d449034445039034074080b41021302c600ca000d444c00780307041e088550a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 654622652 1250 654621402 654621449
    0xa0e0105271807091512060e151002100e0c03150906010504050c040306020a0210020a020a111c12020f19020f030a02060324040c0306150305150f1201050103050d09 72
    0x244e0703c1110104805180e9a170311040c03003543e20354240c120b8401d0802c510741c1c50f03a03180c045030542250348078000710001030070074558079048180382006481c5a00034284a19031130700d40408ad01c20000070481d10b1203081d2540149550034419505250006a01c818003807070000c41040c644001a403045002d180f40000b0b2060b030b00064400c48068903041880503a6462005404a25245080c00d003540018404104800550781c08503106070050700a030104030403801884108001c0c0741e14184002c02c400c200010500000b400c81c045220a19800e0042d1002c0d000072070600380c180f0400008031196402a4a080d404510300080b60000a010580051812002035804540c06110207800500e245080b80c118000500251082003404000a00103202c0c1954460026000c0d14440c01025903000c001881c2d900e125109215a41c0700e10410006a8411b900c0c030001d2142410101c00304a800000d880128105000b0901a2074025031041009182007100c0d424020328452554000005000241030b520b0407100 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 654623902 1250 654622652 654622667
    0x5030a080a0c0801060807020a0611040503010f05010b0d18051f050901020c0d1206180207050d140403081305041d120906030f101205030307090f0302060a0e0105271807 74
    0x401900302000e281e01c41e507c060f482c00396040300080c00709003400c00048034495000c0107001100c42c25002800224140d02902c0c00b907131424042c003035540368240320900899255801c050b480c0342c4c503004a00d40206480c1c40d25030034104484200c5040c031407076540c80b0a0079061403140700c2c2d100343c0080c0214288684901240d4451a0703041e552020040d412142404854030742e8054001000c0b462907050700c818a540b41ca00203074018034011307107240c0070704c0c0c200340303182c0c0c0c020803d075007500a000041502c2e080c21507542740c800380c01103842103d00340e411107004034894950344115007e81c0d010b00310b80d40c1c44248420206140081c22060280e15607001e100d202204c1d01d0303d006494010848c04640d00e91070f6902c0340400085012607202c030481100c210f124805100c8080002c50068400b82d0f20000c4550329030b01142c031b00080368800250441000c01030759401600c03d01e80c640381c1000c1494a036203003820b81041c500804005a541c1810b03184030381a00701c468500010041c0000f401c40c000002c00749000003000d400d41 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 654625152 1250 654623902 654623909
    0x80a03050901021c090b0105120a060f1808120c09180604020d1b0e060a0c300207090b0f10050c0a061b0e181803070f05030a080a0c0801 60
    0x1515100880c0c0d00c5072080d0151001e00d49113000d041da211409080400261104a0080e40c400c001d0400201d104d04001c00d0b00c0ca860440900140709413409a52480c00400810200744c0500d542c8404e040010036000e164003020360300039061551543d0211100101a210142c02c1c011030000800c183c04a40d02c2d812000400c4c031900c400c0e603440507510040894003030310031181c04040d03191030000c0e00346d2a446402c0c0c02c03202601c1e030b44e0307030350108902c01000380403081c130a021074040802c2c00b00602c1c40014885030210701c0403d0281e40070480a81900251507249c12650aa580144e000094103000c81c0a9178410403841c000220f9041030070800700310100c0c0030440b0701440d4000f003241c0000c60b00000307013040011486031035000004101c00250781903c03403d007c8200c08890002076801c1700418540c0303006c404185000c00014004000c907101c40d03d0031020118101c1980d20103000620020000c10300601c3c0441c8401d004902860343d075075503240010229200180f080b801e4525185c1c14001e601d51107000d00d07055 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 654626402 1250 654625152 654625157
    0x30f03050c1c02190203070b2a0703150e0f07060f0e03030f0702040b06270109140901050918030f0c010c020f03040b03070c0b130201020c100e27010e090d030603080a 73
    0x612021700209041c01059040440c0d912000280d29452586800c00180c05048101c0d440c1c0c181d44072603240750b80794103542c800034043c44104c0300b01e5070101303036190302c1420f40581040484030444482403105007810042d03400800492082071012a1050b00510788080040c802c41c091441e10841c07a0070070800d13005285002c1d00642d81e0715000c140580ba00d0381103a00aa00c0c400d82c00e41c2c171b05100c91b0314100e0700b0006044640020a00e40c00003507110f00325003903820308040041c0041d150340e08010920103007600042c0300c90380c400f0b0404014084020240020719408240b540c2260342c1da4504246036080d2012030310701c541150b1111450304030f0550084180c40039503002101060b501d895014088900007144003014155880020500c82c03043d043c0009252036910070f07001e540f06200c80900308450780f4501c09000740415001c0550300030900d1f0158004403100d0220805007812425038440c0c0c41d502000342c0065074441010418001010000c201c00c03141c00c0d206203000e2160302e0440d5039403241805012288400d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 654627652 1250 654626402 654626443
    0x1140a030e0601140f18160e0d1a07080c07111f030e0d0e030a140a0b090a0c09060f0e0a060b03090d110303270304030f03050c1c02 58
    0x1881882600100000c810741c0d021038071256140c0442d074001e90583c1c1c202038428903040c40034520904281e44101c041c500c40c2d080081059651540c0002080c490b040600c04005060218044503510207015010301402400b00221038215450b0000b42d8081c090482000d12a00008220600c0010011606802c1c0e11113101910410b4440c04038585481d4400c9007049403000c2030008008561560050302800114411698001507400040d00c66910452480350140c022040b0540411030743c10542c0003100002c01100c90094280d116102d0201c415509005240c010a6095060050a14982c40902102c0408104e0b191a00940c1600c002082c800ca000d20704101000036400240740d4821001001c204603866928501041220b4842c0031070f0a07214041802d00c3e50150b08010000b0a1324483d0f07c46214480c1303100d10700030917142c48915030940d0071041d210801000c00001d0413650120b020504c25100c280e10749640d18655410a52090407403907041d900f00c00031104d91903000903106a092040e036903100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 654628902 1250 654627652 654627667
    0x50603040803040f140709230103080d0b01021e031306020303071e020f150612030708070816080c0a020f031516020307140c10050703020303071214040506060406140114 74
    0x119010f1070100d0041450007102000150240c0982082080800105030108d07071950b07070380903058010802e0102400c000820b00c1203103a45070056206540d042d1050049030002d01c134140d151400d500200d40c1a0700540c00c00300c0c198910714442140000600401e001441c00d516003442d0007480d201440741d915005400c03240c1d521442034002d001c1d2402c410b4207a000d82e5030030180300c010200045d0b4140c075800e0149070050f010040c0c814021090b00c91880c2d1040c142854001140c580d1607540d0000c10950742c03008050104000000d016074001c1c40c1280282c800307001000300030f00421586000b06a815400b035041850f075203080840c40848640d00142c1ca12414664040d030440c04c0b840c50103020002403505540040c4d0b001c9620000032901e00320141200d4500c2c03400d8951604444600a140c030040260f4000d1010032403440c09024214071080751404002014041070041811501041d01c2c2541d49403ca101804003c3c140341c015500904064006c02c100041400300092080821a24101a0100108498 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 654630152 1250 654628902 654628913
    0x10c050406080a050714130f1205101a060d0606080a0218010c03030e07060908071e0909020303090d0837030e0705030715080f010b030403030c09051e0901050603040803040f 76
    0xc103c4031044071070691524800302031003410504501880d4080c8001c8c075000a00522800d0103c01c0703103680a00940100340c000c0a12034080d181d41c4592059090004a14243d02d450b508007400a008908101242207868a003020b4000040030b0700c6001640c0c010028084031a03100044540640c000f840c0c0f00c8182c04c2281800c6009000b5040e10744014040d1000008460742d0094004090b2607080081c0e915865580f9001d0b00c4400b07100001f05042041d10f80c0800091095900040b42a400682640d18101c40f000001f81021408038040711101004202142c2078040b044400c15001d166202040407c0c580781818585030b036041584001b01601c0322400b070b154070800e00854004000c01740803035002680710b03404d0941c00200b4001e0100010320003800250318290404040b4102d800070003180c5d00c0d68660b600c04a014140124900d0103002440c0e10005031500c40400345a0560710703541a00c4400c1030070108000140f00180d20680c030805c010b10911000c15180340c100c1e07800680c0b00401c00400207152030319 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 654631402 1250 654630152 654630167
    0x18030109150606030e1603120c08040303080106120b0102030d02090a09050a09051006060e01120e0706050901020f0105060631030320190b070504050301020417010c050406080a0507 79
    0x81252201401d01000981141c11482c20b6860b00d440601a4001c40b16507240c1c0c5a040c125141101c0a1880c01000810b08034440030701c80c0807061800d080d076030301c0301c4e240c00c40598072a40c4102c0000f990300c0c0c010000c0d5940300031020700c0740cad503440c0e424820085800c000039a84d014600407045a0703680020300388000c0e035a40414200501c6803810520191a0401c40c50009201410b002d81e161b0040b0541c1e01c8408040c0c1c4991030a59000b031301d481e010582600c004503200320304081c0c23412125582e4031038200c01d0401042080005c6c02d46e981c03070b00d82c1d40d00c024000a080603080b0034034000310383c1400140089540d40809984c4010841d0f40d401419003d00c892840e150041480c8a8803a030310040008010300d6070061103980d2007500d05250802031101031609603610014481e01e4021940b0099140000810318074840b0742103000b0389021414107071900c0000382260b025900c1685d8070401001e021143d01307400e000320741c031103409414518142441d201c030150410000410044120780d031000001e450034040c2c6c15 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 654632652 1250 654631402 654631421
    0x100503090a230f0109020906061903050a020f070f02030706031a15040e0a020706060e0402090402010e0619181d040f0c03150207060f020307143001030b0a060308180301 74
    0x11034200c000120f520320300911201c48181d02940c000e00c001202810301d48103d40d440d031404d00c0764006020342e010046000f894084e00344641c140c2c003002154501891200980111030086101a2114180b4410035240560b158410300c103042c205001c024820421421401c00001d080d50702e44540031282e880798109200300d4102c42140e428005c184034403015a540078040c01f0384100d204004842e102e0040a480381011a8000d40c4034400b203001030010351180010448094015052078140012100307564078038007441400384001001c9500c43c6405e4184c0c1201900100b0b41411040ca1141c0481160503900300010400340503007060013400e2041094400f24900115040070504200580101803200a035010200030744401c1c2c1048015048207000e4400c07240100081d417030b030782841011165420201d421403440e103144840e4520a2010003d003060a080514400707a1118000358150710b003208100750042c2000c4c02c054503010044c800601046c0840d030050502d004100500c11a0b100000e0240601c0c16 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 654633902 1250 654632652 654632723
    0xb0108150f040b060405100801061b0804060c0f0b01140301050c03070816170a051501020706021b030304090c0206041b03120311090310150b1e09060d020a020c100503090a 75
    0x8050b01f40b00da005460314140e405903920039040d000705104000403d082200701510030b0400308410800c10340102c2e2050f038240d01c034003420080c40a280d1100d00032500240d1003002d01e82403080200c5d1003442d080c480e8035802700d010032206045007004440182440d00040ca0500e02000d21400070490900071500701c204018402601500e5250500f204000303860161406585845109046480c4e58004140d14050300c456500602e507150b00b031840d0034052580c520b0710a1700350008000100b507038071050080c803040034116001010a401c0030307e040d2194001e000760307800100347d154406000003050b014000c888140c051030081018a48024072421503c0b074040141d6051140703041800350b004041d088a102200501c1040420580d103502128881c81010541c10a14070155608000e001040e400b030880c007400540003a0901c4051549041280c2c014051440981e105085440180c580124181158042441c0c19421400e01131040f543d600c0001c00000c00d0b0034060105000a101d098101401782d06c401c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 654635152 1250 654633902 654633919
    0xc0c0f02120f062802031b030627101a0909071b2a0501020304030204110702030a03050301080d050403050c0904260c070603050c1207120f0b0108150f040b060405 71
    0x3d001c822050700748a481440400035544c1c0e0003520000754401c0c0c0f1b11517103107029070080e60781e854282c542459200800050784208001310010603410480b84100410718460b000507003e051440400b240140d081d44044520fa071395524034090b00f00d04138251b4003240c400f81c800b40b4058544500546441420a0880755030f11144200e050030f01240d601821030205204000d2450604006500314000406008e6035002d64020401003006042c268072800c030b02c00410780a40d0038440e0607400039040422103c02a40025400b00040c0451034060101c00349001803404c101d4501403542e0f4901d612503c000144500c55941b02e0002030038030002121007502009143c1d2010b0042a08040e81c64498114049080c11b0f4460807601040d800d02a10a10380100c101c40c1c1c0c07172801c2c82c4400d420f641e0780b4a002000c03001003100d08a044c5080803082e000b2240d0811286902150b0003096400040222000034406960080303a03002c1070b0a1038071616981104124181c1d00800c040704c690700070401c548919800641c00c40c050 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 654636402 1250 654635152 654635161
    0x2150d021b0d12180b04060e150106030b030a120302090310111b0f0c100905030d05192c060c0f2b0503070e01180305100c0c0f02120f06 60
    0x810400d1100c4865281c180b00314000f10b0307002c01200c802a00c20405100002200c001060100302d1250b0300610941c0c010940d00c0041c1040340c2841c1100d40c44144030410071005102041d01130050b550108000e800404802001e0344031288003161880d03140c0d05150380010700c541d03540c41c00d010803003c0490401081c030050080c1600021b096101c515081c0c2540c0200300d14660031140840c0100c078813a0041c00804504039003030108501c03c0c1440d20800c00f480191040003905840500554a40e801c51307032681c640711010742c9140c840c00c4100b06030600410003218240a8012a60503000c3c1002030138250000714080180c0c081079041c403071492001c443c0c0c4100070700181c2e5a5070014005000c450394411400f002d5607445c0e661105060038030858404507100b0f000003103100d441569042c201c400149400d108407508060404000c0110381c201340d0b119044682c0c0c0003441d04150040c600c0d07550181c0f03000b0800d40a503881d8043d814991171002480b55030507400c01c1c00f14500030408019480102c4042d910700c0e082 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 654637652 1250 654636402 654636457
    0x5100b0703030f0504230a320105130212210a051e0316080403080402011b0b240a0302010207172104030b01050904050d030e0f0a0c0e0c0702150d02 65
    0x10b035500911780896054210341400034080358a00d0139580c0160103003100c0f0844c00d040c000c070003000b4a1030408154442c078048c540766024020030740903034066810703422038204a00602480d0540c803040603400d81d004120758078248807424550900032040e4488203840e9200c2040854242c0f05540321100740994444482d4490340c10302e001503000705aa9150042c181900500c2624090300c1120080d01141c1020f001802650046e1800021421a00d14040013404595204112848265414078040a0b24a14040405030b45403400903841400c070b4603540c45501e10742c0000c1d40c54141d40107100e40e100001c10070030324684082180c4140034070482c00d00c8000e6040e070000940540c0240c801a54981108400007070035013410101e0302d018a03007103006000ca42120100543c050002003d0039070b40c034403520341416608c12003400300300501445034000a4416160141810a08401420280c94940108403900041c4d03211588003070404261f00b0150b81340d20340d0724610300c02030094100f0040925107890107400340f00c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 654638902 1250 654637652 654637673
    0x601080f101805090d1704080c03070b010b0d0e0c0a03060218060a170619090c11030d09110f030703031b0206130815010503100e010e0709060806090105100b0703030f0504 75
    0x2c19480443e6400c2c0c900c0b1408807000754000000680c046c81e540042004100d1000052003a0980841100d2500d50142c0d0768520b40b40d001d03485040d0148020405c0d40025250740035034100001048000d0031081f001c80c1c00640801020b22000b0941d50340010959115004480310100310900100f82d2a25007989040c0030f081d01030742c032800d0103c00150000242092038801403042e0ae00b118482d444003410304000d01c0000410442d40050180800d00c590740441840070001002c014100041c0410214540c0c40c01c07000443e40c00c80010301c200100042c001e401e81700010380408403500341c5045c2000404401328845400c218a0001e50440350011703010083c02c04045043d0211500b00d0101d0b0403c0881c0a4500c4050001380078175541900f00402d408040d03444c2d0303000580300740001c1e00000340b56200c20039003924103600c581c01044581d464107010400c04105104160740051010003c0c8a0361421102c02818030160703004080024402050700010301d4440e40c0310840034010a0403c11203410075090884144 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 654640152 1250 654638902 654638911
    0xb090c09091e070c02030309130204080c090f0403230705071404181b0b04090609110304050304060819050f10060f120f0e030307030608010b04050601080f101805 71
    0x540301035000c01c1c0001c07030a225081c188144000100025101c824086134134984004040e82c2c14071090048030b509a0701c4520b160004068000010303034a528055510742040b010b9207046110b100c011b03003000403e00000b00f103243e0080d41490305c0c403144941d6070070005c1c1d02811140460102140420301004000d00010341d50159446103c0c2c400e585940b80d001c0000340c130700481c082001001c824201c0c41c0050140841940c2d00b060511f10100d07480d4a54844004c0c1d904143e1000c51000c0c1c40314010040d010746440f4519100300ca00350a203146240944071160f03681b2552140307208001c2040d0000b800c10701c041c05000c1e030004c00e03401c0c184070340e050014050030b240c1020741e040f8140441c2600300103100e5000744902c08080c02d0649507007106801940352000280002c2c180b040d0000e1320303845103040c1810207100540c440c0780c1584000814a060401c49800c440038054064010707868070b400d006c4162f8100501c070b82d100c0007441c41c0012903500e81d6403680b50303a2402c3c0c0c0101242610170100c517800c04c0541d040f00307105 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 654641402 1250 654640152 654640159
    0x6011403010612030e0108090705040920010305040201080f040f0f050c0102160510050d0f1506030507090b07020d11030105090c13020403031b03020307120302030f090604020a05010c03030b090c09 86
    0x1a5140d07000514501c0c0c0c4a000240440c80e0622802c5c0ca40d40602c5600e98800354180c20366099075640c10102e01035941c90340c0100c6040880c2002d55540c1d894a05a030010b0000a00e020881751605a0020b020f4000140004180e40a50400102084004400035603e00d512514252900416251070303a95507850088850250003810100c40401e0b25441948003110001803100d980e48240000695181d0b00000011003815290484d1030701c14021802006500ca6800c4028403c4901d00f08009044a00c060404001c0212180040001c2c210400c20790309030300d40488184204034502c2c900000305190b4150017035015401c0c00c0421003201004aa003100b03106c420b688850440180307080034001c0b441079000050109040c9094070800601840784042000d02c640100c0789800ca9030744854a8041001c110b800000350000f08010101c40c00600f100c1d003242181004000358286940060440c0820b80221410042d0ac4c080c28828148203801140403840050f2140d800c50501000d15480b035070164014500 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 654642652 1250 654641402 654641411
    0x51c06061d0721140901051501140706200a080a05010f271d12030606030a05060607062409021c0b06040b07050c2e14120f09120708040b09120601140301 67
    0x4101088c2c40d920180d1340503550689004a10841400c2e9608200e10030780d03e581c1d4902210130300078501c0c02030700a2045640f003200e4540b03d50030300003000315078004e10302e100c2d550400c03004111111004442d0010b8039004034942201042074000003004003d81988050007608000030300f021245451038103800b000402068840103501d02441d0940e603c402d40b60544c22000400c0040c100300342c198003080c0c001c04000c050f10702d040c01d507844410503103826290a01c0f03950701c50b131805000703803e110314070900400f01a20f080d401e0007103204d0000d0086d441d50164499a40d210494040d865a41c0c108890207040e040b04041e450329000e0a00315a00c0080081c0c45004440b86002051440c0e41c40a0f0b0100302c1e02d0780d4100341c400c550b0035030080f40d0001c01100014100c1d502440340c070a00c00c8441000600c24004c851600c0643e1500103e9517251801d4070a900e0a440b00400401d004550351030304481c182c0340310f079201d655100c07440c50119a5103411442d03004c0d4580502c000100300358200c044046080c1d06c0c210000d00c0f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 654643902 1250 654642652 654642661
    0xa030e01060902130e06030a050f0606031504021008090f070611160515250f11090c04050405040c0506040e040c0816060c0309051c06061d072114090105 67
    0x4224804c0c0c0d42e020503642015141004071360242240280e00807405400d8413500c1d000c80c1d07201ca141c1200e07400c192910b9000b1000b00111800d003000107509000b84000e04107403905042c2c02180b109034044e901d02c410484023400180c5445002c010011030721527100e00b15485039654400003401c6030500032404040e4001d6000b814903c4881d0440c032001d4540c000d1038629111401040100f065103c861045151803445140b0f2440f0f601c02050b500c460b40c001c00388601e000f80c161520f4952118003c64161060301031800703100791600c107202900c0560310181e030001030648441c14200340e0040f107548429801000054040741006481c141940a42d103d044085000c5484005c200d0b00c4489403941c4c088441c1952a0820480c0e1243c00301907401800380c2446034003551900081480030711106031204d02c40d40058014010041c442c401c610040468244101d801c9455000c115981c2d50050900030400c90800303c3d200712850450754896560103a95400c1088500048074142054000c50390b007080355103000d0028 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 654645152 1250 654643902 654643919
    0xf0b060307050909070c081b1014282a0207080a0b070c0b042003010204080c150f04060206060103060e0f040602180603012607180903050f0a030e0106 66
    0x60780580a6600e400e4100300d003040511558078401001c81040140780d200050109410900909551500ba0803c903130700084124220b20304003c24645013100c0f490421403c81000d039904100350060960740c010020305201a00c0244810102c18280e4801071401001300404007105800c800040c80344805d902160f100c101090384c07160700520407808160401510200002c0c540044503500c00000e05041003000b034603440301a400341c1d04842c21100c14241d00660000e241040040c41d03450130301100203529040c01c0061440d00c3d100b03180c00385801662041040e003400107501041da180407003985140c03501c443d03451200964400303041e940a40800c0c544440843d02e00004103406102d241d0018400659840b81d58442c8001d41c400c03049540203034140c2d03181207400d0740c1c0c4a006500900210340959400c044280314007036544a40c038040359003548501c9003001719490034512451000e00c0c14ac00042c041c1d07281e0505607028464200c3c41320110100040d69a4019010350001c1600181c4e44000c010003910b40c03869 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 654646402 1250 654645152 654645157
    0xa0c0b0a1413080616021231030b0a0216060504020609031c0810080316031b0609060f020a02070306050a0b040e030c0f030a020c06450f1503060a0305100f0b06 70
    0x40a0040c1c0002d07c000d0505540b0400800314181c040c084180503600c800b201c0303048d541388031000c0340c40150720101c1002400401c44449401800c900d0301103190a00306a5101e0b80c400400400400c2542c90380c00150541da41d540c1035440c2c000e0082c2c20f0380c0c103400fa04000204550003548035440465048408038010a02004051044d54240c1c00194940280a00c95032440407801104a040000084003a440140b840305042c031b44a03c00c1c0d101240c039000910303000007a00ca102841d4040a8414000040800c2d03001420f14202c9030003003400a00d135143c00c0c4103071010384041c64401d5042818101003800b070324000030013060f488100c00261849010303220b60050f282e1040e0482040181c2c04a804028585800d030020180100e0a00c1c0280007010900d44a805c8807449103203140c1004040255201e18411190f404094814101e911481041d5924005050b542d00040001d41740800480010b006441d03040d03181000e1b640020840d0f0701c036040c030b680a0002e4814008070464003410080e1150031030906005 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 654647652 1250 654646402 654646441
    0xf081b010b06071407080102460f030209032a0108010e01180603060c030b0109080304050904032f0f0705180402040207051002030408090f030a0c0b0a14130806 70
    0x1014508443d58891288104a0303c41505543c011202c0006a0310700074401055141c0c100502c15402e068180300444a08003600040e00407100958603221403e52041c0100201c0b54040c10401070300121001700320000d0241c0c00c01d99405204144516a002c0c03080444102c0300c501d142140040c0800e14801181c41804c00e118a60082c04404014459254030014104c21060006400124140d13291140d80070740e02c05145640c080790740e400d8031461070f50717011000502804065005518003460031000c940c4c40b1400600190030000d03c0c40704640540d00c440060010008111801e80e85443c807d000036440d25100da425003040c1c4140c15001980c3d06104008140300482d03040e40d010150303030303e40070301010350720503a81114070380500c0104807800c01b601c2c800346001314005c2d0311064940d400b900512241400502c8154829804800b0301c100003505d02d11080207440c200700480e5140c1500c0c0078203a81c6140b03851004200d040020400b903541d40f540b0b0301c5010403240031204482c20b9803101041420301c0e4007100da = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 654648902 1250 654647652 654647659
    0x302040f1410270f0e01120302060f15040911090a11040b0705070302030f0f01050709141e040606080a060e06010f030207030e0603010b0309010b01050322050a0f081b010b 75
    0x500510381d801010010b5031400f400ca2881615400010160b189807000d411914510b0b416050510003120003000c0a0702400031141c0040707441100c0c0c1c401942d01c8030002d1903444101c0f45800000c1590440580d0705480c403034082d00901000489242030148285203581250186020600048101000303006110f00d40c1180c2d0310151401d030600e401d4400d42e9120800035203071840b031080c001005880401508404080c0280509410702601c20000c1c00e607940035002200b007002c0a4014498285040384818406104950405a07a1500d50702107403c0c481082c1940c1e07002d4580400000d05541140000d8490611007008111154603240c12490000098903818002000040c3c003004c060f000340c1c02070100d03034001e0a26182c88610380b40052020b0f802600a00ca16410101c24003050000c2400340300010902420051304518050b500c515456444804c058400c0f0941c034046014460140040071821340c0200820800055506181e55680c2c440c21101c03050400e03030040341420410612030311a103030000a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 654650152 1250 654648902 654648919
    0x1e0906040b0918040b0108010b0f0a05060c010f0612030318030903020622061101050f0108121b070f060f0e0a0b0702131a03070f05060301060f090807060302040f14 72
    0x2840034940d9030010038500b500f04444601c54540d150701c41c050248034601c201e0b1058101c5d07052429590035655542e00c441e006500748600e0050315500c0109500544405543c095250881c004029001d480f032440c4a0907140d152403404615007403403c800c1f000d030f64003980702401503040040305400040c040f05406400110209001d2006203001802000c820407038a2069128044105885680c88059031102005c2400360135840b50050017070080301d0740140b2044c4208950740c9040d03612611060008440203c4880001e83c1c0040906580d40d101c0c0345510840071191016250b600c0030b840c034045401500301280c0201b054001d09031103480328101d000e1014000707505e190700c2e110352036409400c408003c90740090442910824117046105804260b04c0101040110031175840c1410300b01016a00171a2400000c1c103000d00c2140c580108407411140d013858882038036407100c44201c8919a0ba40c00080080c005d040b0000b454a5143d000b400a41c1c4400888001403a507407106616003000c400426604098507 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 654651402 1250 654650152 654650159
    0x30e190b0a0c0203150f010905010b090a051003090605090304030302160f1e1d0f010906050d08030601090308030106120b011b0b1b0705060a0606030b18040f0f03051e090604 76
    0x206075010510b0f2018084504600c00402105150281140c0c1d80418400c550010094404140541c0c0c0c0180501c0352440d2a00601c2004211010100d000301750040c50b2a90510705114800d90144c036a060b0000400c10003406d0050b00503413250701c00e102c02c0e0300600c1108407081c40704030448500011607146110311140d0070b2405107612045010044160401a029800011003480142e040d92142103800358404580c603203051000101b260603040030404074503188081c0200d40350140b0135080150002000360b00d03070b511400100c4401341e940d000280702190210000900c0d6400c00140030490400c071001b8003c800c90030300112140e0303515a41f481240503c0211440100361620b00940d00920101031001401d00c000041e004030303600ca4142220355600c40401c10180f040c080c40b40c8006030040c0d141c1404407030b00c000002841402e1031490103104041c2000450104408a180926004c1c0d100e070400002e2032107400c0207032954100000c0c180c11b03010007044500700e4401d090700711a170002c0d00a2506003024103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 654652652 1250 654651402 654651407
    0x30c25060e04202107021e010b12031c09111e0a06020c040e0d050906180d060507030510030c180f09050c031902150a1704030e190b0a 59
    0x40c8240150000da5801a0010030f1002c0c070001c2c0d00403014002c0325603079000f082034000340502914406a1000d026203061154496002ca10a151b01c17400303841c58013103d0060340740c6c540184100c0d0700701c0c1c0e40310a003814070600001000c0060992900101c68112107090011202c0c0242c50f150100101108601c00415900b868001c1c400d540100c001500c400e044284c0c4004124002c0c42c5400c100c015034003d200341c200501d440d010b150700814a550250040060004d0050514005d2101280c4140d90100d01151901c1031b01c04452450000180400011700341030408000419040d24070000090500b40044c940301101160141201e03442040310b40790b64600a4004010f50f842c8000885850b1a00c000602041041c0500d003d1140108050f01c00c0e480f94004161800140303540f4004840c044000300805a52141c0d00480c420b8405050303142c0d110201001220703d003041d03210852030040c4600502007459400b8080020304803040e10540b07511004460150121324a91092011600c0304101d2056040c4c0b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 654653902 1250 654652652 654652667
    0x30c1005061509010203162a0f2102042d0b040614010f0e0418060203100f030c270f0b0906041107120e0d11030d09120204050c040512030c2506 63
    0x600072000f05001c03886011841c0310030a0948441e0383c00d1040090140172144005271203070000c0030b207000b02124030a070f6030002c1801c0d04520500030340b0031541d6010900c023144500700d14003441140c2c15550b0070007041c40400e0400034503804114600442ca0550041004480590550171201058603248040d102809007158480740c8011910740103500d510004050300c20541810207403034030400001d80c603032410394103000d0f2038942940301551071982840100003158904d8440400d5880c0b640041d203040402c2445640780901d00d0352000e03116442e2005480f0b2030328003940028a2107200f103d0b076070f001c0e0321420100f00648502209403910000d08100c4000062105c501d640380280144c1080c407014030703403440061030100d800b07441a94400765810018400d49020702c0110306a1203181000c0c0212030829007400f450b5260b004000b030165a40e031001c1004000d003402918002d24008014041340070603170444c0c40d22a0001c421070800c92092400407446000005882241c07850307845031606642e46404400c44880 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 654655152 1250 654653902 654653947
    0xf1c05030409060305030702130c0f111e0d0305070807140702030f01020a1e1728020f1804201c060f05010f0801081c02030c1005061509010203 63
    0x91004000020b4050400d000c0d900040d8014005191030b0103a500500850360b140181920b1218a0810b00004c240e4002500c01e4030340d40c40d8504003050414144070a441c115000c81800c110814000450075680c000140e1720244820640d014416512403007011b5548181c10742d0400040364015009280507090400900803a0303000408450020f03807414030640c2280d1141d90504002181c0002c00c00b42d001402c1441003a00c1600c1c500700c460000e2820a9075041400640440c034222260490513209a0800303250340082d410400b411981d80c0712002960400340e01030a42c0003402e000041d2070071003d180501c5111592011000b007038138028200719420590354032103000c407042c1c100c0d42d40314265100080d03c00c1d100a443c0c010030341c44500b03061100262041400350740100c00c10400700018480e100f0041607040f441000440000004115210140c1c158000d10f10401101d100712130994100c030b45070390405c40c0118010f545c003414540e40480c0c1c8404c10720030000340901682c810007840030007042008840400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 654656402 1250 654655152 654655163
    0x2303060606130b0d0b0a0819022e03020c1612030c050a17030a110a09061107081609150303050f092b0605090f06060603040609050d03050103050c0f1c 66
    0x2419203d450b00591034001c1004c10032041d40d034054001150803d40072590282c42e81ca8014405100030390405525072550b001c00034003680c840200f0802101c40181c8003030035009125592228100008002002500191400704c070300e110340d50403815098a0640200196902c8024902d01446d15407010340c2e1003610500101d0302c0340b18500141c40419507442911080300e105000e00c6036607042040350202074030540e589004080008005403c0c000341c005000034215155820051a011a034060395424030b040350b840f40d1182c1c016886290365880c000625501a40e1921a0030801c540c04c003083d01c003001502c2e0100030301184041120003180c030403101c080c0c071140000a0104444410703890b081801110348543c00700151011500708010003162b401015841210a0000e20f2080480c56549581364406421307a402080000f02040c107004941e0041541ca64108088841c041604003004000303000034403066845000310700802c10240f804102e043c1d1a00706c010010180001c881c040b070304102600d440200d44 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 654657652 1250 654656402 654656437
    0x1a0a12170d06030314030c0d050709052806020a0c1703090d030f0825080901020705010501031419080f1605010606050d05250804050a020315012303060606 68
    0x41220550009141030038000d00d001c070362070349913203406007030f0420003d0301e402100414020042d000e800751b0f0603100032441d03000e80841e19468002c0180c0e01300701107030401c1c0e0300240b00d0707404040d03d02c0c51841d440c1030f284030140101c0c1e1420b543c0d510490716401030a00042c10b0f0030410008011003015421000c0c003030075038001680c0c07408140800066041d60003950440200301100c0d00e03449001d4000074001c3d8000c10703420b0150b0b404490910050285803500c180b40003407040800c0801c02d510402d505a84a0940c410b0080281c1d50312414035404040020555413110b00c00d10f4050810124141c43c0308032440d0340041c0031400c0080c600d00c68012600241941c07049078000315418004030f0424090301004024035200c660351040105070f0041600c100a0400c00311840003804000c1901e0403100542400c46a890a100307940c4071460000e052051901300a51f251044014956030240007001060490310741d0304590221607216030301c0039030700c1c04400b0540d945904039200140035810450018245681120541103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 654658902 1250 654657652 654657683
    0x7090509040b04050c0a03050c130204090612020a1202010503060f0d021e0a080a0203060601050a090915090b100228170403060e120313020f040207060c031a0a12 71
    0x4020310021902540c51000384010700c42400014014800004010754039000403d0a58035080c1d17441d40442c007194015154103499414411703566042c3d03400307440a80c20038814241d6800140d00340540c9804268441d9032104000100280c10b05003201c15280e040c0c41e4039085554007400c002010348404043d42e006407000c040e030001aa640403409007800707aa50106100030361442c003401508281504080c500358403495119015a03400142d8542c0302500f4606640d4030400420101c030034104a0740030001090030b084a00b681c03003200f103000e5019141014010042d00a0300d90420402c1c041000481025802010052088805014266095060f811301150108001e541c6004034140c0c0394054640f034440202e800d008002c4140500c11200751294000c1c0ba41c4c08020442100030b12000e080c54442c1c1d51060008411521780c288003107000c0000400031912402e6500b800b20107031150244141c0081e107040703188803200e800e1540d034003985080503008a0440d402c0622240c0c920300b9441060391054806da1482 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 654660152 1250 654658902 654658909
    0x5180606031e0708010806090f0a060b0316080105040302120f09090603011d01050916060906030f060b1c05160504180b1207060807050f071b15110c0901060804020603070905 76
    0x164024420b690395004c43d50300d4540c40e2410410040c250003410307002981c42104011000481e8581d81e90441c00002d2405c0841c000240f13000d05043c1e0001482580f02000241da00d019400700707103d03500940a43d09420502c071000546c611416029803c1c403071041c801711444d030034881c0c60540d001c60060300003c4e1070030a40c000c0c5c01c0d9201e110400c51600d0381d1128208035942e2002e20194200980540d00c40071000e00b80300d40a8145801ca0003039104050342c80c20007100600d6241c02007002802d80340c50856440f0412002c1c0030000f82102840c408241c200b10100740819a01d0880515005007a59540e0a042c14415507010724a000b28400000584a58000d08540c0d40d9421007003055266000a00c1d40c82e2404030007616000c001030100048c0441404400050141c22040b140480e0740705442d2001503200c02e02441910001d5000303a4680300580940140301c5800c00000043d05010008072001c4483c15404c20820b44401d01510b000141003002080050a14802554003d440ca0800c3c0b084542c803103001c07 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 654661402 1250 654660152 654660211
    0xd140a02091305070504110a1d09010905181507030908040302100906080a05060d2a0f1d100e090f0a080d0e0d0f050f0c070815010518060603 62
    0x40d1007180390b1010080030800100920401050140d806102900388005000080c0c001d06200005000019695403c1140f0240d02030b1007120005012a0040d40c455800b8402448100c5441d01507003a01c02c20040007100000b104510100020401d140d96901d100c1e045000e04480c0c84106d030701c0c020a00000c00141d9030100540c480c0012956482245840c1c818014046900030300300c501c0d924640070901001e9146c005101040380d8101c0b42c51140c88004542043e1101b00d40c194800d030440c0700090219108280686040c2246e140700d42c05d111845000c0035803003c0a10a4030048861034008200f000f10207002c409099110308000f09580015680550320f5083c4140a90100c5110f240001c01c416a00d034148501d420140150004100e242c0e101403001c1e0242c0e0281941e41c092040108890301c2001418088070b0300d201d0000150383c41165100b06d40c540c2c0e002c528480c01d041555110000c1420306040080ba007800c2000081c000c41901c0d10360070302a090340050710a000c203000c601c00c00d0700c5021403c00e4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 654662652 1250 654661402 654661411
    0xe030408030a090501050301080a0807020f0d0606050a17150c0c0307030c0201080114010f03090c0906030f0605181b03030906040b0d2a081005090915150d140a0209 72
    0x34590b02e504001005050481c141c124506000d814801400b01d210300180c3c00d60240d034017402c107030394070398460000032076403030310000102d901103070f40f48d424000c208580c0c0260048400c01e8460301040350b11030a94070030034410700c8949c182070f50241c0304c4820001221500c850300030081d07034401c43c030b0030341da4442d260700755403005c00c1c141c0c0404c0526600310115680b06080c0c40c01002200860340c2a800c6c20310008150305451203482c0105910f07021410280102d0307004031001000003100800c0300d07070b940e45011200510409420350307041d0315000c002004000442c080d031503288010b20240000d602e200c0c4d41c0400c4c400340000000d4061000b8804580c80362902c0d0010300c050280d06d600c6a45914102d00d07000700303a4100c0c000c550140400310121800c0d5149034030100010b9090b40c2442a0150707220b10151070710064690006a01c00440d50a05c4511080814414001c03030b000040c04d1407903620074241c0201c202016440c150081d0030042004042007030000c60032032084150003552410750f8280c000407285001641d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 654663902 1250 654662652 654662669
    0xb0c040b04060f0207060203040b0301032907021b0a082e0501060801080d030b0901181503030314090604050705100215070908241f090203091c300e0304 67
    0x240c0300d409013a01044a03c00a211070f10003945450708002c4001c4090106110050651440c20354411280700018003410340c0501d034280e4500c40e03190204000303640b0109000135104001614510b4109400e00408030010b903140200100041c0510300c000d0119050501c21100e0502658030030b9210052280c09480d00900040e501d1000c00d50520100906158140100300d05140c0780100c41c0d0382945840c64407030304450305010607540c42e0744110407070790161a03d404854440001a5004400c241e0941d02c011300f104c040c004100c100ea6950618903079a08410388006c2d01135400348800b008686849410141e070b540c40e80c4150703600c2d0000524020001042990140b021494104043c00407250800401a41041c0e5a86130f0300542002c0400483d90480601400881c44202c8607a06804240410010080540ea1000c66480c5000e00c6007540320302c8951615104c554601c6242c446003842145503407004d003c2e842001d40c7c8d009044401c0404a06403160b0b0100070750301c0d200d1001c01d000d02031010303000a12502 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 654665152 1250 654663902 654663917
    0x11040626070314010e1504020a050d061e08070b04120609120c06051501080a0c0c0c0f030c06091d25020304030c06050712030504030e15090a080d05070b0c040b0406 72
    0x506003e405910503000742c91550300490801080d229241004040000240e9005a68441850045a591051815150b05a0704002c0006903410328000466800c41b4900503c0c1441c0d600c451490740c0314103c521071141208420700090046900400450f10024032800002071000310035580d1000c0008007441010110f0107480240c801d1004502580d40e0000911408000402d446070028041c03007405069a6000e5984684034820640503440400f19660018160002c00d035640d95100c0c90450613000840c0d40c1004c0c21000a201401030301240291804112642030708581e1074058803d0a000406076901c100f42c00d0350100130034031441a00c0303440305180d90245950f94103500700029151019406501000010000400410750316500220041500e01c0c0c0425142c0307031428201c030458a15a1256802403480145107295007141e4001e024254056a100002c10750742e000c202e03241d2500c0c4082c0d0021881c1080074600240384407011070f60214881c1032040c2403a07252030007101990801d411003130108000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 654666402 1250 654665152 654665171
    0xe01090c03061d070f020106050d080c07080601240215131a0a02072604052101150e0915060609150f0307180f0b0901050702032509110406260703 64
    0x111700003c2002c2481d00090001600e030030049045030447c032402400201000c5402c4c1d0000340207018200090500c04221a41561034107100b61410300d03070340400d0f09010f4402003440302090001c940d640d200c8c4880541010f8030f543c0c81e4040022000d01c040c04440d91701361070643e40040c0c4a403601c0d06010356816000103840ba0b05505d000841e01c503080d1400b40420b005030b00c00c040d01c2001882107505480d0261000644039002c0980405c18284135003140b5115400e103002411400020780742c074001c40f4000100c0002e030361950020340b901c983c0e8400301c0c00d038480458000205503042040c01880b2050f4003070712040c1c0859013010011810b4101c1e00011282480000602c1025039102c500c1b203418242c3c07020b001c0b09152034007900040d03519003032085a0400c00c2c04039400e03400340c1c004c0040e51540798004e0705540c03c03011041c0c00006044d5800c5980c80030861022004181580c10b4441c40c8036442c42140c10311300d00f81c02d0640c140e400e611560642c2d4070701d103045140412989a01000640109000d0700c012074403018 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 654667652 1250 654666402 654666407
    0x60503060a0801020921190f060c0503190b030a0605040f052404030c1106030a0e0d021902040e1e0d08010e060603060f010207080106080f0106050a0e01090c03061d07 73
    0x6042c0d116107083e130700500102d05142d03205400c00309142c4401342d43c0c030000500d8442150401000096a18070515405010b0080c0480d0b0181c9035011841402c00704546280c034101a201c5020640c0c03060b0f2030341880c080c3d00080701140d41c441c1091400040480b002c80316a603941c0b9050700ea00b101e00f01c0b824690030784880c1c10414200030107400a00245901808105c042040e00c204410041003c0c08021040044a040c08050713483d0802054000e05031030780d60700d888110b00c0064010a03d00107583d1055004828800340b000c241384400524804101c2c40031900e9808000141c2003841c0124054081c0000c03218408150003a202c807400e1110020f84201c48103510043c0040005070700090014402d1420849560303901003c40b6407144e8201c0310040d064003007070b0040340740c5000ca400c030021a600e0a0000f0507545e000040310038480d0401802441900d40300c109000c407010f15482440c484004100041c4005103241e08001c64040e040e1500003943c81d9940c890450001c51010f00c01d400000700707002c1c07104655 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 654668902 1250 654667652 654667669
    0xe03130b070203030a030510030807080702120c0f1509030706090f1a040e09120307030e011113030b090309030106090504030f0815060a02100603060c17041a1f06050306 74
    0x68540d001400c0022980100e5100d103e101c103003104055880d000035110482c40e00f04a006150010a229284c011910784140c00703030700181c4168424480350142e03404896002944050407000502140d8914134000140700041c80d440000f1122030600380400780c0d054030b080000d4002060b0359504c03400c180c0c1c90512800300c1e5000e2508080000800c0e14540343c0140710b20f40c102c0f03044900580c0218002c0d524400c2042c06c0c0300301007070b031001f00c040d00000340f0500b25416000006c010406100801c01c403080c03064000f100e8810154810210b10451208002140401006c55031014402c01aa0300d00042040000d00716200c0d5000101e2103a079070b1088c0424103034050286804203049003481119418034a081c1e0031039443c22214984038500018000302881d00c00c0c40600b0840c00c14440500c0301c1602c03858150003070424081140000392200891201d100110341003036029039042148030f1102d4030f6600701c1d90861100102048040342003619098500700544404c81c00500c0d130b80c0d0300c098803424040c0070000c02c00f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 654670152 1250 654668902 654668909
    0x9091006080c0901050c01060608011a0414061e07080711010e0a0e0a0f021201082401060f1403090d11030c0606060d0e07080a02041104060c02150408010e0313 70
    0x5009288090021a4001e5611604901c140400549503203001d001291280716400540f4115424107400140b620341184485041e100c01009041d070400911200d200342e80141d10880140c001031040c0081103080c8100104228180400f900d00041c100151040481d400210100c032030340c00010700e444c1403107161920100701d41402d181819480b01a20002081c41c0c6442c0290941e0b0b0b900d42e0045a1032a40542c8002c0604071401c80664840d090082e044081540920510800d0b008001048440210806251204594140d04090640d0030980c0843d00c0c249000d2000c03007407104480c504205a03010401443c443d0310040d00030300c2c03250500d10005041a045c02c2010213658000d00540c50301210211f8502c2d84407070250b131481d881e01000f0304e03010301800d07400407942228000c004000c90400c0021901c002900c1c020348080c031003d20b0404910ba0184694400e1030005400c910b101c000514141e0846031b10100e0841505040030b1720f8011441c212210000210441d03400000c1d00c003540c204004001004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 654671402 1250 654670152 654670171
    0x402030114040308041218170f03040e1902090d0b041b2d05040c0203030702060f040807020f2d190305061b0d09080a2705040902010306030b0403050909 67
    0x280c142650091302142000d0b100034111300141d4842255244a08000419803021191724861550345850854004406140341c0102d802424000d190354600001207038211002074070b03900c5066070380c800603801308041c078905d02d802c09800f00300545061b9240c8203c1403096000389844056070402e40341c412002411142904841d0039910000c104804540d410a04003214024202481003e40e1685c425082159000603034818500301440c0801075000018500c10f035855000c503040c545a0a00d07625074903100301c0300288110b000b006070400500344480c00c419000805044114038071b0380c000a210205002c803143c00741c00d048000c00301245203020508000d0211640a40d0502d442c11030b00c0e62030301d591340104a080c10000c219a007000100314070044a0341950900000c00102803141703401415544420701d082e0011300c0305d21406040b020030101094404402e48001d108080c6030800b400050008010142c1c18556a424000040307200000c016202d0b81c400c0e0744141d5240646810003807404005841c4140 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 654672652 1250 654671402 654671441
    0x90c080601051c0b03030f0301030c0b09030c010c05010228021009080a080c04031704151b1509020901080d0807051611060d0c0306030c081b040515120604020301 71
    0x1469800070304070741c101101480e10b082140c02c03082d80c3c2e1001d004840201c9800d80b00000d103400d40011100d020314141d0740f0810420500c40e0f55140151240e0040401140c1e040c2c01c0b1941c1304c0c08540c0039050000c0307402e104000241c14000d200d40c2c2d050f1294182c0038088558061010701b907a40e182d05000807045403d400204201400460f00c9561050041c060804203203c05100071820247d030030021380e0001e50b807120f04944400070402e03010400d908144500ca500690328182080703010300440712603405c00200b11881c00b00b0303502c1d07841d000340700c060908800c01501ea44000c0080541c81c1d20750454040e120010041181229000006005090013084c40c0304010090100000801c2c0a4034001c03115500450001c00072464440002e00307502c80e103221b0009561510300240c4a103500340d0010002c890040400c10b0031030350703904289511202c904003a2994050010000a0a17180c5544095001944c080c015490980c15001042010b000786e070f14004554024410072046203424022040e81245140c42d921 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 654673902 1250 654672652 654672661
    0x30f010606050304080c0f06040501270206031906080f0106210203061602100f050402030f0d0504090906091a04140102070309050405090a060606090e0a0209060919050406030c090c08 80
    0x42007404041c10041030185c0021b011181c0c0042002903a450740018016100b060820b482c115000780f480c006001d80000310402d11803081090341d456a01d005402810b1030b0303e15913540700e2019403c031403070340d144110b256942c1010076240810003c1e0b0003100480c1d80009402e41c1003860490101c2c0481c0d402078143e0b103041803c0030040c5c401240968024081d0480e05941d03803030828090f8107015401598401044c07600e40b03000300c4260140c0160340100e00035015076000015800c0180c1d00c54103034800c9540130a204110400160029500c0700d014070f4002c000003c3d244d000350fa10091080c015003119400d0030950401d04c024001c01d407062210b85c84140008514000346984c014042d189070740314461085a9500004018000038000065070b158000410403071680c441c400a08140c2c03040c021070322144011000102d440c103087c0308503582614000c042c1414105040204100f140c07024009502c0784403074030800902c6440e030f8082c6201543c4100c60030030301d0320704084441c412140d8044000f000c000800d070500 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 654675152 1250 654673902 654673907
    0xc0a0206010e0114090901020f03250e031c1103030a0e1b0d02012111190203030f15031e030d0c0e0a0306050a060b030f0a05061915140a02010902030f010606 69
    0x406003c602035030b8070217140c2d852140c0e06009000344507400360303c1d080c00010046e840c2446042000094017080c100160900e085c1e104403442640e101e1202e406030b0100107000c0c07000241407268064038031a481c102d0f44901c00a1455400c5400903200680c16940710210031281d5201406440c2d02d000002100013030916003200007440c83c606003440a8140100e88145140c140c0001c1e030035200314241e00c40306100007070950850103025407200002c19040d120349518040030620100c116401050b0314211010141c40300c01c00c00407a048412820b5a00d0311500c1e202e2081190098203600c0c052521502070343d10f0b4821902c11000303903a00c007040c81c81000740e110070384c0e17541d03648524160003903039005103001407595103a4440300028080c540200c5001c2e4800b208021205103503a580300c1c81207800010a0004d502c40d13105100007a000441c040c4034840b0200814403404401d0415103587d28006d203080c2800e81c943ca02041c0040c2d00c1003600c4001071f51201c0b401010b50400700030b007001c44041640208035052901000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 654676258 1106 654675152 654675179
    0x3071202250b071d0a14010c05060702010c021903081305010204050d0c140405010305030403081810020a060c020d020a14030f03070c05010e0a0f03050d0905060c0a0206010e01 77
    0x2d8004d980e100c0c00203c038005009082c0074081030401c0c04142c0400f4505411034100040c0c503008402051042180d180110b00d190000558a214014000d08100314171702a001c010031006018030000c0c6e80040084d91002c0e01c4400501c01d2261464850b01900c031350303406154007048410300b41d014442e200c50f8000c22100160780819202c8130800502050b52024400a000d9401c10310041020510082c01004c0003d049140068034154500010b50046010365103503005038080460301c010400ca031b01c07170803044805070700050207906440440203549aa5000000f049101c600f0600c80c4686810000c1c1d0340302c08401d150440d242c1c40c00501c002d1004008250541d00e070b6080c42c91176903c020340814440283d5030041403844041085850a4940b41d000c402c3c0315000541d104c0c0f20001140042c0700f07060140c0d6201d961541e4900000c000203244c0081030300001108401000100000b9250018 = true := by decide +kernel

theorem cover : BRFrame.Cov 654496402 654676258 := by
  have h0 := BRFrame.cov_init 654496402
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654496402 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 654496402 ≤ n) (h2 : n < 654676258) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
