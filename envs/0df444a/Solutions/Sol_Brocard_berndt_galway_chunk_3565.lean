-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3565
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:01:52.409258+00:00
-- url     : https://prove2.me/submissions/6c46938d-a16a-4e08-8b35-89e883db518a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 641007194 ≤ n < 641187050 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 641008444 1250 641007194 641007209
    0xc0b04030305062b030315090f0b03120703090b131806060e31020c1f0510140909100608013e07050c0411030a06050f010914060c07 58
    0x4640c10543d0801084c003210b0506a191002d0901580014162015081c1c8075903506040c00101c0d2020b4681c4003120714010740c0040c3d0018030b44810701d95010034a0b00610f080e05400c40c10345110802e40348440c2000e001d00c4d00050f00041e4540000c1c01400c071644000d19003900f2641d40f58020701d43c4c83c012042400012480d003a403103500c0303c204110310b540240c1d14410060003250b0f07441d07052128540e070124030f48107407101c042111400e012030001d640640d41107070102d0b030707424007a034415299001080d82405490106482c100381751070b0000e0313070b040c4a1041c8003003035503d102d44841d40d40200204100b60694003501990580c0a004607480c01609a84903400090149070008501c50600c48228400c07540b00c0f0b4044440d05010b8008207620b01d8400c00c04030840604040129103805041c100310f4074002c080019243c00910781440c2ca40b43d240c0040186124591300c0c0014010309450381d051203100d5510740302e500c2c040703a00580140075030045d40b000004991409000c441c20004c2c40780515180c07102d913620001313 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 641009694 1250 641008444 641008451
    0x80a0c03020f0708030a05160c1e08060606070201030c11061005130c1b060b06070f020f0a050f061e16050708010b0f0d031b23010509060f070c0b040303 67
    0x204164041c406070205407410300c0501515450291256200c0c03103a104508200304d0000340c0b065070091001e9000f4005a04507000d4468542c4614411054609055040b440000d14000008220f500000e15910845020381050b09285140e40158058062000341909001043c041c41810079420040b642c880c601c8080da000e4814945014070194010b841d4450591605100e00d1020560300810340c00c080c2c2c048804a1282849682019801002e405002e90751000000500c0310901a811410700c180314021100c8600c1c001000e410030100180c0c80c89003d40119031415003c3c940d1800c100500294840b0704c03002c0b40c41d0010004020303c03030792185034604039030f003c2982103c05100041060601805940000700309004004000a410501d030301c0000d4441d00304c100d2500105481003202c1020b14040e61503907902e1103014940b1f14203201c1100403ea202040212400c0c0e41180c0c14001c00f0f0040d000030f0080c0c170054a030074101410110004010606000c880700c8a54001600200c845100394002d680c0003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 641010944 1250 641009694 641009717
    0x3121b02040e01021b0109111c1416050d12121518140405060c0703121503030e0a0605160f0b07030e010c0521091f020c120408070e13080a 61
    0x1104640c002c03a042c04480c0e8500011f18000441540c070380c0701103a2080b18041954100207030707090201851114003d2090082070382d85540c540c80018a0107441500060310304920303486d50b05002507151400c2c400b0348045485601c180c0043c0c06008100f05519111130041140c5a020b00d420064800b507901c80322000300c64040740c030070515580c46031400d44000b8100c420300030f0515446a83d0303120409403603e2a550300000764801014012600364090903903444080c8090303c007a040034030126401d48415030124000310b016140610b02850340500703441d000c0d1127440c180400e40e0036215018030503041c21280100002e81885c0030510703030b07070180f84102d0f800c1d0360200305420390845907400d541041c01d240c0709001081c0001c0350006003101941402c1300651250207007559400f01d000b1728010403c0c040554410303800b4a1094001030540040030441d00c00700071904a07841c2100601c0d4684100d01c5801c1130f54002c0c12060092801441c00c16810801c0500e1400c108100750319215090f52107000e000d40030030581080c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 641012194 1250 641010944 641010967
    0xc0e1905090108010c09030303240e07020f010e1f0b0612160f0806060c011d0114090703050c0105070f02090a0b040b011d1005040b0a020105060306010b0403121b02040e0102 76
    0x4a000d4030100c0f00070700c250788034080050500241400000c0030705440c0d04480841c0c4031a814038100d80b91135410f048440b20703610344280c0b42c00305083d608100140981101070007503110501664000d2400781000b480c0c40c9030040d14803207600e0742041c001d000150f05c4407078400c0103071340306000390909580720300440c201801d00c0e6a00c0710f80c11039031010b6102030010300d01c10001c04a03008803172690302a000340c41080e51030525507100c900410b031000059055025041450359142c90551240e0042c0c400c8400b14880d81d21000036003950340c101d9110003130180d400081183d40c50b500c00c00c09803e11910640c2c00640c00ca42e80da0014812650844100c10100d5540c0c40310070f80c07840d10f4000c50140c07200c28205107a100080c01c1c45043c030300240280890046580410f01d0020341c0c4104d044400401880a0740740c0c503140c0d6458024040c1c4403c5e212a0f10a105400010480c1c90803a405c650803070703500000d034801c09008080c7c240c03a00c0402c0f500e480c100d044a00c410b80003503101c5009011848010390b0005130740384c400346030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 641013444 1250 641012194 641012209
    0xf0c050a06140711120301030201030b1906020f010c02060f04030302070317071d01050901080a050903070501050c0408060c030108150601050903030a0e0108181b03120d0509061e0a0c0e1905 83
    0x20000e81943c8a0620b80c1800c1d005c100803207041d641c080c40d0100d10758041c540440d00303070051490031550a01d480b41001501c5036020030a211400340340002800389240303000c000ca990700c406540f18422440d02c0c1c008200000e00a40c000c0940038420308094a00c00d42d02c4103070300c5000600b103c140f008516203940c41241d00320f500e214540c000c0c0007424001d00303285951000070192507000f0403000b403203640c4001041d1050b50402c00d030748207150f00c400240450314159203400b4030350300a0711a807810752141d03201081d90b0b500d6013420f0f0f82c180c0d07802400411169002501e10a88a00041c02080c1805810404180c20b80c030240000c00d02041c0680745d013201c21008000041c003620340104060001040b00080e9041c2803804a2204030841000d180198841a414002400c205403201b0b5042d99040028a40003142219080140b1600c01d140680710b0780d907a0155140e44210622444140c1071401c40300090045200d82d00040c034410031440c01100501c13841d804074003030a961480c000300c078400c0040301700f0a6180110 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 641014694 1250 641013444 641013467
    0x3100905071b031b0809030105100e0408070201090e0c1c1a121e160905040b060d0321060f0b090609061e04060f1b030f0c050a061407 59
    0x44104050300c1c000d0002400050036902210020b20b42441000c1454411080051443e04581008042148600d0110f04584c84081c10500035400e190000e4000124459504100c40c04c141c504686a45c0715620444a50302c2900200d05028039040d0110b5209007a04585204181c54076000d541e403c0c098082407050a0041202c840850a04004011200c5150000405140141c07080d00c942d0130401c154a040c05071600124484c841081500c202d07640c0002520310403500410044600103899825600030385208507409407540c0c0200002c190241003080c44600094020703d0a038406170540629a11054142e0780c0610416031544814002c5008200100000b0000c0d00c3c203103458900c424020582c180514083c1c41e101d0715000c9241c4040c200314502303003000c40480d0403031596030365125070010b81442d494402d441b0008000d50340221010847e912581501c940540b645000052906d0084410003072032501207640b03020384c4560400080c0140200c680341000e80d041702a4903e41408024450150038 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 641015944 1250 641014694 641014709
    0x6050f0c030d0f0f0b0a120c05060a03090c0603060f0b031905040c0611070341010203040b06010318060b0118030b150a151404031209030c1202010503060906030a0203120310 76
    0x201c04036401e546d9440304604540f40d880748038255170040d0515109004060340700c207411035000030304400020b0b410b90041569510484148100507250746044044415600074402c1803042c1e25803c0c0803110b101d40c0a1750744046503644039100c00c00c4200001055604c1039500301e131810070b41d003010b00c10150400701d0b07010960203090090400703507d152554410215020a00d84507403803200391521814010900d9031040c0100840d000701c2c10400200d0450003540120b81c1903404481a0002c1100c0703600c6402014040e0307584d4000140004559180c61000f04000075509040c4482ea00011508004e01c101400c011405074414105916100b580040300003405401544100400c0e8814400f41203c2c07110005080010710f0900b00b8000301100003a820b10840e00b028002c015214008024641c2c42000d50042c2e81c4254008500c03142d48409400e440c0300b50680003800b103602800002d51038146616002e6004100808569401c003c81d0046400c2001e02c2c126040301c00d00c00400c00000d410104800e00c01840c81d0b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 641017194 1250 641015944 641015951
    0x807080d051801030e06090a03090605091305092526061605090d0b06010e01031e0f060506030f0703050c0304032010060b0c0c030601060906050f0c030d0f0f 69
    0x2040d40050507440341070194614010159400c41c0564881e80c480108500608201d03059800d100c00b405595000b0800c044000840c201008603110b481241546c00031100a4014003030025090682e4010744001002c4481c20320501409801c01003050300038400c13200031070000c64855420901d4050544e6013a03045080c950088881a0040e1000080c0300c540c0500b0b540c05410440540c064115564420180d5242e4441015032b4904140207402d8022401a03000362516103844c28040300640aa407000030110740391020314094210a4040d640002c0d190f54815000051050785800004185400c10ba40000e1170403511410020501d4143c401d20743c1100801c030801e811490517507001804410701d00104030b08005865504031a40300700b04030030010320710804c005102c5036441da008401e05030480d080c000c811303100e2000403155a00300800c402d4180c0707105a807600f0120b8144081a19039a01c0381e100d414003241c0c104500503a82c407041c009030a00c02c058400c0400c08401d00d15204090f00e065025003141c1525 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 641018444 1250 641017194 641017213
    0xb03060c03040c030209040c030203011a010f1403150118080c03071a04051018091a0d0c06050c1e060109050606030f07180306231e0105150408010c0306080708 70
    0x1c80d00c44803c04ca90341280c07600003d50f594546207035040d20b680e10007905503003084050300080c143d00c8152a045d500c03e980c2d0030360f40502e0342c404030351140d01054111402e41041001c40d0f142c0380c0200c1540318540041c103003180c14000802c03003800004159880140c541d080850720b06940c0c60188002c5005220341c208500d003205080034140d0341031140e44585071084440740c98100c00c950048111014003c12111000001c0d0350384d061034405050b44903c0c0d00e246034015038130940702d440c258417244e00482d00072070702038801c41c14008e00b91007560144d9102140d51261101c15420310203110003a0710510400800f401043d451b107120341042d600050610b074810380e0203104101c0c201c410721304c1e21540402103140142e408100e08141003500c001a03000a842c440c24501461000303501e044090201400c071403e1059650794018603100c2905030f42c0b641c090b2484112004201a1414981001c900c01090411910709551403120901f11440d00c54180040382d2600000c2100700c40034441d800040600301c024042048 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 641019694 1250 641018444 641018453
    0x30e0f190b0d1422062a3c020f0708010e0106061b0b04230303040b06060306010c0803060310020a111c050702040f020706050c0316090302060a050c0c090106030b03060c0304 76
    0xb18143d0042900d01d040e4a9a01c18026240c100e00c1ca143d041400d0512401c000202521403070b40c0030a004804100343d60301d031414104c250003500d687c0804160740c00c1e0030300503545581000d650000c0304980c114411601c1ea40c0c0c0140003404510002c002c8140001a01410390032000e0941e0841c1d440882484000749a00c1c8803030103041c002082c12644814007225580da03e04d0405038414a118604801c100300c07410030404100004000d50050b8004d00c0d50781c4640c1d03102410442c0c940f1086803243e000030900404840060300c00d1000c3c64001c03034000c0a4419050800e00c50800301c0c0c0040c03d11100094000c3d2420319640c60600c400890010304a0807110880c1007104058080e101d9040300030b01a1780d5500c40d03210605015410340d50700540c00081441541400c40c1c0b49c40b0b00781c005503040440c0a085e0ba201c0000309001d10001c00880380c0c0375140609000c41d405c0c00340d40f503411841c5040510302408482120b642d545144080c0030b0070150f01c0003c1d0603e8400300381450614020a1a040d20000f0030500c00842c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 641020944 1250 641019694 641019721
    0x209010b0a02100c090608010506040b0909220c15030e0d0f0504031b0315051b0a020c030601032f09060609150423010c030e0f190b0d14 60
    0x466861800681e03030303407150004030325084401c42420400d0385014907110065602107002d40c121441a80c0b825116603c0e2010400d841c480d070b02c661429804c04001e0b8000d41c0c1000701502d6841445ca0071980a0030712049225507102c01c4000d0b040350081000f94061000b1100307480507500340c0403075103000c02049882003044c0e43d03183d0740141e0701030a1200781005011694883c81c11503002c3c5d54000c0c45000074000414081c0720311086408222000c6014402420304a02c59218140c40b8408802c030100d10014140407a00e40c0d036100110220840c001e0941d020000c1d00c1c1007140d54001d5119a40c0c00c0900002002c9803105021507041c03600d02001003081101d0155100c00e4915040502240c001d991005508009207181006480c0142a090301280000d0700e040443d0281c5010000501d059010604030341c0111070b01c05103000d0003404240910b030300308c601e070a00100040400c6806400d050005106620442100c0041e0380302c80c079402c10004c0d2405d0449041d004280340090805607054483c2042d244c41780b4034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 641022194 1250 641020944 641020949
    0x1b08100b0f093610091104150c050d0c060603201003020a0c1203090b130512090913060b060d02071109060a0e040302010f0203011401031a150c0106080f03040303080112020901 77
    0x3049203804152107444c000002c0d00100081601080744046409411071190410322440c01d0082d440341f9104c011310f0181031002c19032a800b101034902d403e1aa01c066031800072000007030707031403030360f12080480040c2c0c810407c0000c0991070510f80100c59280810071140c00210310300102018018441044a5600814207003081c9904c00c0d80c140090301880e00440003810900c0c005801c1020740018008004020602c1101c218003c90965484030031310010301010b4443c51801c15004401c05001807071859480c130380ca61042c1d1007441e02080152847d80011500d4008204c58450350b580000d44408104c0807107014405201c06940c134066510b48100001d04481c171601c9018100c9540600140c2007500c02c1d806070b109041c04803400c64607940c40d102c2c2c10000c910304101301c0f40420719007198041c600d405461003002130301d80100340d00c031507a801142e50300c601d41080d6040d0b00340790340310000418001d02c103005107100640d90100543c0c9951540c14020003000044e4011003204000005034030150711101d190605 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 641023444 1250 641022194 641022289
    0x4180506150406050c190320030a0e0111010b0306091501050306040305072a1503050f0c0316020a15090b0c03060904060203150d08040602101b08100b0f09 68
    0x442d807118201c286d085c40c841c0ca0006c120032103500d00c14020190010341468001c2c2041100c1c0d00c4184500c90040d41d02c0c8508510074001c0346140c000000a58400c074481250010131030f0021900302c8000f40441e1400a0607920b160081d040b81d4440341c8102d100e9130419004100403001011141090780b000380480c410300318080d06a01d031005500b5002c0081d40e410390002d8603c8852070342070a5031620b01180702e205404d00000002e04182c082603e0450400c012801002100411465074a80e1030200403080c000e61145c01c00d500034918048082010903121441158424101103200c014a14192100010083c0b505115084c18401d01000391107285a05a016501180040c0c2e07e40300e540d981c010210f05040c0c55644a20200d00c2c20040001c407030040c0080340d10036000c86445d01562002d1a09548400450103808450392080b443c0d014420114240c00080c1c814a81c015262601e0184070207520800c41c0ba00070320000545412035003054030321030310f603402206860b00703d92500c0140c1503440c8156003002038 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 641024694 1250 641023444 641023447
    0x30206011502070b0315060705030c0601154103010e04050c03061911070803130b01170a0204090804210b0105040b06030f07050405030a050606030f1507080910020418050615040605 79
    0x6d03800d8407804102c600058015084076120b448282c600d981d2180301b402080c40003e000120315000300e02861003d60014645485948108001d4015410f0308542d920b859000c614a402e00402d0040000000e42c040c042d00041403c891401e41029403520034110a600c0c080d90201e410031140d0a2581d0001c41c0b00080b40802080d80c8401170002e41940c000c42c0b601a200d484004188081104080d4640354101d114000590302d13a0b1342c03080180c40c101d0428030420440d401412a081c014070b00703544182d035030350300c070b10715250400fa01d03074105101c0d0010501d400d281a9507070f0714984c014042c010710325a00400c0704032000d01030b001102010a803d0700018110080700c0502d4400b1854481c040c44c20354000d814090700301c0c0c510440d581005940c1d02026101a40240685202c5d55086040070540200038070300261001410740b1109800c849501d4010b081c559113000d042e06a114a4095000400040c00d030114080e405107140218401150000b80c00c2500c20283c008a03880714000d03420549049420500313003036 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 641025944 1250 641024694 641024731
    0x7030f0e04060e010608060909010c05040e060d0b0711060f1018061a040e011418070c0804030f060b1e0402091309060e10020a050d0e0f0a030206011502070b03 70
    0x1d805000c05070060640440200b0001c65825801150284121000c6844a4450319803038045801c076100c2c008001d002034004c101c1800340c2070709201829041180a032065070000160346030045000b00684520002468001900320020810040140c2081e407c0c440c0361769506001091b603010fa601486002d000004c210030000c1d00d41d140758017041c01004070038100151030408030307003401e459805030240b40c115159400020818615088001d0801140501030000841ea00301c11701180d10030041003c001c00624085880c0020118030181009620801182c1e1800d580c1e0305d00f220595400460302c500540c42d0703851012021000c41c41100b02883d007550016912104007000c02c94148500015000140c10700003c0300820603a940590b0f00c0d0340c20b201c2a07902e01d95140380380030240e124600410000910900185c00300c0c0c812a4090104005518102c0f0303080c00800341410b09003290001c080c2c01603080340c80104a000710380c006c1d00148a4051020700a000d080440049941c04041c1194800c16a00c020340c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 641027194 1250 641025944 641025949
    0x302010c08130b03011d010302060f1b030412110f0d02040c111606030e300c100b09181e030c100203010306140408030708060f10080114010507030f0e 66
    0x48400b400040030341c8003002515030303010718250b5100f0303c900d4102c440021581450301e144800018144c030750040050349006424040a8210f8104940940301c03501c1c85000c12403d03100400040000704400c02c0a010070075000d0030f210300303010101150240901d412001040081c0d50390030101c81520f1781183d00141000c01141c0841e40707649180b20140c0e10b8482c40481081614500c005a0121450307030350203005403850f10411076180d2140c100c02074104114551020383e1150f9070ba4050503003566281e8400d04160b4025071903450003402c0741001c40d1407a6603003810b40403801c00c0b040103907000c00040030b03031984401c1c1804460380d40c8003074440b04000d880400d0001000745105000316a070400400c011a0780b0070240c60081230080d0310030712044031558545606000c4900d00840000e00c181c1e000f1007003500f141e1300d0310010b482c49140100300d16403124420301140d81a6a454a0304180d00740159211861036042a10750035001901026413814080d05004000000b6804940161407102c0783c94181e0034101c44101 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 641028444 1250 641027194 641027197
    0x8130309050a030c080615090a1e05040605100b3f16121b0c111e04050912042918210d03090c080703060509120a090302010c08 56
    0x242e4454020007000003803005416461040e2241e401c1aa4079680b00c1e20000b00400c0541c40c0904c0c2c0002c680c10015001c100d441d07210401c20491b85110307003c1a6007841c1c02c03104881d000c490888a07182e80c2c4041c0000030306030301078800107804c15214a601d000303800390303081c80c0c1104400c1071092652021126010586d403181944245941c48000803010360500ca20440d0806c0032044103240003d040400c0c001507807844d07008903042c4c09103181e0341c18040001e01d181140c000d414500706981e01c00381e100ea822030540f181c0741c90410f1903100c00601078003018003104000650384017801c11007044e071100910507000710b03159048030100da40c449040c1030404800daa0000c00b0680701080480c07403c00110b40b0a1184c180c44c4420702e40c0150840c2c210b0001e80000300c030484141000c4101c0007055004081c198a01c0303010b0360000c200180100600075815aa5200c0e02d45011400d8008030307102502c90082c130110300c1c010046505404889a406401c299039510010041c548512029040043c41c603082c4003440001c90 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 641029694 1250 641028444 641028449
    0x504020c010f061212020a08030105100302122401090f05040c0915080a06270c022a102c0d050f0d08090a11061b100f0b0a030308130309 60
    0x6024050140c3c0c0700003440701600b03140f9085d58218031003001c1919544c8040f07000c000f01c079413000c030160650742480309003d0200343c0b2000d00e00c14541d0070440c4014045158031120721031440b110114400384030b4107141002545800c800c403418040d48003c1840300c009201c0c040003d540040c1e900007218426944101c5c2c0c4400749911005190303001d007806185050b40140c5440c880c00406074240032181c4d07103e11035522410500c401c08080c4000320300f40440460325800211022945c2e1045a096980e000328003122540c4d00e0890610800071000e01c000282030030f801c20010b08a503400d00d00c3c44025803842010340030441d000e650072000b511080c9007485139505c6409000c61900407040384c10848031010450790340c03c80006850003103058070340025075005000607141001a80a400e510410300d180b0103200240d00422800003034450000d668115509040104035500c00610300d0108a0000c1c45102108841e031942c442c50060b49003200902c04280c00c1800c0e150032040104100315414aa8101150007001d140c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 641030944 1250 641029694 641029721
    0x1a04050a231e03060c0a02030d09111914030309030d030e01020f0d0902090903091804080903240901060303080f0406110409020703030e0303100314070f0e090d1103040504020c01 78
    0x209402031010b41815002e40300390120780c800e407201c10700c21046026004000c0010703401040510344c030110079008075030450711641480b032071464008000303408040510080d1a01c02c0903403008200c120381461541d1003980d41030b0040c500c1c000406c00442e440f030100045038405e154440201c88900e100942c1103400c10840c1c00051a103a50300c44c9540c0c809000001e0701a03108a12010100e041900b0101c21580d6208004101c0801103111000d100500d50b4000c200f91620401032202c080d458409200d0b128140d0410024145900041c14503a4411400a010501c0340d03850a0401d03c0069040712074550041040c00d92920302d696140341c0034000c0c05482c004d141c03440c2808640081c2503003044c4c0107401410712030f031814844804031f118055030360b003c201da84044080003d2002c0010179912910300742d008016206441115460301c20040b0034165030340c800c85e600c07910101040407880b400d00c6411811040b81c078205a00010b0003031160303070743e000f64024580b1599000802000b2364409600102c010401c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 641032194 1250 641030944 641030959
    0x30a170c0307060b040b10050d0e030409020a0203031015140f090301091b060305090c01030b1203030f010e130b061002030403050a0b060117041a07271a04050a23 71
    0x4526120f0041e01d0180c2c0c2050245051445d100d00d01d01d4080c500e08814113140e6189810b00740e5a45611010f04008040c040090104000108030003045000078a42c55025800448e0740b0b050191124091001c55481034036828111040200019800862840c20070800c56141e40c490380b010700e485845105101181b03034598038107820350041001d04080880481015200490002d654a0054040ea50304a0710b290054100d6000d03800b20350701a5224801581b07020744821032400501080070b00e90391040d109441c10310328120040280000d21451240d0041c090368000004003082d0795405d01d15140070307008903c1107001c1250300c14800d00c204169802942c0100032100007a0742410002000074007a61018005a1210320004020300031b000007600480d4018100c01c031200886101420585002d006401080003084415440c040001c0300000d0100c52480c04071142c0e86032101e21400024110031409800405000802c0f45503648104802154458017202d00c8440c5054208080c4e20790081c1696440300c1d5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 641033444 1250 641032194 641032207
    0xe0f0904060c030e0c03070b0706090f050703111002060708061314060a3314041d0f06240c0115090e2a0a09060621050105030a170c03 59
    0x2190b0403140141e0b1041d20100403126078202801d0302d455516003900c0c1c0603031208604010300360780c101c01481c407140507107000503c502c03141e0303125401401c110406403103542c0218018828013444460701c18031024126028240000a1038019460b100000c0c08903060000840c002650307034448005078000210035000c02c11120404455001c80c0301c1c0c0c01d481c054000c01240074081821452440280c007000700c004244240c02c02c4802905545402107003c2400300102c0314984240c1c0c40100c006800601861080c1c1858980c01000c071014101c40100f9250a000b003e005204c243c0d01d03919407058086110515550700d10301031a40a01c1107106406000c0700301d40c41c0c0900400d00b03194031459042500c60101c010b1055101e44000c1a6407602c100c005500c4013616906d03101803a89854034140c19076800500908141c55440384003400729281a0700c000080b40c00701d07002d0401d080e0102720b05d80c0400c0c0c1c0341504111550504000c00c0e521880748070b0003410300405100815055a402d400e0769841542c0100b01c983d03484 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 641034694 1250 641033444 641033453
    0x1e0207090509030c060f07020a0f1a070e060f070311100b18010b09010c03031805010b0a050a1a030910050411042d02250c0302030c010504080a030e0f0904 68
    0x48191045001051030a004508800e102000b1107065194600c01810552140442c042c03c400020784204250310408001d400040c250443c0000924001c90b1444021a900c40c64040a080300070700400c100002c07403001d006540d403414140c5188828450a081e1103110600d420303102c1802c140380d85255440364050407150034245030802d45280400b0f640052981d0050a20300810f084207026140307034001d00b403194100302d500ca402c2215049000b8907020038030401c071441160340361040400c20f40340da94440b00803c02d40d060088154006100a40710003101502e409448602103c0d0504001c1c400c10340040882c0920301d00b003284d402d0082c981d96081003282824682640c84070354400d00345004600388410b81d030742e1703a03074141c07803030b1114581d06001580a500c90348003800258451000405490b5140d00040070078401c0090340d00c04140f28a00a0860908600405240070003841a0504111040005010800c2c0208000740078079854241542d2001042d070008086190000710550007010311000c020602 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 641035944 1250 641034694 641034703
    0x904060b0c060a32060a0e0907060914010203030a0213051215070309030806010c05030c19060b030703080f28031d0607020c0d060b0d0c03030e01030204050f09071e02 73
    0xe4032050000c0203400714220280358a642d00040e1a00b080c00501d50703138104050451501e40c0d0206000f40761081c40303602d494a0b400300c102d00703681b10036a584c00329009000ca03540003c0c0400107080036203014a14030300103500003940d91000030280d05032290085509010103080c060f80034042c0c0401400d9224104102d042c05a880340c00c0800c9484001c4070001081e0321501074410348507120303019501da0b6140c4da5040c00550780c4950080045410707102c2000460000c001c10b01c5540514102c071103e201501c0e20354104a000d440c0b841101a2107504085000c0000a100c8811100c030ba02c50310000c940c4030003003e210f4680c41046001049404452a039103072074455819444914080003008401031440815040380ea40e904044481e000541c3c00700500e0b10f05c0c3e1800c584000c0a651060802084200b05880461341ca0021881c0c1102c032500d92030302c103108041d00078068518100080c6411820702d40713050001503c107402c2205442c0103502c1c00002c108858414104e1400c00d801e5030028401c08401d1000081d41d8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 641037194 1250 641035944 641035951
    0x7270e0c030703141213090b030a06150620060f040f06230a1a120a0c03080a08220303020d0b09010b220509180f06070504061d010906050904060b0c06 66
    0x440c000c1101c61902c1d45c14003401c0d11018042d408141c0c1c031050500306074400034004c00500550510a0f81e4041d40052641d005001d27501c408901c509045614011010301034030140540a4200750100d0001300c41c111002403040c0e07200702a62840708490320f0320b042400080003082e00c0a05401d0614101c02a034104070101c5005c090600710200c441e5580b1844540d0031180c4515842c0c541d90300c030402e810020315152540d41c04650540741541c4151a0a540d5015031003465402202e40c00d00115000c010f003600300300c200b82d1000022130076244016098803e003403003080c500402400c1c580d01046401d40b80c44c0c01d6018803101c44000d001042296107039040c0200a401c0207104040c01c451002040c5000c04501110b40112003020740050071640301c3e503103960980e0341c003045100302901c20014002084801045014040c0406456041d501c1d03013031a0008194514120b01480003081c01c2c008000b8070b9070b000440d4400c440720743c50034985400c2d544001601802144c0e000c96071410010650039100301d400b1880320f01 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 641038444 1250 641037194 641037233
    0xd140708070b0612010b0d0204110c1006060e12120d1b02060103170c0c0904140304030311060a0b010c020411040b0d23100308070f08190207270e0c030703 68
    0xc3c0c4031554005080e50300000c10f2035000b141007401c610049c00c00d50802c030038800348045080d05200104031a07a10f410185c20007500f503107072104000c00216030040d4458170601e0058521103e41360501410aa940c0703100c8c0440d0174100000903503042090f405600c1825490107401c41c080040c0011030000b99140b100f80000e81d20142802d40c002c0514600c24111140c880c05032000d0820b0316108400c01140e40401401643c428510a0f074207000c00d4020310007800614429100c03840c030320307002c0100c061030a5001800005607a292040504840c2c1e00b10481d01c1c0f8503030b4120740200b01c0c80108140300c03c2600071a400201c5070350380030401c00345080040d0800b0191703020001d9260110440480f2060050f0300c01e96010b1315410600c1c41c180086103d020007007034414040c030316240f8000d81b1582c074110039602003609040c1c3c620041c800c100130983c1c18081d000c001c12106414140d86922000d84030080005000d00c001c0780e540e07407405948120703030512540001c1c0301c1c0102610710840c1d0f01c2c102030008444d0082d0164 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 641039694 1250 641038444 641038459
    0x22061508012903210a0306050d020a0504020d06030c06120f020a0e10050909040309082e1d0a05030a08010906060519020a020a151b050d140708070b06 66
    0xc06000c144250307000d600301542201d041030310441c40254400a200e208a40502030189540e06038001000e10304071001240c11031503a036640f6200c3c01011104643c0080b072140c08400000d80142c2e440c40046030907204101c0d00140d0359080481030380010205035000400b044041d00002071500d0f00004a800b07502c00400d411b000925003040c0645c105d105000001000c540700c00c54101c0c0c80e060024281c101c0c0d44090504070714200e0320400080ca00403045504600140c0b10301c1043c40100410b10211600c05400e4850f600a0b500100c0703d014520880c124102c0c0c0f16a80c0d6080c9100800034514424035280c1d000140c961140660401c01d8890303114013641804640c10200001b2481c2c03644c0700314012180195a014203210728050380b80000c0e004200d0680451080950a401580d5a9600b417401040340c00041c00b0802c02c6d420700501b00e0500460000c0f4101180404200450300106030f90300384268515162903802d01d003050031995800b400c0e40c043c3c034808002c240c1d80200081d20070480d005203000c88450 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 641040944 1250 641039694 641039699
    0x2040c030e120909010b030601110304080c040f05040506041b1205010506010206060909061f05040516090510090e0c07080c0109020a05090601050a12020405060f03010306270b220615 80
    0x81040c3d00c40c5a19450f00041c1c0c0c100100040000407021f1908500149800d000c0004021045495a0003d402c50400c540018203842c001d460302c0d20840e40027010300d400034402813600d078541035250040184060b00b52a01003504100c4043c0044a0901521400158010050701800c080d4008c04080b030740035000d44034060124400340390005040b0310419000d001080c0c584c4c0c541c0c0c0c580c565034915003510102c107220b141001c200c82e40c035801254851101d0000182095001c1e004c001c200c1c40300d0f54860f6010320f001e001d044000039800803e81c1c0503034400044600a0341c4603900f98200d18420400c01410120000c02c040a40560640007188018022108656480d4507030041001c1c1001c295403003030200d02d0800c481030003580600f0244490000c030000040c1025502ca010507015030150403c01b40c8514000010700030007455118600760842c0010800e1010043c030314944c0c0720000399100c00f502c082d41450008840ac098180c240718400f184061400203150b0500e0f0001c00ba00100c444142c0403e41c03075401 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 641042194 1250 641040944 641040973
    0x615131e050a140a0b031e0a0c1a0a1d0306010f0e01080c010c0b06010207082d0105040305070b0c0906042309090c040903120501080c01020f0304060f08060d02040c030e 74
    0x2c0d540d014a00c246034880c0c0e82c503039142e050f009281c5160001e4040c080e061304903005080d0707030824442c803000c11000740c00d081c80c4034542005451303469009080205280c1c41106034000ae40d44c181e03840c1c11348500384511510b100042140c0286151004164903106460000c070302c04201c29900300448000d0391100281d80d17211b11000f034440107000703440390020f040d510707054020500d106174003500081c1c180140d5210540343c404050a01324203044203e0398a20054a03030b06101ca10079031528042d1030102c020461410581d4006146114804000e0945402007001c5001d00e0300d82012100302c414010140c2d40d841351341760010242d03079040705218210000c140900603580d061020201d03100b0321042010342a20440c840c100002004140d50650401a0190300701411020501c00c6601900450004001c3c09491200080c40c2c0061040d040b0201d400900c400c1005903080a4010b640d665507060002c696610000403c58001c3c0e6644040c0d805401e20a21090964142d842104451210020351300101d185258 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 641043444 1250 641042194 641042201
    0x3051b03060a09020f090c1c060510050c0f060a1a0102190b1003020301090602070615150807052511040915090809091e01170615131e050a 61
    0x11901a001900052800c0d0255440700940c3c910083c03248401040305000f041001d401102c042c0d10901001848510301c0d0020b20440c0c071105a0000c083c00f07594180008240ea03005059591421300c000825a0300482a060102844103810380044548078075000b00380074040e00c800c449201d074508140001c840254800700c0d5407606d40f41c042c86020340d0b905495aa550030003038000c151008060740000c000c0010380c3d00b03010328485240140c0c005070703c1760154101b000c1110010041c1c0054415401d0003045020400311611510800f1428011a02e6903122016201032051060948506130300c0c9106040201c02801030401e010700400c151004410450240400c03941211805000d1800c503081d03401890b0074036004180035612038120a41000300f840302140c4032000035034004820f900450701030205c038034420034204e00604016561070b01e41c00c1200181d0ba02c401020b07281181c0c50104001544aa07216401c2402d00c50301403800802080288a011016004040c841c030040700d420880440c44c120410700 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 641044694 1250 641043444 641043493
    0xc030a0c111902060c070603050609060f130b0d020a0b0703270306180f05030c010b03010c09120512180906150f131503020309060709060206060609030307050708070305 74
    0x40c0100010100c8001e8500b490810740012a03100c8010451440b030058240f112030b009002c1d035280410b441c2005801c104101c84010400c130b015821340c0304100800da8480341e0700689122884000240d61040380301244048401c244003a41103100c0a00c0003448411110003424154081c0d555040724051304c003110965400071901d0042c0e0a10085d0b000e1000c180c0652001845851503d6208166803a580e606e6012620203c0155050380020a181001078820b0048003000c03407044008102052603e04040c2113542c1501078007405078501d17482541000b2007040540303a505040103000d900c0e001e0031349010604011480c5540e0081140101081040c10b00039403080c0085139900419003051407400400c0e04980000c0c0c1c1c8000e0010100400107021042c00d02c000450b81103c0e903000d40c2da0710388280620b02d0100050841d108102c000c1c1020000154089889900310804a0302503940f11755960000349180202040074105006d00f440c0041c0301e6200140c0901124401d0099665140344030100151110440 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 641045944 1250 641044694 641044727
    0x3010603050c1003200403050f0a20040914061b070507030b06011808030706060618030b0c071505070f020303280603060c030b04110405010507080309150c030a0c 71
    0xa0b407079101c062424010000c500701c52480c00090140d06203070505100c903030400080700b1001c000907090050110901820004030521002040c0040032603868504010140403042d0050901540311441980c030b940121101035040f407126002c0c405d428545c0c94032070605403490358088203000c0f612007040040100f61201ca54106014040c0585503895070700101030018845810400000908980b17080340000020152003c4401180c032946039151030012640c2c607400007800e00031fa541d15007025030f070104001c800341d030351200140e105500c82c846282d1150040784c0008000f00001000c1e0b03001103c503540110b2090000f07a590408211206905a0b1070b440141c0390004100f4085021a0711445044112985180001400130799103a4944600c802c443c8510f100900003902d80c020108030740f4050103500d04000307000209a281603d41000680740b4030440341e00800ca008080006843c503032003886001c0090849142c04201850804400c00c013940c003c0b113100009070702d00360410b0022885401101c5005018 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 641047194 1250 641045944 641045953
    0x5010509041d060c03040506010b09240d09051612080301030b1e01030501020306010f0f2a0503070c03031103041505070507170d030b0409020117130803010b180301060305 75
    0x540d01440090101c0500341001c01c618850210503034542084080d104a40c0210942e45904182c904035061841c1a4805612000b0038400021700390740d50b845445008090300401342c000c0345040011030f810702503400b100c0c003c20b180c04402404d00c40c0100c1c0303090071108a00e0665925544400c44c3d80c00444120302e01038000c2c0410310060002541c00360400d50080d80366001040070084002041500810903002110180d4001c000d0002d296082036800020145038140300110306d800200c02400f900554001c0120012009130740c01610240c03210a00c0c4284d0018207403640c50490381040204420140300440014004840c078035960341c8040180c4007a21441c00b801c1c40700340a00300042b01c0c91380025006071a140103410f0001501c980510810a000d41040080e01c071446042c0c602404841503c1c580c1400703181840c0c600c00040c0e030300c4000325011840900f9049015100d42d2074481582000c4000140241400000420113016075009406111807103440c140b48030300c00c4024103098880c1c030301c8001c2c1030703902 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 641048444 1250 641047194 641047207
    0x603050a0203040f081b0a06060305010c0e012a0206070b071409090c180d051617030316110f030d18031205090a0215030115170115110d030b1009050105 67
    0x1030004044030a000c1074003c040310241c200e46d5040c000421421a520390391103904004000c0d0a01401100c001a410200c0100340280c001901020041c4511628980d080c15460344031400481c0000c0340c1c54024040a4407180715252903000302c6c005072190004030300b025409a8090f2080011501001e0015040340703100c0e04c1c1c500c0b58072a81c2d0441014540480060641c1034007076110050034100d2180102c0080c20899400001c452041e100d5030040885207403009140e0a00310000003c0329001100d40100301103100070101e0407140c43c4101c103140a4940100006c403100008000081c0091182d48541080100e061460141c80410131030001804a8a1200e00b103000701c4d80c1c1c0d40003030b600c44174540c19505540100e42c000340000c414000c0b450b01c15140440144610980c90148036440825803c0c0a490120141c0c0380c0c1c5c4401c48144106c40310350420070b10103c0041d1080ca00c41d62003810782e00440d1144508054050054800d52080600450074480c22400d43d910801c0d4001c01c40e013068582525020 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 641049694 1250 641048444 641048453
    0x51b0304030b042127030b10030b06191e080d0302131418190c0201020408120c120a0903081602042703080c04031208180111040b03040302070503160603050a0203040f 73
    0x100e2040b003441c058117010800404a1101941031b1310901002c42c0d20301105056181032210700d0340207003515018804654900c0c003800c0d513220b01c13a0b0660701c1e038024078800748400d011002c082c0c4800d500a21258040c03c0c143e48800b1342c042e0003415411000040740c0701026240c5100826000403120a107a100c481070000a1807152031900341034002d810800c44c2d456545081c0306800035135010340462401070b0344c002010050a401400840703603040d0110540381ca002c0e0407070800d598903101d400080c1d000791000160905610b01400004004560000c0d407143c5610300899411a441c0b14a0000e0b4020750034001c0903101c0d4854040d01d804060010216500340000e1510100c9001000030704410080c081007001001180107041c500000690310740c2c030f1240c14600030110b00303100ca07010500c04009070705210005201218a00036241600c100603200307502c079640d9040c201e1400440b0b030301c1280c06000304044140c03000b42d0350002e5400ea562030f071028002905c032000382200300e1008980141241070824410000034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 641050944 1250 641049694 641049737
    0x120c0b060f10030f0906020a02070e180c130209100815010f080711030903100b12010209090c07020414070806010f021f0207020d080310051c12051b0304030b0421 71
    0x10400e130b07001034849020b681d814103c0e4031504004000d6440281c080000700c5202513450762054014081030b0101808003200350ba01e12031500d940d4855604000002e4018280f94155148020001e124801c050342443c0d015204007403d48502c1d1840010746106116540515002042183c1c156110145c0d582d918604444041624101c46054003040001c1500f070759082112100d401e10014000541745060f0040111804803003951284076401401059a156541d070202035200c08140d04c100d40c0c910b018030008000303200348042540004040c0d0188120250f02a0460b4403403c000c1c1c81d000c580545018083e61340318800001031510f01c01c20319500341841525000390030540d1000c0c012880a0704a0381e82c0c10300f41d42040354480c260440d40d0340c081003d0718200d113a2508810301c410f0f4102700840c10340c8036500103800c4401c00c5414081d00042e400e04c0b2607a180310526650540c2002da9440d20303101d2510a00c0c04500303403419107540002c02c0c0c400161041040450041c1c500355120308800d04120350000602 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 641052194 1250 641050944 641050961
    0xd06031a040201090e0c07080403120207080a151d0319020118020d021003200705070b040501230f040b220b030f1e012c06060d09020d120c0b060f1003 66
    0x203146e01031100000081d50311011b440035500c02c44202c0c810080307040340246400403551143d886036101c0b80da1040420510103d5138002c4010042c04031360355031499895044404001040c400780c2c40000b030108881240010070120b40c1082e64000d102241d00c000d0baa485010345228083d501c1000c507098040185031600c13442d14403180b603040120300e0120101018009621341100321800e03c2c00003d0301d0080100c140b00641c040c04408045604042c02c080000304413010f070341e010350014544103070000d0200c0b5200c400d031a4644a80d0400c00d07522501d0361202070f5584c001a00824004001800c0134014004004914054074015000e05040d036036241070311180200c0103416080d00b050301040f075440005440c64818013a00b5411007080040c5d0798014518040d800c40514010307030400d0300041c45966551001114040030300401e01081c54559400090303403c0c0c01640d03005001e15041016042601d40016003d03960902855490b000d81d506c0f80b0034002c124181006150303100c1e20000107030031681c1c00b0707a11800c007 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 641053444 1250 641052194 641052211
    0x705010503250c290a020c0c0a081609020a1b06093905031c091e15020105060306160309140319050c1207050a080d06031a040201090e 59
    0x41c00c25040304200740002480b602c6000803180039445040c0040c0c2556012499142d00b00c070240549030280705441c0c10005000c0d210f22640006251440b954100041400300307900400da40002c0c0e40e02c1e07181c29603c213000482c510034880b90750400100d48281b8402d607600700145499a4402c01c04054038660450030740b0000300c51841e80c500b03001d40030030038014002c0c074202c1c01c040c2c40484c07441d600006047e0f5003e01d8075080389048610382091006840124101002e040540d000c17403402046581e05a8032005180c00180985201d803160011303080600100504840c0407081c080c0c450501d80c44100e0907038030111010341c0c1690041d00400c4142c4407500c506441c0e90003a240000300e04019039540a0805101c000c85c140c0303640040340c008a189405c0c95003003000801402c00d14501054550269200c011500c0c000901c0000410440244402840a422038a0f4001c0329555200442007e010042846000948000d0070059069000541070210a8001d640507198040503600c2d0082c050800c0301d00a02524 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 641054694 1250 641053444 641053471
    0x50f010c170c06041502090f270c0307090f081902060d0e010b03300703020c0d060213060801060518150d09060b0607150c0c080a0e0f01030204080705010503 69
    0x4000700c01500501520601ea1024010074100707030520b012070707038070b0b24440c0d21102d4070400001d903095695200c841c805060a49032549103030328202c21885550320341010031480007480c4007000342180d003900095219882c20707100d080080c0c0e16203140c9400030780540102581c81c0d10449800c03400703200c1345000d10140d0344000c04c070f06c1c5003c2c210a010750581e281c011088840d0b1b9128a004100d42c030f401c3c030000c14000950002100c0052215180c0b190392001c030022180c81c2940000c0c07000a140c82800348000f8148007801080812181c0c3c40c24400075441400c11910b6080b1000020450510440366241240c05540d203d40c1001040340207880c001c0140304166910400036000070300048940d0028281c2e80c10400800903684009040200030341b03104a45042c818801000200c0028000d085941280d606101000500e20070340713441650b100c030b0303d030101500103400400e41400c00f03948120000204a0140d0354a04118941e4006400b41e000d9801088100d412840041c08554031560140d94003407110030019 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 641055944 1250 641054694 641054723
    0x1b03011403012307030b060316031508010504030f03050f1603020c07080718060b34021f021603120c0f1a040309060212040501030b1305070203040618050f010c 70
    0x82183c22840824082003002c0401400c0394162241c4601c03070009546803480e5141451840301000101100741c000d250b41e1700502c008070403041103543c006e400c42600030005030900e4140500f84140e02e01440000130305000c005605201100405030283c0019454a000039400302400e401139000b05c0703141c8a0a206a220010301703084d0820a6000429103d0301c0c10807d05129198075080e10100e40144421200401c40c09140308881c1e803000c10910b100710b844c0102003698034001c4650f1600303c80d0181d88200c100c000b980d0240300003000c2c0c2c004000607808440c09411010246031030341d03000780302c0541103803056031541c080d5500404006c00303580d2040c04c480d0700040b1a5910341101c5803041115851f80c1a804003040b04058002c015080900b0303050000b0302c445150500441c2e0280f00e14003401c2c1c101900c0c0e00491a090703e443d030018000c105812024026440c1205000750b8a40082c800e0f600001c00f00d03043d02d02818040c14080c000e440002d850040061511001500c45203611b050403a0006120070701c2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 641057194 1250 641055944 641055971
    0xb0115210203010801060b0f042108030906070e011e030e030f130e06010207030c030809040207020303120a050105061309150503030d06090f050c16030210091a1b0301140301 76
    0xc0c0103448096410050310307941069601400c54038503170070440329017000b0404401700000d0b400070380c1c048130b0039050145440c29109019690320451900c004000b81404800d000c3c8040d030100354144a03080607580d44d24140ca24000448a107246211b40810900080c4242084030340b194106041c289070740c00c2100e1500d180400540840d40c40f8107051042d035807141c1003e0119a010310301c0c054010200344014031000d400e507200c08110084510008082e0a000540c802658440d82c06070751403603800034150394580c0b51980c1180e00041c002c030b42450307509150a0020681c1e1508105071010344200c41010622541440c8441d8020000c04c0381101090005030b00006445d9030030070040c440d8000340680819004c0c9801800d01c292140c55840c0c5950a08000030400424400342c16110102141000300181c010700341000d074200101d2140844200c0d003005010400c0c1b000512908041d0b03a0b229a46680315500d00c2e5952a2070302c00340350083c180150800040102d0204590080040030300180002180f8100c080e1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 641058444 1250 641057194 641057237
    0xf030f1107030b0123031b031005070314010501140d022a0f0708060c090904030e091315110406180f15020105310f15020c06090304030b0115 62
    0x2c200da4254402d8014880b0001d0580e00d201850100385503240c00003203a070002601e810040150810046006203950211358041100e504000d01072072040000f41000311004000e07001301003900584a401c500000b070154441d00c02070350445180d402c03032410040074003900c01c0030307601600c1d00e84085400b10945004015075508007a40c0180c0d4440101512059845443c1c205596940803100a400ca10100022038401c0320032601035110488081000360b85525040d540b4a02e003454541d0044c01d510300b0000c0d0300002550000c8243d0141c860452082000100b100507a01560a0203c000e8400d00c420009030380540d405c0014841c1c0d1503172510103217803540800003143c200b9a01038505603030703042c88103040660280700d91034000c100c1d12680d8040d0700d5039590b0103c0208241d840d0509a9078400e50030b505000c28210b68070b2000e5403005012040d0084060404e0180d042039500355003034024500820100f86001044030304a070751210380008941c1c64102340d4014103c0c182c01d07120070301042c0380c02d0380c102000941 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 641059694 1250 641058444 641058449
    0x1706160c0807080c030a02061b04170f07090605010207090b130e071a0a0e0906100807030609021803121201030803041707050f07080106030312320106030f090f030f1107 74
    0x60086851b4049180c00900d0540054145401d0701111650101160100011030301035610041c158041e0b1084060315919002c2c0105d001d4405c1e0240e800080740403400703500203c0c11a08241e00b2206050b4648824104031500c2c07200d0640c2c051450700d9103035407800240d0003026400d060300c800d03600016640c180d6a074010450301300e5401d02840001d108032003035400181240c0b082d281614803070070503d0882e001c60003035101c40090105000f209400250706030300c242c01100c003a01f440c1400f0342d10703280398a8003e0702900d504601c0c14441d0180840d4018428242010b440b003003203080440403060391035906d55a5140c0d1001c2d005407001c0080494280c4410b114000070000540301c1c0c0001c00c015051005910f0600050307030803441c1642d04100c82003000c03035404407030304070700d00b0b0703110030000301302506040d041034081c0002c201e0500c0c2a1060944000a1640c1c0324142c100c80c107d4400b80710380060040f2000454101c042c0042c0308000140101d8042441900e007208100920705188a0300b580c400c03080c1f8a001e240380d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 641060944 1250 641059694 641059717
    0x4080306101b02040f1805160b03040302120a0207091a010f0201020901020c0f0a0801111308070308160f060f0e1c080103121403101706160c080708 65
    0x41480304505141c1d10001c07268556140c0040e4041e034a4640724160181807002a100d5916802c1d9141c003d402584440303000d84c0c8840654030241c003207190064556088041c541c42d0302c047c280e000564880c0600c03c0301d00c42e540c5980034000700c0d0221403100f11590000302040e030461144c0c21011401114070320807088c640c0f0b04000251588890000014041c9800100010440e4018043c00740b00366000100d1010000086a0180d0880a21000b1903680c4200c7d0b4003c020b550f0903c1a8601d10070039220051040c0c0300035122407c0c03404d454881e5203944007514030005050140800c02c446082c0407c8100501062080307000003071941c516100c0c18181c1380c09801c09081c141c1e503482c44081500040281d40d03040360f4181c800e402003502600014000c020f052001030004681d5031965040d0301d10400b07200040300803200080c0c0d100e090541001484408038061500001d15549501c44680c2001410341e104160140c0603c1500031b00c0c0320201c80c00410108104c415003002d0103010001644031000d0441c40101 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 641062194 1250 641060944 641060947
    0x601052206053c0a020a060f05090d020d08010b16060c02030d1503020d0b071103160308280c02070305070b1815090f1c03081906052101090503030408 66
    0xd5211501404105010b2801d440c41c900c43e905035484a0300f4500418840480036464044040c0c05906000a240e801007070f0515101c9242405041c0703506c2603014100c00c0c000c407801101115010399640801012000c0071806510040100c0d1800b000104190110001d0100c44841d00f5176030700301030f80c81c14281500135820100d501050010648030b082200c0040a5809051302e10715004610050500e080280426502000054505000701440c07100c200b10081180e035034444039110081c4502d40c0c204110300265107071340441d500e5101c0300300c2640e41b1414621041e402500041e1041300405034586030406601401500001042040c00710500500321084071940c6d0700501c444401d220f10601c0074052080c1074001401000381f0350034040d07440e10704058805a1030002600e0000780134054031a10103c80508149051f010180d124806a00039240e100d01c00c000d00002d1040641910042d0062942050115818161285814103c4120382e080380d00005584e4195407619419540115001d40324142c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 641063444 1250 641062194 641062207
    0x40204090c12061b090515070503040f03050c0406061713020a05030a060b090a020703140f0403020913051005090c01080612071e060905090103020d050c21010e0a0b060105220605 78
    0x81d04004100b080c8080d20f807895540e418a000920a07e0b40c4080f070600751600800c0200400c00c080007250050003c211000d00711390368901e405030743c404044080034095414141d00045484c00b49440c00d0754402c1400b050340c0c80340d07940d204980352007070380c80e80c07c0e81c0c003801d03400b40094145c4040c07060381d0710031b03000d00400326148905a041c40420304010b0544c456180c410020309010aa010102514007130a145a840c1d0b9096170303020004c280d001e107400c0690701c8007184060107000b0103104400c2c0704941c0b043c416148084c205240c0d0008690003110b1000090700215100a80396105126480d84101e0050100544007600e83d20784c0e02d02000303a001780c00842c0c603030180c4001100d05000c1c40070090200345006049142000c010030150001803000038000d68003011b002003040b4080c041a511000082c0ca0000942048110072441c0c160748545101c00e5460f21400c0c0c443c2c0d4002107010302c1c8554000f60404400c1d21054011100c136442000403140d00d11613409180b580306c10100700301c0d000382850f42d1001e84946 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 641064694 1250 641063444 641063471
    0x9061a1203090109030803090a06021903140105091527060a0f290702030a11011103070203061f08012a230a090305070b040e0906040b040204090c1206 66
    0x100504481100c640c001c1c411444075a901c080b40c071041e40d40c020f060035220744406107403500d0b081a0f007200400407070000c120012051a020500e03890109581d0342801070815038040280d0000e020b000d0303a50044924000203a00c2495103042d82480d9030302420280461209040d81c03c19038000010310004001920f0a0081d24a801d4a070745000e031540502c12140c0d1443c12201d6240c801d2554500e0450440f03400115000b185403e06483c16241c0207015500181003514000122209143d00c0c14049070280341c0d0500050000030a0300c028680c0900100140c1d15800c407148059002c40c0403040c060700c2603180101d2070540c00c0c003c034840c0b040c44280e039810070040031810000e450072541503801004004803c42802e90b00300303a8a40c10880b5114401c0f030390b4151600c0304417004c400c90b0300302074a24411404005000c04e250320041040710031b1080b49980300d0311207051481d100d64060f507014200b0085600454090f01d443d034000303410701d482001400106030341c41841c41031011140c0d40603210b2a0f0746020089910 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 641065944 1250 641064694 641064709
    0x4090204050f090f0402090709032301050711070506180d050703020114030621012301091802030601030305030a02071403090a08010c0f20030c160f12021309061a 71
    0x49900300c641d035903e4a40100503509a0078018006032245140d0f00c0850282402418003401450304100816902024065010040c103036111524aa5610788000100603c0c4a034441028108603400600f0241e0b03d4441040002e400651086070030340c101d0550841c40313079121884001002d110300c0180580d0351440c0000340207000110001d11000c08100308000c1f6030f40c0d540342004001c40c00d044100c988848140180ba0041a107101407000d03140c00341c1645100690b52400c200d0480350aa4814000d02000241d610302e01030b803010000750142c2c8010018800a4012005035038000d10301d02006003040720b0340d2a61401d4140303011000c4a550030000c0c8044d12400d16a0f0300364040c0413080300900004106820080000b08600120402c0044001c4020410b20481e03000c644030f4882002200d841d8030075203040503110800c03540410700c80c5050714400144004d801c0a007078100c0d030611250081141d810340034018800b41d02c807040a040c41c0c0e54055880000c0c080d2041a0200b0216511060000d42003014081d04 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 641067194 1250 641065944 641065969
    0x30d02060a050109020301031a071e2007030b06010c140703080403150e0304060f031b0207170c01051e1c050a0b011b0f1403270916051e0409020405 65
    0x13890040006102003220070b240d90711019140c45c40106c00350b83d80c0e5000c65009001d00480100064038800c0010071581c00611925145a2501e076000f2035820340c2d5502e0751b500240c3c0303c02080100031000180707640d8040d1004019850240d00a03460010b02c101956003021070710b400c00c4480c64008503080c03040c803d4070850b4000a188406082240e902c0210b001c55032401a480b5150402030039200c0b28803290b200c3d402c4030844070180f40510911140c0e048001c0d4460525010307030501c021a201c11b2440080001171001e8411070182c5030700d841d04043d02c031008008800c0311096003440d1010409081d1840084880780351190580c41300041a0505109840c191040d000350b1a04200303003840e43c0704038001070340341103026079611400320b440c0425145084804001c2e608100da50500012a00950100c00d1001c4142c450a00d810b04109291917441000302d40740007135510044d441c0c2c405038403640f15801030005216440c50345615480408006032003031000d42c420341107200c42640115040201d4204007620080f0b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 641068444 1250 641067194 641067209
    0x150d0c1e090c08100b07050715171006030e0a0c030807240e0c181f0e0711010612211112040305010e060103080706020f12130b09070510030f0b030d02060a0501 70
    0x130704050b0b84c847d1075031200c45003d485404503804400070320541c01f6544410000360110b5000c0b0203458214215445c03030407140b05a20120b410071180b49411100441e200c5c1f03e07554851a416010f6046440d40311a94002100440e241c100d000c0451501c0f20b00040d6601c4821190040400c0c0000c6084030301d402d220480c0c04c400d004c0e41d5072480801c0400722060701207500000341035a95039440100307000581100d00c3e5521008101d4280414442034690181700584174042c01030090100e941e852400014041c084440070300007244114485034540d40f80804008100120f10300074035075140300f41426060106006510b48103c0000904204003d0203005400325980d00b01c016080030361460311076649a214880008290b2640092929044044001506c0c2d004105144844042c039103812030700180000600151070030f1450b0400107590003000101c14042d42c00181c0040d038403542040094024000400d45d00910a8541c3c040040e0750324200302c05495100580c0c020035650910298610440d04103800c900e0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 641069694 1250 641068444 641068447
    0x150314122a0609150603032115190905060d0c06200d05041a04031a27250b070305030f0112020d030e0105070b04050303150d0c1e090c08100b 62
    0x8807003c8041101001c8a400484440c0d40b60f40d040002400c41c85020103c154201c81e050320f00b54000b800c0345400b40701d0003818500314185c42d1010b0410081d401451001e0722000d02c1945c0c2803200b41c216400c456004400a08220106000d644c1d41616480032500a80009080c01036000b608413001e03040d2260312080080603100042119000801511450050010380c04280e003050201d040c5600489008541003031131940490750300c3c505030a81950030348404140c120000c40450784c5e140c491203003024580c0b007240104020450712981d00400c5400640310803100d0060540090040f4805000b007214600c6550740d996a0b103001078001061940603003007a40c152003940c1c0900c2c01038a030340140203150741d00750510310044c2a103d00100c402c1d10039101c005200700420010700c02044000006035014040000081b454a0034010070710801d01d40c1e4080c0a0308000000008000c600b40c3c9404040003a180348045011072500c85a0071005c0d52100d0708082c000840d0101081076108400641102a003100003010307 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 641070944 1250 641069694 641069701
    0x10f03060812070503040819060c03020307020c0906060c0604060b0406061103090105131707092019140a02070801060e070837020c01050a150314122a06 67
    0x190b842440c010b0110b2000303000599002800710400a80300140941002c5988448080280a80413051410100c0b04c0030300701108440e4040c003d0007642d21441581e4014440b04502c0f070100705507580d0140009800c0041000f03041c2c08400144110741c172850040c88003095640c90079040c00111185503104030308004082c3d010200712440802265040a02481c2550f181d01c0c807241c4040300003030250b02c42403082d542c40f2100d49062401050520490704d240380100481e42542644400c0004070080c030050f079200812000701040c005580c0c041c1030303c0c1540760480498143c02441d4050f40c0c80241c245001d6448500e080003441000d00440c4080c20300307440302e070b076040c141144042d18140c009845491114003107031103841d84034080d00040e040486800307562000c941312520b02c0c0000b0b51012102e40155401e200005604098602500c85003811810301c07165000e26648440c41c1240800c6941c101078082c6070449140341001030301800313803405c14102040501d003080055403800c1c1440c0c0c03240d0b00a6000323101003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 641072194 1250 641070944 641070959
    0x1c0c170a080406030e190b06090f1501030f06091d0106080a021c060b0a060f0206090304050a030f08120406020405030d0e132705030a231c0b0904060209010f0306 71
    0xd40301100c103c1d00700031500c05070280c3ca10382040c0303030070701505601c1c28500c0c2003905004640107482c1c020314003610403d9180c1c0382d01d00b10307500d035450844120011080c0303200086c030254843d80c005034010100010004000d0340314440c0300c050312022003003441c0241c440310100105e442c00f841144000c1044000901800c4075980c080f46180405c107500040e007024585861060001540114040b50401024440420785982e4054591202580c24100520600c000140504800800c48007601e00003459a0207881ca155580401e20707151805c11a000141400004005072042c80240d001d10710441002d0384a5052600749487c045020740c0c220104488118054002d48a6001700030300320380c04103000f260107240004009011189036001d840c182c3c920340442c00c00c0c8200440900442602075450240750500715041c620800ea91007081c03c019030081081d2041d282c07a803e12017241c0c110b40200810001d1422000852400c000c850035075541d40c002441c00c80c5907070700c682100f1054610741810800c041c00c2c6041c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 641073444 1250 641072194 641072197
    0x6030603021c0213020c011d010e01060501090e1305120313022805120c030f03030703111e03270c010e010302040e010302121e010b01092408061c0c170a08 68
    0x140e00c440307500046e030f901340050039003107800660f650038494155144400c0d2004d00808215018031625403038841e01094a41c071800319a012039842004059403610f462906c203401d440f11034011030f030512800001010160503035000d944503501c0300049848404840c0144800b844000303c4c10341c01140800d64031524030214608580c00c0d0f82003684c1c81e8080340e10f040c3c181868180150070342070307040c80794040c010f1140c500040114418245940c05105200b03c030102484e2a0040900301c219400da03000765805507080c09005164002d100d0300e1110b05103064007560841501c6084011801a000000000f1080d604070082d900454403e103400c5290500d0002080d41402040c000240714100389074103102c1601040001d65200310003100700000326000c0d00070290080040f0002d207408290b40e02c00004002030b003001000284085291007208006000070221940b4000a02c5641d0101c3c03c05030ba9070036242041c403c140160700c1010241c43c0681041712146903000e4440458840f54031010001c00002c10450 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 641074694 1250 641073444 641073469
    0xa0b0a06090315020313140c03100b040c08012409030b0a050405011d101e021b01140f060f01270e010f060207060c3305060d110112060b030106030603021c02 69
    0x11140000b030416107c00c02c0c01c20041001c80b0303a05100d991005160000300358844600b01c501110704120b04034010005640541e000d2188074403031840740c218900044190003075514044035910703082e44626101e035190608000700303440c0030760013a907038408101c00c00009201e81480b00e0420245c03852314400f100c4130661b41c0c000014120800b50344800002c903e14800c07248203038000740e0740c400a548400107007074800c079400d0043c3d0b050300d030b07660801c0e8503c1110072184e03400328000c03107a030034041c08156680020302c00001c8007900c5031410031403100070882885041c80240b21455041003010205a407030044101407120041e0400303032680c229244108021600080c401003100c1c0242002a82c000081c108100c800c41c40440204c0c000307100d400303440700001e480750505203008411303101000700b51621030510211011064004080d8000c62410140740d601481071116015041c810100e803840d210f401011050304203a114001103078852505100714a03061040198810468032030818a040b181c0000b0100c0c08200e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 641075944 1250 641074694 641074703
    0xc07030206182e050a0e0613080909061201090b010f0b0306130b011b122015092b080c0703050415050702030105090610080c01021002030a0b0a06090315020313 70
    0x310b51490022000c0710100144189814040013145170603174480001c2e0581e034011400fa0f0081d500001c54000b1807502d000b61507a0000842c80c102200102480316490028010341c7d407040b40c1e1410942100424081c0e81c15440c82030000000d10f51402442e0718a459881e00000300d074520500070084191a50b04030105801c1902c80041501c191035001a544510400d0484c619644070121420902806c00250708243c00c00395194940404403000e2400342540055001c03d076900184001b1640f406034120594001000400381d856202c04070a2440784200314140348804004441381c000300301c0c3d42014050f50f0012100b0191480c21201d1354006149201c1c1d07005010452042c120011007447c410302c107981d05180d000c0c008103ca804c0ca0600c191f9601c0007143ea841e120ac0000201151014000c0303040d95941a068000303010300c0112100b020041c0d0001004800129074800c28a803036562500c03c08002401f5a40b108640d09044d400c207582c40d181000040344c5580c4c0104140032041c0d01c000080705030030380c12 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 641077194 1250 641075944 641075983
    0x1015090509100f050609060d05040f0b1609090e0a110307090e0a1e030c03081306060612060503010b01050f03041506170114040f0f0309030c1518030f080705030409050c0703020618 79
    0x3145040100a141803801601512640700dc02a240101c0caa120045003030300c0c0c440301c07411a81e0342d00200580d0603a03104510140c006500800c0050703254200c2c0803805100406450840e0349490860085a502811900c500c1e44403203462814003c0440382d0014200d08809254030640058501030300c40c0c204000020b0400c64000d000840c101e809804100181c0d038071a40511101e0380c1c484006002d084084980c2d1245071800e4000240d40c43c051085160291040c0c6445040c02074110300d050703482c0c10092094030b02141a20005500c0d10440c8250005095642c04280c40141042c0c0c02a0854042d00103ea00c05942c40c010301c00416107060303074075006582c00007213411051110b20302100e07140000c2c1d200034a5400b1480020414240e010001c100300c403415920080f0324040b0000400c9062000d1001404510101020710701180c1c0400007481100d00402c1200e00e001d0342c0340905011100211601008847c0c081080001c050341400610707040410540d44c9803d02d40c1c1740d601c40c1d85800d400f8070900242c211 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 641078444 1250 641077194 641077201
    0xe061c150b0306100c1b0503010b011715060f2107030e1b0f18090d03050411122104050406050316050103020a030b1908010e061015090509100f050609060d05 69
    0x441c0c04134859040c1c6c886c1410440c03603030100020729031175914012580f1a5080c00892010ba52080d0b8850340103500380c420701102a02d4444641050021f801c40e030701d4020f0800c005203441000d0940c0100a1602840d68514104a840b02c0260404501614520806041000e9001c54280c0003482c0c50740201a50440c2c0c80203000800060446840b080350640c01010034412041d443e010000c41500c24034104081d1210001e020f0780480888d001140c0040c00c41d02e009a010120303003014a582449950000f0465030040d00c0e0841c000c80720304002c5214640341000180a0115003082d018240003044103900404a50302d052003030050008807030084904065020540481091090300301421648010f0000038082d2001c0781d2800840515018002607982440321141c61400c0014101e4480d20701d4003903a40d81281402214403500d03950040310001c1090503036000c038071950703190101030250b0f200c9483e40c4170b50b038a06414905a0f040b42d078082849410240000222526039108071140d40d030702040001504d0381c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 641079694 1250 641078444 641078447
    0x11070e0f13080403021912050105010503010c0c031709030c0303160e10020c04090606090c1706010e01090e04020406030602190f020309031b03010e070b07060b041a0d030e061c150b030610 82
    0x220745071f010007042c5480348421400c1c4507042d88514180e403404d4000703002000412005461046c00460004c0000d580031038440d80c06200e80e6500f54118041e4016646001d040094007842c50f002541d640030080343c0101d501d031a581d004000c0500102d801e44d80034080040080e00030f92504a1480524000c03500c4509030740c1040b6a580c4130310040e0041d40c50810445141d800000c1649001700030864550300300002180883d0f009030403400d84c8041c165500400c2c03504043c44084070440160003280c00c1511000b0203c0000c11301e00280150151101c2504e0440000c10700040640899507084020b64008010100301524040759890488800300290791441c1500c1020038018038800da1480c21501590102045040058004200031401402c040c840701c01103000304411500382117800080e80c0e444086041c1c96042011302c6d000c9013800782c18070003444082d88020a0969020040c1145440031490308214400840c3c452410b0000780d80389a440780c0c600301102e500081c40041c00844c4100c21000b0901c422a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 641080944 1250 641079694 641079739
    0x4170c0607110d1509150506060306150f0412020f01030501140402070c05040903080f15030a060f0b0a06050c1005061005070c120308041104200a11070e0f1308040302 73
    0xa5031102d02e12503060074401c500402025440c00880e0920121980403400c6c8060b0f002d85400743e06c00034406480c648400081240078070b40410a80789065090043c1481c800600b07024200a1070b5110113188020920320400c840110040708441c1418035250050041101c9940c001401c3c2e90103660050359188503041100750420180d0003540c1c49400c1c0a5101d08141d07000c0f22840c051041c4400104d00c030348481804041d80c1449000b4190183e004d11444800301b106d41e08880c042440c2c004000900c50480c1c03002c0b8110b00344e141c0080c008101e001907910300c5804200031003200c40e410000700304628100301f000110101400c418182c1017202c0480c04609000c0780700445001460118a11080f450103860050464481180c0a464641d2503035152010340c14a0b009001580e408a5041030000f07020402c6203103aa001303000e44104000c4100e0100c00126000c100100162005011109444c90300240041c04004000d1100c4038480c0d10040d0b400c00540040117603400d0302e50495003031504510008258849 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 641082194 1250 641080944 641080969
    0x3180c090b0f12010e07170c06030c0403020612090d0c03080f0925031502030402220e0102210601030c351614040b0d09060615020304170c060711 64
    0xf003030034001e041104110551200c5000c0090f2026113664540e240700310300504a01d025102215001481720380308600d044001564040ba070b0420440c245504c81c0c002c00c0054004549982c100010607050100c0c514082010f05901c2c1c8e1945018103885043da500201840e202400d550010040000030601440b024045507000d801174455000b0584000507501178081c1581c4001e6840d80f00d412260f0b52030003d140220ba204580160058402420441c40c0d0300340c6d054244580d5136616035a0411000c070075000e0000344134440381100128105001000d100c64a54000740003d81810715007402203602c2c0b6013080c50b01e00341004401d2801503900c058036840700611841c1d10920100d1748001c0410030310341d40c1c41403141c110303a8040e5070f1182d003402140041d0949200743d005288001e1400c0c0065a5121026005a24021f02c541c00115031140d8510b080c2041c140c0c00302c5840056000820240a0540c0402c90128511050001054840c0c1c020000c02d1052241e201701421214004600700c0294540c074000341403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 641083444 1250 641082194 641082199
    0x7030b04113012040b16021f03051012030f02102d0c05030a1805030301141807170a1b030c0f05040b0405121501030506040303180c090b0f 61
    0x482840030300102e0a54030144014445248a000341005041c0002c406a0b00319100d0800c610300b508041000740300c1d412010b4504d9a400c5a480c0820068507104048064010070405001d810313620500060706881004010900b00950103100300184407200f090014819010305103543c0c4481261002c0b030900103d402591001ca0910014480043c40d0702c51308140b12088000c0c4845a460494504003a60003d1a0042c000355080c00130805140040d8402c050414241807442d464500c5a51090300f180c0003640b21801104c0390300c41c203440506010314015292040c0c070004031103e00e07040034081e200c018900200307100c1b0300441000a00700e60341c940c0281202402240c00e0518503c1540009000d0001900080d000540c0d9440071740e502402001900e09841900d0001070510b0309090901c000035408807071a07032562103a4a5200c0c49208004600c5000c5c5019002070602d5183c10b040c0076090b00c900030070140a1900d00004400810320100a44040e14140e403004100d15401d4000a40c20b5109c0a502a5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 641084694 1250 641083444 641083459
    0xa0308070302030a080604020c06150a2d060f0c03031808070b1503010e120a05121603060b030f0a0c0e041e110a050708030601200a17030907030b0411 66
    0x8181a0000050700546504c0d0341d5090440e50713000180404e90007002d14440b4142c0c03200d008542c594090307600e9045800006000c100c0034943c0c443d401000748a040803d182c034820420035a00700641d07030209610140c0300f60f0030458114885000000e180b41c82d5024050700b09a920004103051621100c20035035015009000361b80c40d1011418020000d903000c4d10300d6900c135074010f61000c0d420700301030244041e02e20329100941400403800c14109003c7c0d000d040140204a01002807806107030000400780d010f9075442030040b2802c0200b40c00a0105e440a40140500e0502401040304080303000ca001384d40502039810124446605417800c0d5480d80d00500c01640c46400e00251200c00001b200341880040741c010814000d0070441d84049a00e4490301801c0303400510304102d55030100300041c008641112041c9000244407403082c9400d5a01c400c008040255034025a44110502c0130300c5049900c0400c14002d01491402c00260080d603504544c0300c010901e0703a11000142c280302d00411070700c000c0c3c0c00151004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 641085944 1250 641084694 641084707
    0xa110c0d0302032a121b0d210b0f10020c040c120b040507052205061341030102090a0906240e040902300c060c03030a09020a0308 57
    0x280d103940140d900d042806401d00b28900054680c0201d400d01490031101400c8400c01020200c6400e0380030891303841186d1040c440c22040c102e010029104003010603581d0788924921040c583e18102004035a10b0240b505081030f03003100c0d5030741c0d005003208000111210040c0c0b80c460351007031b4103003618050710741e911030301d030504130114980c112040c2415500c0c402400c120000d09401000708880b400c0d140240082c41c248a6441c40c0c1c6503016586040f001c542d00c00c1345030255a00001a10307030f40043c0c00d200126600c1a03007009255000003480102003d070503541c030000c4400c40c003040c45420079071364250191440035410041030340f070130f42c121400994080c101e0300200703448407080406000355228280d88032602105140150700494012424407940d50b039200744059001e0200030103801500c100340c0c0d01501c0d2624a1090809295103ea19141944007910a100040d0029400c04241d80c004038043c110400c01d500c120b503000b10450b40e018201741c0c0006080d0071540046049039030350f03030002466201e0010320b5 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 641087194 1250 641085944 641085947
    0x10c1704031806030c02070503060f0705090d0510090b06030d0819020d06030c0f08030703050315150d0603031b0c091a101101050c090f010c05010f150f0e010b0a110c0d03 75
    0x170240301490340850b056180e40b4030a0503036a140480740c90031602e455801107003002d8455002003965800042281c8425607254451a080c842d15032030034810300b95641904402c128030351a895604c4071040740948440e407190000034011000043c0601028403985890050f54541541075074046001e240307041000380e4491a020380550f00c03d00941219009003600010300810000032140c010342d050b91202d083d525000040c0c1d082c980400d01050f4408107001d000c0030403801040291502c0c2c5080390000c680140b0b913003800340c2009e548800720f240343c6104144090108045140000855241e0f070000100380c50702c18580e442965000d90885d5110545101c640c0350690b10007808510041d04900800c042c0c0c1ba4415004134900c140250990030030f0014101c14000c0d03000300b040c0c00d5141e000b003001040ca01c464200baa4101c40c5250380000c108c200f0000c041c4030712135944541c0310103016100c034086515410040764251901581b507806040083c1d000000c0007401e4240803a2540500160a04010a41d0740c42d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 641088444 1250 641087194 641087201
    0xd08041a0912061303110c2809180305031b04080a1502130902090a0504050a06030308090105040507030f14010f0c0225060c080c06010e010e09010c170403180603 71
    0x16058850741864014820740c4802241e014090745044000b0383c1640030310307502550035448002000019014180c4a007d0301d8507101c0210b0410301da4540d03500710941084408808400341a0029820340d407070301c01180074000108a00c081e0850b01410255244d41e01d10340c030910942684607403482d200001090018401d07500140c0c92185030b1060700484034141088104404070b0103001c0341004281115603040081d501150300801102c1d0014292a24460710f4901203815114180e500942650366004208107040d0300207500c076048880c4000a00060625880f120381d954a2801b0151250061811840c2049141d80102942d649000000d0103038000c403580c107400501880e00f00c90058021a10900407600d500c400c12480c0d44c1e20080042007150912000701d80221213a031049541030b0042240341540642000064001c00c43d40340500150342c18074400c00070b80703500580034410982c10240c9400700390790441100503080307201c1214003d56645604044954080502d181e6110391301d1620f010400942c141c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 641089694 1250 641088444 641088457
    0xc090b0c0a1719020f0304053f160e040b0c0c0f03031b030712020a0c05150a060b0408060a05040201120207060b0a05010c050c060d230106120612020d08041a 69
    0xf1120005800b6103002d80e2180024806107500e500200024030440c0703050104c10600000003540480f0307101c80100e02c0601021800310381448546040000c14a0140c01c105000c0001150380560300300e10314007818013103103200161009004082c441c0c00120342d40141002c0d03a81c440c10000071600c041e40c1c07081810761283d000303503651840452400c50306003e03030038801c0440e8040c00e0140e546039410b5203c50391040007904103042c0582045144900c01c0d0100e80704001880c0284011114100d170360600c55400011500654001c001841c0140b008004010780031442a40c403003018100850140c0e500d10040707903035483e8006242622407010550b8418000160700511608038151204005240c80d00015240c0c07605d9400018030951103500c0f82c4d031050030007101034690f41000c00f001046011201e202045540344a206104c0c100090100401c042c03544000c6407107104103d404100b0006051084401c2d03a00d00c611f0001e03008021000010703081026039000c42d4010401078540d0703541c1c00c040300d04c3c00035a40e0211 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 641090944 1250 641089694 641089717
    0x8060f030c1306080c0a18050405120a11070e010303120c1206080109031d0a091a06040b031902070b040b07140408010603030e090708040210180b0408100c090b0c0a17 73
    0x82298140d40e086c0030f0803120907944031401005851402d80510b0340a1314004108541c640070300103001c1c0d01d091130701016160710304171901d60381c00035040c55403198541140c56000e00c8000d40c0b00b100420201c2d401190b85d0900810b001e101180c001032500c03007503031291440d0414241c114031340500020390300019400740302144e110b81d075043c0241d0107115059142e50200600954001350020040000304600d510100101d5400d88011024580200006609030040d0344403000303e283c00403c0050803e0041130001c0c2c51030360701408500300426503d03402c02014000708018164100800030403185070080108500c8152030b000c2c545c0e43c0e15110051030f4060086444100e000c50188000c025a40c94000900b620844080d0b03039501c0c103940e56408101800006004407000c1c024004803520b1800d1120141c040584110050b40d9a61403800300c01900d8440785400049402d80303845441e121995004800d0411290b082030001e4488410720b4415040118000e0010040400c1c1082001c00308220009400501d190 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 641092194 1250 641090944 641090953
    0x20c120706050a06050a12022403040506010807030b0103151d010e071403030f09061204030c03140c07261005101e050103090602090301090b0402041b08060f030c130608 74
    0x58043c00c1081e94007a0044036171000c2d1060003806241c1160404564880c00202495000d044c1c04030b4240101461146907285c00d040001000b06019081017290300505020b00103104c4280385854a00b100c01c030600008080c5011711080810b0051550025829031640c44148102c652021200600070f04500d40000e0150180c50760014840382040c00104100c0409000307103140200e6111304c0d122381d51240c44020b500210600c0300e940021448400b242c0b165200b40c48100d60b0f41c0c0c003401e0260405506840ea814944030030000c400001d540440c0f00c0703003103840103a103180c84c100b40c040036944459008084072455105585401c110440340390030050003400c03400344800c011354480600d4225240d468040f6001101407410401c2554402c0c0d002c00401401030303400508054005001070b0a4030941003081d51150302c0c82003031005600d001d10a03207a02c00911000303080050004440a049124004d003918420400c9542852454038180000c2c4d04482d030050401c6010304142401d603004110034000c1401c035116 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 641093444 1250 641092194 641092201
    0x90604060c0306120f1704030602040f0e041a04110d0b060a0911070b1009022701030501140118080d18050f010c060e0106090e03090415030f020112020c12070605 71
    0xf84a440240c906034150761008810f0f81e00e685800c4000c11508892100707211070803003205080c1074007400c080d42c407481c00503a4a600d440c2c2c0034121540f05402240c0c4d0040d00806000c00500754201c3d188032010b042c071945d040f0755580d0a000f12500204e070441a00040f8a00d085d500300506081c415101c0c03c405c036240b050250320340c5410741c1210305021402049007010800c140c045034956115a5001c15142a0b107048151500040c0c4142d801c801b420f901d42668580002c0e800e85909031000d041d5010a180400166152502404154148074011030500801507005074115000b00c1c6004d01505048040340c00007041004020325840c13a601d40c07548840c603c10340c04107040c80c0c81803901840001c16502c0740d14040c984d4031688010162513105844941d81e65200240e00105401a800c07503940a001030764540000c1d100f400300b903c03a141600000030907040c20038000500b03582c0c2c001c002250280303480d03800520500a208024410f003807008181d0300c64007a02080e000311800080c20b42d035215580501260303c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 641094694 1250 641093444 641093447
    0xc070806040f140c04110702040b0d0b0c1602060a020c15040f1418070e040f050c070b10030f0b06010323060f03070e01030605090c090903120601090806090604060c 72
    0x60098400502d1405200400781c0494540b05500c00f80807000c80a413100c0e815141d00080803108401194902e4400110b0034400758646442902812001641c00805400280e915442d41c89002800d40e0208400890700440c079200c404080389805a001ccc024503541c18500201940d81c03400d4101080c03080c40081d4200058000c0301d130580b8104c985500044919505040c01100c80b0b04120801940040c01c00e00d00c02d0300030142810b894054000e5460313001c00d101c07031001030000703650f01c90102e0700f1214240030500c42580740320011a0803281c4c101444031055102d991145c580c034081680060302100e90000140103100d10310051600408098034204038031900c12001c002d0340100a04000c040f00d0b1054002807060808111402c0440401025501d136039032505400c11f046d400a0f002544d101d5039130410482c0f440400c00c8600c81011003120203480b9445e00da4222980d034442c0c604800c0341d540c681404a1350b1a4080c109a1003d4a503820584400e45000340c4c0c10342d82e5410480d0182d86043c24400ca02c103800c0d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 641095944 1250 641094694 641094703
    0x5070c0605010b1b0d050301060f1115180a0f02191203020708010513020d14012c0f010b09070c02030a0f03020f2a0d0819090608010b0f070212070e0a020c0708 70
    0x441606d03244e040d60f01c0c10b1400c0e1085000c4400b800c05100800300b03242c8040d40d040c00b041d598a240e03a4268074141c10848002140d9145048242a1642c011142080031400550000800650407030300800001d400810146083c04564400d0f070b00c42d10003448880c20503402050301815164a0402040155200d562004211030700717040c042d420010301c503081e0b404180441d0f407810041340005c0c004614813600d0180e001d119880c1101440401d45d6030602000842028400035003103c0900000703100c11b00b50900090074076031002e02140144101c10700d4020441d1001d02c00d003003540d0707041801000701c803100e8100070352140d4500c5a1100300b0b008071083c01004051401545400e0307410b519400ba20840700c10280a45808000c000f038480c25070900010002102211003c5802e0900e561040d42d035929042000d824180183c0281501041c24040304e03403845164401c4d0750010f0303012100380290f486c07000313929424294070342c011100750703c0b4403810491300c0580ca03001131401c4610041101c4c1321076510007040b501c8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 641097194 1250 641095944 641095963
    0x2070c031217040b0a05070e0307060207032102060115020c10030204062714040e01090f03110304080a0f11030a080316020708060601051e030f01090b0609030a030305070c0605010b1b 80
    0x2100c3c071000c04580c1170580ca80c04540c1c408001e0074901031001d030450020345007450b640d1195005074004e140078070820003501201030038a51800340c403803030b020349402000e0345404c01401419241c0c1c0d14a4034120a240c42048820040b1101030802100054103410050296005001c1c0300045010116031001420108030500d448070284901600040d06000e64a922001d0b2240c4260344261180d980805601080c8960b064040c0300701882034503001146009440d0b0b42d0614038010039034005000820522030302003501eaa8403070f40046481406640c3d443c0000b440030380d8801c1d80340c00d840350200640401030345600850003442c001071014828104c2000803aa20012070051001e80c0d00a2800700303065501400182241c902008207480c0741805184e0100029081200c0440e5107814070340040102c08402e10460000344800c0c0c85482c40c200a20b00860740da0140980d00808040d40c80000405262003170056a1045030710010030301495940d01c840016030f0b0850800310302d280c002d21604400740c0a0000d40d0452 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 641098444 1250 641097194 641097203
    0x6091401020c150c0f21030f0601200d08040606050a0b120901020f070302060a050a050403050306010f051e070b0603010b28090203040302010c020c19090f02070c03121704 75
    0x1195281c0c24014120f1002d2520000000300b0b0160429a07003050100d24150304c8810014041d808513a026684819210304800f40d40420800603c078110745c801c854039501060a00b44103491100b840c62a9440c9000700e90821a24041c11100b041403c3c0d00c880c401d40284e0140318140b00494940d0104003440d11603100d169010041004051810341c036a00f00141d001e504036000500b011707241009110558046c482c120b0040c0c00510410100590300d114040d004110b0384020042840c0554010740648005803505041c06140d030000b403da07138400c108981102180a222200380580351b0900d64040d041a901103c0c2c0d4000c0200203407550505101749180c418000380310744800f18920642c51051100000c0811042e00065004590172105000071800f4501c40d40c00001d05020808000b403c10350500300300e9104030b00c6140704001e2070500d4940308042c0d400b0610001060380003080b03080024071a100b0005c014002c58040003050100291b4403c1059070641c41e1031050a02d04400408200401c40d00100f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 641099694 1250 641098444 641098453
    0x506031626041424131b03150510090207060905120c07080d200106051008060f01210218030706050a0215071d040b0904060c090501081302010c051f02040609140102 72
    0x8141d1450500c06410140703a5580b18041720241d02d8103004168040025205800481c200308108401d12000890380100308000300482d092003840d1800251641c498401400c2c1c0201d42441405607030b500900b041907000084a6801d9002800e091282c0c011412041c00da000d8400300003450f4001080032015908160b648096910043c02100d983c2c8800c1d10308040150751702d44022600c0d45694400e801c0c02c00540d207401d04285050420400030300400511141000619080c00d490b4084248915401742415800507032508084512050400300802e05260300d4415140c0c0010103680082c001c0500c040141d00380d0310200c62845040c020303035006440e5030000800d40a950030b002190a02e104907d01070040011891130400c900055641c10207603016a0140da40301b400322101038010996000800c000e09141c5100d151548602d281c034508044080d042c00f0343c4240e40f0007041418410203900d04601c00304141041010801c06000f50050b00406010440011000c41c417414084491002d08505038010f1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 641100944 1250 641099694 641099743
    0x7021e010b03151b030708191404170d06120c0e011805040309050301020c0d0201060f06080402060705150f091e030d1d01020d0b040609050105060316260414 69
    0x80760900070700513101c0a400b40c5241c00c2ca007030700d14019070141505541d00e00e4281030400154a92400312400503014901d0f0501c05d5107500e040c6803415a0081c0c014503145a5042c550324040c449215017803030020030038030f003000c04a00300402c200e5040c3c109014078240c4850310785031101d42d54056020701842c608031140341c1d401440780f055500f0895019100e464100c2426950700b01080c00e903000300c1d030001a25000040d500c11183e078244240d0009101e541d40040c1c900e40390a0740034040350000b91010707006040c006a0807060003400c121100d807000d50b880344030b28503181c89401c02c5a41001035507036804c24001e413841c90081c10742007002884000040701c05580f0307040040300d5400060212144048a220410029529138a000c0c80503211103208010007180c0040c2d00320401045800d140c03c288481c914101c01403000e6102c900079654010001e24a034030300e0840321001a00c240087ca00041042004139018441d07612f2281c0b0094000c42c41041c0701065076480d40c0b101509d403000000c0c2a00c000c00c0d401300c01d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 641102194 1250 641100944 641100973
    0x5041109090628110901030c020d0540030b0c04210f080a120501082b0507150614010f020c040902010c14071509050a0608061807021e010b03 62
    0x1028401a0f24600c001c0360741000d04040c000d542e80b00082c001540340101d203150455030140200ca040c081c0c14405406042c0200101030813500840449042c502040c0503040034400a00c07440d030701c0005100d01c0309480416184240e03141e00045002c200d401802e0314002c01c04603d12074080d00d0503101d200d00403100d10400b4140c884440010804140c4260301e00e8490f050205918000801b941d85542c0e503120143c521440540090714010b0303000450507409007050000d0203800400c511070519180507142e203c2c11a0220849441c0074104010740314070a0000714040c01110380c0d00c4101210341a82d601000104510015103c1d0a00d40c080480945c000024005107840c280c5c0c80078242901c141008403a0148a803680c00b44500ea281c2e80c01620f6010074414030121a152302d012022008916140e00308500300400b14141d15414802c01003880201c10104013955030351070120f805c0c054200d840300c14620708103100a50700d40c60242c4903c07072446512240f450005c4103005446506501800411555811048 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 641103444 1250 641102194 641102221
    0x190915140c030702090c0904180203062806080d080606070209010302060a02031c02041406190e04060306090507090c0905030304051e06040801140a020307120504170409050411090906 80
    0x1100d90104020000050342d84445041c060201603104581fa01d41035400e01089440ca94103801d1129030220080740140c1d4001161175005119810641400c48003114140041501c0d42d00c13003004504110700480c0d40380c00000da00900824680d610b400a032540340521045126031030010b5044441c1b14010301c05420203900410008480c6e204403071a02d2409031a00b80c080d00315400d0700903d1a0005000c0240c0140b032031a40c036800000302c6440b450a1201083c0100000c1d03210b00701424000d420002441c0d694442e80071000440e08610203204d19580b0303103013041e103c41841c040c0045061800c0d001b072003104c3c850020741e41a5100131380158606401d100c100032242c2276800e02010198969103070401c8580b28000900001d000c04000840c0c1205c010004444001008091801c00e503c180200615190b0040c4038108114828900040c01d40302d5050080162381c084280c03000c00c0c8000900040c801080342d001c14800d074000e04000c0000c51601c07017040207000060714514607591005020410070f414006 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 641104694 1250 641103444 641103457
    0x711010f05130215130b03090115060230070503120f070c1e0c18060504020304080d0e0a0c060e0102070b0424030e060114011d011d1519091514 63
    0x400d802d220f0701d060045c480710707599040701c2d41482c0040180b1118090034001d4040c40c4010302c1e141d4102d5420810001e64410b50b05c1e44400c2140c101d0000d108050f40398031a0700313803813a100c1540c0503502d007240d0808035070705d9100e11a034002080001001490f01c0400c2c803001c5001d49515a24188074224075210609190590446032400c3e2010f44600300015444c064004e004118441100d203090140b603040400322244ea9002a01440c010000c0100203240c003011101041c42d01d84001942d01c0b00544403901c0c002c0d01900040104d08120300100d0aa0740046044080d00130982c03c4031629500da0890300004d006078852000803084452005c0d0b03c451006401c407421807440c0ca0001406009075000600d0b1060a0b1f01450401814541c051600e5900c801c180080010149141c1010500e5000091101c80446644000d00307c4c540b41c000202d80d1000840b08030922074015664440c0040880c000444ea48480004089510558000307050b5007040d0100c00b0408490b21201d680c0d05440c0402c05644d44500c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 641105944 1250 641104694 641104729
    0x5030a0e12030a0605010f0201020f16151a040b12070b0f0f04060306091d060c0f0c06040b010609230d2112060503070e01050609030c090711010f051302 67
    0xe8a169100204640550f105800321100440d1103450500050205010305403142c0c11640100f0400343c10b841b500040b1003010903e42e4003208131200c203040540d51030315014001494142040c00c030000b440000450307a480407800722000c020104d6640c0420400c8201c40103800001d82008400304010384a08016040c100307020744000c1d03d40155001181c0c4250300c40e030000c83c0401d5035840c0038081c078170451003054084920046005400b0a0090300c003503982200a00030f00711070100084500e2003c040f0342c1521440310b0705504840003410245009009d580c02401220001182c00c4000112142409083d24141903040b046a80c4d03910788030280030b82100d40e0b0105035461300180f0041900e49900c0010046407084aa81d4824002d5802902c001a07c00300e500c8548250b021001c1402126240d103006070444808544031950f50321070001280c10a001030b00c10316800b5000c81d080281e0036400c8080381070030142d044003c03c60700e00403013503081c01c5840a440f90b0802c503000c820002c006003005002c11030400b018 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 641107194 1250 641105944 641105953
    0x60f0e0c0a1a1b070312090506070218040309050604080703050615180c07020603190f0e0c0409060e07061e1b0f0609080c011a0901030506060108130b0c0919050105030a0e 75
    0x101c00c054580515a8011070b04001c144016001c2c5641c01403d8501829089913440e22b080c400b1380028000d410740502046801c01e01d0000301e01094011a900e80040c00040d000740d8445d40d40b1007205446440c244010b40d0180603600c0010210402c0d0017070310308088002020f40700321070305000d0400807207a030041c4050b0f20014200042000f40c0c4d1284041d521601e0329a9140c4084044070740a00151091465201c1891f401d00451000f840e40200c0c460124840984000460030310764204807024181264680040f4012601c0114000b03030b20001a010b00e82002d03403040c0c54030081d040304456080001c0b5506c40800c0645a4800c00580421069174000c0c0c080c46011445128680350000b49900805000b203441c1c0d90342036203240c10b810303034620f6440d0700030101c500c03201030740c59900d602c0e80780d0307000030500c42c100006940081d40400c100001c10843d1070700200b0b94503045c42c101480d0105540240704251007806003006c2010900c0041007490b0075641b0680d1a04c0c01d50300c8201084014040c5206114a18000c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 641108444 1250 641107194 641107237
    0x1092a020f160602010c090807091a13090506130819020307051c090e0c0306010522081609020306010906030b06070209090309090c1201120c03060f0e0c0a1a 69
    0x2802c01040203024084511540618030b8280f0203400c4800401c0c0103014401000c10403c014900400c640046400401001c10060158160410700d9819000c500340d200605040042c42296158021204288103e003207402a88032506030001c1c0042090300106007840c204100341050201c80215200c6120b50300440c1d0410303003140d583c2c0b42401841ca60301c40070807a52844040006511036062001084032104820007030400034440a028480205000d0501c41e001850ba00072400850303842260343c01180da884865a11100940e45a0008a6020034819020400400c1c1400cc92003180d00901c816100c0e01c801c140f03030040c16006030a004403810740c0014103004d1a00581c0700d41c2001440345a05074069641e6001c003c0400000c600d01501070110400103206503401d070601c800c41d10b0f056880d02088036443d4001c1d0314114445440c940c00c000c10b00760800300e225500c2c0b9003d82140454800b048259416140e5040c14030810380807500c02d800c9941002049042c81d1400900240500da108a02491542d038 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 641109694 1250 641108444 641108473
    0x1e090207051606050a1713020604080d030f1103040209060406050a0b0d0509070f0308070510020f0304030e0906010c0f1106030403020609071203170a060906180501092a02 75
    0x8000c0038003940e09070030030781040c00e0039880702d010b14024100904010f4145220400001e02039402c40070f143e1540354002011800d084101c034520380b441c503401494107a940c1c0d11411a1364440c120300d13402001007803c0c460050f819034060700a05c00d190301f014402d2130035a43c481d000c0101080001d00b4454000d42e07a42008144c64446020030350142c0502d49555589200380c00c09442242c00c010700501c003d4001c0307141449003000f41d0b00000100c2e40c022020700e80b039900d1420100d04104158201d1051203200007242c016003039540c00a10311640c0a9112900000c08600034800c3d0300c113045a1840c0001e41c41d03501710380000c000301e009910392401800840c0c100424007021a1060707209a500350301603404542040000ca008011182c05411841240c00c41d0701130a41d0043d010b001002120384003500c0740000501d43c041558803420007070454250901103142d640d0000304203009031030000f100190401c400070468640c94019001300d0007074058031540d010441c0c4198080c504400b2142d4086010742c0642e42204c1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 641110944 1250 641109694 641109697
    0x1080705130b2b0506150d0e191a07020601050d030201020d090b060a0f050607030c060209090c0406030e01020313021017010b040e07080f0412021f020a030b0d08041e0902 75
    0x1004050420000640c20000440103c4005850119110705020030041182c803142e1190f0400800e020445486541080000c000303040700e0300021016200d5404201b55400c4c01c054000e002c0d0380180d85005500c60720030b45c91351028800b22040750169000744010480c4c0c0c205050086c8030580240300050401225120043c2030311380b0140107988100a60041c44107030b203013454182000b0481050000451460800880c005004141c0c015007440003c240300c0d010300203107404540708014014042d281510f4042d1803107200307401c680100c90001e490010408521441403080728003803500155030342c180340138643c20044503402c0d8030a103508120300c81040714414600005410301a2002c1800181c455042c0f055028a40000410304000c0152500600c041d41400c41007503030b08250000d42030070f69840049011b900d41007280c00e081260031024542d03408034084d04e40c0070b0984447c490740c040c0300101d000030400075080040d003409010322104010801c00e038103461801d034503020703040c0c40031518640d80c13418410100d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 641112194 1250 641110944 641110957
    0xe0d080d050906010501020304060210150e040c03060b03070e0c220905070e0d020d0201180b070602030906130b07080403090f03050312011a1204050106051f08090c01080705130b 78
    0xc140c5800911661620902156015000a20040d4281458060025502c0c540c0c010349071145a40c60403600c56051000090201602c020240f000080c2090b1900c00f414046521042e035900c2e203881c10b015603e203400b0509104480000a051819485d48102101da40c1d00c0f2079401901000b69400f610018004954a403008001e087c50018452914500c0070388902c2c0c009401c0f40c415400300304601c0c0141ea4959404501c1d640a10b0080301c43c040440000c00d000441d508a24405c5401061107000c0041c40d400844c40744005800b500c1c1a5150b0b1a6842d070046c0b075205008010140c2007002030f840134403d41100303902c14000d103401c00c0e030646d83d02c0d4507942e6034160742c0041d0f616820001e000c02c0c00240303000c00e07603004040396000d01030106000502d6039143d010f0b80340d8032144e0489a5012600b0b1003025000b0f44060140140440c10310b50100350401c40d00c0d848080004003240403200001e420300c4c0e0200781c40e10601c00603161000560341c1c4840c00c4030264460300680b035400c04034a5010429899a1014101 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 641113444 1250 641112194 641112217
    0x3090306040c06022b08040201030605041b030b030705060708070614010f08010e0f0d030f11030709031520030717071119050a0609020d14060106090b13060e0d08 71
    0x5040b41800f07002820811100c0c1a12442c00e00d8052820070182d80018001045030185080141d41d191480101d004d0032159002035805400c20f40324800b01603020800a8104240b51420003a200707680d000d158541c0716610074158444014455540403a030188000e0008501c95000050f20a0482101d208110000e820542c1014281c8205100800c1d09209400307001100000514001c2002c04045580d1708242040c0300030151101e034142c0600d101a00a00d03000c140c41c1054a03100e250080004160611910042d2a0b20b44140141c034400d408034401c0700c500e00c06e080300c1224800040115401154000351400042100d0307101c00c1900f51140041c044e0240c0216682c01440c400d555481902c0d146c0d801405aa83d540d82c12070081c0007541c0001c81c07554035540510081801c2d8520700004480048059024082142c05402d101c0800404100709068034007903200c1000f215100c2c2c0c4001064001c80c40441e55603035008906201c070b14020159000480002040c801c5201016a02c1d01c0322b540100c0308844 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 641114694 1250 641113444 641113463
    0x607080705070e1f0302240d020706180804090911030d020109030917061b0c06011806060c0317040602040504020c03030103170309030a0e0604091d01060905060f120309030604 77
    0x494120203c42c0e581020320192001008800e118103060601a5440002d20613502c405041c55104c0360341008920740141104101d81f20a61192031034041d500c451002c46034030746420000744568110301000e08940d40c00c251014105070801407440d006014405064905111b90100602d69039410041000000e400d54008100c0000c0b51501400d200000e070441e2007003050f2011460340342000000c400e9400325003041c10035035440300c00480e00c0c0c0c00e10594000360300354024040040f51a20782944599607800200100b046020f40e12101200d010904140050004000c602c02042a90b40155015040340c01800014903042c0d0b0f80000504030392040301d800f01113810110040051100120300070020750000c1c1215443c500c1e100624589902c580007400c014008040340a0500340c8803002074070050311040000708402d48260303500550020445a9400842d070802c1d0b80070501240c0d5004460140f00082d0001008013111000c104d041004822540c125110500c50307850a681c04114240c0a03d001e0071180 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 641115944 1250 641114694 641114699
    0x1e030702010e04020313110609030106031208071403011e090518010e0105040506060d050c090a060e0603010e0c10020a0f060e07090c05030106110f070e240f040209060708070507 78
    0x2409a1020406583c41140706204001c0b20607902608451060340c480b0309180d402e5101800102d0368021048929019840c2a102000300000803102c001000c58036243d806090761a114221040c40302140e118081c030b40d040c0010800c10088200821000742041c44111582c0e445240f0101200c80881e054448140c10303800c030000c403180c02c0c4208008007141400038010b519145d281c0139900e00c0041c3c0114007a201a1000405102c3d0074094844611002070401c1b445e1306100542401424490052540e40810b110101c0c245160510400c03400c0d000c000083c00c68002c0300340801c070155248088075402c0d8002c0041c40b0f800607441802e944034042c82040c0009071900c07071500d44e40c030b03140c09908043e030312078900300e00010302503046000d41e41101c006150000560bd680d510541c00c2800c82a000d2205110740000440d009100f094003510400d0025500100054070240050918848844840c0c020882200e0110300d414250010408508040c100c94030b04002a5190007207680040820385603508803003000d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 641117194 1250 641115944 641115947
    0x140d0506100f2c060607080d0236041d060a020a0e0108010e0109050618073912030b03070303080f010e0412030c030b0604091b020703030f08091e03070201 68
    0x24005002d00710390010404080750f07140101c0b64010304420801c04812400114a50f84000403914402d0348170300100d4503460a10104000303500902c605144000c1d1a2075160702e1358030306044001d2840d540d804500d2050030600b00b84002000769800303050103039241c4c17182010852070030402c003409140c2002d001039544009090040c83e00d882c1403072903410032210000400240080440582c10b41c3c100c100001580c0d01ca207800036071006080011886510858020050700c540c1003400007565907035880200c4114155200302003800d80000e000d005280616110f030101140078046401812001800d002a0f52401d040c006803420005038411800102034004100e1041003041c0b086005007800d110b04001d500303141e655000742d408440c03034a800301540d520f1407001444c07184d008152005806495aa0750700d860300ca0305009032101c0c1d002800500011542c24034002d100159603000c490b016501c2c60440c0d1107010003100ca900e00500181100d10601c08400035148900006403045030325200210f03629820340c0300 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 641118444 1250 641117194 641117219
    0x9090601050c120304120809030304140304120311010c030623031e1b040b0d0602070609060203090d1704081b07030c0609090e0f030f0d0905151803030907140d050610 73
    0x7401c1008407150034403201200000030381e032f081503011562407800e10303c03550958a180660b502000311840d05203603071000d0541041c0460a03401c0c3d410024002001103003002e4003501d466100d1f0282d0210714114190389400c505c1c91141e20320300000d0a58011842052100c441c078004a019410f6503003222240a403502c41c04510407501d20803d6a09001d40707010b000005941e0402c0d0b19000d007640382c0020b19041008144e43c841c03080154400c074110b442e03080600e0001d80e5180000071110100c0c4010311a6442124001d0141d4030a6600006042c43e0440681c0e861503d401c01c0d00100129105100000c000a0140a11000903204a5960980d0140303862890300907900c443d811420603400841c0c40c90420b0780d011003107492a040400d051507a503416102c05200a100d2000003802a01948070031300b0118151191081c0500c07000301d40300c011081c140200e0343d1680300c155030743e041c941d110071802c02c101983c0f6a060010f800c80200340c0151803020340c0b11242440782c11200c4005001c0051014009101e02c143e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 641119694 1250 641118444 641118473
    0x60601091202030a080a03020c0604060204050a0b280c08070605061c0b39191e081e130203063304020729150609090601050c120304 58
    0x61400c0303007942500031980b607128620b000740480800040c0d0102040c080d0301107400420320351302151564541810000c0c020741290080d03c2c0b01e09800c0301d0000d02004208182c1e054625040c06a44d407400000220341004a6072000c0303901070210f8072a4002c0030030075110291810314003c02e4049400c0c904141009421030303c81c03d4541d00c420308001e445022501420b05190302040210444c4119000040d0100108070400341d101039640c00315080d14a0140b0450261881c8004e124024400010706030055a12503860302240d4500c1d4003045a0012843c07041c03051542103041108074000305030321511610002c801c1260114031002500c11848110705042004590110340c20403070560064081c40030098074000f0101092040c51020480d104903aa00c1d03044516440e440761030a6900000c0000c0d01c000000b812071400c4a0811101c00210340c903c00003005103c81c00e00034842803070900110304006880101410740307410041e061001e40c0701a0010003440e5001701000c0c1005403a407a091a010401c85100c8 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 641120944 1250 641119694 641119709
    0x30a0503040e100b0f0a122c060106050c03220b03090303091e49092c04061b11010e150103032d0305060f0a180b1c0506060109 56
    0x802c6400c0104980703001b511280902494001607000f1a500c1d400c0c013900d00300c101c0941c04100c045040e2104010140d44400b01c0b0a90b0007038a4a41e0790f03070300e0241c44501400c450044030307070800c01c20b82c40720a540a03100b02449000d00323106290907440380521806500100c7d0300341c005030320000034803103144800c100c186420056242d80070385a4405007034154480342d1840c4624480510301b40c485105115280c0131002e100000350003000e07402d84044041c0f94503130015000c5008106a10704c08504a41084e05280540001e00c6074060035440c4415042e0000c00000c10558015540c0e010b034051200c2d20131a03919111310240d807010030b80c194a412036800c40d0521006041940c1c0403d5200b0031807560041c0460440b82c050900c60b00b0a88884041c2c04100c240304a40c8100000114009100903003560040c0d019400030b80f40c01c00707200031401c140080d29002c0d018040344898804028040301500c0d03000300709441c0000d0184108080400307900f402c0d25480410464042d04440c3c100911541d0100020b001480c01 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 641122194 1250 641120944 641120947
    0x180b09090109080f0703030b1315060e100f0e120706091d06010804050f06040501090c061814010306080102040909060e0601033c1a1b0904020702030a0503040e100b 72
    0x50f80d403402c0c2e03d40b08584146410300d102044034801c1c14020b902038208400081d00000f41c3d85d14040850000b4201102c41e05e500b40101c0401042c903a04c103408260342c042c405000030f41070715207107402079170405103a0300b8400800c820007a241116031a842c03001f08501c01440010150309041850140c01c81845401c1810708440807109c0e860106110310520b82c01641c2030030100100c0e01e0301d05002d81000102d410600c410702c60a0240020400c0542c0301c01c40c01ca004c3c5a40e01061512500100c0c1c2800102c01d0142d20300c96200c00901080681102d0300321003c0050500150007a607500115003660850f52044e52600e5070340740d1210600a980c0a420101c4400001400c51581942e41c0c0610990003003003000388801350801e0745040c1d0f129124000c8240444072010382d00c0c5003068500b0030702040401c0082c43c0244000e1010034000341c40d5a200004c0350f41c2031000d1030b01b800122070a000081d013180c00166818400c101862010075010300041014110481000f245413400405001c0190482d03409044403410 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 641123444 1250 641122194 641122211
    0x308070f0b1609030f17030f1005010507020f2b0b062b080703030f06030f02210d08040c090507020706030b0108010b0405010c02040f020406030906200f0c07180b090901 74
    0x40c0681c0d68016254000c510301004030990a01904071603c049410507500d800002380224511500d4500d485102c810700c19022240d200c074011140c9002d50340700290842800d100e0940e140c0b500310801a4100c1070081d8042c2049010361001800c2c40c0c481d0820348815001070188002420a10b071150b5140c846001e403d00e180811441d9592003603203031790380540030500100b04801014440d410543d00ca040340c0c401400401d849090900c0c40e80c84250049100e003000c03c0442d002c0d81c20087c41d100381182d40b00b016143c1e058030328000b5240b965005000b1602400c80c6040440c0e4142c40b03100301c5028403d0359009290107424050054103e442101c1d0a5050141d18001040b605030794104481c140c88081ca0061441c46052001c600034101580d02034030664000324000c5501a85603024107540b07801030f9024012112000c1000320b0b03180402d01203040d00501000920741c903042c1500180103001d00c1008642c4802c0c2e55058500c0000f0825500a42058071407104881c01e241c500d109981142c40c02c0000c018000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 641124694 1250 641123444 641123447
    0x21c0b040311070803040e01090c2a02010c050322060c050c04090203150403230c0601030809131e05150a0303030f113705090405060a0308070f0b16 65
    0xc00007000c01c41c1402854030820030a210090080071410100ca0300d654441070080e005840900a650308035103040c1054001c41c1c4110400d0180c0301d00c4c8031460a00f07501c1885040e221910012041e81480070400070040084d030200f00400401542c500404590413410441400c040c2c44c1364051070400c1000c0501c44045440418540362803001205c0c0052402d910f0300c01300f8100008841c031009003080c0e50323007000107042c2c00118a02991b40c000c210942a0310f4402291541c1d405440c40e0841c1d0741d40020010b01c006202c00006200100000307060880c207d00d8010f00e807003607810040400c20400c545a45542040c4503d020303484d0810a101003030a070030120803010480491a512014081503190208641000407550101c1520f1030010390040e030718041440c8101c0510700300c5049510000e0440291000c5051100106203500d041e40e83d501d01c2c04912000300302c080d180160426500a51007800040025040001040124441d200702000c825042c1000c07507110400904144440307a41c3c8240300030b0745 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 641125944 1250 641124694 641124713
    0x1051503070e150d0b12070e0118021c02180a060c031206090e060115030509060114150a0f08010f080709110d0203070207090c17180a1e021c 62
    0x1110918088071002549000641c0c10186092204010400003c0c60720002080384c1018030762103030560790303180c80320700490b03046565000a1013a2010440703004010b105800102003001881c5100100c013508cc4801c0031140020521000321801d20640c2c000391508441d018903081a0b28110201e0340003240902c0d228000d03181c480b81050040c208140320701e201d20700c030400c2c0d070260000c0c200001c410800922040c030241d5441c1000c0c0160a0f080d10300800900c1554403900900d0700c108081d2001c2c0c102ea1b481c148550000d0b00d00d01d015654005120300540d80f0f070b200800080e20b004c0c14540c0d140100c0300103a010142103010107800c1f04881b81c50001c0180898000003401d04211048543d0004104104042503591401440411624140000180701c3d00c141d00049007030948001d4001000110040ca206440c280d41c0388000141c54080880010110001c509503039203001500030541d00c3c0301e0425030354011090344041c80000200c2a6400704801e50500008a003441c02181043c03812600042c0c0341c11190 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 641127194 1250 641125944 641125951
    0x7050409020f010302090d050105160207080303070e10030b030111070b060328060f05100512030901080115230d0608010501030812090a1403030a0c02061902182701051503 75
    0x5150700001c4410481d22002d0107e00c1b450b400078002c000f0f6003400c22040c00407041401d103e200500c00e541021070503a00100440340941c0254503000f080034251002d20a07003011028038030302450740c0c80003031003940d4800b2301a440004074040c0c409a680d0f072041c034180151603c0588214044e0744080e10040303d0811107185030013040700301c0d0002a10095945481c03000303081c010011701c040742e0400060122580051842509654003101c0c115559050000c100c2e076030b805020710303050004404400402003c1204440d0200540b040e00d080b041e0001080304c2210f140302c290090340402d240000b0310203130701e032034601c200405809408028800e03545540c0341c1e500540209103181a06101d20004586081c00070080085100d40c005c2c01d1600742c107000010b2a840e500101c904090450510342c10700001440407510500c1400d1010701c1d402010b1168400200179041b003815a500c8002024100402d9a5007264640058080e9404a440318515020303503034044106902c03840c00b400340f04000380254041d00b006d8a50 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 641128444 1250 641127194 641127197
    0x24090b01090f24050f030a050607080705040b030f06010e04020a091a0c0601080a11090c0a030c031d07180227011202070f021503010501091802091c0507050409020f01 73
    0xc10307600400d000d100509030b003080c08030b00c0e400401c2600d120700ca841c0c1d184004c5503000c54282003505070100071b241e01d40c0c00c401401045a0825000101e020b400344032182d40003021881d046080545070001602d00364015101e040d1210700c4001080102d69002e0000381c5d10407819103080d4101030316a20040d00c0e03c1c169029130f000480c0c000040c400040c02005c107591700c1d403101000700d0b40103503544c100702030300d44000d10307003e032030000c20860406000d040c10a9682d0003000c107100c03042e00c0d00300880030841c028038203800c02c5001c243d03c1d901500301261001d80e4080603c1c0c240d5015040403481c00b0200300800001d07045024095005210841e00403141c562812007075540420b5245241c0c10440049070b5106a850200007010300c04a804010b00c2a40003880c50040d209071007407961805200b40000381404248526400070305a81da00388282c012082046030000790900303000d400c1c480b2020009809030303002c80c0d102005030704416030103090190420002d401400103540400c5003806540200e0114008420741c00d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 641129694 1250 641128444 641128451
    0x6010306080304061b0c0b04030606090b0112020c01093306081e01020c030307030509150408090d0203010b0604080105240d0209041a0c03151206130c030803010324090b0109 76
    0xb0700c40344170954214690240440c8001d5407600030040007a00300c0c1c08262134032490107c001c283c1100d41e220b6010202e20507104d60090103059840ad0019500c9048822002d540b9146480c00013041d1a0f00d0140d0003a04070101400151403a4004070b00d4210038002509603410501c04000400c008560140024100700118688400380d03036085000e440303812013004852200204000e45150f06902c034600458030b5006403240141803580035044140250f5020340051400c0202151604d80005103058851000d0004500b90011900103006a0002d5000911703d9440c2e004004c00110105800c0c41080d041c56141d0341601740050105003000c0b042103009008000174004981408414800d528000d881c1072502d20862500e203021101a03001665144000036041c006013140e40361640e189800340034403070000c0c00c1c82d5480c400d010304c1e4000c8541003070700e850f400340e48080041884900198042c500505e40121070703180030604d0381103404060200c1020030340740605100000382c1d50528141114035081010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 641130944 1250 641129694 641129717
    0x30b2e0207080d030911010309030e091801050c0d140103151d010510140d0308060904030507080a0903020102070e0c030708100f0611010c080423030d0f140601030608030406 76
    0x141d20781081500800b2903886019290000d00e64560013110f0051703c982040c0c4050301ca110010b40a80d00d111000401244140240740c81900b00861821752254080c4a02401240703445801402c41d402505e62440843e0001801140000c00d0302a8070b03800d800000c1c2d501490340c59900c075643c04c0e5402d69142100c03a910346031411f0000000902074482024030034020010707401e0200b20f03158114640c0c8154030050110300001e00036440c0003202300d0b2000c0c1d050384900050f07980f9617003084641d600050046050000a02002005c144010301a080d00140342c0c9410101c2400c5000181c07602c2e00c69405072081c042c0100401800d03151100035260008001d050a881c41d4550810b60106810642c0000310300030343d20307100054401d138001052001091b03a0030003002000d0703036882e0848056101304c0303001d0404040b0880504101303a20041c1260030202203805d42c1d042800205080c0c0a41d004c00c225803005030b40f5070466013040346001c1d0f185500078000b400d042080a29281c40700e501c070f0107144540006e014070103402 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 641132194 1250 641130944 641130947
    0x180a050403120515010210020a0f1107030c0b040f0e0c0706020903010617010c230a350f241c0609050f060c0711060703050d0c0f030b2e 60
    0x1460445030104180182d00d400d07040340b504918159813003030041c454021030140e03501162084500c43c00c0640e40d41c40e03207407807100c000341c40344904d01811101c0e038400c03a280040810300b02d250120107011003c80c116512860080c0c128131005c1540c0003a80e80340910018401222608404c807035405603c00c00240c1c0751398903035001900500e026030000e030340c2202c540301c0007800000c1075210454490340e0ba01c4250b400300d0b028409201c00c203107029405441d40000c00180d0a00e5001c0c0c452950703001754501c05007406482880402d150122540101c0202c40303511001d000c807601c80d0340303112540049210780c01d440780380824045000e0710300944002c5002c0c2c00c400680420a02d9203644c200c0c5030076040725040c8403569080c900595a610041c54141c0940246404103030422000421210081d800c0a48900da20320b100c0c080101682c0640c134120113000342000500302c88200ba018860500102c1d8507004900b610462010f001d0300c7c0201c01d541c0c400c0c1d140c052000c0f149460b5001c002c52080340d0100c0c0c01ca002581000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 641133444 1250 641132194 641132207
    0x4140304151b0c0e06100201050402060d090c09090f031d010804110105040e0f161818090203011409070515070b0c310e07021c121103060f180a050403 66
    0x82c0584183d1400420300244051540b80181001d07200b13880b032905e030440102d088070340a0721700940c060b00400c0719011320300c2690001c01d0a0340c05099411701d03c990341c1e0003035030844090f07020845030014518601410f264115101100000038944404420744440c4002080107078010002400d80d013414841603802d900c980261805440c02c00a50505400c0114041c14000c45c1243c1e65590041145074940095110340240c4203035098034407411641c5414655403500c480034204010b00055900c80c01c050140e6002d0250600c60110034090100758280544d10a080c91260f800142c06185803810000180c92850308441c0f00c140c121405e140d01e900c5513440c1014600c03c0b80640104006d001981e802d800205511000f40c10741c40001d0f0180780c5654204400c0c08050444014015070407800c081d110181850a000f5003604552420501c0401216607940c11503509000c0d550165002004010040c1860b9272000d0b00354030b040743c0c8015070501000e0700c0d60b12682e0003402c0358443d94441000c54200340c010314 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 641134694 1250 641133444 641133497
    0x40f06050a030c1401020d0c030807170f070f02010b060f0711220608010b0604030b06180c13051c150209130b040f270302030c0f01050414030415 64
    0xc00d6a035155a0328100340f20b507010030340640300e44070500d0502807010b0b40c00020071707500549054880d0448480c1d80d440035940d80074010504810f0009800d0420108001404c0540c4188500c07182e900741c44c1050308004141030340040190742903a2415401613000c1c0c0e54442a41d0300d40f0902000150740b183c50b4a40011070100c4400b4554000790b6440b0340c3c0368075440c51540b81501440d200c8007000000ea480010030309940f140007203160400b000700006d00100d880c5c10000f03a40800040c2a003010101c448607002159a0b08903a00000c81401140c0c0301695003402050000400c6e00b11000d0030103110450304d000c80daa4042c00018100c00c1c11040903030031000707560155481d0007002020904001e1000030340d040544554103000d0310541c03510b120440080346038810010046c3c9521042030380030703030b91440310b2a020481c0f9405506611081c0b02c02e1159000c1003041c05c480d15080c40000c116402c1a01d03044090113002c00c1da00300140c200780028007010981103904c40007a0407a00c1d041035100c1d50300003481d0640070f002 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 641135944 1250 641134694 641134699
    0x20a02151b1c020403050114130b04020411090d0b070f080603060718080f10230601050a1202030a150602030f0d0c030e0105130c050616060c090e16120203090a02040f0605 75
    0x11800205110040d1311a0449884945015005580f11201405002c40c9c603d4010800380e1924041000b5080c03961003140c000b2072076501640341103802000908843e0041358121f5480004008121080380d021800c1001e02856007080b03585428044000b0703481d00d10040004003003207840d1028044e80c14180b0813400c01448240c0507030b0003601508241c152103400c99601c002440341007c40310301c8006040910880e00c0340d44212265000e072a2000115010b6104203084001c005031014240003000c0070384020b60061224500024204124008090f04d00111b0790206055401c14040f10040c018000101c07114000c1e00b900026240c10003c8044e0020503001580074119072234881008800c00c2114484a0700d51f00900b405500c1d10380d65410040d0501c14031541c0f50b030a421040c4079000182403a0454101c14409013058640030740c80c1c42d08004e91600c00c403908041c509041040140b80c82e0032890b00c04400740365440552540c5081416543da4150401340240200e6031440e4400b0001101d41c042005482c00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 641137194 1250 641135944 641135947
    0x81212180a1b0303020105010f1d07210f1d0604030c151d100605010504030b0606070827010c020a0506220b0c100c0206071101020705010c03020a02151b1c02 69
    0x40b20040d0707040b0500d80c0400c90156282c803001080600c0103071105070031120024031848907602000300400080d0700240240007449000a40c0c2c40e002d031115550040c1d505110300002950030484c0d41d8500c04d8035030510036014031150158090900700c0c00800d425a0090300743c10071a90f085024035150300c0c1d00c0b562000c048801444c00c1c0c2205481c4407121f0181f14009601130407501a040340f0302c42041254814460140420020002000020507580d144c030307031044000f002c0300c1c1044015181c54141ea48103010004103007104a40e0740c0101c034080202a1070810317081c680307240340000b01e0b0f01040c2e4802050198034803804002c14880412030a101103842c12100c0e400786003604c0e903074a1248040c180c202101d084d23098000c090b415501e4000c01e10035510848826070050010761240c030415502c83e601a0b074000040e5408012010200d0f1090003480c280d0300c500d40e00160317503030b59090009003403424040e4003402031800d01082c4140742002a0f008020300c0b55011109603610300e920180c80220105400c0301034080d00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 641138444 1250 641137194 641137223
    0x15070f17010b04091d12040f0f0f030807061b110f150601181d0604060504020a090e09101a0306090f0a030f0507080310081212180a 58
    0x1404102005950a00e03140d0020384a8490544032212109010303007001040c051008106128560700446400c007503e4580701c103550307062a440d606045244000002904002904000b00d00c2d14401c24001803606180c25030348903042080b4070141e800d1520000e0175a030000700302501403040f540d12401186d0f441c074803185400325490070080c01c450000c82404003c4d016a0502c2d41c081c1c3d4000c80d02110280f0815600409603903004019100c8950b2016446600d4101400108804654200b8020340e50040c041d030200c07a1078100200001d03581030340c0025001e1401800600707035090700080311000351044d8510f0700351141d60310310049180641c820b641010407400c01c0701421114090080201c08001d050707064500540e14400450751b54035820505069550118940c440400e10404034225101c00303d00d0010702e05591511041130580094404020a2413403d004101c0302900f0403001801407943c200032420218407610b03003400c0c0c03100140315880705c042c90076a501c91650103022110740c0305c1c2d01c034030340ca0318610713 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 641139694 1250 641138444 641138447
    0xe01050d0e060105091e0112140f100501060903020105031513060b04140a0617040503071205180a14040b181609090912050d1b03020c1507201507 64
    0x10020f00c2400c1c010545d51010500c1421129045800c0010058404180317902e0304140c01d034058040e000a88406003004000340c1c40000c140003500c1071820b180c1c010610f104904255904490040c1e1000f014004141403c00050340c001007566400042151102d02400708080464803030008000c80040f501c1c41c0100100d42a8100e4001c0c0040d0b8443c0c2c510b40c4040c9a50405010b441d03500c500485000c03804000310040758005007070415074414440c0303064908011013680c1d8455600c51661010000c5200441c0c00a41fa0a42e07845c2014003800444144868500d440750346c0c04076607201c80074980500d8450b0359160550b220410282d1031070b490100040054a0134803820100e03103d107000d52a0003d50a002c000131007000300d0142d1580c0d20742019680890498852003501d059000d501140f1049403034500301081c0b810092488000c0d140c4c03a032000360b601e41c2e80c2501241010140780c140c030540d1a41c0740500c40b02c0c0c0d03441080316019646c0344039168440b0b10074080c0c451074860081007421400300b40c0c404008002d03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 641140944 1250 641139694 641139703
    0x11e020f0123010510020f0d0c1b03152a090501170403051c0b0a0605030108101e0c02030d060605071203050402100e010e06030915250e01050d0e 64
    0x20820002005810940c0001204515210707400b403800030460750041c001031901800361600b9025500407200520008070b0b01c5030811041d200380c900801d101d140d0720810702c040071807000c00121116044480e0302e829a610414111003490f41031070b0555032404c0d02e141c4940300c400c40c010700084007001070518642c505001400e907042409080e00158582c40591000c4c10400c01c1c450107582d050b1101c5081500c42d40c046420482407040d0086550344400300c00045460b0845403801070309440d0380300c5a42c3d605000c5454a0440c041c4800d07049189000c1ca160459108410350b1010b802885001040d4807801c24812031840c00350181441c3d41d2854480b00107181c0d030b0410f0040140505c5420100408680e0311401d500b03c8500311000794000280c0c40b001d50300b642c40b594111000e9481414610526402000410f5550b0022110401035a10010200000d401000440356100c44e10141c2c1c0c08203404207040a02c040401c40b8050b005100d0088140600c03030f03016909a404036039014100f001800d002030a016500c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 641142194 1250 641140944 641140963
    0x909010c0f0504141915020c010206090a2004140c0414010306080d120e07030605060a0e060102100e010b0904060c0e030316110f04020a1d0d0f0b06011e02 68
    0x4646110540304041c1c0c0910255003c440c00740d05203c1072184074005000c0c00d850142e04214400c94460004240440c40e24440050040b565004000b603222070740c00649400d2001d080b020369075100d021010f001801c001c007501e00050751107840f01402c07110350002c50007030b100300c000101e070002e0f000c1d04100f111000080500103c52503280c1d185035104103c0015801c48502d401440c1e00c41d00300c4074240001e1400f80c1d40d82d6441c6840102c0000f0b1002c0c10584160070029507404c2141c0a075160310500c00185005140345010300700f501502c002604010307002035612080c011540c4205030b110780c054041c0c10320070340c040d1600d80d00203011034005182c1850481c009020b0b102c0301c40003280301c45044504900340002504d013012528404009140400d8a5980c40c1c00c24640080c0d0780911940300d600317140d0710356001a10f05500e01d51222101a11100c0080000f003101d890040e004407602d4559102243c0d40c40c01c0c130718085400ca0441c4aa03a01e503c401210416071800301c1c16800404800305007030440c0c0c009000d400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 641143444 1250 641142194 641142197
    0x70501230403050a1a011a03040c0e100608010b09060301120309030204051302040507090f23030304120c0b03060312160506040c170307050a0b130c0e1006050a020601061d0909010c 79
    0x44061424a510512010030b0280c41c87c000b00c1c9076000055414950010358100d0300880a07075800316501d030303564420800b0448601a0722502c8010400005d600328419902600240e21814144081180071030f409000c1403168003032004c0740b490b10405040c00744441c200a036401800074015890850607140025880000c201d000b9858440004e941900c207080c0001a100f0501240100b0391500040d0813803040300140203103281700e070000b20302110740e01040180700803c4920100d1406c445039051030f00390a1140d610611038828100108451503501150340b50340c40b460252550b0b01c0d41e40c042d5804c91701e5085030000920521442061005105418060008503200d81d40c04240404004070926107038024038600030020b80c003107480d8600086001c0f0b20303140d00000c201854908201592100c08106440d82d2000a070360b840c442c14003079051081c00c0318502400d62411701c98a1b01c201c07040c00a5076100140f01301400c02c0700c04a40c1d544080440501c044003220700510380036440c00c00b0101c050080207901c11a40 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 641144694 1250 641143444 641143463
    0x130b0705030603070b1c0e100b090403120906021b1006050d03090e0c0910030b04050601050406080a050c0f070503180d0201020604030f030204170a02010917070501230403050a 77
    0x440251084003164820388001d40508a124609000c8404a41200b00c070b5117036540404004c017400d0341c074a10800c500e6545840081048000410000c0120ba0510451500491442d0100030111307420042c01c3c81c00500f40600041c12110f9418150700a004004410000b10780f6006683c0041900042503100c9500d038290811015599104206010781100740040104a60400401800002e61160756205c441c0204080c0f0340008100004c030300843c01c0c1e01c50030200c2d5135050760b02c003541041c3c4609a40311400f8204140344c1810300c44060003501c40140021f010702c0e212400a108050001c0c25a031804c4204000681c0700c5606246c06522a000b008480ca078480c4480070b014050310385614111500d03074040e0042c1215449988040b507421140380c01d810281a001c210004c0e40f15115001c2043c120450b034040e008203c41c52000420784a5140d020702d03d1440c2d141d0307242e8400e51000c504441241d41c00d00741071010201250384000703440d9074100d841612060110340041441004140050244d21403801135 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 641145944 1250 641144694 641144701
    0xc0c07090615031b020a110f1002070305070e070c11030a05030d0605040b09060609091b0d06060216051e010219060509060c180d0201180b0406020c03030f0a05091206130b 75
    0x611151500813114005a100029040105a014147c2d060174003000d000c5200c03100840c0d000c6410808481c0912005078803001041080c0030091002c0350107800942d50790205420104402071a580c5103901c041d2a240d03201c2c1142c0340940e002c104403200950300100380d0b40c1b21001b00c071444005102d54415180118101041800e8501d00710f40314a1103081d008115506010440d018405c0d001801000381c829072880112204400d41c08401070031400301c2c03840000c501e0a040800c021300b0074000c03030b60600048031003440030300c075a03500c0060542c000d810404148441a4031b00780100d16214180301d000d04001001031089090113000e40081d4440c2c40d1b8542202c0c071588622264950a05c07402c0c441c0e000142c4508440585840c0c4840c03804d4099005140c5407600b114000060a442d04140d40804400940010304010b2640c043c8440818290205e01850a0a5003c9003031403c900c00c034070309001040000120b590903951070302402054040008200c8401345068082804441028882960a180f000000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 641147194 1250 641145944 641145971
    0x501060207060e0907030509030c2a0d0c060f021501080321040c0b0d0621060621060b041104060c061406100f0201020c0d080f060105120c0c0709061503 67
    0xc2c0480208041c204d2140380e950303a5404c40050101802c03011160004110440800f44e0800c0825a0080c0041080c0142c255801441d458010140040da003d10350750303504940415445100d45084480c28100b006040c41c00010413810112101030030f1018002880c008503429100101034000b14244917081300300c104100903c0c00802c2001c40b0000c0c44100300000074000c4000f40c001420400c1d40f5402c01188040c0c03500c40900682a20400240c0c9842c0b6240815080c0041405a6001002d4019141c1464084079403081d00b00e961a1038094040f68944407003d42c0d0f512954072841070728504484258a850300d4880040640710a640709407002400d2400c030719001c441c140001402444000c01c01c00002032005810348840002142103010340d54240520060344c0000d01100c1c903014050394440d602450f0400c8a8000307210050640c0d41000820f108100c42c5005100c90942c00048172520143c6034042c03000d000745011002d4001402c000c0c20007600043d200b6480ca514540201c1c5520140950b0880c03424 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 641148444 1250 641147194 641147207
    0x304090614031e07030807032102031e090c120f120301060909060b0a0f020703080d020909090a11010c0516090203070806040902010906031a09090303090d051207050c100f050106020706 81
    0x1c0f400c403507401150042000aa03c5001041e0680c400d007086401c0350340914480c0d143c010b40b9044008031603000410031072a15081c01180c0594801000403200b982012204035030740d814a200e8181c000c02c0502c50750310a49a08104503118403030840200c4007400b207220f41c5100c1d150428070685000c00c00d42d810101d00d042d82ca002e20b9055400c03454a00c0d0400100c4038003203079074043e4140d00c241540244c08001c000b264504000f013402000044001d0b070b40c0c1080744203008401c0b100070800d5980750029040500080c4132899087d100c0728007480c20607003000c9941020750800250354002440c0c8004c0200c00180100b554010354071481c40d5458800140c1e41d0f21007800140e071403001c0c0090010721005400e004a9011b5803110340e14020700140060301c1e060384804102001c80075500c00d0103e030300200070440258401c00200c0c59909040c42c006003801600c80060198000183c03504e0144400030030401d410340b004100e6a8002004000e003403022840350721090005050a0007440010b000d155000720f45240200c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 641149694 1250 641148444 641148493
    0xc0b0703180f06020c31021306052d0f030906150315070f030204030f050a050111070b1303050708190e030111030a1a09040303050105040b15071202030409061403 71
    0x4024000340c000c85d600700300012004803510703058010307a410742c803541c0320312654210030b42105503400581e10501032002213035440b1254064010444200100410038140e03000c1d90400d0f100844006030307a4458118859013500400c85007014041c000300801110b142e00240281c01140c80315001c000c0805050180740c2c0320751092200b070003110009800700f0320781d42c421a40e02041040b24540141800e44940c0d0b4580101904001503845030701c9400d259060240030310038050406080320300207207810000c3e911104500c0c0001c10361a02400200011410f16000318111500154014521550350881d40b0326205010101d440340000280f40c0c41540c0000d042c144140d0400d5461410000d05550f6050800c802811105000906c000609920411503458009200c0d000f98441d490204040d030612040c04201d0b040c00440c28403c1000e648603d03010b1040310b0481d080039400010000504104041c1a480c3d40b190703601c0000d4841c600300c4000355502520010050fa07040c04c5003a150340040d400e005031103007403c00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 641150944 1250 641149694 641149697
    0x22a01060e1504150b181c051b01081e04080403020406080307060c030515220203010303021e01141603060510020114340c0b0c0c0c18070c0c0b0703180f06 68
    0x208000c3c0c01e40726915101b01c001c180000c01d1443d04812003806081014401d00c0300700c07060780c024180c09a001c0840c5648540018080c40d0980b80340c94803403a0401e048003007500c8890030036401c034042400d01803c00c0031940030315000740091103015030302d00b8110356a81c40b80c101a20300c1480e00e00c06480040c800e0040d14050707501d641c450340120861500300308240110385e04030401e04041c0410343c6002c0b038440c0003850086000c1e40261814250024165000340040110407030b95915000865030304540c044207e0f5000390f44c4203000c18cd210300302581038008151507008641d00c0703a03800c4c000c90100380e415002110004280d100c0d2000396141c113407400c461032480071038018200f004800b404206d6041c201030400c08068918210855110b140c03600b50a800003500ca00b00c040340d00007524134409900b00030302c4491a0040d0341ca0707140b290030410040c01a070000381c00b54040004220440c0c0510030310354180c0c00030380f02e4403141c940c0d20340581c9409001d0441d0b01c02103060304020940c00040002815100d00c0c2201d060307 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 641152194 1250 641150944 641150947
    0x1f1e0e04020a050c0604060204050a0b1914130305060702011805062a0408060609090307120e01110f06010905090706020601120812091e01022a01060e1504150b 70
    0x1404100030103900502c0d026820040144007080c1c1ca141d0401055000e60b000e0003005035500d003000c0c00e000d80d2068a41210301d1400080103044204103140700b100004800c1807038216a00c42040d00307407000714030452403240050115803601009002000c29114041d034400d40007040005440290714523104503241c070152040c1c010300c000826074006403000084400c801c4840c42409480b52007428101c2e0810b800003500c586c88101004904d041510314641c0020401005506160740783c2c1d0b861441404800c050810840301403100c1c0d400ea401070120710b81200c43c481c2a00c14042404641a40d208424450205014100804a50110b01c08110030b02520516406095030340c0c01c0c52032118880300ca60300100c031032420070005070800811802e1020700811811010f04803400b0165643c40000e0f280207245002d0f41d00c10000000007030807041c00384118103604400b47d62821000c0c1101d5006007010b5004910040000080120104400c47c0400d403414080703c0c1041903041100c10300c4c928000500604210a00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 641153444 1250 641152194 641152217
    0x81e0c01180b0a0e2e1e0c0c0b04031b0506041203030207020604030b07051803070518090f06090d03060b1c18061b020c0405090303160207051f1e 64
    0x240000180032034107482c1400c0100c00c41d2480404c0c143d2514450840b900c4003182c09014008071180c0805218400c241707071201e1130541d0b6400446c1505040c03190170b0244841451114100150070038010000c06200c40d5054a40356242081c2e002842e6001d000c0010001c00800855945041e4050fa0250b0f604000c18011101d042d960640007507012900907640900f080c84000001021001c07118403840281d070303400791201e40360903540e810759240038903042c42500015028010740c2c8600a809600161481041c0342d2a1107092140341440113070030801815000303000411501d85000120380c6e080820540d400c028030b50b0754a4400b4118010824840041320b081a881841248190030880341c912203a06442c500c400b071591008122029802d8402e40001d42209621640d0740500041d0f034240401e4900740710700e19014006544a04c1b0043c2141450100018450340081c800c105c0003020700400b43c00c4107001480901003040c45100492908006401035210386190701401e040c100701c070714aa888020743ca11 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 641154694 1250 641153444 641153459
    0x1403071a0c0a0609121808340303080f281a0315220f0308090f0d090f1401020c010e04090f1a062704020109081e0c0118 53
    0x7030000301080c0540c410380c030700140400c007640314a40a02d441400b03052065211a10040c01400d041040102d00c581080c0007040305a03400714082d40508003a04207550412011800c9000030301d548000350614084aa6020040640040e1214010b003002c02d20b14000d075541c20009499480b803447d0445d10142075401d849040d281ca6040181001b103c01c0d90405040c4c00000030074a0104400c48105125010000b44042da40300c07403510038158500c44510007241d1490741c80316000c0d03189040c402001c220300b807000625480d009000380a00e40303048105030b03030a095190000174142c1d90f640c01a001d6070b4a8207440064000b01010b040174813042d040c0c000d03040407407042c401510030103481441260440e4541c0d0048000407a0101c068034000c1c4200d03001d04800325110035064000400801c1d0343e0140c1d02c1181c20304a1700c1c100226040c0c100c41070110800099983d07100407102d5044c2c40c2d020500d60711802c00c818550b05060601600b1111f880e1003210740c4c0c000d440004441000c001c548152000f9103025051100c003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 641155944 1250 641154694 641154697
    0xf0d020414031c0813050a0c050103050112110609010e0607030806090a0203040f0b0406020d0e0601030c080c010c1403090a080a02010e040c170a021603050d0b010302030408090405130b07091403071a 87
    0x8841c00b15000205080c6c0310141040f4100c4011100078816500910007903805104950250004180c0700500d4041d5070340e08000d103009945454820400819650016841803d5000914a02408190325a81d041c0341c00380803010291078003413007424078000044980000384252031040b5000301c5945056201034403110040480070348142c84080d02006001003046450044081da095007100400d130700d42c55030130501d00900c010b40001c0c00c59084454107040580e8800341020a04d17401c81d9020012002e5404c80d20301c0c52003502c0c1c9068200d607903000005100100400c514030114000e0326846907d00c414020801156568000400803601c1002d46000d041050241280e011000000c01071506c1052407403a0044012440114001480011800f1410100340a1070421240030309055003507040c15600c0d902d582c0160300e8030381d01503540da1001074225041c0365031103214190814191450307814010b40003001e00102d4014040044c5403003c02809500380040d4900403525142c200602e29240d01e610344445 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 641157194 1250 641155944 641155951
    0x302100c021009030c080303090309060d0207061e0b040b1005130512160914041104021210090b0603010b22031202031b0102070f0b06060f0d020414031c08 68
    0x2000028640e040c01601c900305001d0840006446010b103c500e1407030041c008030a42d41104101c3d8100303100f444101400002540c1710325104484171030325010402e207403134000d01940c00302500b00e50a012002e184071810980d40f0001e002c0c00c250900940f41040240005d840181e022607070002141c22985010394490300150150600400060100960b00c40c0068a0100303204070003006a000b01042210300c000403103080c0c005001d0040c00307000d00140c0049803c2c501d04020702c00360880d41c006c1c03010500d50f501c030b90441c1d00030200d075a418945402c1801800300c1540e024001c594403585013508003002031910782c2c1907a048505480d2214500518014131040c1c100d49030107039208540e80110080006040360700c400d861440707a5402503464051192840010b141c48a940d00e03a01e91041084c0404250031050b4141310715003101601c0a41e848a10210f0424441d007682d1164155000c905102c140300250001c00460308a4011131050014000426840b05c801d240c511091802d00c01c11443c4083c000c9950550 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 641158444 1250 641157194 641157197
    0x7080f090406060f02061b0702122b090b070f1b0807090204050d1104060e070507020306060a05030a020409080409020a050409050a0c09180609020a02010203090106080f03040b032205060a0c0c0804030210 89
    0x2420040d50103c0e0300e041100864281700d401015040c100c128903284000382078050702c1d02c85074190f0104400a0018901406803550dc4080051034005119814001312540742c0d2256440419480200d4003c0324000790b4001c40a4901508500148113a030324001d072025144002c003c0e610450710b0356900c0c1e000810302400c0541140d222003000410401c40004284104200d440720344e80c81c54244109820241d005081078802c1c21180c01c06d00654070009442c1d024640c0c10b9a001030a1074807800c2c00c00990140c4d5014815860000500710403440c1e1000141c0300311200d0117003d101c581c035800c40120681e6104180040040c25480c802c11030814058160f03a10030942e4a0005180da4a401080c0c00307031380c00190880050b031340000600544900c24072a49000b0101c0c0c3d005081001544e0b0113640c2c80340301e20302c1190594a0044045900c0e071075541090b08445502d100342c0e908005042c6450380e1140700488814504500d0030413680c1016019860000b00b25070b1100c005440e0600396801c0101c00d081c1c4605040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 641159694 1250 641158444 641158447
    0x4080d050711060f1c020a0804080901090e010f09060e070c030c06020c0304030b04122c120d08071716080703140411031b210307080f090406060f02061b 67
    0xc1a48400c0f00a02c480104091500d690302c40110382000a003000d030002500d0f891040240182444d403001400390001da219808035903541036803004a4241500360420780400c14100c0001551001070314421040313030b000e0a018407003540d4070404c40208010803106240410b0351a180391002034402c0c0642c07440c25110307010044c240001030505516640283e001200c540b40d14800b80020302840d0070220506550624200310350701140c90742041403a0b4400e42520389a5007000340f0700e01c590740c0e1020200d180344070502200c0124442c6100181040c1098403c4004035815400782e9400000d8410082d00c00c6800c0c1042e4088046a801c0c12a51410b00500380c41c1050b540e050700d074a21217807400c401405140104403650700c4c12400300400d803c2803411186100c5013020b0780c80181594444815007070340743e2060140d80303001e001340104150462084610041600744009030189110b0202000380044500681d030800c041c80c0c0300ea50036523070901e81c0b4a8143c0542d111100198040a08201201100f1454213010307 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 641160944 1250 641159694 641159723
    0x609070b0a11030313060605040e0703081b0f0d1e0e2101090c0501030b010302180607020a1707091508250b0a08010e071e0305060f10030506031204080d0507 69
    0x4038115002031715290b0850f49100d914506208190240380c01402c02100c1c20404c5845d4483c00c195549094071008080250204007020100c00c0d29002401d60050141078039170300030f041e6800d03940f58079882400340081103002080e80b01d5505c0075604a10125200d465500c1c80490304d80c01c1204450344129216455400030000391040c0500307016250b07000d032103224800030039800d210000d8182e540390f41e001d604040c0f06000911051090300c11980241205940c4155612401d00200d8044041d6400491490f901d004440340110307000111841114480c850410817a4600b040303040144003c2e00c42c80101d03a200540500c6010b05840a20324007070408091a4899035983c9900e099641009050001046003c401000306c0a4070010302c56100360285414030400001d090006800740c2402803141c00c1680d03440004201d5100c207110302c10382120080400d60350004422005018020031a456030007401010460b0038181050401c1d182591b01001c003030401c45080f01c504036010342042e201600e444a80303d410 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 641162194 1250 641160944 641160977
    0x1b0105010e0714071a060a0e24060d14190504110f0a0e0907090b150f0c0a0c090905190201091505041203030b030d050702030c1c0209180d020609070b0a 67
    0x6440071a01c1540245c502894800308120800341c03580c2c0f0a840c00b50808d82005203c0c41076000c08800c3d5508440c0805e105810302c004038826020b003c003810441845e00128100464559805a1103980c20300d0780d004003030810001d0841950020b890007800f102056035408100d203810304180c04e415030060248005695100544010700100303a6000c42c013030b08180c0041c44a0340040c010f00703a07107180641e10100d80c0042c0d44003800e028881c460610030550804680c211200c00d0511048003d01d40010840c480552140d00010050180080445a61080222100603102d00c0e11201d403440350140c4452000c41d14000d0560908840c0d01c000c982040402c00000c1f8080c54000b617000d01711380c00380d600043d00001c05d0007850701d40303050b0340c00100500100b4002d600069900150b0f40805403826a2021a01d607010b1080d010401c040c040001c0d48141d46d00b041001448654450f00ea213100120204c0c2e02014226505a8545000303507810807445d0400303c01402a2840c1c07100078003119200786804104291100913 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 641163444 1250 641162194 641162213
    0x604090213111b1b01141b0d0305070e15090418050c0a0b030c1e040302030d0f0f030b0a051e12010e0c0604061d0f04020f1b0105010e071407 62
    0x30850002e011488580c40300070120728200d86859034000b011800110420f03a07150148520b811810000640807070003a50400c0025100300c03002041d0424228a200100140c43e410f03030700d202c0780019140c2070004008510403406a4030045001d4041d9444d41141c600e440900d51081034413075000380d01c4450b0954103203030f004030781e0082601a102401070403400108100712074070b5a0380008161402401031040040c0c010003107079014625150700d40e4140707080560420f0381b400f542d44080d5150184040500781c0f5504059070010248950342c80e8811000c4c00300050f8116004401ea603904141c10310000e104070305000800b2980000040680f00c2d13521a060001103038041c0d00d80e010b50859444448500c1061410850b0034400e00c0304030b80c070a01f42810200010b0942c41c040e00c1c541c0500d04080744218154499a0100c04d4040300a002903680f404283c940a200d64840121100e10140303c85202e401c2c001d06100360f506840030034040001c00d4840c1e001c219004c11160800030f150328020458000001c00700340 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 641164694 1250 641163444 641163461
    0x1032301080d03020403021e010314010b120601020303070e0409060603060213081002120621010203070509090a180b1b04090605010e040606090b0d0e010501060201091214030604090213 81
    0x140500940d604000440c2d003400380000b01c0c1400d1500501040c401030380d500303002c007548812110460203001c07090303001200540108a070070300c100d100c0c6800204c1c003908041d00800500000200c01680c6840b05001203a0703c0c801180d18400040d09060340324180d00d0301d0740080da0850b00030340c8045000d40c0ca0761161400c0764095060b00302c09000c1082c040000302400d0002d4440c40420200c218100000a035a01940000040c0345c10300c60403080140f41c000c4052000024580300c4d180000f151681360107071010704580d014100e6140304220240c00181d294800b80918032178070700626080c001c95005540d400809001c0984200072104051301101c4c120f02c440400703480148a034a901003070b039901c0c003000549035220301c60391580624141403090241d980c0018080c012107040300741c0c695451a000da11040107041944140040e942000300024149505400880d00c8601900040d4400350b0300307032019030300c0a80c003840701c042c098410f000291503454140e00100700d240c000780c48060350448040300c0b54115082c51 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 641165944 1250 641164694 641164751
    0xf093203060115090e041a0a021c02180303070c1509030f0804260a02090901240501180303020c06030a060315050f1014040b190608061801050108060d020103 69
    0xb10002000541c1c00071001c2c1c014000400717075001c1d034240307a124030070b0b03280e1503d960101c00c003034400c0032402c0b13800d1a5045500744040c012030188081a80180480698015254020740d49145400b1a070685804401c039412258408509130009107420009060380c2c103400801c40621038090350020102e0a80b0030248100b91181a0040d03445003021080d01480240c0c100d91301075180d09421540c0d0012000600c41100340d01103c15114699540c3c03005400341c08819000e44c2d0b038010b42d03004103449013001452581903c509032207a100c08404080c414400c00228030000c0c1c010f070702120458145040c450025908004461408641642c0b00d48500c011460b04090b107180d07481c0d0341d4040040a003d050151500401c0301e40c10743c2c280351700d00303022009884200300750f05101d650385002c0d401140e6100c0107560341a03020ba0400c05d85c01940e03142e0203800250102c4071180140207020504d6400440e500815041e07038070584a00d1010388924007408207018943c0400c80c14960780300c0200000300c0701100009049a0328 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 641167194 1250 641165944 641165969
    0x60807090906050a06080d0c0809041e0608150f090316080a12060506070303051806070f1b0c060f1701120c050a0302010507030c1707030f0f0932030601 67
    0x80c41e00c2c2c42201c00007480000711624112051120702d8012400001c0b10711540742c440d040c8200360402e01402d1040c00c904a030b02515105920000070a00d0620101c40000b410b01046013980d201c03900d1b9201c40f10a040d000d01031302c45a000950004011800c82d0b00000244102e034249010500450080580c03010191907004c40070400c0c4075019800f0745400e4211901d8101031101c3da151001094440c000c0850003030a25440703c1c0000c0500109140e580900040141112a00e081034a405040306107a00030403000214400103141c0900c003030901d40c6c201d0540c0003041d401c40a147c03901c21030300919003000110400c0704a00082d040300c070100780807501034426000d411035480c40745d103000e030502074050384001e0050030424001c001507a0044150342c0f4a94042c280310340e18040514200403502004015403580c9040800e24130f0505510440701c130f2010403d41c40e035000005071a042556423406520070781d041c8a07820040c40305564815550b10382e030340c801c104141f0a0b803840d8034002800e040c801d030041c4021021 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 641168444 1250 641167194 641167211
    0x50102220e130201090b09010516030f0f03090203070501052203140c0301090b16180e0106030b06030603100e0c090117010606111b0604030b130615080a0f030306080709 74
    0x800344415005006100c0c00301401905900190582c0c1462041200c00c542c01f00385401a45d008900701c0e003038008101c5107070056134110700e130141519180894900002d2859590182014080c1c421310a466400400400c4080d151000440340d56101c80f880310703403001c1c0d05421201c80c1c01c480b4820070091441046050134075010001124505010f18640da4402e030305000b8500045a440f20900b50010301c0e483c07a200e8042c0c04440d00351401000c050140d403007407006540c0081c84c8034106042905a501d95036050080301c44860401003c0e0105451156154004401000d800e2030f080c4d000713803440300310281a10b03000c01c608400100c1c2d03020264828599003540361150403201c50300380300d200003512003400d0200b10aa1a003281c1c507641c8803065a00406c19100100f124103984c0c44c0b03001c1c0d5004640c4401e0515052070107020440818405050445120307040c05080c0003144650141c400c15100203000405940305181c440e1240803941207016028140e50300d5002c10200018055080078200c86140440c2080 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 641169694 1250 641168444 641168459
    0x90c09061507050604061b20160f0801151404050a0b040614040507030501060c03141c020a020d08090307110f0406060c050f011406130e0d0201060305071202060708030405010222 78
    0x26070247c4200101d849041da82c02c60345801c1151007201c00200322440414900712075240d407408003002400b03140384015603400904880c58020950540d070ada58002c0c0044d401d0f40d05107401d030a030703036000c0d20791402a1103025090a003081c2c0e110643c0800b0074903011502c450b9100100302155507a4125030846001c0c1c4c0c00038502c1d400c1c1400340640280f4689004c10483d03141060080190200d481e000741040708003260143d222940d10143d0741c0321141c14000039940320161803140025800b0102100c094003c1e00442d025080c040d03042c40d803041c01810099440c02d41180e48916010701c44200f060391000a240c82507515840b80d1051030040c00240d00c0e580103241b0241806880d104000800007190f070b0404a141000c0c0d210b07805015000384040e12011186082116400c01608000c420542d80e80f291b0140343e046c86505400803030880340540d094480a03912444d00e61070342c2424210194210808004a1000600c40001941d11a015500050a02610012905aa0784e40c1c846030701c054103c0400a02284 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 641170944 1250 641169694 641169701
    0xd02120c18060d0f0302030903060a091101090305031803010e0a03092d06211109010311190f110a0c05120a1104053615090c0906150705060406 63
    0x40c0460350690070300c1d08030001038800811103c02000d2510000c03425041500800683d144850000c05480961829450200041c05492800d8441041005080040d54003441704082542d0b08040994032b81001000072079444100300300103580640d40c071307803203034a6900052200301041ca200395a048042458480c415401400400001005c1343c005140072606000c108440c070100c0d00300f81050241d41b035204a481c6205480c1d03100c9510181c0c2403800c0b586021264100904100d80d00340c1381000040f030910900f0704240105145d0905100080ea40f00d8512402514002e0b6204002c3c604650783d005071094503409c1400d02c090071208600b10070418040c520b8500401c42108203244020003100d40c540d15841d89050003295114021540c48000c03170411000d1307103005a5001a800851a10001c00c1130800380402a000325620650040d00940e0200c415030070300050049090a005094100700139040150140c0302903c02903011010303c0c6003180d40703600c03500075220b664001c4c0042c21291404c0d04004056 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 641172194 1250 641170944 641170969
    0x81501090b0f041401170a1a13061e0602060c0c030408030f0c070e06030604030e1306060e04060503010b130c03060512101a130908040509041b050607030f05090d02120c 74
    0x501c1b045203078403040c1c0000c0c40d0744554441150307070003c62805070070007601c01088100d012290700000d108018242c10f0340d054207c0c10845444841c500000003584420005a003041c0c00f403030005030007071008926110165800b41058041c40d03001e484c5404e40d41e10000b89544c0c001d10b0404d000341404298031410800a01101c4000c08034288040c14a180401c00251600380041004007032244502d000c8803c1c0c1c817042c160101c10074445104000c1aa00e8000151002c59510401e901c124205036003c01c8905041c0a800c110b0200030300800041000802a00044d105010420003015030b43d0348001500e903074a245441d8441c508801900403440360a8270042030310798030b0407a00a4004500e0151005840c1c04160503100049040b0010b1715030039078500368119102e594080d9078004503a900b4002070103001051480300d03040400d400a00d090303941e02402114040d045000c1c012a09020201030150300810080c001c1c0c000003000460807003100d60000e5420036510710001455800918103050b079007800390f01c0300314 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 641173444 1250 641172194 641172197
    0x30322050d0305041514030106024b030c0a0807060e06010e0a020d021909171c0507020102190302061609141203070605090c01030c0f081501090b0f041401 68
    0x22002801c1d100035207244130b20b11070b0580c04005600c1c0744101501c81c40c0301410240000703012594959444074000c0d03607815401044114003042040040782071048000c2c070802c504403800d030000401903950b081440100740810302049804104000286000300f800311641551003403c01a03200c070041d0600c0c80403240c0364900c200595112000600041c8221130b401a80600058030141e0340e40384025a580180c0180e103030085a10702401039150f44144c1040400007941c155484841c0847d0300181c1c2c003a070791480507091010140e280340070341009500c507a0003420001e006004403582058810b44040d01180e64403c1038005030810024003016101e02c043e44064103150b840c2c4503088034100b440c5140c022008a03c018880e068920300901128414070540301e500380c000307500300024030300110096181c20707002d00220300003490982c0c4d40b5415400307201c080b641c0d0320b40d5507079041c081e41d218000c59080e0940d40c4140d40c11b0002c402e00009612f1516030081056829038030740b1984440c5422f00d01c000d040c5403408541d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 641174694 1250 641173444 641173459
    0x4080304031217130b0615041811030c03010501122a1b020913030e0d1101080a0203010e1303030615020705040e2e060b1803061b04051e03032205 64
    0x711a070500d05100b02a5006217007081541c07204000940620302038109500c0556000c030780000e00070401158400520f040301d9050092022040700b2440c2803104460000100d4001d03c014003841d4821108207062461000d0000b58a03403c032071101d4024a5216501200189142c2075000c03180d40c030180c894840d0b07003441d44052a054203680000d03070b0700000400046c14002d07071008940070306208500340c0e2602039014040000089850821180002007060b44070701240e40c900100f500d51455100f100d04071488040140e00d9615070100c0c0c11a445038420041d81003644403040410030340c0c4201d440402c1a042500100703811032612003804203070b40c0c3c0c1032148482e40e0066004c12810032030180c2400103402c0c80103400207845074041c5d40d440c000e141e00d8200e03000592001c0b0304555aa0a00d4100700b001030000c401303d0f025541c821408016103403800512003c864814041000f043c2810f100001060451603141103480800401080c03558105607014103000c2029900b070b1050a58490164001d0302090352842c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 641175944 1250 641174694 641174701
    0x90204090f202403190617060f010f060c110402030a1a150f07030c0804060801081c0905010e04110f0a141312020d0203011103060a050103140c0a0504080304031217 72
    0xf03005a603104640641d01e0940000051208126403105031104200e003001000300341e4690001e00285024000050014840c00020451503641d58034043d04039200046008500e41c100350040b10796500035031040383d502824000700e200e00e03559400a0342c03054141c010006800d40840100740401510a034809000d170000034440038400c0113032400c507a000500c010340c02d603840c50b55140c00ca82c88103000401500c5a5808200468510b500c405150704a4074094212480e505660b120880700c4800d40103402c0100320072800401581d4042c2c5c0f25030221030001440080d90102e405088440c0303a00210b15031a0310076000800c001b0080d000100303801d0700000b4010072400d0410400001d003043c42c2ca030080c03110340b48030003001c4011581c51280f0308155a5000d002030100d0a01c01c0b0140c00c0a0b0000e45240344528030b00c100c0803038a03522a114180418032803151b0405651504200c448942d071001d990041000803c001c04221180100018001144502d1808c0340c1c0301d260040c024848142c0c020225003880c501c0060 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 641177194 1250 641175944 641175979
    0x140d020c01050711120f01050c19020d020a0308180303010f060201060609060819090204180c210b0606160f0314070f0b060f0d0302012003090d03090204090f20 70
    0x20381d044c1100698140701c0e843c0034410b0151400c2420303004000e0540c00d18040200c0c86a410010b44020901e0210084040342051016a02d070740003004940010303445049040f0200e03200324aa0380d048801420101c0d00034002d020b00d00d0940e442600403810044902108001750740d824403c1400408036031902c0da5001c3d0070030030000c02c14000a8020380c1d1401107140d9840c2011040d030f01c641308c256401007042045401d855149900512042c1065400c0c80c2c44241c0060280182c2c1d441d61701107600000450402360803030b41c2d00c0080c80005014190055000d01c09101c0c1d0395401c16001480794000d40c030005581800d0314004140e51a50325180d032074040103000c10380c0000e040b1204041d00b01e41c0040760101d140c0c0c0c0c40012070a40d1041d480a558042d5042e0206000c0c590198000c01e50280e51920300041d44c1001041d81c60184029101030413140d100c1201d042c1c040e0320a074890b00740644020300c013042c400496102d508180318030304400d071250b00d040500d10504240d503034841e00000e04140d50500801150780803 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 641178444 1250 641177194 641177213
    0x105030601151701030f0210110a1524171b010e040b04240819021009030602030a1a030a0b0c0d090203060103050307020310020c1b030a140d020c010507 67
    0x2c80d000112442032015401e8040e1203002e44980c50041d0074012076039a4200f040f2030310034901e41603004407078080c81002858400c0c01d0000c8084102c6006190f004442d998140600b00100000420550340d04200c0d0f2840c003510440c2007114401e5485042d04508190b413011103000c801c00d019031182c1c4814000f0b00010954060030303607626424200364800c1c1e000030f00441e01500401c038659138054a028211003c0c04510b400614084891500c4003180c5510340890940d00c0881440c42401105000604401441c06000100f101c50300c0740740072401030fa50ad40d1405d06a800aa807040d5000d51500c2c074041032400458000d0650440803002003504050b5034072251010b46000d010f038491a070000421b400540c203140c021864056001e0b0460344c04e5030b03603800d140d40c50b5040340c0300480c80b902403004220400503060007070f500303040f2800018102c291601d107880000e440020400d10307010b01482c01741e00d0200700208502c0c005901c400d001341051002c172000081c1001020340e45681441003d0242101250742e00c0f9 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 641179694 1250 641178444 641178449
    0x180f05040f0209150c1b09061011010903050325080a020309030913020903061308030c0a0c140c1f080c090d0209010b180603012904090c020c0a06080105030601 70
    0x32400550054980c0a920191040602c4107400000025542401031140001003900b01c2058040c0d442260500100034005c219400210382d01000d45c0000c11400e15028a00c0c0d0030714204c3d4101418925542410749094543c06a010380104801004001e060000301031a00340483d018048410a86100040500405c10140109150680c04800501c010008104036180d00e8001844c0c003a45c4003580d034514000c2d5200300751150090095201040e0500103000c05840c10644c002d10050559803405d06601d03545c6c12892400c020000c01c21029400300b450100328000d03034030119002e0320f105640c0d08180320750200000720800c04980d0b03003040200c1c150b6000902580000818503143c2c2e5a408090004501c3d982240019505c0140f0303500001d44840300000030003201090010080090991a0802080d0301003440fa56040d1106801002056007400445044171501241c2940c01c01b52101020002c42300d00b0500800560311000d8400818609895140010940f41c41c0080003503041101082d207410061 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 641180944 1250 641179694 641179699
    0xb1c1b050603240604270209031c020a02060f091f02030a11030415021c0914042a020c01020c040606090303050c100c0309150908031807080a0b07180f05 67
    0x2c106500091003e0302e07005142000c018821900c07070b51262008160410b001d500c5240c0c5400d2407895203140c255038025103026500c001e003c0c20041c03004500000045102c40e100f20114020250001d00695450001c0d00005281c11507042c3c5400702001440380c92417088072525101e02005440001e0700394004100c50441000c0c1c5083c0c0c8400010700c130b86c20300e940101d400c005240f802e080480102542d00003121082514855644226865444402e64644005004060300c80340040d003119803d00300340c0c1000c074080b011044001c102c400e040c01d43d600c0491060100c8401a044400700c0d051a40c4e04008200e45e41c28119410400d1038602200034000d482035100c01014001c02088400c0351110600101188080c0031001303225143c0400340080c010807000303070101e84411042d603505041c41014070800b1140d9900c07481051031030b01d0340c421b91f01b039104548084200c148543c04010541d883c09001441c00e035881039100d0405400c11207c082c140100a906008c1045004c910800c08030301141c5444003110f50a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 641182194 1250 641180944 641180971
    0x3030f030513080d110c0a0b040c0f050307150c0221010614030606100210060e01030c09140606090d0611031e0403050d11301e0105040b03010b1c1b050603 68
    0x7014212400c50161901d030a01c6ea004124075082401024132603d44128880d10075103448039100c003d0622002001d008007601a40414401d00585000120042c102019818aa082c0c0c062a900040045481c2825000680f04039010000208802d004041c00b400c0001a240745402c504008642c0da018000d044601c50050311002d59031071802400464103c01c4812400d01c02c140c0c84d0301c46828444c10a100454005550590003e404091403040c450005401d048901040e2111010407500784c1203603000c0c65000000c1e03c0104000780c400e10500201580c81000b9036240d240c0211600b40c0e00009005500364200700d0b03403c0100180d4080704513480d42600ca20005006161000d040085000f00c0d8040001112001201c400100c184000314001e083c0e0540f0701c900c0e07aa03440f581005560003a080220b00d85580b84018031451500c4e030050300c82d01401400000d14500749600003000640c000c4d81000380140000b0050040c004c091450000013551015114038051406000c103d49100040541486906 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 641183444 1250 641182194 641182211
    0x170a0c05091504030209011d13051510050d0b09010b03010b0102030a1206090609022809210c2306070c090902130221160f0c170403030f030513080d 65
    0x84000030398011350740107000d1100c42d684410ba4000c20050a1009000809045000031001d03c4100c01d60045560301c040988071042216180c140d90031000341c10512200c00040001c0b41903101c090811403514000c110307101d0b49050800345242114405071000d4000d034100904d00c04282d80000c1102d900d69050f1410703c41c1141019242c0f00245081c2c1c118109450808400140c5e13010a50040e000103504000ca0074009021026821581c03c004802c1c080481c0b4080c4042007151041540e612001c22151000c40e0f4180850f07403520504c404540001030840d0511065a04e1404144000700c609442580d400e480c00031140c42e02401044c0c1c034421b00344e10301e4803a04c0445c00c5480701c4654601300c841004d001d42d21003089826400c0d43c407001000a00d940301d0000005000141503240d44c01c03400106880f40d40951001000846850f030716880b040d00d084075581c801ea0449015103005200440c00f0740c0d502c10721081036613002001da0303402a0140d412038882c40040e0000c540308104450400c041d0620000302c2c80c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 641184694 1250 641183444 641183479
    0xf030a060503030d0204080606010822030c050639181306030303020a1403040c0b0703020f0a030503011a0c0d0509010c06050a020702032e200703170a0c0509 69
    0x1107070300400d4160001007501c940a4120741c001d40180d65601095a80d1942c0f54401111040401c43d120302603c103038021000a04001c0040140d5120301900d8103004440300c50704c03003d241006c140d406000404101801c04114503503203801215032501c4001c0b8100b00b00c50750303291310141c2c05600d0703402482d620700180e403c1280c3e80303485200720f484010311420300000341d0b0781c01e01400075004a0305030808075207800c3c00c0230280c1006000303c2c0e1040b50310070030000b034483c1856011704954003ca0001c6041d407017070304a0b08500250130000c2c04c0d5868426502c4954a43c1010071204074406d40b800750311700d02c0c1c00138013026802900100b10fa058040241c5081a00c440d16600100d88554140c01c02824151401092182e101002d030001c0100b54000e0b81152050301d174403103259031f644034031504201102c007500c10031003603000450700300c4040b48201368440b81c04070210741841b00460784041000c4010480804201408003804070100e0303441091120300300000650075001030003510400315071074030582c410748a80a502 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 641185944 1250 641184694 641184701
    0x40308121b0423040c170105180406020706020f03010e150409050d0f090b1605120906070305130e010e0a0b010305060d06020c03120c04090b0a0b0403020409051f0903170c0f030a 78
    0x1c50f00100203101328104020080e01d40102c09060040c0f04080000120701414441651160048035640303c43c460303a55a2910402508160003c41e08142c0070419040e2038030301140614007034103020700c200304941881c1020028560080c145079018034201441040800c102040c2403003c1000c0b41480c82182e41e9040c000c80b042e109680250510410102d401c0c802000c01c240402c02062142084519103801d00740b4102c664010340d0b00c00f96111400304031020000340318001501c481c454a080c10011542c03511034545515200360080400c61440b0010060210114061a600c44000707007410422400c2600105084401480018045540024140305051410030460b00707040142c00b03085006050002c0b01c1040340e40a03200311101030b410a001010a454120340300c0040300d00c0030503124540791070740c0d0910003d0105505c00361070500620f105e01c00c20080840c0342a401448819000401d03400c20300d0302510032480b4007640285055104200141c500488085030140c81c00844c001c0e44076581c10351328501a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 641187050 1106 641185944 641186009
    0x200d0e1606020f074e0201120606090b360306072f0a061505031005271207060f050604180308070c08040308121b04 51
    0x41c1c420042e5001c1d00d50010a0710405e8403040441c03503103800800c00f40322840d01e5003102c04501150b9201104207081c500c0c40004024031800c0c000014132246141c01703040d0080d00300044503250746d44201d40c0c048031a42c08503070607580704022000f400a102d41d1500f4060191003190302041c5c903035008088100002c204030441c43c0441c00044030103407610700761b4420310704030b1701031058048003084440c003070649521913008200240e545098281480c0083e6080e0942500e85400180300e080c0078120b0520342604658a241048070fa00844824100010343c2c200480b84500040c030181002200d411040810b4520401007109603a02000c3c081070ba0420503035414506854002c3c04000f900400c0855001941441d00c0d0880d100e2543e42c05800c1c1d80641c0007543c86a030041880201c2d00c5111031003d80c020100c102302551848506401060760265005142040980400f40c0c4414102c20306110385 = true := by decide +kernel

theorem cover : BRFrame.Cov 641007194 641187050 := by
  have h0 := BRFrame.cov_init 641007194
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641007194 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 641007194 ≤ n) (h2 : n < 641187050) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
