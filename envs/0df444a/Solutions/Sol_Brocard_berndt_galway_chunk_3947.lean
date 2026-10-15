-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3947
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:08:10.656868+00:00
-- url     : https://prove2.me/submissions/5431d385-0f0c-4140-9e5b-d4f63267ea55

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 709712230 ≤ n < 709892086 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 709713480 1250 709712230 709712249
    0xe16062a051e210a20030408060906100e07180e0901140c0406031a130b090106111506030109050601030308180a02091f12032d02060402120708030f0301 67
    0x400102100e41d02c0c0c03094101d1000b4880341c82c40f04414022040042c00c0c1d41241400c12004540c0ea282e0b181094284151400709141c0c804030b010001036034100103542d0440001d0340078180d035080400003031007110380500841c4a80c2e90408045008240720389004940c40080e04400c2803802c4d190030626800610031340e0300181642c02d10051451a96004461a0050490491081c605441e00b06d007640034121a511012100203146480111500e40f250342064807010910002100140070302040f80031a41070700075008000c000d444419040340006051000303140022095152669030000181c054440c606d00105240247c000001c1010382010010b800380c41402101061b599500b00101c0e910340919030080d5200402c0004200900544401030413019000c49404cc02c070303900c4800e0b243c1195007000c01280040e150102600044d007035451140c03030620741c1800b01200d03010610750007540c071000600080c0c82044e107950b0310070042504001c0303070006050403000e5a4485807070744010b5010f90400d100b0880d60 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 709714730 1250 709713480 709713523
    0x703020a0e010f210b060f090109061704201f020106061115060607023109030215090123010302120601031707050114040809040e16062a05 61
    0x40b0340c02800c9058020720309030b03134006070800288040c1c4c00e0203c420186190441d994180132071541c4403030000b0003090200d0041c2c1c9550302220000141900742a9006404104480f40040c1c40c801d2100d40da80d410981280c003030011800c207800755231200e40407060400d91002c182c00000124132194140d680da0100b940d0000c0011a0740d900060303410000c5070340f05c0f5003250842e11241c3e105803540d008540d000f100203040241000596404035403001441c01c10103160500a0f240c039240785030304103901c8840b10401038081c8184880703a640030759142d0204c0740c8052078100000018951100c00d5100f6400f0214801c604007004012a00701071612000b0300069002d001c044440c20321000780025075604a9034091034000010a41100c00350840c2c101407000c4440395244d480c0c52003028115481680500c1c000c07450b285c1d94503004000c01040303039501c0d1b140d1085a00448200068540c0c414040000c40740710741804501d00c500c10400b81000b4a980a6180c0c10701c141e0034401050080c00220500c41c3c0c00d40b00040b490303 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 709715980 1250 709714730 709714757
    0x907180f0501050409020c100207150c030b06070308041a01060c0203102a11101a0301060f150302090904121d090604111611150304020303220803030703020a 69
    0x100c6880c502505011075010041042402c282c1e41c020000c44008201356017003410072034001b2060346d01c054002d64060001e814166a080d005110306021880c40e070400700f120400311030100e04540980400901407011110010701400002d035036074030f5030701c0f880719810900e982c6078075025041c2080341c0003c1e8060301c14242000707c501c40d14031440440500015282e04008003400e210304044207071201120400a019582020340700d8104060355003041d00300780104200700b8468414119144103c41588240e0405004108912284a01c0c801703441c10081444800d20274640b040c1e0180c45080041c036000010441000300f801031314046c15403082015038441c080041080c0a94408018031041c180d48151603030042a5146016401101d030441031500585c01c0800c1c01c031034405464000c0c0000e5030010f20b00000310340075143c0000404000559200c426055092035004a0303074a0045440145400c140000c02030b494410700f0001000800c0d11801302d9035240740c403680003400707034000c070700990301040441c01442d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 709717230 1250 709715980 709715999
    0x9070801140f06100c0605070818010b0a15140d050603010c0503310501050f04060f090c05060706060f0b180a0501022509290a050d1709090718 63
    0x900a075140003682e010341d10742c6410080807103800312a5000b0302644c0c00e81d41d130000c1c8003030203107a00c100d07050303142c60340d07186814169104007035580360385550980d140201030180c956401000d030040d25402c1c20322207900b504075502030350021001030285030701442c00700b1810451401500718521440c000e800920405102a0303050b41c07c2d0109035a0b11074a090070503e0040c0703002c0703005120705a60000c003585842c00045a02c0380d030308440d4107a40860703004140404110070701c5058000c040740c850b1040003c0201c40e03055224102030702c005008040c841c00000403401d09010300c0e508000d0140019501e4042079035552082c811442d800320780103420102000ac1b0518052078100c0c00c0d03804940c41030f009405076691200e40c4102c01d038042c00c080312604585844c0816502c038548640801108900c401c440042c4072200981601480d0640040c401d0210702c00c00c0c130a0340c0714041c841041d954131a009440200c42b4504218030340c090f030892250080c40d03120400010950001d485450400f48544050601d61910b000c003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 709718480 1250 709717230 709717271
    0xe03040f09060f08030301062d08070e011110051905070f030b0427050a1403040906080d0504061b0206030403080f0a200c0106033e10030b01031409070801 68
    0x281309542050004004540c041c488598400c0e18201e101c1041d0440501030388035102c50080d1900000e00b003041040350141d04044c07000520a024200710701580640c801050392014012410440b5030344031004200301600090880c50a0409805d0601441c070b032651009020b940560748a20010b401c00c0b11618690900740300703800070aa00040140341181c1d085c00da0032044c1105280072070300c510511441c00c010890a071034040000b0510405950394a1030840c004ac107603581034000d0744468000f0480c01da01e50350400c046034100c07551410641950020b604100c02200903100019400900000c1080100b560040109100b103004c001000b409071100c1003e00e0072180400b0700300385000340e42d07600e4000040e03e40e40a8041d04d51480700200350161aa0340300c0c82d0451107a2011088c05620b01e40c4110907074102c80451442c1d005110700720050040b000002001a40c03440940700c281952030304c2c0044a0b900c203030460301d1121003031040001c1c141000c40f4002d41d50319540c85850140c0d40b81180000c2440c0010012 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 709719730 1250 709718480 709718489
    0xe1201021b07090c090603180f050c031203011d0402010203070501050a0219031a0f03011503050115081519020d09050c0a0803070b0123090705190c020108190e03040f09060f 76
    0x9024409050010039002014605107500b40c030065900302c03c00198403400312002c900cac400c80240004400c0581403501d441c0705410900b80070681400140210a03001980780400041104611340c1c0743c640f40010703415803081c250302a020307500300340800c030340191640c00070440c0a0031464010b140d451880c0e411000c4544c1034840f154118613001e9007075107900d0408102c0c0b00c070301001000014010340302131131a4043c0a103584212516515800d51b80318800c02d0b440e0307000003800c1c2070000d07080550100510031241800204440200020080b084040c160b4a80c1a44c400d90a0381c041003050403218107001d560340460720213084c460b00041304040786481020054881145e03010014400c07503400c014482c02884440d0001c4107581c0940700341c65101c0e5442d26041401042d0b6600c038181d270b529110011991310300c90103800c1400d0240f030701264001030340e00050a90340600303550130b03144080d504c858200c0c01034084441f00d80030612010070f010680c1601d0220150499400c048204602c503500d100d5801c06056511a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 709720980 1250 709719730 709719737
    0xd0b010f210510080d030b04060b03130f1a01140411040f050d05010207050a03050c060c0421021f0504090e0606010207210602070c0302010815100e1201021b07090c 72
    0x8001d034140e08038503041000407a41c110000c0e201e615291501d1208512440082c2d15030b03c1c81001c030300f803078810003003d400140c1184e4030b1490600181000b03811854402401480b140d00a8001c0c084101540022001c6401341103155503514824600e402900b182d6a038841d03403810b510507600329950812035049484940c411803050b46071a0802540000b5118140c401d55020400070001600501581c40010701c0303502c55035107a0703040001c02840c00000900b1007040b01d60403c4240280507520240c03115401c51011401900401e61010a130720f500004081448070710904400c045542c0c000014000b0359041290401c569080f02007019038940c1c09503034031400758100c0a070034800b0509060764541950b9000c24007000d030710b040d5900c6104980c810f440503150110710701c1d01442190b03403124a00c2d03000408080340212400342c035000218480300a5001c8814010240b5440d96213484890b03600b0a4142c9400007103444003002380117000001e0820503040050b0241100c042130724a114454104044d24655 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 709722230 1250 709720980 709721027
    0x120b06011d0d020607050106240903030507060b0d060606120b0405130b1b0d0f0b030a1104020a140c150610020706030209150c0a0c060e0f1509060d0b010f 68
    0x180854458103200c144d801110411031107000c01c400340900e80050400d10300b140b40705501e4444d280b8150f0341020110042203444101000802ea01400f92805103401101c005a030f00d428000007002a000103200400d001c0c108200002c2440c0c201c1c03021080480c54400a01901c00078070200012140111030791004402c90b015a42e0215000070f20080d8014107044120a19078aa4055800140c01450152100702e4850b440c0c015a10414000d045c0c140e50f09800400310425503a980007410400c20722110b000305c0e404113507481114801c058011603051400d48613a0b9901240e08255120841141c0820031070740b41e240442c0d0700f070528042050401c400359001d082250f0512804801941c010502142e00a01035a141e62214155400800d041007580c0b0060400b88101c1c6070030045502d150b40202c0c18060b04044000140d105d0688540c2186400c90309090b07105000c40585640b03000d045245a0409804a55000703010800c1c1e00a0201800c243c80c1c0b040c2d0300001c0042281c65140c0c10101c06044900c03030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 709723480 1250 709722230 709722287
    0x903030c08090a0b0a0f140c04080d0e030c0d06151805160f0509030115081f060b0f0c070e090f060609040c0e13080a030b01090b04061e050403020a120b0601 69
    0x6e5020300d00a200c0c1d00030100711349181d0403036034034164800e80b8041c5d4204e90006003040165000c2010001c211010f05141413480c2d401c500103034543d54030300a02400307a09203410f08001c1210540c03100303503121003004485488a40754071521154010403002e2042c0c5d82d1a01003c200d4041380030a100c40b21442d01d644107007541800324422900303a04804a140c1e01503403141c2082c001c80c8644c0c1c14840280102e1401811100e005180111028a07000ca100450303070318184040c00081d12110498034034805c10a070b0141c3e2b440c9640c81540c40e0020355404446051802414040b1413070022400c01e20040203e001c607a0240c503a58200308041106231313002098485202010403c1203500e02c24103503c0501140070418211303241c1c5036180e590f8413a5004400203a03603150904810368000c0c0042001d041e03480c00c801e04050428401a102080b100c00c8001002003241448114920030310403140511f0380075040304111030340d901035825081c1c100b4100321860380d0b1640010310b0035440b940c401c0c122000202d90201c490301c1038 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 709724730 1250 709723480 709723501
    0x2070b2715161506180b10020304090c0e04020d0209120619091a0403180e2403030c100b010e120d050f0d0e060105090921090609040903030c08090a0b 66
    0x240044444106291452070b00716001c0c4982002440c02c0c5c00c01804860315620300b00308031415210f4181c801d1042003d0014400d500100341d60503241140b400066040c01d00780203643c0301100c0900c0c541c1c014000221200304404680107069150000e82d000b01542d82c00401c0c00b522402c0840d00709007411454001c00c004008650401c25455000d807060320f21000c03541b0464540740004440c01d80c0801c4503148515114683c25240c0d40c018502e201034107406080007100703071641492030005023035941981c48094070b03580c2d800c0c0215603581c11000304503800086c1d0400a0b0003c0c020304500c0300c4c08150300b040c1c41d907040d0a0030403001c0384080d102005486d03503903070003101074440e03400009540d640c03e0030601c41b482c00321841d840784500c8840305800415441d89411b04004040000070030140c0e141e0414002004841a03400c4001e0300640f8122000b030325500340e80041402c030b00074910225409400c0a0701c0c0424150540d00801d1105000e070781c0c1074120f41d00c1d00c0001d82c0d60041110f00601106041d00054501c540303 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 709725980 1250 709724730 709724767
    0x70612090f08030f0114012604061806141b0d1109311103040b1510080f18030a030504063b0607080408030702070b2715 53
    0x3103000085003507a01c9449420454204490f280e0300c008400005000c0020600f0201c18049001d1074210b10b03144002c001302141000d038100581e043d041d80c5c004901040a00d400001c980880202d007841c00403007605200c0040c1514003410700b003802100000c50ba000c030b03a41050340e4070514201321851030400a1014007009140c2c44400c0c594082e0240011007640d0380380d201c84c2c0804140c83d500c1d40d03010400741500d41c5125841c0d24050500341d2401c40545176070800201640d9006401242e500090b544d80c40b40c00500020300e0b03112551050b850040c4484958000000c240668071003138012099a44100720f0840d0042c0482d0305180300d0b030040c05050042c1d8400e0704150791040c0719410100d50407402e50400110701d0945800c054070044486030004e140100b00c000d2060606980e4020450760810702e04c043d120341c0d00a840a0308d604400000100100e00802002c4014060609150360700c841e2802070f0328241c1c0003424400c40d010010703800c1c00e40a1170400c0c404011241d92a00d4640703440490800c10300c9694 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 709727230 1250 709725980 709725983
    0x8252114071d090c1003020715060509010515071203021b0c010203031506040302040f0e1b0906040e0a050a0506010f060c1a100806040302010203100920390d0207061209 74
    0x8510351089519481705c81203440d010186440141c0c40f1900d81c41c00c00f0b84409074195110701203280100802141c0c2d41c84202c00d0466606446104c640032048007070066621a9041c00380559649980c80648994180e005000c80004400000e40c100034a4441e113884d203050b00700090060740244041140b540320a0003442c00d0300002090a441c00d5038076800b1800f594140c00c1603901c49941c503041031041540a002130242c1c485600305103941d50490b280003036000706010703000c030340566030b2110310300304810040000c116500d411408640742c2000a190003551140f0034080c54061001103100059114060000c505d0000e9100c10000302440c14000e8009040c100149040407140e10b080c5d0005c0c400400b40b06040c02140650b00260380da2918031200041100b056000c0030050703107002009401c0b035056000010b2400c1d42150404c4e584c018030500400c0c0754a2000d00c1c05903079680f46503501e112050007850788104840080659096120801044c2e8540c2e2191003514041080c810340c5c0e001c402401e42c070042415 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 709728480 1250 709727230 709727233
    0x2010209152203061a1012020918040606180c0c060b060f030c0a18060804060902040e0d020309030f03070f030f031118011808252114071d09 62
    0x140491010075225000340d01c00d0b2030040d41d0700780515044110301c1781c4103800801a03403141031a00e02e100c40204020484181122005e0380882c0300506907440300d0000400f07000d190210f00040c1400d00b00b850082a06100d20580000301a4109506e84624011480d40500c00c0c1c40b0900044556145d40c0b0251010419980d4402c1040244414220f11a0b01442c0910340f0350420913114889804064005450180c0c6502d000000c010100050381d442020f1660107603000d48085101303a003603c04500504280000705405000e01c009910700c01e5400030103005955012000c66180c420030f041c0041d00d030b110f80c01016101204052050000c44c1c080c0c40c4450b0400701610b0006a84d031240e4003100d42035000f040074042c118541d504203401e25a0f0251200c0c80809a45402458803860304400c5562404400302580051030580080c0320fa115914400a00900d8981044552402c045110a0404404c40d10803100041c08240c0c0415110b00001c000007070361440029107840180302d680904d0721641c001d10b201d034203 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 709729730 1250 709728480 709728517
    0x326011a130503061f0b032e09020c0d0e04060302100f11060109050103030e0a0e1b07080a081b03060d033b040c082e0b180f010201020915 61
    0x2500c0c00c001d414880d14441c60082c0644904900c0c481170014181e104101101d024824010740004042c5544550904041124542c01d04006c1840300740b1695441048420b2011a4501e11403a010038105400086951400c1584011030100011103e05001c040e402084030b402480c0118020b842c980664060313030610b0101640a041540d00e0000241c1204013800c0d10b80004004040d0041c4448a00e01000c8841800450500301e6020704020300401002c15200004070000c402103001c000c0b00c44d40d41d00150259a940490b1b400600087c00c1503030f02d0107071070020248022400b07030b403001564000c1c50010183c054140640e02c1c11501d060071200462000a42c0f6020708502c0450312080b4070107c0d28001000384010701e0041003100f1509403050680600010302c08005c5070841800a04052a00e6000200d0000010803e4200c01c5509500607a00c2e0600009141c220307034a80000c030243c580c0c42100d2000b900649a00124241d0240142d01500180c0046101d0b40c00b42251000d45010400110032008 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 709730980 1250 709729730 709729739
    0x207030c0320091905060f0910080601080a0c18020c030a020c100e0f09040302011524091401080405010b03150901060906050d0f0c090204030326011a13 67
    0xc410085610440d0320103004461400d4030080d00e00b0040d400e520071a02e110440c0f806054804d461100740003682c0300300399510300154141d03840b00c651140119019084480388e1415250041c3c0318000d0380251211842200000a065240040e8a1610030b03401620810064a8080201c40010703240d18200c0c001c0781c003400501140074041024050b40b4415038010203080040343c0074030003107003402c151403030421150348081c03e210340702c1d807111045110302034880032100c0e5983d041c202c0c01850340e01c0e00710740740e201016000140b01104189401d201b1216040f040f40242c032564042d9400181c610607210b030043c0710881090207602411000d40e100740035000101c0d03903980d030030000390625608120141c01c000882043c4141e440d42480b0720342c0a003260407420046c039801c2c00e0010382040e045480c001c0c00d0344410a10641000b80c0000104001d0041e00001d40d201d03510792030b014058608ac41240c8510001c000e440060310b110407441e160484549140c28140c0346510f68015181c0d030b204040c0e0507082c1103030440004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 709732230 1250 709730980 709730993
    0x22101091b1418060616111813110613150207081f0c0908060c120901090f02091e0412080717070e01020c151b1b040b0409021f02100204031101030507020703 69
    0x6003418800c0f150107c0207041c1c002009101074440740041c0000200c0c004000355800b0b000410709001d504140024141d07580c80000407030341d105031110311000b62401040016400342c1c3c04080e200100e856000d035400d55072200c6c8003603a16024805140d0300a201c0c031b810000200d4403680098003112141c6044642645c48503201c904d03004c016070703851100050000d514120345c1c00c59914540c205800d60300901151000351608400721141490283c0b142c03000801248100829051110486103030500c24001450582041400070350507643e903001007240400010030103131283d040f15080901c9031081001c50b0300c4000c401c9441c003044000785e5040d8428600036407410f0342c490520650f500102107411f5601c80e00550304c43d000e85040005544a540303e14242848807501c0c04d680c03003403010141c1d070014242c0342010025000d00340300d01003c0d4000c410000144545a4081c0c2203d4070340b40b241d0202c032251625190540101d100e04d11010b020f018041803041015032003504850b801001620480b6581ca4503502e881 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 709733480 1250 709732230 709732267
    0xb06131104141804050c0f060f040902030c0415020d0f020319050309030403140715020f0c0d060908030901091e0b01050d0317070507120507020904022101091b14180606 74
    0x50310b550f808091b14844519080c0c01a08007003200381c4006042103000754001d0a14040e43c0500a011034020000039109840b82e42903030003d044010005440b040d150f040039458441494045000400010301c4441081c000000c65070401c0000019540240016600720b8140e0406410804540030030880000071661940089442e25024000380041c58a4107554008075900c0302c0d074100c150341080c0700c1486031402c0030600c0c015600b13064404035070303030182d0b46018001040d81850003800701d5004030511240b00300551058090521644045a1074202640c4400c03038064004401031908003c00c006111030304102c1d88800c041c51182c140140c005645c030f100c0040888044074507800044005c04e5400900c0071380034010495400d45e007400c42ca0130a1640108048a4000304003a014006c04c20704c07465414188014813003219200402005042c0300ca00c0c0080441b10180238002e00465090404143d2011140342001ca40070b0080101d07030b90f42d200b084404202e640042c851035001c1002d1040925005d41c00030030703 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 709734730 1250 709733480 709733483
    0x6010e060d14120d0b0f0d0b0a240801050714130504091a041b0f0e01030221060a090b010905250e06040f03051006060e0d0512070b06131104141804 65
    0x104a2030005420700003444007440c071181c07081d03034942c80000200306400d801c8c580010742043c01090030468540494100c992221640011010000001035417941c1035200e540640010340e00c6030594a80c80103000258000c03c1881c074100344e13102401700320525199001e51081803099055102d04140c000102280c1d0a08480c1034500f00342c072129180701d407400c07501d03c0704c0034204280f81c18401174184036142c0e00100701404005c1c094000707100c1c100c01d140e066a060300c482444000072200740340380514540010381880d032402c81d400c05001001081050fa203000711803156803038108072400b8249103001021681c09040d00d110a1003251280d00c2e01540303541004001801144501e105c00c03510314a40645055941c100e0040301a02d460b40500c0455844499002800400c5441006035000c90400504100014840d079086010000741c01c41048158910103101c1e900c21601058100076041e000410303605600c52032040100108014808840ca0594000032148050b10482e10745442c02290080507506650 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 709735980 1250 709734730 709734757
    0x703410c07031823040f1a0f0f060f03060604120f0317040f02122814121204060b090708090127120c080f030103030206010e060d1412 59
    0x500390203050300003c2d0105407040301050300111a10300b050304001c890004440e508a420714001c9459a651680c20610854007113a2040040b194074500d070680d0042504042c0f0f004081381d5403003484500d05411521800300740504040d2500500e8402e40000f9880202003682c044800d000101b001101c4007903401010303100e242040306550881c20041c0c6000503009480c6560202281040300150207410200b002c640e05540700205d1410518100d0301f030050b01c64030310f0001d508540750007451524140fa0950407134054400341c540c10740c0b824551501c944c00c0400c0e401c006481008a003a9102400e10042e42c41405884001040100540000d08804055503003800094004003032014000b0284503841c8101140100340b82c0b044400b0501d8040038810700c001415014600140d00300c1c09001b84030610b000ca80c0140c0342070359041252801d0480fa0070070f00040e4018403c1400104a024070303440500d006502c0140101449200340da00d21b035682c10004000c0550780202c50160f8010807420002c0e085450300c110 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 709737230 1250 709735980 709735987
    0x3060415090606180303021507020c12030304140c01050315180403080610030203072a1e062706020a0c150f0b0603150d0c080601060906080703410c 65
    0xc0002c0c101601414103184c032208a4004000094001900034000743d18200c91041c43c0e610b101069042a0000140315008485003c60743c81c0c806c80400110320640c818003485205d850803005481c0d032904199082404034000f007008c1903000c0020540d00c0c180040040c0820300c0f46c500640340c800d8404041e1022000308141c0c0701401103515011200c02a455804d14003141985007401c00185212440308280c421504201e890f83d646400341103000c86e1a03604503d160b5800fa074a090f078150324124820303080c0c94491802041110f800c00c0518060743c0003c064210901000b55916440300075804221401d017444030031000c0100081c8010303043c0708081101e880009071034034190500400da804800e00c03240315150030403c021900307001c26002e40f10b001050795503100007080d902d000c82000f0031a4000c1c440d00d1051500001c0c05552015207031041d5865641c1e60300f0561241c010517004e0b201444892014080c07400c40c2d00c801111002555804800b8555501c11000140c1080410810080e01c10300c01d400c1001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 709738480 1250 709737230 709737239
    0x3020a022413061d060301090f11040b0a09090509030306150903011506030c08040b04140307061407110a0c1e092406080c040308030a0e03030a05061005070b0c030604150906 76
    0x1101e808001d6010b00c0340c0d425134040300f10005d041c522050241101441e510904001d070700c0c1e240d90011700894a81c1c01141d6840e915014071420580001900c2d0300002c120940110300640c0c039008042c000c141c400015421600c90324200103860f1143c551104001d00140300c10703071081c0d4003406004d1a40c0386816400d02610309150000b42512030310040c0106024044050200183d18901000d9000d50005462408001c0040806045101d070388000703860603040c08da0b005045030050342a6801120180c461000a198100301552591301c04003020f040c0488900e001c101080601e503c6046c508a1070141100d000c2d224100f032400c6400660403039060f00c0080300d01c900c020450141d00760161407039080c0203c1c0c5240040100b10310340709a00000f0001e02c00030000c90b41c446020b8000040c6240388406490303d900c0c144040c3e038002e110441d0074500c030f0311582c9104155103000720100c0f078071181c211200c940980c0e10031032100c1f140e600140201d41c006035510b07441c02d0055103620341d11018142e1440d0106256181 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 709739730 1250 709738480 709738487
    0x403020d062703031b0804020f0a0509100e0117060a0e07120807060c020705060a0507030c0b0103150b1504090e070b040f0e01060504051c060f0608070603110703020a02241306 77
    0x1003400702a05c0020705451000403600861031607030240d41101e60200e00501c010208400c081180d011942200e041c40034005e908062000d40029194440c203180160f0faa41e03ca410318600442150f0303075180d00b00303a01250303016a151300144840300581d000c41e00150b03651585450300d11540f980964100e800400c03c141041f000340110045a01d06200402c0714506040025100d4801c13078650304107001c4000713904020107010380703208a41c50360410140a19913a5900700780c003061003005440c0702c00525101c05e04d42030f803802c03400716101d914a640e113060038035042c43c3c45031004106524100d0143c0c803c0c8200010400304100051028000b02401c0c216030a1924201500c0100180c02010a00c0810b01060010782c40e5070340c01401048102e000400c013840d107402c01000400030200c0c22034002e42805008a00e80c40f001a4500031900190b600300200203801d40300c1c649600411800400680100c880320001d4a86406c101c60949219980161080c402860106165215454988010304114420450b5a40 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 709740980 1250 709739730 709739741
    0x507050a2304230403030f050c0a0f0c0b15130e030717030c27041410061706090408190e0109090516080702121614030c030403020d06270303 62
    0x80a40301400300d03c5a035142c015007044074885583d407503d04900060f0606120350031206403246d4440b0108024204a410b0008070f6104c03110304404036124030035055550381724000030514640c10030700c2d82403252502d1a8440220703140c1e280c2d8a030700c00002c40710841c41680503c1b404941201c44001036a4030060380c54040c142440000c00c10303141880034810040d4240d0800200c810140d00003204821400500390580541200c01c41d02c0c0303406c40d1804006051445400011030700a451480884030415514038089506038031a6400042129183c1c0119005040c440043c581091046101c503003030621000300903004d06c0b45403419900184803c03400151558202005070b010380700441c3d003031003e40b0b442d07114076480804002d0507004005100d80041c45040c4240a00740c0082c00008900385d075660341c1c035004150321a44041c02d031624014091a80c407110b000200311425500b070031010b10304092541e02009424200c410b802c2c0c41041d180c82c2910140c000d1000654514540d232210180a50030b00d0400030110362 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 709742230 1250 709740980 709741049
    0x210a0b0a080312040b070c0b0a0e01051317030403050f0d0b0405010e0c0703080601050d09050c030d030603030210021e0c06090c0303130302131d0f161206090507050a 73
    0xb0410000a01032040f4184010b50040d0400d0202440762941c81c5c00700c030b04510000c4050300580411040c4520005141c00a941c5115402300a01c000d8070340401750812196802801450185021001c00010803403c0245034042d001e42001070030b100c1a00301e880c030307551300c0355040d003041c655103030910811843e083c400c4038007601011201502c113160050401e020740c49005009800d000c00840000e4450f0311a07821280c03601c11940b8148035605d420324200c2d03a581418488a840b03070043e008440c504610902c101001c4a030168001e1141340003118400d0f00039804100c0348207956031003001c0000c03800d000750002c01030360025100804042c940022000d0170503080b2130f0309520940040007a80000307004104104c003075030340450721894004000410000240300c402e84111b6203086170954100f9003078000c038980c982e1445503016a80580c0f0a0049103158001e036020b0b85d00c101e04200d5414010841c0c55106508051040d4222100c80b0780b214006030100805610200e221080302c12030110080b9905980d18080 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 709743480 1250 709742230 709742233
    0x406061e03060f0b0112020903070305190b090a0201022d1e01290f010e090a150602060c160203151009060801110414010c06110d05160c08210a0b0a08 66
    0x90713040c440000d20280403081e021b128241c02040001c1c007a50103000d940015a400001c482c034a940040701c0314007012400000703507030111130b190009580c0440800c0351004560305034080c140807040d1200ad50064040d010740b410600c468001c0c088404181040381094004100da04400120240360115095404452102e4540804c0454403840030b89200d01c07030040d0500444406a8210584d0012a0444154035007168007072840c1050145e10901d9900030025000e4183d6413035501c54490b4000d982d103420a039501c00410004001d0442050450070403000300d43d200500703450050300a1080c85501c0d440c2590b01c0001e4080701c5a080000103864881d81004003203420003071003030781000700b0184098025403142e094030b000000020446a8807a0302c0100440380d000070b0402100c80d10550220403a044914003a015078034080102d04424001030201e89102407550310001004229952402e0541112000c1284c10fa030101d42d1106032401090003920480c0c0341d50000503990030b0b01d020480c80c50341542c03010546 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 709744730 1250 709743480 709743491
    0xa32040b181506060706140f010e04030c1205090301091406070306051516020904080d0c0309051c090b0c01150909020918030f0c0c130b030a0b0406061e03060f 70
    0x1811000300720b0030301c0540c800902c501e16a85940100310b01d84500302008040720700c1e158410310b0881c0703c00301840c042c0e42d090711131244980c0ca0794503101403010207507800703400300e08081e1820000409011408150507140d20b003a03410910341502103400d6032800e01341140d82e0080030003007802403031081141a03841141880c003400110704d040c02007a84065650000c0198000000d00f40340301002081071940102c0d8041c0031010710b4906030505159640004e04159140340c14580c03141da41c0c6e4070900a00e5201a000303000780140401c1811941c542c0a84400414103000100c0310000c0c0301d8121501800c1c0406030200041001c1e01044202d858000c0703c1e40040c1d101d10700d018008400344c0c59984405900503e25540050700822413246945107001e8140d2050460000060881400714045140603800200f0b8a60040e403003203c0441405580d00540001e415030b11014180d40070806903440c05400a01441001070344030f44604816032a01c1d0085074080042d1502901002049014403452242d00b0620700200310 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 709745980 1250 709744730 709744771
    0xb030c09030d09051e1f050c25061b0c0617010504022b0204050607120e0406210201050702030f0312071b020f030c04050711010e030405090a32040b 65
    0x4400286017002e25501450380482081d21192204940070703030441c24070b00c49201c0040005140c1e42c0306410200c92800761401d1400c0c0711944100e03038614a070317a29002103061810464103c401e0820b50f1801c001c004800f040300008609a454071a01502d00d0750740b045503502010f41c0440c008001a0301c080d004501c1003049100307450b1250a5240b01c5110300314034000143d0325a010b01c0c00b07402642c1003d0b0740414006445030810854404094654030305458844c01c5640100401044440314401d00c407a643e11800100040d88521846c140b090348141405400c061141c1c002c2850592107001119242c2d10019200c00a8088910400d5210516140440c0401000c0c1c41c10800c01106d840020300801c1d400e869981195000c0c04003000400010704104400d00e03224000810201c0030300e8a071140340d4030b048506a1380040110858058460150403c040ca40302c00040710001e007809850408041000350040b55070548100c10b112950f01040012009424a8100100c60300c102906200c03440551015098 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 709747230 1250 709745980 709745989
    0x5030307050d030e0a14030d060803070201080106030c0302041d04032703150e010e0a1205040b12090a0b010303030c031d06040b181f050a050f010b03040303060b030c09030d0905 78
    0xb03200800d02e140114580584c0315442d4604080d030100104444102107000e0b48090303001004e443c12802542c0d0510420703a0301c0d4100b940702e200701400a8002203000c0014040b9034001c0e0030100c11147e10740380051402d41c0d1081000b00380e011003e4040c601030025030500051581c003500a0b10b03171030420843e42d440c0803c55100c0110f0b1207881d2100500e410b01900d8091146425035003d1090006407400034000141450b0f4103584400d0041c80840b204040c10100e03219851265058406840e01c00c200303035103482c9001c4c0740f44d00800c0700241024000c0c411151070000040791010000e001394400d81700400c00c4500440b020302515001d83c981a400304d503007078100c3d074820000642141c010740c001400c21020746401200d185c4224503070390640380030310502e59800c0340c80050318200120006402001c001c0360700c2e054484400c0c0c45040e41e642820200f204014001c2c1d903810340013103402134032900b40060800d5651014402d20f41045500c40981d040108000d10b850174240140136446020f4540394a01a08050004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 709748480 1250 709747230 709747243
    0x6070302030d051b0f0405030709180b2d1611101802151806070f0803191b08180a020111010b150d18150b01090b0304060501081b01050a0f020a020a030c050a0503030705 74
    0x20709111107500c0420340040c008002103980423751504a21406c0c5031000009503040240d07650011103000344240310b44c1502c100c01030040c580710f5402504400e4422540b2101400c00798000640150a440c114401680c8400c17210044601e098441c9403a48441d909000a0264000c031042c0140c1c1c04001c03143c0000e002c001c0e124000750b1301c40200c0e0b84076111107000e105002d42c00085415460314001c607080724203038030038140b43c2509030039601c41869a60302502d00307071321005441e50042641e211040c1140150700405482c031450003018000110300c0520000a0218494880c0d4440c4061001458204103422070007180c0410186080700d07124000c0580c0c5240c1c07054004161020030555a0900700c006031b00c074038883c100911414442c10380341e06090800000800080c0b0807a00540b0904204070384003e1001c040082c03207101615a2810454003000544a1020a480300011400740c400b1110041e50754624400155000741c61803042c2904103414811204c00d80d42125100390700600ca06800100000b552 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 709749730 1250 709748480 709748483
    0xc0f060f050a210504080301090b1917030c070f060e030a050d0305090f0703081b150610030b130905010e0304140402130e09030a0e06070302030d051b0f040503070918 73
    0x109115100d00c040d441281443d1108040d0030b41008284000d11a103c0301a506035546400200701c1c0390649400c20811040040e500751840244450801c05100d811240324005240e61003601d10309103d2681a41c2401c110303030411300d0584560582841265403158421300d0500c0b00b42c0c010440c000030790311190f42c0c4480100554081585400006020368828080040344180380011904942e450b4681008a40c02074075000144150f001180000100c000600d40d9102842180380308d40c0381c4881081c0305590810007000e1041c103071104070300400b5440e100d0810344803003400000000c0608980c07400b0350075601d0840415a080c0e00901c07043c0652036111a00c58a0000d04980041c3c0d83d121300b206e280d40700c884540c4200b8030b00011030200980c902002c0010300c0c020081da42c66600c0a070782d800c1040500e024201000c0d00582c4180301140319000154421900320804c101001c0c207451401581c026581d1000c81e0b00000b40b90041810845801c04012030b901404030500c05104030030030706103010742c1c81414400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 709750980 1250 709749730 709749737
    0x210020a20030408070807030213060e04060207081201180e0c012a020a0b0d0b0a060804021e09070207090b040207050d0f0c0204150303120b060d15120c0f060f050a 72
    0x5149241e0a007002154010043c0300d0a440301d80703036240d1040e13444405622090f40520400e02d0343c1d4003207030700610501080d035400f051001c49a886903100c031700094205190849044034100688812003c00021650080104130461130010094617400f0042d607000105281d61076102d99100d1115030b13002084030280c141c42c2c1400c50f84809000c424140844059000650048031007400814000341800041003d0342c1018030911030404c85409110a01c01a40300301400100d03080041001850445003642440c101030481d181c8480b221000610348440a40f45000036a02804042211140074000d0060b2141e0813901181005a40d071101919075030350128070b600304074504441d0b0440e6800345040c4c10708240c0251040003160950314078582010198001540891405090000410303a540144115028090804c9082100c204448805064144036021121408510100e0344594611b00e19a03080e002c1d000c0c0c01025890301c1d0003462548559000241008070119183e1910350f004021100e10112628 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 709752230 1250 709750980 709751027
    0x708070b091503010b0c250e09160602010e0f0606030c060c33010e060a090209060d151a0a080c03070c140a02040f140a0f0b0a0806070210020a 63
    0x60b90306400704001d0716000b100400081200391004025203070307110614044990364441411a03260183c08441010300011790503400344421000000001c1d0400b16040856000600000103174401c0e40c101d0b000600141c0d511071444a8452781080f003501e240d079038800508142c0c1440c4c0c0121351a030703c00da440b05008050018100200c030204100c03100807800000d034000c0c41d40c18111001340d815619002030411101d800800410304090a10030b46009201c0104024001071500d001c8402039003280e08030540c049418400c040384032041d4041c20540903541059020040e04120030046041394028036030907020b10a004000c0000d0b000907501d03410070044a042512913582000440348407541c000c0c02000800c1d8018441c000110000711400041d108840030302507441ea02d9030100444041c580500c10f90540c1d113001c42d04640d1203038010200310704946008a0840c8160020801c40011a03004031403d078490030401c50b510f51305001c03040390203003600000c1d03141ca0a400d60051905000d840740303800100446 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 709753480 1250 709752230 709752247
    0x150303180612070f02060c190c080c01090c030611190c1e0f051b01120209130213030620090f030a050d0e01030b10020601031b0305011a040b030708070b 67
    0x60503503402d0020180d080a15141c01503005040041010381c40c40988102d00108882103940420380b0070500707400812641d0007a40c1801107441030b002450603250044104a05100c6500038040c403e03226005015040c4160703e0342c0781102c11039030130307481c3c12464400c28450101ca1600e07540c0c0c0c0c80b03081d40d41071403c2c2c0342502c580e052400318162100303543e401c011042c0e00040d00f004007013040512070798083c50903104003003407540720318204c012a087c44038000744901808036050390f01980940311009001d0041d041c00300c03805600d4070490f803090a004543c50303214042081080114010206000f03980301c108402c244541020b010280070750400184140843c20f800f8425031420011610450381181c200c45501c1245840034044a43c0d0b80c2017640082d040c003170148201c0c20078120002c44070030640e00600310b03a032031515083c01204120074070b105410711556002020501c00d009160b0364012008101805200c5002000101c60710851042e020b0340018100304401240440e0900440b40c0e08445070b681d51020 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 709754730 1250 709753480 709753489
    0x10206040f081204110117090c040c02030c06250e18070c020d08031b07020a0b220902030121230a0f0b040201020705010203031b0702010c060903030f0515030318 71
    0x90540f00140342c600002008203205c024040c2c070425400a032540c020341c03416040401840c6808440c151100e5000903100b03012410940e1001e01002e11501c1907a06210502c00c000781800c4003511403041a502d8040800380d00c0d0b65502c81c1d21410101810b1140300c0d0700c240c20120f2601c4000c1540d580625081e0000600160700981c0d40003000352340148280a20a030a240440c501d400c1665100042d102d40750000d240381c1030810490310381d9030f001402c0d80c0c0d480389004020213040e84084503c0c4500b2500c403081d4014001917040b894050200c019000d6100d40c1048607191004080e91224030201984200784e00215284250020352000440782c12840d02d0302c520f06451900022440041203445110001c80078882006c1c0024040c074402d81c255485261b40c1d00049940b8002901d0300c02c148074020580b42481c0844800501210748103041501c2d6000f000e0722040c089480c002d8041d40030a890b4000400558654405d141d40403070502c99440b0341180b40780100b6524015203040c045040c41d4000419200d659 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 709755980 1250 709754730 709754737
    0x706180911040915091104030b0a0f06050a1508070507080702040c0302042d060c0c060e0a09062913140a03050a081c05040b0f0709030b0109020c0c090105010206040f08 74
    0x503c2c40b003403080c03081100b0601412034141c032400b0380c01c1d40b1703120b640d4004081d440121070031039400868403241510740c3c40308413009110b21010019525640e0000064035200d902441006019049000000c85020980035108200081c900401c2050400035200029009014ad401e80341d0180c90000e910005c41900b94024131507034000034803020040d0034000f0f60701c410154a0402c5003041c4881c111080c2d690200341c45d007000c1560001c150847d210410700000d48540c48010f05803134010146900e40d9520f170f50041c01c6404035005912940d802c40001c400d1081d85500c1d03584071240e541e030a14030385a402e42540722351032201e024041000803a10407000490303072500c1c6c0c01c41c00345800c0300035142d0001c50b40c174021106500c0440390704142a8030322070005234509d45200d05d910030758000f20310240c40d644d0310070484c21820008100c0c0c001d0201101020000c141c561103614080c0080c0200160340b0342c102d050007864000c01603a9244601e0300c4000510542c0d902083c5240c005c1da014242818031102807030003112501 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 709757230 1250 709755980 709755989
    0x50a02010f02040f0603110405090f100518061e090106031a06120f070302180f011101051f0506042402190303050a060e240d0501060b030108070618091104 68
    0x3400400d0120b64400b504d0060404c541d16914204091904080507031002e029a10601da4007200c018000384c000280c22103840d40c00600c03c8031914545132a000000c000721a1200d081c9081050705040102030300340b00013500308010101c401d00c50881101130016800b41014003c02d07041540f43c01d40003d80803200c80400e488000c1c0202000d44031030300c1c24800041c111003251900d2107500644c020034040d48c040c0c802c4030840129402c464603001207e1040c0881041805682c0b410401200c03945100c0d84000c0c480e090161806044c803408001c038214500121050940049101344010001040303000241c07103d511726040b079480394421810240600707070304107a10304904107072946524580d40209039041e070180788503610f001010003c0c5031300e901031903084400450b40401080441203162100c80301e002da100703101707140c01810540484840c0c0d0352035007950282d0f400490044004001880303900380c18001c0f003000d04010702d00860b0b42c441040f40490300840768803911503942d03620283c0f80c40400d201000c480142 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 709758480 1250 709757230 709757261
    0x50603061602011508010504060c05041a16020d060e0d0323100b0f040510032922090210050a08011418091e030a120b040605030a14010b01020c060a050a0201 69
    0x19917840d50b95003e05000c07601211074620704440345d5070840c090001c2d80c0680d2058181a00100b85980d194030440d801941a9080c14104286000040e942c040400310940c0c8070303d2000c1400000c040a0a04c1c1c06003074200f400c18503040140400c00311210000c00048860340c0316070081d030f40d213401051f45d201400580010241a200240095038840964010400c4071402c1d143c100d070321400820118115006400070311040300354480110300c0382c00144041300003c0c000134a03000d0a031804030312141400c1e20b4192910403494071113400c0810b5107840400b10003c41102c0c05c04620741101d81c5001000c03050f0500409021103003c20b8280340070f031038040f000810606040f1501e44941000d609030350792880401d00700510b81e500701d8001651074001000352041700b15039840c0c041707842d03003060580d1001e0520408180d4001e1364500c070020382941c04001c1c1c114046e02034050035481c50010340019081d0b0790748030347c1d013415035018440d03400361a02d0354402c85106e60440d240007031715405210801ca026200ba0184030401c0d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 709759730 1250 709758480 709758521
    0x706150815152d01120f0e100e030703050f0f04031112150a020c01150b03071805010c03080a0f1103060a0e0115050708040f180f05060306160201 64
    0x215032040410b80560601c0000d10014001c0030200720039400c00003000181221210340c0040c2a403403112622041d054141030282c0e0f8410820106000c4980c81084158001d8641c4c540401100050000c5010301d40c0c10390302406410b80d05039a15640b0703c1100c00040400c4000150010240800b1040e02c807120741181440d130350b9135540d0400e40700c48025001e00500c1040d25020045490303c00041c0c80101d10240d01110880750340710075034400290058130f000112552515800306201144101d400003601d0070b1240c0c0b83e100d040501005085c00c8510b40c0c10940400d02440c140456a00000200d208075450b1521000c0c540d113800c0c04c0000b50207254844081d09050040d002c451f04401c0001e513114281c15100345034200e59403032035140d86110030b11500541d004030780803030340c201c40c8611f00805203d4080c02000f4901903858000c05041207080e400451a82002c1c41e00e03180305503090044008420b1442e000340054140003000980f5004098480d4284041c4042c014184c03c0c002c1d04469404c0940c8401c0120 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 709760980 1250 709759730 709759753
    0x190b0d02130b0c07090b01020a020d121e120209010302120403110f030703082a04060504060915020d030b03070504230105010207030308040f11090c0702030c04020f07061508 76
    0x40d412a40c108101c20070341650101d807100c070300c0702941c00c103a8000d0b00900003545085c0c1a200100104407a040c1103004001c2400050385550f0380a002e4603103e22004615040c03204002090031550401c1014656180a9490762450340814030004605050314016610043e190060b8001c1c403c0c0d260034401060440104001c0c960002c10320751703000500310141d51003100900d840c00d07241d2065000080101d1a41004205500d00780300301054004101300f1643c0c02108418001c2c80e058120340d0040000810018090104c242d1004089008220a10f009003081215030001b13521891035120b080100b5030b844c03600d41000e0358102f02240c01407070060820007201d8000884901d00d80c4141207010600a0007800001d05544001042c404894160f0355008454489569000211003481000d886114400c48070404541d240b10116001d01400d0118950b0f82c591441410306088040d04e0702031166206200c9032900b44101021590722543c070010000d0942196640d950700510185c004618a00c617280c0380c0300707 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 709762230 1250 709760980 709761007
    0x906030f15090212010605040f140f120a03020d0201061a0d0b060c0307030e0306090303010b030403050d1104080d030b010e010f02070305010204141804030e010507030c020306090105012111190b 85
    0x2c904c1e903c07140100b4480c1e803144401c0ea000d02c518807030007a00c2d1440c164200b08c00000c0d2454082c0d4220000c0c280e00c00d45201c0d40020340d0b035620b510442003181d00248404020150100711740e01480030ba5000038410305141030301d20001c00400e07004c5042501c40010f0031244042c0745901c01140d0080c0100f40c0c0e5201d290360504c0e00d5032600103007000c0380032698a03100380b0502e00e400103c070388c401c4a08038019031860b82005c604250030f0300050021001d02000340f000d881c60b1000c1d030103480145610f808195403200c0c0740407100c40c503000110795914103251902803811156640401020b09400d021b0900700c003c00981a400ca11341500d5074005000c0d035102140214020107034090002c82d01d1400c07280402000c11a586a960084d403c0d2002408920211100c2d1000d502940141009901a06001030360708115004a824540111a00c4103265503580040c48041642d10851510545100000508501d1a603c488824180203003003440382200c004140d00c82c0c5c40a8580d103018114812a141e2150704842a00c03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 709763480 1250 709762230 709762237
    0x9041a1f0801110301350105040b06010c2102030c1203060f06122d040f140f0709020f040807060314060d020d02040b0310020a080f06100906030f150902 67
    0x40d1099580c180021880c405000e4070b140690856a02071641c1d18020740c81d00d040c45485c008200d50a006030041e40c0d8042c00d0700070491102032000000c941d41ca80740c41e1200300600000c10a5051081041059000c10841d001e0060f1039400d5010329a40142024070580c6140180903405d120752182c1181d0100e10640d0802071402283c0a07204001002400d004029490055000305000143d40d000002c1204110440c11403a044047c4020400f01f00e0030803a20301d40550499040c0c0303070782c007000c00c4110030045840d12882e40b004ca8100504002d400070304013180c03120000d201c3c401845801013501d402e2151100f0441d4002c041140c205c0780ca1507031300d10001c6c0c007a01080c0188000c04400c10006112410301c042085840d6030700034000700229206034200710080c016a009207415204034010441c1c2e0b03000c01e01c000c210074040b07512001202c1c80c100c026404110340051142d4010f440c201c01003120b464020550b9000d64159003004607122003e8000400245034214a551140041e60400900c54485034000c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 709764730 1250 709763480 709763521
    0x1d1011010c1d0607081c110705030304031403010f0b0c0309030d120f051603020a031410050901090b01020d1b0c0609240509040e0304050402070503030f071d09041a 72
    0x3120b400380c01c14020000359000300c1e030b8050103500301003014107200d840d01012491026502d44d400182103c04500030100d54101240880e282da00000910040c50380221025040848140d402071566040c03031003048010025100c1c2140c40c510109042a68403014000e0340c40241d00502140c5031030140900c020110a10051000b89207440c116901120303048078040d0034442e00c501710320b803183d81c000e05800728003d501508103c0c0425075111980c5445070041d5100501603030782d501c16030211354141400c0104150b010b0303101c25400c6161000c5c184079640c000c6118020907086081c0500030b1a88038000d41044104104000c0050300c4001011070191f40180e11542654a03582c03014004012041c404040ca112010320600405c1081c04225003d141c06d410032000c64400398241c1e401c25998001040584e040301d5812101c031382001c0b080007180d80c01024020b9004089140010001d00e43c8203007580740d4080045540c1c01280c90200080500203400f50206210245031051310080ca412400d440190070b83d00e44 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 709765980 1250 709764730 709764767
    0x8010c05041e05180619271404020904020307030b040302030316110a230303010311040c0503040b010905040f080a020607020d090b180102010603150204030201030c1d1011010c 77
    0x7400ca4a015a1041c0d481c00d4800141160b08004030400101c034843c54010030040d8030004c44c00800c1c0c81c140ca20a200b80040200b00d90081c03100c00a81f99112856404100c1c141c80540381145a07840c052000704580d400a030140c40000080d00c1da0700200342071905a800140445840c14148010176034000000c620665484d10b450001c1c807808442201c0d8400498290103444c1d1200007098089240302608080c081c20020f0b40034004511816902d080d034000340e1040cbc0710104c20428a4040d0700f003038010075034502e03014a4464070b589050340e06c03441c4400040c05002c56095480340002c0411405030554030525401c8291903440f8245803030001d40d21078084850b40018015004060351084c001e030038490070354201d47c0905042c00d154982d40c4103200760300c1d49103c0c11592150302c00800b19190310001848450700b9034000d686d0314118000902544c0303d003e002e404010103020008a00b010513808a0024038041703992400ca88180d61049031300c03081c004450a001d5180c510054081500041c494000070390041 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 709767230 1250 709765980 709766009
    0x60b180a05061804050702242d01030f02130f0905101a01111c050a1404050a140f06040902090a08010c050a0813051b09100b1c020408010c0504 63
    0x201842564043c200c24491626039002c01c020080c0307455006154000802d104072a042e5800c0c50114400100d150b0220a06035180c50038000f008a1140781c004040315400b281c1c80695112210003015041e0501c8051311920501c0302c2c00f42155107440c00313204895a100340a01030354514400c03260050148100c01c641522400700c40c81c044c03030040e0007001003184040d5164842611200d0040d5594016280700c200301e80204424281c004180b41c6a140603020240d035840c0c1ca074146580d0180c04070402c06440e410b0310b41c4c01d010401160b9560400d00080e07600090baa030f0260703c1d002002c11201c428401105a0101d008240070403185050b81c050664000220b034640c3c1d0141da9510010b08a030507050401002034020810b18078014080c040b4590021a1403811141842d07180d12454100140f4914000109038078021001c0c081ca84401165040f00391034401024491501a00f242035210700040840ca0081a02c2c0814030303905964151b13002884520005c0c01005108030740181980c4c828059256480c0c802d6 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 709768480 1250 709767230 709767239
    0xd051615110604020f0f06091003050711011e230406021c0204050d1103030d0e010902010305060306060a230a03120306060804121209081204020a080f030409090303060b180a 76
    0x1441c18069500640035024817102801840b4425140800c0d00f50844410018481d060321001141149555071303a0340041c1d14207003580c1c020050742c400480410a0b0303060503080507148843c6100c00700311620880001900741000344141142c0307044162150031907480c81c01000180040340c2c000b42050f00b1348242400780c0d084600902002c038080c501455410080b141404000982c00c3c1240c6160b00301c00a044a06001c1e0b025140d0040e507a2003c8812501c0c0d44a00f524001c6503050701503240c00c40000c81c058070345803074045c01003070f0400c0c1e0707512903002004901d010845e2a40c1c0c900d80740c140c2c10075024014045880c0c07039040050300c00d0355071600c4600103407421a000414500c900802802180c2c88164a402d200702ca003c02c403010320041d01c1203482d083d03907098032100185009000b040040c020668854840c0751a00410071400016403041d00702c1c1d00500b461501c0e0000100498080d00c019403400104010703503080440c018291904015640840018540d2081c0400078186d2001041117600c224150b40b00c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 709769730 1250 709768480 709768483
    0x12200a032a230d060209190f06030b060a030b150a02010501170f1b0f040e10050619030b10090207031d031506011d0411090906060403110d05161511 65
    0x41c41c100d40c0e40c03900c0d661040902d403ea501141c0b02d4058007000d81414851400a800038241c03000031440540141c000b08104a0b2401414004005a040801c540c61280c0d012809a215800800b41059961100d40076107036140341049200b4108490340a803030310701d000f6004e4000d00081c080c55451a113485107039281d442000441e000c0705001a4003074030300d00300c05000340d0703c44181d11841c003540200005110f10560300d0350710440d440303602d250006004002c030020b041812a48042c1030640210030114584001d443c45a4115080381d6015400b850720740c1c1c81040340d00d445543c0e50800325800b400000c0c000c09040c1d20607011001c2245200b00b01c11402082c03000c02d682d800e110451400323b2403000300020301e10b600410254040055901c0480d80840603000043d00312010707103207040d005200104525880e0300308004041ea00c0700c0d040e50158a0141075407180110b111b0f410012a118640440f042030400a09000d00034a102a5007420350315151034500c0007004e00c51081d01c0c2c50003d0300c2000e200001090 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 709770980 1250 709769730 709769759
    0x1503060f01030f170f0304081b0c153601171608130c24050c120a0513030c05090901050417030a090818010912200a032a 53
    0x303003d20602c18020013542ca82d0704601001c00501d500794401d0000d0405d05000400940c880e6101d03c5a031555244c1001c00340c01800c070020070f040c150b5030002507c0140d6480b101f4816600c454000c20080d120362400481000c54042c1403e06000d0b19040000100d18400d08490390380b81000980f14580da400c908081150366080032202c0203518503c5285001c0503500130b260709a003040c040380869030703131560b15251541c41175003e600c60051003040c102d6002540611000c0800c900e050781c90114904418001110781c1c85e807120040344003007400001c0340345445001e01308407100e207002c00340e14200d91944c0341080901d0360b680e4850b0740c0c005c0c01c17000002031024506200b00fa1080c3d900009660707624491241c268540e41004114010f0903550b444c0000100d1100350140c400070203014401c5100c45110740004102041c25032001d000d04407020001400103202d0041d00042d055803180d650500b80c10a0f0024802c16915030010b09050300300000749420840c5072100910019520350303c02c01150f07480560040019 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 709772230 1250 709770980 709770983
    0xd0b0603043203130603061413020a0918090b0a050c0316050d0e0f07170303040b130602031602060f06010906120e1504060606051c051009051503060f0103 68
    0x160404a005003445030381c0c0c0d4103060366003112841402088224100c0c40c6a201104c054444008030b0810045a903250003048094548a00000c51030000c5202003460700e41e825549410301c90700400c4186143e4071030010382c0d0041040d203c0c0e03440d4407500c0c0c01000c4020409c100080d9210040e14002403095080750141900454040c000546107907940c20002004500701c107211010020104200320a158680c01040144950140500070070311003941c03002d240c41c012307600c0900d006107202c540c180800c10100540303a001e600511411401d81d01c000d0314108012940340000c2010b0700c080148507001403032074100340c1001c1031a02146c5494039000781d07082c0101000c0703801a000401d00d903000d2020b10b1183e00d0384000c0f101400e101041c1c9a1840e03d07070b24100550320441c41e01d902c14290801041c4034032406880010412030034068500344408040c280101074031110031440949920200d00402c0070300c1400801002078103070800203410030134018040a2443d2680324880e100b1040407410702c1c07007078011042c1200d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 709773480 1250 709772230 709772243
    0x10507030e06030a06090c021b03060709171f0501150c020603070507021804030e1f090e13140606180105030703110d050f03070204113402150d0b060304 67
    0x20301d010400002d50b0004200e0190035803600350025620300340c0e00505003041c0c626000340200340607404100c0c0c03000d0944417443c0d00c43c0e8080404c0c054116081b0308040c05544042a215101c0c0b15200005c41c54002200180003445248a5180c800601503a00081c16150114410500710104a07000c40301a0211207000c3e5003d5420004140807074001c40041c07802c40e10241c103800d00d080143c032812140000888066011803c07a0303003600c1007072801c0e03038220001240842c911030b0a2401c48000400c42a014010780c1c0514450707001041c400500c0c0b410111015502004040440183e10192034550f40c0035104a030240c001042c040d104500c030101d5490581e003024005142d43c52a54403030301c488110280249401158003120781011400500c0014948002200299524809441484115104034411303440603001440390603400001882400d2601d0007241400031070110341d420340c03966001010b5000398016030742d40218421f2a004030180c00d203984500c0007044071040303140a1000910040742d008184 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 709774730 1250 709773480 709773497
    0x60e0114031018200301050603030324011e090509091516030207050303010b0c100614010c0302010f060806041104200304050a020a06030207060e010c090605070501271101050703 78
    0xba000c031540700b0031507000305058068900c0140e4031003070181109550281031651007095000c03040d0909005d103903004241a40114035601e03004110420755000107040080107032440c01020003a80c030601d0b00c2a6450940d550030309060303030700540141442c0c0c0e45120702e501130401400028507410740400e2a144c4021100d014041566585550403644010f0744101410b250f420b002a202080c410806580a03182175407040740c1c1c3c1c5108044803454034007000d0004034090700344841441400e0600c215958210001e08000d0b0020809240a0b405010002c4e61440c202e440e020000800c81000900a4055805031031480c03100442c000c14041560003400400540390611504100100380701c8005551050081c0261484482150f001401d40e0a07182c1c04000000d0300420208240901842082071800064008100e100c81d0240c01070f00010b4241309440c1400320104401081c004290008804c41e0140505149a00480e010304242449110010364042c0a90311404846501407002c450b44c258060b190301c8203 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 709775980 1250 709774730 709774753
    0x30b0a0506041802031f060903170304080a030b03011d010c2019080c120301031e2607020306040c0806070e03030f0703110d030e010b04050105182701060e011403 71
    0x7a50020384651805110b1010318440140603a2800d005010280ea070f24144270302e07604101d0b000d803040d4014006102030800074040001c1c20007048817460a01810003007220300400000900400020444681c0e16400d4825245400c0040d80b013405000041d48a1348403412007e050b660342041901403a401171383c003e020040346903281c40741039140c40d4410480ca624101080d40e03480d007401d00302544500d4001001c0014402c1200c2c00400c48207050740c0c0300c0c21320b10b5a042d548071403006c12000c1d41240b00a001039003103049030059400032110900d402a048514600305440e140204e9211441840382d18001c0300c000c10001880703400300d02401180100118204a072000910625520503801201448a00a20001020000e0003880c0b104046901c000070a1541d0003071403401e4441c9844854070170741c46c140050001365109003992070150010710107543e00340d46007000400071100c03c802c1c070030303950342c501c2c0c2241a008815001401074074582e0003010a1a40c2e1074100c2426800c103051070942c190005000d082 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 709777230 1250 709775980 709776029
    0x20a050103110712080a0605030d020a02011b05030f0721020604020f01090810050105130b0a1206110c0d0f0c21022a0f03061e0a0b0907030b0a050604 66
    0xc580c0b410200c2079490121035039144907a921007011001c1c00b0407494801c03c0b800c40c01030b101d0b00d0004d240c203501520380340c0c2d05080000d44074904850003c0c184441c80000c105020500d41e40e8540307681e448411240d4507465011002c64541242404441c1c1e42d14000d080d400c41d1001024420008050f03400403c101c3c1c485508000c0708111300210300b07041218000b00000d40000801410101c42e141150005a5505001c04e01442c400c0241600c03070b085007000304d02d580030b4580340c0841c42220b9420390500c20104541c40d1000141070781108540c0103660104006941a1010134200c400329070640b200c4510500108c0c00782c0c0c0c00c01c130f5440043c00480c5901e0f43e01c81c41180048100305120710710f01c159440d1110501c400540c21501076524011111001e000055034202444000c6030a08202c000344590b107001105220140c140070420303e103407103a40000c608000801c1d0001014950010300002c0ac5240160000b0000c00181040a200321094440090f540c240703d42150107135510040f00308a18044801080c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 709778480 1250 709777230 709777241
    0x504060e040f021807030b120d0e011d030616030b0a050d03080702101505030609062a0d0c050c100614010f11120408100608030d0c1205151c020a050103 67
    0x2030b030300036407110580034050480c0440c162095080d61000100c00d4407d01c103100c00c600c0024a0303141c48d688581c1083d504260008680e2041d40b10902e050b44240d4560f0803501c201480c1903100c180c00d0300c03401050004c180320340f030305000c06602150780c1000009824000c004084210f071003555000501c103032010700440d200d00c0078554469282d0044550b54200b41d41810100c0e02c0e25682211203002d8100180202d103010b10010fa00302034108010046410600412001995412103282046144160b24580c07010100151410050700040811560108541c0607080354014801115203004080714132400118511440e800d407021480d94500104ca03c00c015034459001104000030700031200c0c10300ca80e2550420030300d425041c40c88030140d2134500d4002c0709842d1a4091040c07001c141d0400c9400d0080c014000306483d4403071080d1101090400c0c814100b0f640c5c210500d0b2003103a21a003060100400f1400341c0e0400d070400d200a2361740c5101034200050800c844451400000d622000e0101c08202079803003a00300 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 709779730 1250 709778480 709778483
    0x5060112060530060406020c010b030c030712150203010f090c08150f041103010b0a08100b09010f210c081605120405071203030e070b0304020d17040f030305070c0504060e040f 77
    0x6284078030f02d02c02d4241d1400782c048804840c06600010700c141e03040c00a00a04030000d50980003480c41c0340100b00083e85524482c0038000b040703641090f181c000d000400e204902c1c0512090b004540d6035840c0c6091048489550181386c134085c0c14441101c081030300c00d004044c0708074104010700310a04201e6080009446541c3e4603070ba803280e01c82c0c14820000d21501d00850090102a10550b031703455281802412110005000181c0f0000401e41000b000f03040364200c442c9140300740307001d4051401000e015140004004100b20000e030f0404442401080c0f140c1c860020007906448030400c40d900c91001d1070b10090452104c0001a000348200d034000d0905004554120303224a0030741d4501c584803003201c2c00046107684280e000070f13114520841d020400784203540140a4000e0028034500d069004070312112520000144544e200c500e04401041d1100d095030050074003940c640180a0b56402d00601c1a00301c0601601c0d009180400001d031032030607210741400c030f5010441c40151541c0d90389070040c003e07156420 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 709780980 1250 709779730 709779799
    0xc051512061906051b0d05180a0905040b09210d0e010e0a0804030c06031415010c05160f0b0702150705030d020403120f14250203030c01050601120605 66
    0x700c0c090003049414240b405400256501c03130300d038001d0b0014040c80c80d81d000080c040301c0e001841c80d0901c1031780c000301302d0700901c003034182c1201410b80071004551003424651120a40900d0403050208100340b4170280d5000300718003012520302c03920403481250741c08550020a13015a04c100f10072011032003141c1103001000a500d0001402280f0500254107000040c081103882100025041c01045801c503111000b50484c3c1c6401c105c40c40d07148550f002030300c80180480c02c440c84c00d41c001c65000da11a002c1c100388980d12500b03868103000300000310845a4014007034400c404103560400f103076520441d0280d0b240260001c09001084651034041c0703e0356801303210152074500003004940f41805483c00200004d504c10600c00b40c0e4002c6580e00100b0001d0400c409030104030380103c0d01e44d0344502c80c0c03007915000e88400243c1c1e800307050030080c0b1510b10426103200a4042c00b0203d00c07102c0e41d1a0660005100d030780c00303803039511300c80c050640f40310202d5450b402139179885502103019661f058018a00025140594823 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 709782230 1250 709780980 709780999
    0xc0309080d0201020714030c03070b060d0203100507090503060412031509060f060906020d090b0d140a1a09070c0303020f0c03120604110f07080306010212040609030c05151206 77
    0x30266003410904107411000d40e40004e100320401070b0140c0411610079841c1302450400072091035031901c80c4502d06015200b1030300303074012645965a111460040d03941c001d080302c07a1608402e218401034101118550041507002d80000340d103040100e810b44c4101e1f8001442e00c06000114030030790080c00ca1000c40b008001c260040812402143d12540014001e00003465030080e14090000b008400f840d00729408540002065000a607004040d10050f2800002800d884400f0114448010403400e514040c0540030340080c0298082c41da801580c0400e154140042104116000e020403414103560b0341e8009103840c4403542c040391281d805040c0c0c8489691541d89001a9981078070300e075410030854103c0d8102220b007405424905032141060000c180240c1d613003810a6031214040c2d034041c60b40060728000700040020b8043c1c0c030a000464065552082490310303076403182e40041010713003140802c03209402ca031724020030700d403528502184083d08401001e51902113141c3c9810000000905450381000504 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 709783480 1250 709782230 709782239
    0x90a031704031e050706050c0903060402150c01140a0c020f0d030c2f07050f01050d090f0b01030818040b09070c14030a02030c061b161703160806010e030606010c0309 73
    0x2103200340343c480c0350780c0d0142c03220301e9030401c9021101701030f0000c04c001108200d5102e00d610007203012940f054048070780c81244d14200400050724032400803c1502c5504e40480c02d005148440392030790240302e01d0001000034540114040e0703a2580032034042c0c00c0e164000c01c20610440e1080d000704d19481030741d20b0700300400629030040440d4408481c0200300c0752000c095180070f00c03100810650004000482c0c0b031000c032001d03200000e000c0d403040c001c05840098496000b07600340200199420082d0703a00c461400b0f25980d5074100702c0d07520b80001c0380c0501c00c07407054109600e0520f014024405c494030014240340181d00c0300c000c1910f4034801c030301046510b80b400c0c01040c284030230280050000404d13242c002e95070f502d041d07880c0d55050003001040210b0f42904146907882d010b01303581c1560b2140b0b802c007209000c2c1c07001500307042092071a401103107004c802c400070030401004211520304944075510384400d40151100001960580500c00c189a0140d1103a00042c1c2690303c0b6022110304180a41418004107865 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 709784730 1250 709783480 709783517
    0x140402040f0e10121212090b01090e0312010602070501020f070303050d05091905030c01180b011401020f07090c0f080f0f070513030f0b1b1603090e040308010e090a03170403 76
    0x1404000d41768101e180000050350790300540e200841e5400c81c0e40401401c121561090f00020040c040c4000190b514040032085e100704008035080040a08804682907944d003200941e01d0005000d40c2c3e0041c0600e082100600300d00280d60b205413640354075a0b50a000d904503000c001090000d0a511203407255a444420049002105520080c000e4014603074a44512030b5540c20756042e00d0352902c03440395840d444400320310004031050542d07034405909410b80600c040100e103081c90404c241c4140e0b001e0100002181540f43c2c0c002c00e640390041d2651040380c845120141d82042049900000c1c808598000070002118801d40c198008850f003852801c0180c0c00150b40427140c00340d04103d5803014201d02c410188400c03610619441115030101d140024500b03e1080341901803d031000c42e418500740d084008160207070381480050074546a40ba503062810703041c001c003082d03420310415400807000e0f4086004000040707400300b55a80c150720350081c0210111100d40880800410540c1000302e030a6281508c40c88 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 709785980 1250 709784730 709784759
    0x103110d02120103050d0c08070605061f121116171c0b091308070b060102072c060f030703020f13050c0a020105250c0f0c080304140402040f0e10 64
    0x120061001800e6041d441c0c02440c003081b0612400034840c1d015911400560088205c80240383c0c40ba002003042c3e02c42c0f40100f1a4003614a07210150b4580d041005101c0230344c06280c5010b4241600c80a005080c1c10008510355441041712100c20034411500301e02c08038050042c84104641c807000d6640c0f501c400042c21008211089904081440e00e408040d40c02d403804034103450704a000607904148809003130362035045e14403400c0b60081c001102c42001551682c000d203d0440144840001e1488030560b07008000103a08140100c800c2288038580482d102d8100f01940c49204400036000f0008103085030208122100c468040c55070003460100031107084107890081602880c0a05070036038840a410801900f924030041000c2e00c1004c20034003800822401c59010420503415080c0100d900d5071034109180070317210310071000c2c001a040d41d42c0010003060000043c021a100d40e80c00700c210500e002c0030081079100703d10801d1503040e5840c0c0140a001050f0303e0480c2c010818441444296540785860024101d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 709787230 1250 709785980 709785997
    0x9110306090d140405012715080f07170a0b0a050d03021614060412051606090f0e0c030f09100f021b030a08010b0c031209061b03090c0103110d02 64
    0x2c00800c0c45042e95604880561508020308664505060500000900c2482000c801703007492001021003058080d00502d0500141856406142051107004005802d800c070640351620b11640b02c1c00000c003071a104090a41c6410740c1c3d1800c0c0c51305902e8000c0c2800c09401c402203540d60050580c2c01c0004c031a601e1790000b0f9100c2d442500a450a00880e140c02080b45030580c0c400442d840b9042c0c0c00391099600c640c111400e8a2240f2900c10040706075042c61407a2200400e00080d03048481080800c2c00e036049031b06032040701c2e120418040d6a5840d40d200b581039510a40c0e5005101d442800851064000324155680c854001001c985901c942c80819400342d0f40070780c00b503514190780007a04c240300c0000c10400410040503c0c000754540082d5010080103800c0c1480742c1c407400f001c00318410444540c280200c030745907002c2400c03114641c10b0104035113440d41e0040d107580078002c0032100003110980da003900307903441207800380043c0826907031410066024012040c2c401c11030312003c1143d650319000b00d10103491000e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 709788480 1250 709787230 709787233
    0x405060411120f13081e1605010b0405241e030d0509011b020112091b06030506212e020327190f110405090609011803090302040911030609 61
    0x20706048203140d080e00001307004da9500c41c0e20181c0510100394030a044031034501040b03c9004d400c1440c43c1181c0454003480d010082004002c80006003805015008040004d0088800f04415101c2509028449000121000083c03104c40401451481c00d0084034004a41c0d0500a07204c8102c8403000906240144040c040800c0300414001420351f030094012035a00070103c402d510000705074001070550914030000040741502c46000744100070360704144400e00911883c038901c070795441c0c41c03000c2c000d0003046034221301950190032068150001d03140baa4040204003409000c0c140800000c00c200e100400041c41030b214840b40c00d0b002d50614034401140b1074003101c00b0b000c9089a507102100c0035142c50300c48592499004c00e09400508107000d56148046500c10b40f040103104030f900d003601149654100ca030381e00524210400c03186013004280f040c41948110001c1040311489814030307000c1d0710725540c05000076122940074001800c00e03a202103d001d004001c0c06100401d844006854482d0440f400f069a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 709789730 1250 709788480 709788517
    0x1401051c050a060c181505190908031c0b041a1c021306030b060a0e07030207020a030f03080f16021203040206070c030c05040e0c0f0420030406091208150405060411 72
    0x40010710200039020704611b00e40310079480c00641008255026840120b011501d0042c0030b050281e0065615a0003045030034196500d80365290a041c20b2460b5029640044070b04054250105d46014480c1020444a0808901500c031104080c0404138131441c010ba40e1914800c041900540d88011110f88070b49071300c1d60045903150451030104060b64024050602441d11000e051003040ea41003400d5901c90b91034600143c0320b4807240000f990703100c0b1960000d000e0000030101340d000c1c15441002140703d030f407403040c0c1c0b080c8684603486911320704030040c4140ea006810401c044040c0000070700055400500041c9454105030680d02c40c1c1154041350343c0101d031004c0c07640e4802c0015040500900510385949009044512034a02c0819844401400558402c56591446612031f003510822242d09103540e0b291383da01d0b031a107071405000a200101c0b00761101211070542980803803081180c1c9214010200e81c0d00c058446a000380006080041c0c08198491740301d0b40000030030b00280c0050700c09140701400c280310 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 709790980 1250 709789730 709789757
    0x150905031806131a0915030106090b0a0206010b03060d1220280827150a0e04050a0b1c02042016110a08101401051c050a060c 55
    0x401d601084101e07801041c00b8802e555000f60518041c4040303600d03495800c12011509803c070a880c0c441d09030301c658400690020108115110380c0a141a01c016886490300c0035141c1c4100240ca018040030040107034000c030018003000c0e509001131908407070702a0007200013541903582d10f400540032401c1d980001d50f151440c094503103c100c140103c00c0d001030001c1c0c045121000e540f025103003c807141020342410198110810040120211a6180b564060413400e941c8082072443c5a02d0b885928030348241c0d01120f11501201003082103031042900c41d00c0d40140c6030310000070702019140007800d045100c2c0da6010780100ba5210b4061080119101c50290040c20409204000403943c0c500041e516141405800c003e40c0c0034281e00300d5950f802d00b110801c8104029190091036888003509403030300100b0309070300060321100000f00000f100d0501042400b4182c031160040d00c0c0e002c070912074a07a118800640e0603000c2420310741c1842c0480d0086050701c440b0403460301c480d130a80301c142c0c141c80001400c4070700035035 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 709792230 1250 709790980 709791007
    0x10605060f0901090609140609060705070e09060603120a0c1b12030908030c0607050c070503070b090301052a0904110f03010e07020d02100b0409140f0f070f1215090503 74
    0x4003400072806c040e100c0ca0f04143c020504d00d052482000d00400c070008403030a00303682c0d00081e15a040d6104c0c00700c501240d12825080711800303041d5004c110304d110700d00100b401c901d400702e108500e851198054038140950190103e50555400d0404d5400040c00440d076040314a10f220a03101400420b04940d081100b02e203402860480705501c0401142c00900c0000002d14020801e10307040641751070320503115040c040a2500300343c4207a0080f07505108403040087c002002a000c3e01d2480004c03802041207940b060860a092800c0444508220702440c1148400c91010b00243c000c003440500002058035010075018155807021031070218a810100c010880c002000030b140b54020300a20281402d520200c101035540e22005070703e890070325110001240c01d900c0d154010101103400212480501d080903110b07540f17074a80d0109181c0580201052125030440004800701202d4102008020701d0707161560080c07640c1c006070b004a4540c10007000d42c4422001500a42500b64002c0b005507590307198a980d0007 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 709793480 1250 709792230 709792247
    0x50a0822330218041e020a02010c08060405092e18050f07030503070602091201180615081c0e060c0115150e210a0b01031a0103080714010605060f0901 66
    0x100d0195004000003c40c00c240801c481401d000c054802003040400c0301c05451502c04503030b0400001601c003044411206078150410101e45080740c07545072954442100340b02c00d50340d0450300440c0d20343c011101d40c500c881700c8101325101c99144078921032000710a42c440c04261044107a8109181d200340ea001001e00c141400700c00b01c908285401040c103180307995101a200c0c0107008015112a0340860035007459101c0c0002c62111035500c80082140030044201050400040704042e40e9461900711040300ca03801149001c0141e6400f031009080c000100d4a500086105500a9030100300c8001d03890303001c94075000003502e01400302200214200d135031712840c2c070fa40c080a0f0b0f12203562030005040f24407900341c200c841d8200d1820107449071344000c0d11074110740078041a45840e0120342d00c108110182400303264014141030f6845104c1c0365025540c01000380700284005c5c007024012a604104050000e480c90100c144a114004004540c4660b5140000c410340c00c882a481e0300078000245607119581e120b40c18 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 709794730 1250 709793480 709793573
    0x619120903020c03100c090b0304060207020913260702120a1421090d081318140a0b090c03130b2410050a03090507030c14030706050a0822 61
    0x801c400d606c80300006041c0d16207842800410440080071600340891501150807a5801905151280c104500400c0788410496015250600f00c009001103808420002c6949c00702120790301c1c0d0810075203401700020b2000ea5000070503540710701511840001c1e0000d2003c2e808480700c50144c07a2840644042040800302ca60030400640e8040114580c02c0e034500d966001c62a401c4402d0b2615007031f001c4480c20782c6156580180c00217004000e080014110141c021600e0000c0e200b402201e0342d200d0785009000e503070f002d40760f182d4000d8180b0300141c0c449626030091507026a020003249020035050300e0b9081c03110410381d40708155101401c1c10340d851114101c490b40d440041943c0c044008400c5030002440d50088020800425407500341d80410302c681000988091038100c080c11006a075240d400d000320640e888291402805140300018109000d002611441201c50301c0f8403d0903910400070b13144c0301e09400060186211040701002c0032981c45549042464406144482881103400c40c04251b54040081e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 709795980 1250 709794730 709794763
    0x50913020306180a0b04081c060f0b090f010c05100908071e0c0303030f150f0801060b0703090b0f040e0a06060e061c0e0319050703031a0619120903020c03 68
    0x1020700c00a50004901152941148980d90170703844a00c0e101e030342882840810381e03d802442694210f071910030345c049070480308141c048a55070369440c0c0d44038840d80252101a940607881040810403540101244c10141e4030850640714085480310700e0744111003901005a170700d00c0d40800d80e14100b0a6271941070164600b2071020703006c3c0c140c0c20350310082c500d44940402001c041d124140f5010b4943c142e00042c41c0300d0600c850300c102040d103a0b00c0700d00c5001700354822000c0942c2081d400145501440080340c1007030340c1650f82c1c80c600904040f5224215881070080c0700110404202c00a14000307149100e90040d03c0b41c80303022030580c1c40c0c604000c248890004803240300d000c0c204007101c3c801150300d45d11001d10b2424640800d00c214801c1105041d80520140900c030140304404071030650f40d03c2001044614803e8804110702c21071611004200041e50300c026412a008000c160040e4030001e1013804249210314110741e03c00c0b04400d2860039242c0c1484114050390000909480714a0306100c8243ea07442c081c0d4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 709797230 1250 709795980 709796011
    0x5130b280b03060412020f010e0a0c1502030f09060403020402030a021803070503100f06050904140114060a030602070f06020c0a1703060a0e22030807120c02060610030204050913020306 81
    0x80001d031214005080148900c44285406580394001e100c030302d094042c80c07c020020060580980c0740c480550300811a0f1041501c0d801041410010948000801c5135900941c01c0050780c407009000c1d54003680c0b42592000e024400003006903194001144118624040035850f154031961811030304c03e8504459100b900700c54070520880c0c50000e8641501002d0f0302c008a00382010040d801c00405840d00b003d40c202d25094100b10921556400e402424041d6400800c801c05072110300351302002c400d03a03c0a40c012000b200c200089403840d0007500041e80101140b01c41000555112400ca0380021402d8000f5004000000d01b40840ca407107851124120034015840d51510400040700902e080c06201b005140c1c41022070032142d140080400703107040c500a070203400b48a5040107404e094045600000040e051a91351114025a0140083d819019002403071f090710f804080150000900c00d400003015801e1000003440e913540780760140901d800075840c140310344040c014182003810040c8608268403070b00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 709798480 1250 709797230 709797251
    0x70b01091e0911130e010c2a0f020405150d051c030b0604032402030901021b0f060408160c180b0d0b040b070507120806030d03060305070905130b28 65
    0x1016603100c11030f0216420124001683e03407001c018100b2007030040b40380d031030320f982c00c50b0441c0c020541c0c001400303070210030341c500007030384c0e011f00350102903581b8014900304aa40e0540f0050400c4c2c1c2255400c44541d40700c10a0780808400410460f4192207029100c0c3ea001c00703c03582003981c1921202d0b14a14a6180510100e0255808254588070b94030008204a01c001101c02d0304409440019031014210708042d5035900700211658040e4000e840d09204d0981e41110008426000103000c407040407085001d01200d94803a02d031030140ba0050b006201a28400c55501c00c0003079000758051020304041c2030b42c1080f405005030036508940c21076902c2d5004040800c900c03400700c0c0c41c00c00036660066111255041c580e45101c81212903005143c00105101c00c1c01051003942504030310031505c526420f40c03c68003400d406040480a0301e07a207200103481600042428407076048150007050b0301c0300803040b0b031412070385840c3d69032541c50208841904500c0d004c184a004118502818041c1ca4281c400060000103401c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 709799730 1250 709798480 709798493
    0xd0f0809010e0a0f0203011824090218150d050f12070c0308090d080c0c150a05090405090304080d020303160f0503150d0506010b0a021501030b0c0f070b01091e09 71
    0x120f4000341007401d898204a00310740c0e09420107030000c259022510250001c1d890460401190300c00c0c0e072650303115006807280c07010300c0350321450820a030000d0600312070b01d44880b14448820340241c40d0902884a00b02c1c0303540070b61114500c41d201d5602c20801030102001028503141011154651300d54910003c00c001070102d2007031a9030000b500d8008074100c0c2c2d1104a4000540c074004000801015944040741c038111b200d2001c03c0b00d200040050325508140c07031680174034121600c11142c4040206405121810507030809070703c201c1d4481e40d2402101d00d4182c8ac0d082d40f80c5004003003907040005900020810500c10002d0341487e1812032982407803182c4400700c070030181060100030100300c401c0000c0c404504030380d914602c05e5200c4a81200c103647c4656115031000041c2c3d4842c6845034003610a100d09250380c2540340b00128101c1b90030650303240403601d864041e030000380e10000c403036190030b4001d04c414004142ca42044130300928103c0e000044280d0010000c0480381c882c80e11104025281110702000b1586 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 709800980 1250 709799730 709799743
    0x3032d1015020304090518100c052203020904050705010f090e0a020c03210106030b0f030703020f060c0d0921120f03090821011a0d15080d0f0809010e 66
    0x40d4114074804010361010807440e6028590003c40076600341402c0c883c0740c2212400300040b03003040c6000d03075240000400054094074403075207241d4000b590422101c6030414a907000d1403490314021492080040d41c980004051340025181642d29030800f5070104419038102000440220180c1080c030a0b85252a0000c8400300006115010b240d0700000c00020030203052040712030484c400c961020380d01c040c00c840b00020040074041c10300824a01000a1901d1500b4500210541c100a00400c0480e0070360b401c1c80754084503040d04640042051004c214240d07018040504115807560f01e80f000d051521038102c100704d402c0c4811201100929003030b00040380e0024110400100d15040190700d8a80c159012001040c001002403c20b20002c80d21203036040040203200c0c0800c0803045545d00036601c030241e0340c2c01c44001c00070000129100300031413400c01603203030030100000004920349680242e40305617803801e1031115100400040c00845951900d030740c01070402c0c1c1c0c04c5040f600003003140d103041405040c0e4824 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 709802230 1250 709800980 709800989
    0xa0f0b01020d0c1b171f020c1c14030903030712050405031608040f08061b0c030403030e010e0402070605060316060e01110a0606170f01050606040b070204060803032d10 74
    0x40744d641681a4a401c8012000e0003000c81309280d692159034400810303103419007102000309070202e00654052881040c0241c541e1000103a02500860700521056010248450301040910844030300d06500d41c0d0a29001e1032050024002450742c0f45002080246200a034600082c00e0034503007805d11010034000806c1d2100e501c060a048620301c4082e061060690107554094a00c281820001081d040c00c0840c0e0b150241c100340000361b000f02c0400c4910545c0d8001d003c1d2558265100780001c101003442a006005451418103115001205040c00b1505a0b4401c02d41034803210b0300c070024091941401c000004020240602102c181400c00750020441c440d5418000d04014071a101c0303200c0c11000307100ea43e0a4580c05002000003541e520f103a002c42d03c0b03146450300b0580c058010310300702442c0c040c020248200301c01026140ba280c2442c80450650700140803e80e006961113001080000d400c02c0114050f150009210400c0c125140d00b950300913080c040e5814420a1440600020b51800306854080c2c4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 709803480 1250 709802230 709802243
    0x307120f020a1209020409050d090303030e0c010f1404030c0306050601120603020604060518030708060402091f12031707081b040f030602070f051b041b02060105270a0f0b01020d0c 79
    0x2200365000040c090001140c0c023402c80d0084c03440c010007464015000030101d81c441d407820301a280d24602c000380c0ba1001080614040b80c00900b142c2400c5101d0403c0c403241c50b0601001a04007a103944a4040d000016001294407580c1d0704103011880d0b07004481d50f122810390f110144845411640800c089001c6c41c411102070120124200591003880100c0700b4142601138111401581d4990140e5a1405c043e0f5040c0c1c060800b00740480c4c0d1074501c0c006000304405c69012822200380c6440300c100d9407055a06019000c1100d81c0d050b40081c00c86039120326028203800d684074995420320841001c6000f401d00c110380000c0c2c800708070030040c5001d00700c0320134110b0f5044040182c0301d035104c1c10844e1485a113650000c0450180d8851290f00010780c15600100c110299004c100c0f150f041c01030940380d1290003200710050313070200004221034034054110415480196032100902030300d06c3c00c404081d060650300c24480c0383d100e42450305110198031541504e007900740f0003403100c1001100301525030a15200081c001c0d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 709804730 1250 709803480 709803491
    0x1b06090114090f04050901060f0b030403020d080403170f1008010902030c0904060603080f04180603050604150f0f0218150d0e030708071401060503010e100e0c060307120f020a12 78
    0x2c0c0d540e1a01200002c14040c0c010701c61303490103d00450007014140105004100100c0000c0380a003094401c0e40d11131503058000300004880c2000c1501d403188010070480401c03404400c42005000310702c054074019203010300343c100c05042c484005186c2d11b1017600900d07201e07850626220050380d40054050400311061f0b584031507985407810031002600c510380025012a00c0062480840300701d060040c4100c400c80100c000d9030240300026001592940d100180540d4042000310b00466040c142c08043c0310f1101c440003034020050800c1005440e4201060102103901241440104400501030b261881d03048800d00c01c108061105202e55000303c204840c011680ca0038100c4800f20200115080c42ea0030444494a0780028500320602d5400700d07400c036406500b001c0c1c00203030505050145140c8400500c000d400301640f04001c1d440104030112981803144641d581107030290319010000c43c004c000307541c4d481040040c403941c1030003603a2284603401c2d603032441000f541c0441648840c15290201100398013240 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 709805980 1250 709804730 709804747
    0x92b060b030c030f030304120c120e0f040c02210f0a0f030e07030f11190b18090709051924020c190801063203150106021b06090114 58
    0x1500140302c03280d54041c4100039140e410f1140000203107120314402c0d5034902d02a41d10003000c4454411034140185111104048090164054480b09070024005000003000642c100000340503103c4900082c0d01503042107d1015143d2600980ca60030601580c0c1d00c20320b020b0740751401c0d035050320501d4280810082c0600f0f00d4010240300343c000e09940400102224262912803e0510018440203400c803241882c0c200a80170ba81400d41202058980048250740510315140d0744107283c0d400011118018110030f591141161b81d1002c03060301600581e6103841c1454289404d1106024504402c62104600028108003400d040c03c1035030700504101030841c4407520440300591a0025a90085500c442c03000340b04607251030002140e10403036042c03100a1010760b541c0d0104111044e018091004528002960303116440341c0e40210110444015040702c50f0007100c104041911803081c1c2008005030420025581d481007083c00c16281800200c0d0110b181c4140320002a018a910b80071040e064280030a4180 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 709807230 1250 709805980 709805983
    0x1b0908010209130b18010305010b0a08010c080a1109030f010506120a0c0b0703120c082401020a06230a1406010e010c03200a0501020d0608030f0f0c1908092b060b03 72
    0x5c484c0d502d40304074240700d51712858003a000e84852201caa000741c10070308000840003030500035040d8500070385c1c81c0c550b01c036221040c124016100c0c0c40c001004601c2e003005510115202080b6103140c0f0001e240c00020a41000400c2044000351201d00742da180d07101540f040701065070447c9000071541600601030703a50401c0d24058911a80380c0e090300e0165803500705802e483d01d1300300c8120384c82806401606200454120300099481c020545043d00603800a003100740000e045500843c0b80d515100401c01a408003180c00c2e902e020310490b10000c0c2141c40e04050302c50b45030a940b003650020700c24200380038902c09400000f4244100c440000c2e04000c2040400018000c0d890405842c2561180030784541c2c103400d04059000c3d601c03c0c1c0400030464903102001400702408000d881c54a912000e60381d1900c4840d00b010b503100d40103050b034201176000c0c1040c0c24800300003505d040e040d2548100c0c40680c44000b181c04101000000307009100400400800341d8842e075070131500030903410f98003d0000605045090210b03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 709808480 1250 709807230 709807249
    0x10c0306080d0e03010f061710060b0f07020f0d05030d060506030f060613030b0711150c030408130f0e04140c032d07060302030907060c03050d1e1b0908010209130b 72
    0x1b180361914000c408200c00d601c1008845804181c0d6045512218071048410b084602d284692001d01d0014040664104080002004058002030443c828040d5403000152840344046044815a00004c2c041032264181d008601c01031400f103408a0071440d0090261140c0e950007008a40b02d00000559000a20703034045a0704050344c3c002c0d440c0c030941d24100c00040c0103240940720368860f40c4514a8103101441d41c1c1c0083c50301c241400b598407411625540e560224030f0b00050384510400b21915404110400c01400c0c840050100713108040c0a81402e003001030500002e0414202a0f400000d10103040340c40c0000d2084600c3c030b6684100c82c0045840a40020f072400c00812030306c160044400c0041c0d48c43c3c0c182c024600034803000b400d0340c000c16075817030042c1d69240c2e000750002c0105606000c00c1c980d00b021540090b07508100caa0b016048071030241010812683c2d025043c1401c0040f00313000701c8a1642c0301813410050140c500085240c200c11000150402041418204403192200404803480e00c40200f032 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 709809730 1250 709808480 709808501
    0x50a0f200106050312031b0c03071203020403060b0f010c020f270601020c0a03030e01080a0f090c03030914010503040b18030d0e0c2e090b0d0608010c0306080d0e0301 73
    0x1000300e00540408034064070481c481c0c0352103407056034003d4040d2000401142d0240d020107008524920007090400302070b0300410a5130007036003c140520000b107061340044801000c0d080ea4016036541c15441c002c02214405600c070350044c81e03843d07400101c070f0340c104c44c10035040d9404030350200411400750006080f443c60541c51041881520344602910480303ca4464002d0200f40c0070754111107000020300c1408070491101900080c010b05046895501a0b524640c024080380b5020818a0390001d07480141e6040c280e04039000e0601c00020028107520040c840b02a0505e903203c2e120106416000030a50300000c0d1000c0c101c03a0410f40450600c15010401480140340c0205030390b00c4c3e200318081c46001301580004030310f0500850080761034038602103441c0c25851034211605c08011541d003c40c03442c000c01c1d840f000414000804404503529400e0300107001d0744040040086405424019800c1c00d640c1a90115020f040c2440740030300c02c1503004a05400142034074030340162218000d400007070140034240d40 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 709810980 1250 709809730 709809767
    0xa030f06081203060f0f09010e100909050a03020d02010b010f1419180509160e03010b06040f03030e12070e07090f0b030403110604020f0d020609150405090a0c050a0f 73
    0x3454200d002d1080c2c082c6104907000c58460941c14111000d00c200030301c1003121980c1c010280720040c81001032800885030080c0b5031901c0307003000d251180000d00490305810015030307566204038002020958100404010320342d4a20092188000600020b445c001a2109030350611842095400600c0da01c0c1c016924101044950410b09003203400c0090a402d0b1103640044254801700c030045120700b400300070035004030100001c000c025001403c0c216022040021002e51554030388402031200d990705409071014044c0700c035000d071000d443c626000c0c2c4222051010207015400c64242c98503c030783c000c914101224281c8607845035603a00c039031044810030f0058103c400607003603030715000c1510303102c0d0000346114903c6a01d07564020b8403807a200d599968011200254491510390b00c000315070421030713400400288064a0079050407140000102e4091020014a01700390001c2410411450720500140d08a030b80000c0400c40d1480c2d289004105208900481080c40814507200e241131b80319a04103100b061841c0b5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 709812230 1250 709810980 709810993
    0x812090d080a090f17060c0d0f0908090301230103081b070f090f0504112437020a061d010e1c0e09040f0302030f0d091b0602030a030f0608 61
    0x94050443d1440e400740c000940c50340e020106411100d421801400442c0800804060343d4080c0300704015442a0b0300f1044054130303000741049000940c011000d41600c030300451625040080b0074036084030141110240042c41c038020110030f26205520513070550b904100816510550a0000303031521040700d007d415103100b425800034107042c51501c0d14056274903c200900c080b084100700c1130159081a503025111450a10401030203180003049512015404201e803640c4895106440209802030342c2e02040c40d002605128039584503007070005042c0002c442c3d84071886140250000d40c0e810060f180104502c0e90b031800407400d40b50381c08440d00020800030003032000c20711a40c8150b440c0c0c942500340445440c0c00c0b01c5d20a010b18040e410310880030401601c000a195100d40718204486000c5001741d06602080002850006030a00140320880c4130312004a0107000610f4101100c401c04605800d03020415401840400e80c00b1003156500300c034030301c0c0205a000803580040c00620844d8441e480c28459034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 709813480 1250 709812230 709812247
    0x30a020d0f0501050a0b01051b2805010e06070507080a200a03080708010506070b100b2215050a0f02120c070608060a0302010f12060b160b060a0812090d08 68
    0x26040310700710911910091010380ca500c0300d21016030740341546940c0415428400da500c18940f400fa40c03040c55200d141180c000c2000d080350070f801c0348094018403901310300344060350051150900034400045107940090002d45881d14000300207025041004041010024250b082c0390300c00e00c110040002c80c0b408034541d000038a1141a600d421080302100451035500c0041d10540c09240e60f039040f00c0010b000d00c0e1402e60bd40ea51040135140007403040010078000300010456a100001070910303482d904401e804900000441d00c401401280e1080644910641002a81c55849402d0b501030f92501e05100c5242d0048850503401c049a8020802d6035290110b0b40b8028400b0000c1c5902c100c9010384c0380d070300715a25a20140040b0841038000607000c41c060003a4640418414401c540c030300420060700041083e101d00d840303205580111081a01e00d8917040c02c0724140945000910b403c200101c07018220380d0f00d409040e540f41e403502042684d8484001c101800c140d19041502c3d07072040d074072815280d81e41030031 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 709814730 1250 709813480 709813493
    0xd060204051815011404300f03080112020a14030307200406170304150c05030d050402040c1e2102031e0108070305030d0c0e06130509060d0b0105060702030a020d 71
    0x311200000c1c030002e140c4007802c40d4090250080c000c01d807141080c5c0b0301030406440501f044101d010042d100c8034582d6402e01c6008413202e5500d180c0e4816007030f465581c0045e007002400e400041e088050700c8488001d104005070348008100c02142d82c0200641c1840b03130820000303411402415006000850215000381400a021003403542e05041202e00700705c0e8646075030080255115680703807041e85900802090102c00c0080f240300c484505103142018a0364495a6518207580200030058034850300c3d40184011442c05000d070034140c1d0020720700322148440090420844011440c1d42c6004c0c404480c0f00303900c4150a4400c02c0310300310700381102599131b420881c5101c0c00c925070441d5504000354a08001080109000c039a150440307400c00000e504111302403d01c40001e002d20100e041c10b010452000740340c4d03030300d450005e4500603001d00000e110141c41c0c1024400100c81c0180f074988140c50018260001801e4125900e06503001500d4007034407445144042481c0c04584035004e940000050490f0f02008803 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 709815980 1250 709814730 709814779
    0x90606030618081602030705030d02060702100b0f0d060b1e15070f0b1f0303120f020406090e0c07060608030304030e041b08042f15030c090d06020405 66
    0x11a0004100c1401c40540c42c00e211441e101000b003003d2004c200b03c40310200595034040c8018002410369400d1a40e4800003490000000c1070030016803c84410069000d030180404035910000c0c800c21710031584110700050242501555440c402d41c10070581c2d00612142c0e910442c4908400f4200490801c819484080d585808103681842181e00d80404c1d00410201b0040d507549503071051250b84850342c01c0d1758042c2c207904010066011f8048494580101c1c00702c0b0066000114025160341c030903042020300003425510210645005c00303004010411100340c0c807440b0300c011290303030241c0e85401da100e0b1540c40c8403c2c844ca8001504407400c01030b0125141318040000c50150b4402e407201c05080c40c0d680f00b880182d4042040652040207111031100707d44d8000d070032442e4004c0c40362080c800e40c0c09400e0003030b0010240c81c501c003a24410070f01911000504080c01c208a09500d1402000d041d442c0107540e4503664443c05146030300076455100c6040c00c101e9182c05545c01350031b008000c4902c02d00411340007000d210 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 709817230 1250 709815980 709815983
    0x207030204150303200c030a0b070e0a0b040603020906070c0308031e091506121e100203040b0105061606020c0303150402091f09030501060e010f1509050103090c0909060603 76
    0xe1a080103856844031040c1e100c4101c0c4c2d815103c20405100c003004104150750744800703500c0d07140200c8031043c006076028840c40b02600c2c030400100c41070f4202000020281181c103a915409100798000501c100d606c1c180a031401c4900f41e107009a40c94800c0302c0441c2c06809011070040051600903030100802900740301461080f10315030000031441e81081d02003c034180c016260210240c000702200262b0070f04100005a0184000c2c01d1801c14017001d400d020704c1d0090300d000304450340000050b01c0c4442c0f078003480360b8001c503043d1110541c1503043c01d85460500410620969120740c1001030324075664803202e1030070000590810030440d00c1d00c0100c2140c40c0c13a94070460300b03078921100e8228104032a25082c4240c440580d40900032029031650305034100001b200300242241405440180040002c100740a480080d00f1910072005495140c28810007504c0c0309c03604068000c8011a00328900c1c55841400300088030f00919011911120300e051850001650b80c2041030500d051143d07076070a2110381d030030880817207 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 709818480 1250 709817230 709817239
    0x1b07050307031803034803080601030b210f060c04080706110a060b0f100c0b0703050714030403030603140105040507210206033705160f2d02070302 65
    0x54018885200300c1032000e000040202c1c0c43c0101501d01006040c8405044821841c6c00c1207180c0c045100c2c07060105030004c1c101c001012a0300d81001010341c00051035030051401c0c2800e00140041800180811225910005c0030000c03100a030030003000104904008056034500307881e0706081442e0340c0120360b446401040128401c00e00000380e101d10076107000c001240507a001c1c00c0e40603420750f0395402401a0701001503115500200c442e4070f83c2d0710144c5240d5210401d07140d10081c045549001400424002c001c4c7c014145020100030781a50400c05031003a107130203805a41d550741c0d1249403e038003d01c1e0a42001c0c0c0400c00380d055481d0082070541c8014001c5019208441c260780c0d642e000d07000400c0140c0881e460217003c0301c11090040c18440080c54100c00c5041110700e610304070707174100c407180b02d02d000038440c0c10000c0c2242000841c04501c20b05400115828110300b0414613507101034001d032860700d0103501700704c004d1010712425440e10051100c1d031100000015000044003900941d030318010301007a8403a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 709819730 1250 709818480 709818497
    0x90304030609080c070e06090c1813020705010617210f1306080906010b18010909361110030e0601060e010f03060513020a09081203150105090310051b0705030703 71
    0x110100c3c2e03600d551007110010180f89003649c1d00484c4951a420511450340088d9003881015407a5564081c1c15051f031031502801611034804d801c119080d580320758005aa4098180c4a003a03000c0317408212440d80641100b080c0402614080303010065218010010005400100c1c5040c0c2c01c6041c400164120f40c459a02c201e600d8651888507030302e5a5082c0b10f05007203c80200424100d4005a46901c0e210000504000044565825045064034802601d216524043c0d202001c03540c4000450243c00c8214040e805400101c255910201e00c404186007600c0760089040310503840d8443d421140c52104481c00707036a1b15503551400075008900183c0b00501081440c00420625886441000110b800c02005801c416444441c424000e42c00204414100000d0510115403488100150628112428900303a171b00c0c58045050600301c1e2543c07000b181041010040720b645a0750002d2410740e00e5181200c001110b48030411034240c003500703400c403504c922880840c0394420302070040043c01140340261030302103a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 709820980 1250 709819730 709819739
    0xa0b070c140324060a0e040b07020124030204180f0609050606040b150a030603200a1226090d05031b010615030e0705061801111f0203090304030609080c07 68
    0x11110390034100c10090924001c0302c16030500038000d540c0c1c0c000d000502001c5c0100c1e11b540c84071101100849084e02c1c035503e004103214040c0e0703091150341d58504c0c1003085444580210b0200d01502007952001a2050341c40e41030b41400141001035107042d40740c0c0541d140c002c0c6160351902601402d40410141c545000c1c10002a905083c14010590034184c0102400400307003041514614582121200c1400c01d40d940c0804000900c450600422006040c0e4014500f800c658041003020700702ca4109003030402d03080502d900011500d50000181e1b400030003a041151142d40d0054840d400780c0d1400d0342c0d200c041d0090010500401000820414001d42021250000d03251449402d940d88d600c651a031410480000030b4100e8881d600c003660282c0c82d04141c070070b0031f41c0d5080003c46e5500204000e10f8801e040542c0100107603001840100409031940103000c03e030880300e9803500d0300d81c2070540d180c800d1600080028460041841214041d41d07101008004c1011681410151034200600208280c41090f00c00f08 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 709822230 1250 709820980 709820983
    0x601270207030224090a170702190e01080a2111061018060e040b0702100510060807092106090609030309140c060f09010e0a061d12070308090a0b070c1403 68
    0x284545c5004004041c480525030707030701c008862030004a5242140612401c0016600d0014480300c0314941c5180304451410301d409036407410f0042c0c3c0308401300c0e440450300310001100111814080d00ba0242020740d1020b82c0c0600f030300c00800d0030a0b80c20032805034030100070540d80c500e0203100c00d480c14002c200d41c0c01c91014400d54112002c41c010b40d8420030440001078006800390261035440812403046d600312101030a8a041683c9050b5481c2c4001800c20b1350501030158441d0303081d81d00c03c00c90700d40740d901540340c05800141c0064000b0305031034690900c1c80100c00c0c400c00d6000300c103800358405010000c800072400c008000f06558002100d403280341c1c40d44100c0d40c0e00002441c1035000d000929181c81d000c02441c00d104680c0c01820381a06100704c103130120b10342c0c1d41c683c03250200030403194581c003114032650004640c000010706030b0070748186800002000a0000002c2c010256680a081070f03650b034481d44002070328803040e944041003480300068003000300400344603440300701c038401210740500c4100d1a0405 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 709823480 1250 709822230 709822303
    0x106050316050c0312060117070207151b02010e03071e081207080409021b010f0506010816080402061806070f0b06010801050f0411040b070302010204030512070506012702070302 78
    0xc0b10f00740d00512020725280016003059170000f03014106039006540416a544072014225411400358218000404c4100000103001c01407041524080101e0700b450301030b500510b400503c002e41003000010300d03000c03252401c00003207011309510001c402d44d00407803a0010040400600581c121f40c003450200424080210003955180d0b43e00c038080d14149401d19080c5070003500001c00e2050406402e050b01c102c3c0d00b8081c8a0740b4014824a0380103c0d040c42c2030300002d004101c025101e1012014652200c034001035100e18040d400641c1103c0d204d548070040c0103003980e00854004125800600080d0940400001e11035051603244241400d50f080d81e2184015078081130244116504802d0f0720120100d180340990004598551007011107003003546070b001c1c041c81904110400c41c050707235000800340300f4484108691040c40d0f41030000246071146075500d541d220b1b5810300c9220b250381c0010040c1c070426070110034a0030611007485411502e403801800c000356a000443c000c200750b40d00303600c03031490000c8104018 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 709824730 1250 709823480 709823497
    0x60105012105280b240313050109060c0f081807061808060712111e090432010906140d0c2715030309140105040504111215010c0227010605031605 64
    0x70b0605558443c0c4247c0e00d05001920201e40e039540c0c440c40107000542d00d00c02d91448021590380d10480001c42d90002c1e052a1000e802003414072403012031802d032208000b03090300540350680303000c0800c0310690080c9101c1c1040d58021441d01d000718010026000e6000d83e10081011400505000e03a400c4122641d10f40d200e901c04040d545008500d0144d440300342d03a4001c24030460060000641466460004901e203042c3c4050703403024289001000074000760361041e20b40581000b110400116242c40c1c00e180c3e10b4050b00720014001c9082c2102d4405000340a0140c03001003581481b0b10203aa03440594070380100801c002414031035460401c0581c0084106000c1e4015654991503000306203051103808540e141c46c2c0180c480c1008810040420251500d00403160201503c00352039468600752500300340c5142000707161524034189031070b030311116a03400384020600c282c042e01e0307028640c0f00d030340a00380c92100e4075a2440342c0a503441d0000070303034103900000641c030880e0322040e0066804d01d4000216564403030401e0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 709825980 1250 709824730 709824799
    0x40807240e0f0d1a010b0a02150c09040b0d080301030f0c0e040302061801110c07080d02030a051903020d1503030f0507020607060509010605130905060105012105280b 73
    0x2005074190400c0804511814016402d0400034485058036411380b802c00d0b005010b45c40004100f00c2441501003010850001c1004d0b50141549450740e00011240103540c00188a40e485042e40041c1d51a0049500041d54004040036a00d60310303820080c1d0484c199501c2291b650180c5000004c00d0f50602d00201d0050750b059001e060744e52a4801091640041c101c03840e0825540e0328241c26001c10040300910000d444940076100d4a881e080801c2d0070440c2c64803000e41076400c1003000403d2a80c2c800d0880d0444000140d400d52880c50b440d07001c4009020712425070440500d40ba484401640e5034a071860100c82c840e503030700d10340280000001c8030715006000000350840000d005980010b40c164100540c0150900000169503a594000842502c0c094130901c00c0165030703c101400f407040502c8840d01504003801d0803266164112604040062010340b180c840d169110701281d0b05542e00d549090010b000380c98404100b00c2c00300451b4004025071180180301c1d40f680900c84486000c050310b030783d189800440 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 709827230 1250 709825980 709825999
    0x41109132702130b040b0a0806090709201309050a0207020a080c0d080c0a08070b19050411010507020a0b1c050a0b0d0b070c0b0c0a030c020a080915040807240e 70
    0x210b20001303008520241544113407940c0da000029220124410b000780030030b5004140a042a00340c01e814183c16230800e416940c2414840f1001c2030040410905080140e21481e543d130140404144840140780c0001100c2c07800c01d0203100380b0300310640103401618000c80b035081c10150386100701c958a842c2c05082c2500542c0c0b00801305c021443c12405003c0549051098ce0b800c1e101a03941e0020039444250100d4607480c081f0144040544118440305100700c0c075000800803800e26444005180d88c0740007600c2e04202c000111303030045440d4030031400c006001c4d200314907458204c410124101c005001012401c0503282400141c030a00003405903090340340b40130308401d84c800025145c0941c2c0440c02400c000c00d000600c05640001296501c1481c1f08492204c6520b1316040c0a00004080e140101350100466000a05079400304141004071481602c0440c2c82e0600801c80c10140c801c43d000301d13400b00440d0301441d00d0020392035101780d80e071510f6000105001c80e80c5001c00c0209032462003540c2006904202040b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 709828480 1250 709827230 709827259
    0x11a100c02300d0e011704080d0c030f24030b0711060a0f0e03070203060a0b010c06091202010b0a0e0411040b0301090c060f02120306041109132702 65
    0x14060030441a0000d44800b00c29089400c0e0682c10107000c000c5000b25528074072512041807010f00c041c90b007030070483c900342c0100100d020000303110740c81803ca008404122500410200301c0305030201c8602d0001d1b9a0203100c00024180050000d106800341880040d04244240000303040c0060b0f40d220584149a10801c65411178994101c800c030010081c00500806816552230b14604000d242d1044083d042e022a50305205824801540d444a417244680e43c014041b0300011f03a0080b80e8158462001d80e400643c2044480040701c48610400b0007800141c0703001e00c48818041039a9180c0c0482c4020707002400380701040414008248034034802c07000140000340108001441400225404000003070001c1034410f09200000c0c03c40e0903020301182d00702a251410003510360032940a0300d50340218005481c541034012841070140c48010140352045135140511403900500c901a0742111001600001ca00c00c520701804005100400b1046484541105181101400781c1014603500781d002c2c190307034007003c0300 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 709829730 1250 709828480 709828487
    0x200f0f070612022209020301030c1203020c09071e0818030901050d050a090c08010914010507230706020f030f0c04050607120e191404020405100c141608011a10 70
    0x46480c0021603900c4202c8603042d0720125140c0805800040345c0140c3d29403441c070744106400b0303071a44021264902c10024001081d004200050383c450141c62003111950b40e0b100488190121101d15504181c901c003881c0c104c241d0182c00b182c8601403000c02203401c0c0e4483c1d282207680340201c03440346001410412000e0300030309658102d246c0140309240f0200e41308445039200d8028107410b80007079049a540e054044103020b46080e4481303d61a50000070046400d000d08010811500303100b5047e0645d040701524620703d02a481207a40d4642c110b00c04644607440e04800325803643c02503544841d01d070032040c0800c1c40c9041c09022141200c0005280c0c0345031102543d0303000031840d03811501100f0f000398508280c4541d16183c2030307125040c4806e003003030003201e0409010782c0c0b80c4040b054000703001340d10500c4140b149403500b8413010072160b40ca08040052000610b42650300240f49140d1140c10702a003002407e00b2501d401c0440242c0b058640240684000058043c40881d1138009c16503002204140741e0090600 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 709830980 1250 709829730 709829737
    0x1c0221031305072102010e19090911040e01020702031209210316140d0e0604141c030c0b0f160305070306051503010603050f0108070303050901200f0f07061202 70
    0x11840550341c02990310034201010800140144c652450f04c2d001c0c0c0e00c01c540e0700c001280c41c0408101d9405144a0301c00e80c0d04e400d0f401e83d6000c2e0341800c9656002d00d20174000343c00c01910345400b005105228040c01010103601030b400280c8101c0c081d20542250501c0c034010300f000d99640031000f82a08541101c1030850510100f00c210344003105020410110b90403007640d4004101e441d008010b078a16040c14002c581e4030b0007580d107810104100b600d00030114170343e640c001150700320303444070b1100781160380408001030714120f0038104035144d29807818506041542040d4201d1000d4060019030203a03654140c000c400c4900120b96603038400c1000c4040c0c0030014041c1c1c1c040d03900183c00d4500024800e840f20702003114220100009100d06101000400065506010349948541e1170b10100883d945081502a43c800582c0002000d000010414101c140d100302102e400c0c1d203514041110500d045401072030b460b0104040c040c2c1e07650045c05e0701c190f540701001a15400315a000d0703441603d00200400b800b0020341 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 709832230 1250 709830980 709830983
    0x90c060d061517060303041a180904061401050105070201050307031e020a030e0c103501090e2a0904020d0c0b0a17040f0b040c03051c02210313 63
    0x654510002c54008204107141c90054070310345032031102914407034059440b075100409051280d4401c00081c800035580200304994090701003440c07900ea20103d0b001c941c56400035800c9070381101601c2c007004103100342500a50038008240c011000306980b42c0b00111560301c2141e001034041082080840c07207981c4681c1c40180c550300c16481d1500009800e100050603640600030000010752652800394400806100e40b42196100b15a90784080004110240910049180c1e440340c21030f03100c3c000d02071364040c0451074504d112210030810311503031500a0840105460503031303900342d88a0322188607110701c04941125010480305448101d103524540c20030041010090080382c000082d6485100011222481000940700054015442d40c01c1c1d00c900401c0d448184e04038600081816041c1310214200401300b0b0f141681101480c0e01c9035032142010f140544265100070298400c40c0c03501c2408141064912021460607400d444c100300700d02824500c4004001900100f03141c042001c41c00800343c0d54800c140d0702c0e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 709833480 1250 709832230 709832257
    0xb07060608030a030b1539011409010c0309020616080708070f0302150c0f030705090915040b06030c03060126070801360c020708031b15090c06 63
    0x8903201d207552030840d0480708603080440d888821010051800840c04001c06121440c0c40e801d100240380441201001c085070210702d03001d0041d049140198030344140d10030341c85060003030003010b60320a44101030101c11103c0e60210b5103099117079844c2c07600c03e0140c001001c1d00100210b0900101a0403212500382c0840b080340d220804106c8080042c441d1400760a06c140640a001c841e00340600b0041d0401c0380e01d203440358684072408204034040c4403100986810713450f00848582c9a030345041065450b88203c1e004541e1000c89031003004100c0c500311152024154003904c06004e42c0992a0502025020545881e07144810501c0012015441001c0158035204803070143c000040340c8200240c9802415210000018002e00c01400301050f001c90510000c100c0200c0c04103020b034074150060a0000c6040c500030328540394110008002c1c0b00b080048041c10310300081c2c03517840b00240c2718408105684008200c0c20b001d03405200501d0950b0b03c5045100300295009448003c8600c401c00410790700a000c0d20440b13 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 709834730 1250 709833480 709833491
    0xf06010906030c0509041104060f0f050a032c010e010b03070f18090c03050a0b221403040b0d0603051501030503030403260a02120609150402070c090e0d090806100b0706 74
    0x290346d50740184215041c4083c200c0741d2359400c190004003024107203080c04052044501c0c440000c181d00504130768540340b8514002a281c0c8440c0040004803040b03403503084001500369106022144190b2151103d100078038002c003c0f200c190014176403200035502c1810310048440000300280c0c2d4016200c0c10720202d0a402c00900904507986852400d00a138005403160fa1007640302b070003001011207009070490341c1c0b501d500c0d4500c0c1c41014a0900c41c5042c0800412940401160b81d0b12598100107480191440070007981d16241006640303401840c0b24441528503106d00c028140901881580305030590750410b02441c81d55032551019240c06035940c40c082983c02e5410f20010b010740342094154040d00d204030300540d1350848024001c804810107400c0512402034503040c800c01c854540b000c0301e05810140c4016031140d1180c10201e000969580c06204038070700b456a0544003034004560b114825455071202c6003407644a00c001c0365108011030300c1e4408028810024081c401e04103005d001c0692068901264 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 709835980 1250 709834730 709834747
    0xe0604020f070312061e03060b1809010903090b04060807050a090803160311011e0b1c030e03060a0203010605070f080c1f0606170610020f070e0a050f06010906030c05 73
    0x1d41d80607800540000340d42d840525514203441c0591750080c00ca21085c14400e40000c41d49081d00403440c4002031801ba60755241118a407030352075059410460811080c1c510385400b804041c083c10360389108400090310800c000c50a11800c0c01aa02624459034600013256590b030f100350f480f9440f01180c001072100034440000c903400100010110f44054080c0c14500303081d1498080e150942c60001810307182d040c40c40f50141050404d41c10a0000001a00812003000c41c2021407450003c00b001d02c1d4601d2130042504d402c2c55003100c01441ca0100a400b01d40d219036510b601241280020b00039140041d5041040030302107102480300102281c02400114a801d42c2891200d02d420507800808668002a0b0068181400d061151400504540c1060182103843d1248141ca00c01d0041066100d4411906030340300e480d02c2007000c5506200c5c650100c0300142d8485250921003c4126041c40e5800d090900154401c0300d10b40a190040c5410f8650040683c1800400c0e0050114a01c2000812209000401 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 709837230 1250 709835980 709836007
    0xf0106080c090a0902030d180b0409090b0603071a03041a070906031104050102060609040f021806032e410709050d1b1502060702060709050a0e060402 66
    0x10100c0354001c01c1c0407608802031200000000301642001841c1002c03d5000d80c5012034003062004940c545407003071228403001040c0303520032500000781c0c9590108021640038042e0f800650380c180104000049580c6807800c1613601ca04d54001d010300003001402c0c010008121101070f6070040c0c8518164a103040140e40c940e0b101101c119217140008490350410000c50743c261103668913020002e1002841c1c6810000080c1d6125405803d05005219200008051098035030700c91544641c010080c0c180340c1071040c0b0034010b491064072040d10a004500c1e50821510180e2001401e5814081030380e00812904d0110f90003d181d100c0c00c2459031520000c03000070400f00310200400000e003d03030850050b100709043c1100080e00052644051080c07a21041c00560348440c2c05419075540b0414101384800c0d41407145031000c0c0d50b544956138108038040c95040700c0c0d8000c104103200303444640c02c452180c0c1d20150119540d000c41e01c1410b4020b0300c40e410a001000300105140d90002000d4001340c5043e281c444d241 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 709838480 1250 709837230 709837241
    0x1505032205011a03030a0e0f150f030f010f060e090405160803070b0c1e0708070b07030e010f1103150301140103080304030908010e19031206180b040912110f01 70
    0x480d210b0b5960111444a590000c00c00107020b14190300450900d00091310152524072045400f40c820040d50003260425960141c0e00c002d0141d0403000243c03504c0200e0344540180d00f0546560316003103d280c001142c0cac1402c1078403440440c0d0076a680c48400d81d1460043c4100540080c10a4940e8003482c01e440c0210160b42c1c0404004040300d0004580e243c5503400c214444440290214241c15010001c07584c40c820140b03036406a0f284004890ba83d03030703401403400c04464852000300602d406510300810407801e0309a880880c500d00d4032002401002c0741c9a440404481441134416103070b00090000c229400d101e240381d1713940d502c1c010340002a0804c000c142e0304a6604244d200b12011800001008101944204d00c94028030900000b8056002e40002840d22450900f042c20039812244d00c100c0c06252050341c1124001001c05c1d0f081150071788849090004204801000d41400d090000415090a29205080d43e403070300305450242080100100319072840c00342c248451948143d8040c0111040203124a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 709839730 1250 709838480 709838483
    0x6020f0a0f080c1f1406090103020f210a0201030e01050f010603180206030a15061e080a06381810050c15070306050a051011070b072a15050322 63
    0x1079688950828405010342e00000ca01c191741900c0035080c020036490b0b450080703040d00c1e811589608210076043c00f045030b56000c942d4080c5554050003c28001c00d001288002d2414000ea03414083ca24001c080a400c1e5681994003030060300302c0000400c07445210307500c172034144c40c00d82c2d141c240c80c1090fa0700051055001a91349203c420390711540101e031020b0b4020040f0041c029410035072940340d0a40c1c12201c00c010b0102c1020b061107184000207040010641c0250040c0100d40e503c054900029503407a041c03400c810030300300f016903040030034565040200b02c1a1007414600040901c1c0500d004400d000c11140985000c0050180600110300d451b4800d0040302070301c40000320b66100601c0e01c104010251a401e502080c00340f440c00100340110b813120145c000003c031540c2444c0701c1100d08000307001c0ca0b2104581c0300700c81e00980428504100262003040118810440c440d10b104044c0464a00e1403030401445a10300d2140c0c14011004c0c680d014038007540e80100c0c42e03894a4048c1000c0040340c1d000f42c4560b0710 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 709840980 1250 709839730 709839763
    0x20112060308030f100501120207030207030c06050c0d090b070206090310090f0b010b0a0e04090c030b011205010e060c1902070f0e0a1a030c1e0307091506020f0a0f080c 74
    0x200021007504c20400365100510008004026180000290071810406028404603400103100800d01d4020002040115404203201c0200c640c0c40b13000500b03503000211045107501824100d684190302c200746410a55007120610382ca0301d00d540e800c00c415640702c011050f42501400d0f40032568010540f04564200c0e001c1d964943c1105054030b00342c160350741c0507000465410010308c15051220391000900700d445000b42d50000e4128924203200c040c00c1220307030008000820b010008604e002c000c092485c03106203c1c030003e000101002c42c0c06500e48030b00300c070300201980342401283d212150b00c0000d4080300e546030040e00c2e0f07180d0b103c02c030f03031401543c00b9000b2101d07941540d0706001100145202d8020385909001990f0300d403c0ca102d0000b074032001c1e412105840b4a41a04001c0703158201c0e140c1803680142c0080464003155603a003016400b602c921903284000080e814800200c950021810241e4051a00054228080d442e9a180901d81000d041921580024416040001d0f03040108601d40c0b80780c2e00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 709842230 1250 709840980 709840987
    0x5101106070e0a0b0c1005090109170c010f060e07050f0f0d02120703050f06151c090302150405030a14040b180316031a0a152d080309010c020112060308 67
    0x8140100c07a00c844e803100c001c0240401c100072108001059802c40b030340c43d03603e012030316482c4c00b01c0381809030142040141002a60000401d1a030f02e04400900743c0c01c1601000307000c101684071555040701c1c043c0c4102900c0080b504001800d0911560091082505c250001801c00f42c0c0704030006007681003503031820801076000603881d500350040030003c0c0d070107422854203100524000c1b403042c155000280c0300321301464459480d01d034041c61480a5881440900c21070400240c0c135450160003500074058140c1c01b40c05001410381c03100380c01004440c0301d00d401400071841c0c1116404106c8520300752032620482c2080c10702020940703200c0e1200428040030008540d540d5000104101070a018500990325240c2084500410000e0f12120003008110110403000149036511560100501100b00d03a1801514007001c020406205a920b264a0032500d030b15082036042c00800360f100c03401800c3c003c031082da500500c05040c0c19840b074032a400341684185840c8050601b00d80110003a60101d8208480c9e01c00c010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 709843480 1250 709842230 709842257
    0xe010b0405090a0b01020309100e0613031a090a0f0c03080c0d080c21040203101d010c0f090918021003060e0c0f0403080f0f040603061701150510110607 67
    0x1001100d411002929042001588004c0080d60b01d11452085038010b00d05083c18141c0c50f8000c5070760000403080603241d03650702c400d5503100c004040760501080303d407006214040c2c000c4810071110184160180001000f681c8030306d807245580510751000c01c4915910340341c0040002259040a0300310482e17150000c12480c0c5000d4405000407030014640300c0802c81c01d1003c01500c1d0a07a105100e60040b40c01d80c10703d40744d141c0b030004c242000500004d109000e400e00f20360b01050019680342c11500d54074a802008003445091048465400b82003210340000e940401c00d11241c290740c0c0c80404003003440c2003828031460b440e9010860300710103854500d02003a42d0702e408019840001090aa102501400300e51812088ae21400c600d4025408040c040c2c3c00d0118809403490341c0d0008480c4035401c510003482c0c5403503484070002c0c040d110740d0003031980d004640c409403a60300e00140202c0c40380c1c1004003000041d15041c0428032203d080780000c0d91041001e2182c035444030384424414030f03009048503a100254560034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 709844730 1250 709843480 709843489
    0x81e0d0e0d080f060103020705010605060a020321010e010b0c01020c150703110403021813080d0506011704170a0509091302010906020d0203030112080c030c060103140106080c060a03060e010b0405 86
    0x210500542031088000410901c10040303001680e10160901b00161218000d00301240140a01c0d00450781103c000a807051841d50004058101c00700602d020038084040d41c2c50000b070418081c0706101995a45000522054680c80007811070390040c0c2c4001802c0024030b6844a00c8c0400c1e4124181001040380240305060b5414010440c00a4a03c911a8034161171903012400d0841e101e0304c890540c00080d00072403900850f10b0b10800d02540c120965540300c21041c00d210700100030503210346002c59400000c001c500484400395600c80e41c0c0000d4184c1d40d000b81c0c0242e0140a81c05407448104114041180010035661408542c2c002c50341500300f44d9402c81148000340c00d108007074110300250b6001c2082c0c1d54005a00008803415a200a944014a0100b610740000035009080c0511800d010105411500041c0000c01c41e0403640a66241341d1407980c0842590f0807641c0500488a03190000e443c01256030900c04002c000c030003003620700020387c95501d900d80314a50780c0a8000189448000401f00301d189030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 709845980 1250 709844730 709844743
    0x90e07020f031605070816080c01111906021b010e010e01050f01150909020d0b0a150e0103150314061e0609070c0606091506090b0903030403081e0d0e 66
    0x5000802034500d40303088140d924000c030309000c03504001e03841030202044030912a00000341148412a112030110b1031803c801c032840f48c052030800d446840081e040307540c442d041185c1502505000740c60021680b06014031032a408560907202d69808016031030342510941200b5150300111400041c8403c0703520801d0742910043e00d0300250f16070406060250800705003091a0444409102c0701940c6240c0603815101d4500e9540018026071000c610751920380c1150b0800c10700c4001c221100c8001e1601d5221903039008503a64003007400502c400390f0910302e5500a900204480040502c00b40c6c455030f81c1c1c0d0721040b403a2420003031a141900300100b44400c46020031a41d268481c0f018900500070301d402c01c081003649000420034000c008490440400b80181580481c0162011071028821301080300b8140240c02c49600c03c00c8006600d0701da000603240c04000c02e40e000007000034059490b151850300d806200d50406405001900940009401740c482e4038002021070310782011002c00e140c540d00141505180 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 709847230 1250 709845980 709845991
    0xd0f0b060f22030206030f0a0b0d0b0609060307060914040f110a090b03010509040f06091406060316030c052713060b03010c08190905150402040501151209110d03090e 73
    0x1a402e5007440140d4030042070742c1c2d0102101d011034009641c0c15100001406c84c6002e055000080510403500b0711003030341d00d1284516015140401240c59440615545201d40e10516000480e103940611450303d6064060400c640001e2000c180122001d0030b403000c83c0e6900030500c10305000000c80040242c2c000b0500780062450450725070441d0325100110700360f01c4000700300804201d44035100304d08100080c1d1000201703e402444100804001c0c500503a50382200b610340c280b10707104858082c00d20080709400103094070350020360601068505030078042c207141c092100b00d40000c0900061401c942c03100c01217501c204014003549950724414144041260740140c40340f8066410316102810032500300130184d4200300142c00c0c40603891358642064005201406004101e4000c0701010a428040d040080740600e0080b6070820850f661510142141d20b1501c00c0780d004224074001d480f003a68a150300174a4494040e0303100298032b4082800140304c00000e06070403800707c3d140c540240700c01604004100d5111 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 709848480 1250 709847230 709847287
    0x20705121303030521040c050310092102340605040806040b0a06080d0e0310051b09010c0b0c0a02070515040513021201060f0e090c0d0f0b060f 63
    0x502099550141c0c07052501000c0c050000000d800c01c8802044807004201c038521780c1c040078240c1414900000701e90080e11810384a481400e85800004006100e184007442d40603031002d44040c00600703005182400146c080c0194003801c007010b0344c040d6407018000e0300007801448170755180385080011a20f4201e5a0440340420400303001c06d003d143d40c00200e454020ba080440c080207691040306070400b03080140c2000c4550b00441c2d19030041d05410a0180c10500000c03010341e0010703503031400034030115002100c80b103100500c00b145d0700c030151b07484600904945206262420300340419440e940740b8a4000e0340c200074a6140092194201507041c000301011300021101910441d80150b220400e9014600880e0700c81c03c410072003850200702c01d5048490f40c5070080c1d50081c1943e07442502910740c6402010030004502203a10003402442c000080c01d2107440300c034030f0035418190342c03401040003003004024020b0b80c6581d034000b404084d41c4180c090054005441416070742ca92010600c80c2e20028800c04e46e01ca070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 709849730 1250 709848480 709848487
    0x18150204031e12140304030e0f040216020f1f0f02010f05130b07020604150e010b0a1401080916030f332406030b0105040906090504060b0f132d02070512 67
    0x514012011682c201d501f40c03600d000d15030403540c009445c2110030f034046036200744001114030700a02040c9a00e00598001c903891101d100c4036005001ca00c08024888400f10308000c903034419454060a400448201640b00002d100d114240294080711816202e102c05044154540c0c401c01c1a81c0300035030b601400501c082e248504159131000020700381c048c0381001e03550f01e501c08511040350940c8400c441c003400404013540b442e5240c035240c4003044040d0280b0300189080300003031584000080d041944020580c50100c4c603074590b45802140303510461080b20503a05a0701c800030383d40c1d01c004500704000c000401e043e180070f01520b0303035108a580070051040d6410a6250b4034502c841040703815011101c6e14200030074240801c400482d1188180d4100324001c03031a100002c1101c1d6141c1d40030504c218881d034020008004202c080060000320001d1080d40503030448602c43c15441e541c0c00081c1c2c50b46102011803080c103441c28401d03203820740242110b06d600740d01045030000e100c010012150f4042d070180d0010314 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 709850980 1250 709849730 709849757
    0x108060a0623092215151401080408040305010921020a020906060f070c0b13051e210a0302010f0606080408030f07050f0d02070209060418150204031e12 67
    0x42508529921610420350400041c0113228031042203c0d100c00c000d20003418101d00c61030851407000c0104c031021071030391a14003285448200610039406503441e002621114140d61001120b420b14001c0088400c680c00380800130018a00340a07000c0c180b2b04c10f1041d05107440140c6038800f50304985402c15000c40d0302400019025840300d045035504468140c0e40d080e56202082c1c590700e468800ca950080900709417540004483d084d1030090f0110f0f10004130050b041d903699038100203045412074011442c0c410800307034140c0641b602072555058104100502c074000318a2800b8207060440700c140607005070b511000c10007100c104c2446801d01500703260a0401c40e5007803688a02815010042110381c0366102c00010606071b42c050419919441100b02000350317291500315488002e9040b440040340603924401c0810f20928150041400c0e00201c001da0182d0709100d41c90b11130031540c8061706c03051219401c20001c404110321040d003402045102c081b039043c01c0e003180f07040740d0844c00494a40301040303107030000c0d000c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 709852230 1250 709850980 709851029
    0xe07030b1c0b040503220602060109140601050a03320a05010f210605100321081317030403051b0303040b0601050918070f0f03050c0702190b030108060a06 68
    0x2081c15421080a500ba5925460000c1c598424140d06a2292005400f8642c00c03210f05404141610303516401e560780e90760796104500a580300d9202c0d00c40101c50709400624254800c00107440e41d141c0926021400c1c44c0e5401c0503514002020140b030610500c40d1002d5003c000075200d8840d00041054030421956240c0051444513058900072040c4540f5105a02c0c2c081104041260710b0f46600010204414240450101c0301b59500e880300311803021075581da54440d551044090300c00f52120362078000c1e0719500d0004000c01008520011141c0000c2e424803100103948240185d846288a5180c46684841f0049010508004c808219184d58000c204120016a1880b0301035004002070030041d440c0c8020070000b4201c003070701c44d4100c0c61200b000d00411282c16840021902688039649600c201d0700b4a100e000c8090307480440b04240b040c04100045001402e01c01d00c0a180800c0c242250301282c2c1c1ca80401d0282d540c02a4480b011b154001000d200812040d8800c1c00700030450680f01c9011452803c9902 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 709853480 1250 709852230 709852279
    0x51e1c031b091a13031506051201020a0c08090310050a05070e0616020103020d0e0114070914012f06040503180907081f0816080c0a080304030803100f0e07030b 70
    0x2080090001c64080700707003c490b4060102650b4486e00740f40303441040b0b031901c8005021600c200780c4903c009944100554030181300b101d2103810181e80b0380040c2005030f215030549074040d44500b074151060350404c1111243c0307882940d0007101303184000f0580f8140140010020380804100501c41d000410860300b00754021383c40c11040c01d9080c01c0250322030f519407401034003c0810032609c0d122075092840700d00d4580d500e541154859005502c1d05281c180e100c0c1c1c001140e1080460101e40854900f8098a0000e01500d001d101ca511041d804104010a680301c4107060240965086079113500204242043c548109000020303000103503006419880d103103c0003445250701401042000300c0b585800c4185056604081002d042000103e910480406c5442e54035807845103d0740410f030041065208141ca400845881200c48085c011402c00341591100465584060000f0710100b89941c00010700100c441e00301c6000307040304c11a03c0e406140000025051b1080614118030400c2c24840c00c0d1080c91a00818 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 709854730 1250 709853480 709853519
    0x110315070516080d02030901021c020a020706080406020415020313140f011d0306010b070c05030106240c020907080a0b090105031e0111030903070309060309051e1c031b09 75
    0x2006140c002da424243c010b0310929480c009214000010050701c1d02054004201e209804810301d003075861035685210881c0100d0710168010382110600700f128a00c2403504c13a0300280a050010310f42503a51000114441c6245495030158002103450b034540740845039600001c200c503950036600d120706000081c540390400113069040c40b03c013000c0d41059041d003504000040304064221400c83d615002002840d8106240403100c202c10400e01051508043c05450100d0b4034410922040405410410000380001c02c0d818003040502880c00001d40e6076584241e01407242c58455590034180782035810141c5074802c140b5406480f6101c010006a1000107141c440011000b104142048101c079540e4050300350f01503c400a8200803080c00240400400104040c0384645c640d48401c990360728054048c0e40d490302c00035100d40c0103400700c545202ca80000c181b000405400c15120941a000e80504403141c02d800384c0700010340d9a0a5000343c41502501e2105028141c2c103003000058034280c4091145445901c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 709855980 1250 709854730 709854757
    0x3020c10110114090d140307050309030d0c030c030513150c03110708040501300207020105040305191205040305031b0a080c0d020d2f0c0a031103150705 67
    0x30280c030031500c5200c040325022003050091100c0e900010318182d18031810307038080c4c0b85409120400300020303000300300c2101c0c04080081181d080d582c176994140c0e0690801040090a0702023040315a003280e44510980c4159015924002201050b803a4001c0440c1e0000344448284130402c483e000110351950003d41550314601e0f00450010380c0305a084028081c4049280b800c072078080b641808020a0a019100340c40c0c0a9850a61401c418100d11226543c82d902e00c110100c06118040c000e501980c00a19400b401070420a16059896880603e021080e4000c02080020f030103901d01002005022800311205d9440c7c464142030440d1034444d00c1e4442c1094441b016030748c04910036400c2e0300c1441401400d5402c206082e0b00c0d040322083c3c940c1c5440445d1400300060103038220707030b0a403640150345804c07800c03840200c0e178944000741060391080800820006c12080c444e400f0164403687d25403507040003652140500301c8071600c42c1002d0601d010a407511910740240310700d00700f0403807a42c400300b0b4980014580c2c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 709857230 1250 709855980 709855999
    0x40b03030919080f0c12061003110d020d211110090f0515070e0312040b0304030306181515020606010c0305131d060307050a2304230f010303020c 64
    0x880500301c0502d580c40003645020340c61444000010102d844140c441090300c0100300c4903603259505440300804c507505001c115074400d0501c04200184202003400c5000303401c0e40003ca10b15000a2040c8000032011035040400408142c4840030354511031950b40c10500300251001c90150380c0a44915015002801380c1341c0e103550040c00d019842c03000b8010550050107451410403000c810b6400c0d00007c5403001c2c041290303c40003011508002070300702150004000342c00e042604040c2134180c16800640305604040d180c160120710140c07100852240034034090030004682185515641c1812501d07842449003440c1d4070354023608690040ba0b450b41c0040709281c45a565056898280ca66002d8007422050b034030758800000c10f00e1001d00c5c03c1c080d030001c0284600441d82d91178108056441405015164004884070020028600c0d02810350010418680c0c8401d4a5560080071404450020070382011041c001c0c01101004200a01016041000c58050004d5581180c0303019680341c06440700f180c0242802c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 709858480 1250 709857230 709857259
    0x702030c1314100503060412050d06060302090109060305060a090e0a12020a0c080a020d06020a11031204061401030f0f0305090402030709060807050421050c1c060b040b030309 77
    0x90044240d1204014024256400030101400c028503000b1811a0b00c003049102042079240011400421954014010101983e455a88005012641d81c00105015090207200210b442501075140504040d0f0f40058480c0300b03034000102005416030205d801e0510b05802d00c41c1c244c503400c0d401010b1306e660b4940864201c0894140e07d01d88041b4200140c20480003140084a06a000c10440c1c4424001d94003080b6168580107195260800d0400081d03000285c100124001400c1d5000381403600000d06080022041c00390106055921070355140d800c100d569001c10040044170b12800d66004e403541e180c0c04856056945a4416118088000d0150140100c0c4201010300c590211025000040d005546030b003800340d005481d51000e0302a00d00414040710000740300f00e22403400d4a08407043d403048450030480343c180110240d20312140c140c1f0580078110359a00c0c19201d4807081000b8a4501d50400001207103400c1c40400c0b5800321019074461800e008103880b50355070010a4a522101c100c9030030301440c802 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 709859730 1250 709858480 709858483
    0x506010b0a0801090c02161d0c0f09010c2307091406181f0e0703060801020a05070633060f030614041a0a06030f140403210609020d060512061506070203 67
    0x302810b00410142d060700480d0038503882090301c44410760a21034500c8e51b1514503811220f40581d01030242e03a04018800203a1030f40c03280001a400c0d40c0208683c1c03c14600b00d4041c0410203048040041d4194041d074000c1120070114401d44a4032421410116660b090000000e010709003240603c0003030000c1a40801c8854214013410b00300e2004406d880946a590f5007032094002604072000070100c3d2070f00c40c0000f01001c1c12f00850b200184640e48041c42c04e01542e9505009005074144800b40d00044410480000241c04204600d011178038014404a03180039001014072050202581c1014107003101080f07a03200c088690440040201c0380894061820280e000399000302d0080706030f00107030b001c1d0002025031701036008404654005034140410b0080030208684d100064800030009034a6050280d442c1c0d45c0c40c001c240c011091070f540403885550302c1c200c8100760381100b040040d10316a80d04041000785080c080c100403548200010b881d9600d0700d0410007854010907800b1a00819001410900f1542c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 709860980 1250 709859730 709859743
    0x7030308011a0f0d0c08070c15020c0a0b090705100203190302090409020d030f0f0809030f03093408011a0609041503080405040e0601080d0c020f04090f0506010b0a0801090c02 77
    0x20b00b083c10340c032400000701a50103070840646403004204110042004d26110f00c0c81914142d8105144142e04040356400304001c0d4080d01c0360702824021400e80d9400135013071074145c80c040c0d40084001d2a426090004100c000141001401c055500c01c000c50b1000003001c80000c5402032881c01d00689030b10078030700464050050800d000f0f51100f0800030b070008054101003030300001c181d141e0b9502011f901441040e1643c03c0e040e10081983c0d8000e029818145a41100031a4070109010681e81c102c4005142004101484070015041604894070f42c1840000603014200820b4510004d100900303442545a984860b411165809000700044050040d1103580100000c102d264050080c1150b40c0c0c02c0c50001900035004441c4110b00f07001c80903900c40390000300541680c100340c2c09400c20782c480c0c000c181e824560310702d0300702c1c1c210040704007454203a5540d10032840d00d18001c03034890320983c001c0c1c5041820440305030070590640c0c1c800d0000d210140c0d44420014103480d00325200040780070041c0303002c1e40f5020 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 709862230 1250 709860980 709860997
    0x301030308040b073e01090503070b09070e04060906050c030f1512070806090c0d02031c030605041e0c030c171b040f150903080a12060302030316030e0307030308011a 73
    0x566005d400564800394854140b840812450001c18001803a011400c0e60800d44c0098050340c81401258003007151000300350b070000031030000c450318942c2c2c40242640c40a021241034600c2e40c2e4a00b0020144421070240503800440d4000e494514540110508030302c400180c444010300130301c24442c2c0340586030310426208028100f4110380d9829074071400d503580e800d01201d00d80ba0714002d44800c0390160401800004060782c1c0200600f04000342d0564000051144034501e104150711080000b6144d00c031803142c121b079080400708803c500c464051400081d0b4040070318050070189044660540254407400d060aa105008284021a08e4940500c21091240e4000c2103400b0000a0001800741c101c0324040210f0710000b20400c0000d082a809880554480c440905240130800032100700a00c2100488034200b507140000504a450750042031940d0403440c140c00210744401042403d154105000064401e02203000702030040c115603004010030018418203440c2c1c1d0741c07004e500c00500342000507281c140 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 709863480 1250 709862230 709862267
    0xf090b12011b110a020904120e1011061003083f160311030a051905070e040e01090218090a0512030708012102130209061308010b01050301030308040b07 67
    0x184010b00c1451414404104800081400c002d0054880c64000c07654420058005012040701e56903511805041c1c00040452000c01c081d10610440300d81d02c03043c40140080e003983d181c11801c0f2000300c0d810318120000d003101c00e800c0c0780054100b000500200803101c1e00030710030100c030900c10303159500940300c4810306000d1800c1078043d604100d01c00c40c6602c0450700c1000102d018084407444000305508403444100018140780d4100001110f0001e241c000e10381194624007071281600c40e01d80c40d00112030080d00c09100281004c80b400c03400f8903003030084890608010000b044910751a5002449214100181c140c015200b2000070302c01201c18460403003103d401c1802d40d11020012060700b607250b44101c81e01004606600c001081e0409420300180789140412088005400e0640800c003070041004103070003003560200140d0100d034849201400004203d84130581c0b0307290614560909484072152064100003043c401003020a521403015604141c104501e060030f9113035042c0886610a0080545490 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 709864730 1250 709863480 709863491
    0xd030216021c1a0705030103030305060a05030d080f01090e07050d0305070f03020c1005030919061d2103040b010e0a090218070306050a06020703032604050d080603070f090b1201 78
    0x844070741a4150203940302d81225051064084001d510004055032104c0001e0018401407000900a90201e0303042900148001c21003030707617540060310702680701e021100003440c001d0500074001031508915000d410002014040c9505003403003195528802c3c4203e510a04a03001800f00340750250003107404c450b0304100881182411800c0280d500d0758031a5496029a03524041511070a110300143e902941c40d0750081c11105481c0c3c83d082c03212010086066400030340d03d10310079840503280c4208072000ca900b90701030f010304080312023805400c0e8076280c641c4d003503140c0401c10840003401d44503a80b41510f4174a0800c160585802d05c081001b0711044400a4010800c0d80521201c4200400c50f00c3c8503001039503040c4540303500d82061021703440543c030490015a004141c1030001a01484882614070186801410303007224000e689114440251815a040e40000c2c004c074031580e500503c05984100700340d00502841d4a01060b661010b6130510840d4100ca95a500c0620705075230300c69520a01c0002c00b0000c0c0807 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 709865980 1250 709864730 709864759
    0x180304060507050c040204030f060504031707030e10060303080601081504020d0b1201112a011103040c0e09030f0a0507050a2102010b06070f0219120b01080f0d03021602 74
    0xc1c90348032980c2500c4501c03800083e0812841d085c02200d0540380c1c000c0c150000074800d5900d01000d07020242084082c0007013056803100c62800320074032600c00e00866401042c5403108002203070800700901c01c2c0b01e2595041c2802440820340102c92103070040c400b031038810700903a22100b003150202148040154403500018002d00041c0d4280c020104021040300e5003201590a010010b088070705420349031300d21050910000c07600c0c0100d4501c0b01d040301c445801d110803001c00d418060b07084440345402d8618002012040c4410300c001c001481001d0880102c413082c06007017800c0240e54a020b9807642040c044000500003000d644154103a4040c96803110407030b110119a86002d40d16103281e00c5007500024024810055000d06c1402984e140f8000a01051302c0c154503500e40810000910000303a030082402c1e00709103400030400da01140100048440140d100310b0318030386000c6002e01a0300041d070316403060400440613203001c50360f160104028180180e845000c1103d182c4090103242c4080e45c0010191201301 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 709867230 1250 709865980 709865987
    0xc08061008041a1e091606030b010c05060903030103050f03070c1a040305010c021b0a1a091f08041209180905010b040f060e010f181e020a0302070309151718030406 72
    0x50058681300300080d459440e070010300e82e83e9003421044149801c1c40c0d82c0070001a4025448151034950603d01010700c0c51140d1a0945400c00568512080c1e034000030041040c408240a4055444240070240d4038055864035610304401150041020740740d56a404a80301148032000c0b24020740e84900244014900f054008c0d4a5481a004520b42d40d0000b0703601030494603101c0b0000c000d43d008081c3c8080e10f5901004141c1305504041006500704108040143d41c52698203100306d941c4071143d4130103003103251518200c079451404d20521002e0100d881d0051280b6042c42c01e9a015002080308009903164580c00d00350301608811301e00b150441e150420403690751800790800390607078140c1003403010141d90302c5451500c20702440c41010a84001c900f00c0302021140c0350030500100808840d95181000b11100c860220f0b4440310348940801d90000c4d45800705900700c0d202900511105c0b9001a0750101c1c150301a08182018071880464030500e400222541c0c08008012120003000c01201d45a903110403015 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 709868480 1250 709867230 709867261
    0x80a0219051b0405012d08071509051801050909010609111b03190507030c0c060306081605010f030905160801050f01122001051e030a0c08061008041a 66
    0x25040d5616a80b1072058285030040d00c2c100d89018610085605510b070310390140485980d43d20485200419001420030760401604014011380102c5a10480104001805040307031640041d01500c004421440501d000ba404141140d4050b54500d801d9070b0f6a6012900602d00303600f04403096440c01d0468070402143d803001e09004503041c1243d0750071001d04c1042d42e030350f030080f0b1400c091007218605030390f05940e1050b0007031b03c11144a82004408030303c143d5194105442d164101000295485404115081e0700b044107034011601c0d084040552410705000070b00381070100c0c1e04042895110340e0301c40d08200041040c03501c1c0004880b0a09446602e512502d80a0102611180304650b031a00011960130100c03101031034107070b0b884060108075551511040d00700c07403261384041d414418103214902048143c141c245085130316036854943e580c5003110b5a14101c401d01c848000400401500300450303503e810f0740c005d8484186082480c0c2c5170380c0e01d03e44140d00f00080480344001000340ca050150900794012003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 709869730 1250 709868480 709868503
    0x105070f020f0607230a0816030e0d0e0a05041406100f09150311030405010b03060705090a030b0a090f06090c0b030601050a030f020d090b1b0f07080a021905 69
    0x100000c000c100c040480e6110603a03031925081d600b01c0000b240340d05006000c480f000455240104055a020030704600301030708100c1e1480c011803602010843d40141c0c0400e0422260490304040002c0c85e4900044e42d0344075558070070a01405608840341c040b660701d0a5a8500420b00188188507082c000700080c81d42420588005003e188000141c00005000d0302080074000380070f40c1c0ea0012503240c00302922a40c81d0030b248032810f142d03840c82d034000070740c0c0190000c503c00e602684c00480d420071020241843c1c0302004116104000051008080543d15601030808494215a03e1080b5486402103034000f030030591f030001e0440480c0b0658004100707440d00070b406580e014180307101c0c070f03203035a0380217211a44812208180002c40c2000010b00b01400ba074041c190f102800b41c801802c00840d280010211000c0c0d46040d1003800c080001c110340c40070712440101c03154408110480c00e00c1c10811040303041c2d0107068002449482c010458a410074400c0007050707040c400d4003548211120680c103019840d42c1b5030464 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 709870980 1250 709869730 709869737
    0xf02070204050c070510090303021b0303040c08280203100c080907080d051b0c060a050c190309060f0224220213180b010801020901080a0b060d0203180d02010507 71
    0xa00f880c064903040d101800e40040141c04d8621610f88040f0080081c10380131400e044c1d09120152080007260280f529018a4100442d500d007050b042c03950f20743c5036940c450541644030546246091b20030b81404103240c804941e40022190711440003030b0900d0700c02c0742c5a00d00c1a20b44109141da0355404080b160003062070318140c810341c07619034034080c1d16240c8100100c004100c0030026180d20b40400c4203580c40c0c0040760425203003210340c100c0c001246640402c8984000850100c1c0318425040c003031105003003407011040108800d021613078001d486841907124450a120088031035040e40344c000d2040142d000048995910f2003400d1210f110368002d801c0e9442c038540d1000100c03a40040304100e42e00c02050b0780042c0264200084c02890101030f24507158007807001c50032411250005040f00b1101c5003e01040000503880e0048040010200360000f003035540d4890900300b070100d0079220b4500f10f4414030198000560b990f40d800002034108040382130085450b10408040c100c0007903040d4003040c000d100751740e03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 709872230 1250 709870980 709870991
    0x361e030906081308090d051f0605010801120311120a030207030e01080f150f0909030a0320030103122709060b132d060f0206010e09060f040309090f02070204 69
    0x181c2252042c400310b4940d540c0c03040070a4008040b0b002d03000500099440142185007142060b551241000d8141705c602084070b11b6414000c091091030b0151602070b0000f8600120a903141c8401c0019030028a0006014400c400c0e10000c0c80c0c44003400440d1304407007150030b0a5960569110010000d501600c01600001c02080d560551584140c070010b000d64918400d4054075203513000745801d20f14070303540310755482002480c0c0c18015459444035203124030300040195844901464018040c0d0780681111a20103506801c4070510145070015241901e412102000180b4060a415035494981b600c410316135103540403103406081801000d080c184c9944031000e014055591506a49a000b4010440054603080c201801200d9032183c1120761004106918803840314074900d80529001681c100c41d0014541c45030540c42160100a4540141032134010460076140407183c4544804005c5c0220011f501c28034046014107208001080180075150710400c07a0340548a00f4000940c0150300490240e810720 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 709873480 1250 709872230 709872239
    0x1803190f0f0f0e13020c0a060617010504120305281a0f0105041202060d050f01090c08040309060c230c03010b0a140d330f361e0309 58
    0x4042d02294404541c40301d49583e500041080400c2200c54050310049030309120b60600d03000c040020101c01402840001003141c20181d01204e0301c40318901c0449180c0c100340600001490704040700b80902c0041c42c0010b100c1e203071214004050700e41c502501c0003aa17070400b0344248818440e8821507454080d44008100c041051040c0400c031003000001c640459410702c01000701c042d00380078000314544018849464403602c1924501154400d940151810328014014001902140701d0004100e8490030880b13100e161507a40201610683e010380002c11000e00880300401c034070b1101d8640c05882110149904060b00b03131317090ba0384032941810320307100358241030030341c001d605000c1c885100b541e100d01c0005038560159800e1010301c41c001001110795040d80b03000c950729101054490074070b410494145000500280c00380038182d41305100c4075501289458601881208250012440142448400d84043c0501030492080704030040b006030600700c0031354020750100400f0b210480754a01c00d445000c480e5459 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 709874730 1250 709873480 709873487
    0x913050f0a0b010e1012090819030603080f07020616030f1701030c15111203010302012601032a080106031b03052109030d080609060f01081803190f0f 66
    0x180031441e07002c5407520045044c03078200165040d10003c1c107402d200401c903a280d09010116842c1c5c01041d03442c180003250b00c9184130401d0307100705002e664903e41880b101c0d080da00c42240600c00e071080075080303002c0064410215100e107400d641801c05004980d0840001d83e040c050900036007035800307070002035004007000b90541421035114140e98000da01240c0d20760400303402c011151058100c0c034080c001d0540140340e240404000020002c1c903e404099180c3d40740d4400074000150000302c800f4030003d0013000c00028100d03182101c1c1140c0d0041c0d1500910b82041c0c440105400c401100e801c510140b9403c0071460010540244c41180c0c0b1541c0c001c50591300000c860540321030280401404c80d0041c807040e140f551906c40740d2a0b80e000e48170540610740805000080c0c0b6185200550b400402c13403920400c036262402100035580000161405540800c6134070000303040b9000102605154082c190088030740c0700080058480103c580c070001c030300910342880040c00220310f074110680003902cbc5901c8400c14030311 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 709875980 1250 709874730 709874741
    0x6030709020a080c0d06030503040f181803080403050d0e0a02150c031b03090604170708011505090a1d060103050105100302090402060a0c0b16180e011a0913050f0a 72
    0x48580c1c50b0400383e1120014141c0f02d5200d80305c0d01c2038040c2c842d500800800e03020300051004091440c0d48003074603031401403d06861910280d009001070f24190025650403807013071408a10590514100c04159114035003034426000700b400d000f480da440c11003041d54050b000a04052403d000300c5031700500314454603018040f0310800c0080c5401307030000c1c0680000b0360824504803100d01e1112081da4104202480880c0c0300390441e40c0104c40840f12420040143c000c140700380406000307160004e0112200700098502c0c003210b24410f03240101003007400590107601c0c1c0d90007a5881c000e100b80c0c5504400f105032010342e42d250280010794a5520b0030303011030079486d060f804440859a002c0e00410702c903501c44d003c01000f60420840700040c00701000e00314002502a200181c07240ca20f04000c0402013400500090182c40030b05030801854071000e4081c8808206e6408250454907031013000740608044d450106080d00418041a8125044240014040281e60001f40c810481107100c0c880540c4e9289071001940c8 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 709877230 1250 709875980 709875997
    0xe4002030f06100b130e25140f131e031a04050c0f180a0e0705040e10090f05010905030d050a020304030806011209050f030705010608061b1e0706050603070902 70
    0x2400c1c3d1900b001000200c0024000d407a07042c50343d44081780d130342d9000c2c01d100b0b4408031403900004516046405040310004c61400c1101c010340b400004072881846248458892400e03142d51079403011031804803d0b15a0b1070020003030441900d6001c0c2c41401c080310030100750303046c0c0401c5070235010300060b01600b0008855018070441e04000246054600d00040c4014980c0c107108468025165070010650300030300c811040d01a0b101001d0010740c81e084200f0305030a1041c507402c417500c19070a1088801303440e00002500b100c190100c900000f00c034000c0f0320346400b01c0c03111214000c0c815400c0c410820141301010014143c0001032100902041d0b840c44042003ca00c03080310000c000c20814dc1c0032a045510600c8224005070f0111800145000d99440d030782d16003007111050f400b2561001030750f901000400e02030740b4010318685000f0242414024442544098a080062510b0001140f800c2c1042d99011100040302104c015043c0e85100d00d0410901030881250000d0003407180c030a0000e100e005030b200311150722 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 709878480 1250 709877230 709877251
    0x40e1602030708090d08031014030f030d0b120601090b0f0f01051c02040f0e04021c0b0f070c080c0d111b0f0a15020a15060e4002030f06 60
    0x100190f81d0529142c120a1840c2e80041c60340050100096021004501429600948445883c50415003000f001407090021f80a03812500300700d6034800f0004296582d40b0445c0001217aa0794403440440c001c000e0711000f201c014072404000181c500210780c005d0311805010355964044820b46400e1102c2c0016660b081c0b070001790204005041031001d1420405580c00c4d02c20050b281a90341c04507842d0211031078010a196100041c2803200b1440c040709240c1000c0309444203280a2442a140c684510070001d1140520500020005a1461040e20380c4011182c0c0701c8a07054031080700c00302c0c0c139079607060540c140c4000c1070001c1d00081c203517140020040e014044201d103102001840b8014040020389001c01ea60700b005043d20049100c0070402c2241d00642c03059801452408400d04107007032000110003004040c1c1d40707130110a00c104460707440d1f4654003068080f0340036040740e070700c0048420003246280110101d04810042814554040c2240741c0300714001ca0403910040c0305c4d500b4203074031600b09442201a1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 709879730 1250 709878480 709878487
    0x2a0207030b0c03070908070612150302090105011d10210e0606010f0903060504050606090c09010e1e031501090c021c030b03030408240a02031303200a0602040e160203 73
    0xc2c000d07000c01140d01a1840c54600c1c921a03070b41d00e50171318120080c0c00002c0403038580714496034450b0aa114a844444061501303500c59440c507008030309441c00600640d81000380d0454400c2c0307441e4410301c85101d080300142c011800080000c100415202035404050100c4003440703981d61458032140100300c000390901028041a41f40c0400640d400d0105080f490284480c0000c008049207161041c14421400f40d00074102078079000b403c000045d400200034400703000d0305021a0001d668804071034004450207881412040c08481d010351001041c02090503418880e01154442a070654820f17281200d050702824400102d8243d026071310341250290080d10700c40c8000c118519244603401954a80c02c003c1c050300d1626072505080c9017021040712800c01c0c412614072034016070b21624001540c0c40740e058102181141044040c50b40b41e1070291501408000a1885018116514511840001e8070b03910807160548458030b01100650414032a01300251075090000f440c0318180322115817100e0050f07010f51314 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 709880980 1250 709879730 709879741
    0x1b07020d0201030507021e07092a180e01170c01140412060f150503010c0203040e15010c05120304021306081e1e0a0203010501060e03190c12110301110901090b030402040e012a0207030b 81
    0x95004904a0b103201301c2f9844440003c1149003005400e0281410310710303021804c0e010528192070041410041410020403070441c60840c44400e05940580c0d00c08400403101401504050b030181010b001c4a00c125441c100c840c0c0d400101000d120380459802350003c2c08070407440c071000d036124000c40c450b200203070b1103080c0040c0302040b031080e100c0d1090701e0504014040d500c46d40c44861400040c240304a20b080800410303c010b500c0c2c07240451380010340441046c800c1500b0801e2003078440880103480c44502a45801004083d0814000207240c146040100312841d029107020969520301d00806130300a5107000c00104202d03214204d02d00b20558007600900041040d01205000d950b2066800d80300002416004650300e5410103040b0002c5001d030040740150801c1c08201800c4030321030016205004e00801031085a6601300c4011002c503501111074a4880e5214000700780940a6541c510b40954a4007003108070741d00071402072120106e5413154058864599031070907a0350f5a00d50002402ca010b1045c000b40 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 709882230 1250 709880980 709880987
    0x12030501050d030c080c0601030c030c0e221a100504061703040e190c0801030203010c0207050f060f090603101e03050c0904030e1002061b07020d0201030507021e07092a 74
    0x120b8540b155217040d10340250103e82600b4040c003a0011580c03020060b40070414020301c0406040501a2003242050604102070103001800e4030140a40007581d0119801c0144401c803e10a80c132482a2403010b815460000141828603549004641c401c626160f00820580c00e2182c890400d0100e5000452805007803440400c03100e02c00421551480ca0f410301005040d0240d070080ea01e80b00c2c91361710b90700740d55415031040600392350948580000715030143c2c800304402c0d0b545408540c0400810740340d8503a00e03034244100c801c2c80e1241134181504900d0010602c80d01c0790303407e111042144c0c400080c000307003005401140c8052514912015020794401d448400e041e1600300403a94001e8401d0402d80d08604020010034407001180c040b2501680141c020445610050f03401540d03030900081e44640b41c200540e00045040042c40342c040e04040d079078400150f00368000c2184103d00001d504d0030034444950301842a60740d0146010b11140c4500704401c02e40c64204507101c00800750440810464217621211046 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 709883480 1250 709882230 709882247
    0x902070f0219150503070e010c0308010302091b120105180103110402031909050a05060601170a09240f0b010306060e0d08360d0b0415021b0a12030501050d03 69
    0x1d5910b80c10050008520040b8100007002105a49940e52240741c04400a040855175000b600d05020b040d02c2e040b40001d5001800f030781900e904640e250030720b4807926012024100d44000d44002c03c41c0001c0e03550551503d100500c1c2c12101d04540082140306034002544014401b032100070902c24503c064510b4500c0c3c9030700070303681c401c0d05440c41205030f80c0b540d600482a00c41081c810754540d0448803040c0f0611a09004450780440f00307080a850340b2040c2c001c9083e503840c005000706142d541d512940c0081090300211302c085104591440c5c0b4104c424801c00d40e0061001140c101e04152408101240c0c550180c00340344100e6440d9100d800e90744590b8414040c02d00e12500040b114007100300140005c9200f00880030014240020b09507000c0c01c0000d44075084c81d02e000300e0a034890f0b0821140280042e0403901d41c82c0d44268001032562480d02001840006070084607090707021580000c125036015030001a00c40601c034001d11110b0a034003203138030094044441c00e0080781c2e0003001a82001012a0264001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 709884730 1250 709883480 709883509
    0xc151204020d020604030602070311010203090a0809030a02030a080a03200306010507020a091805060c0f1b07030f060c020607080601140a02070302091008061806180f071502070902070f02 82
    0x800e01c600350b030380d8000b542d10f40c0f0070b40084801d80d90226164090540c050301000007003600c04001c500d1400e01c800080d070341d0f280440c80142050000661080a610181700d1a003070359a0140840d03640d07010900d41001580c20210744000060301d45004180000a03040000c00c1d9011620803030b510f1510780380011030ba076a1010728144d8000c41200360009444460b4071812001c1c2040b6072014004c882c05240150418a028040302c5103d07000b070019100049a002c219420144200690b1102c001000f05031802c040c890342c40034115803240710b010010301c07003d07410819940301d484e426210b107aa25144280c4040b041561f00d0340c0050001140c6c4d0b06c000702c0500c0104004801030045030951592a40084c448940c00c449400c00500354800c02c00405108200080c0c1180d01803209000680300185056514040100038034007054203a9418172140c0024040d02c1c56181d21901034070301d251f4a90b62906042103510303102c00014442d01d040010540c89a10039510303025400001342100300055001c010000d0b180110 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 709885980 1250 709884730 709884739
    0x30f0203091f1e02060109150e06060c070e091506040e060c030c13090905010c020a0b2205150105030606010c080417030c031201060f0c020d060e100c0207080c15120402 74
    0xd012403c4100240e0192410320301e41d00410056043c6403c1318240c0c0c0810607580c8011070720718000d002851917202500e61100c003da5549840702d01800246140c50241e0b804900101d00c1201072040440c00461420a46c200420f0101410703141c1006101c22102c0c3c18144040a070400341c08521105810340007181c01201d030000d401c1c10001e04120f1550f40c040f4a600240009584807002000c0140a0147d0f10103902e590024250340c3e030443e01c80120600d4000c010f00074451411000c0d9120322011800c4900c26500601216210a460844507880150070b01620b84240304200015560f507201c1e030010b0412960108455081a20b0809024541800b0241d07686443c042400300c0300d200e4174208040c2c20400322005803401d05514000019140824403060902007041c186911000368a13100003120392242d210b600014411482d8a8190401d894200c581e00082d0910185605850380000c11300c0681e0003040560342400554010440d51050103107035241e8204042c04941d29164500d800642d2082c009030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 709887230 1250 709885980 709885997
    0x9030a1b090e0304050307060e060316090308070602070b0c1e0304060603050607050726091c02150408070503063d03062c2d0712030f0203091f 63
    0x61201d410b42d0402c141c540d00c20341c00032600b0001d600d000c22800c4010080760605c800d540c0c0981001c50142c0c80020060342e51f01812143d50310b11144500c2e40c1c02c00070b5410812142d26101d1602d4550049d50003a9026952012184041625101940111120300311003c440c0500740c9a801d00c00032917600010b2041c0d07a0710380e8035940000441e00c01d20090744200c0e03042e9552035071a00d10b440c100801302142882400080c190451540c1007941807001c0301e001c0c08040358019207001c80140001190f00859400075000100c81e83c0c0c3e04030361011791000d48140c48008058035001510340f0241980d80d10202c90510401d52800e103000300c40e50101200340c01c0d801c001052101c03420b040c0070b43c20350264040d42c41110301641d90038080740c000000c0ba01d64a401b4410309095212035207901280741c0c1d242c86940c41c3d200d104162400c0400030520707008009a940a00c02c05441c2555600e07c0140440510b055007640490000c07401c0c50110791010040b2100140000c04e011518800d09402e51300f12004d89001c28140704442 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 709888480 1250 709887230 709887239
    0xb19090e0a02040e0303040b15060301030320010e0705040609090804031103190b010e0c0903060a0b0402041d0709121220032a0f0303011a0f0f130b09030a1b 69
    0x1401080030400101c4025131b0360b420586045100103000400c00303115101d108901d03a001d070355000e044a045a4041ca00780007280c00700000c0c50141d03248151350034410b40c641002d051110101141c1441160720898040001c0d565441c02a016240e6040c0014990392080205000003088900910800c160107800c5070040c10300781070010b10f1460b01e040280c4542c5000300c01000115100c616096110b4260f8201c0c5042c00c145c0800f180c1c3c0d490004d41101080b035110390040703400303445590540d03008020350340c020b40f00e0038900b00ea00040202c043e9080d0000a0700f1200101e0642ca0303000181d1140750b8094104192074078210011100792180d0107a0074040316040040316503402c820805080030000c411003d5017070314050051417001c0d901c426030220103a08640c2d60690010808010307030341119004044d5443c00380801480045500c20b1404e504402c0001084a030010f03092400a0072103900303a0b080808115841d582140218000c0d40503550345076200020340b4000490402d440302c19030240c41049000c4a455 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 709889730 1250 709888480 709888489
    0x50609060c010204080607080910140402010309020103110d1e200c0a0227010e0606040e0903120702100b1c15090b011719030e1002160603020705010b19090e0a02 71
    0x16152140008d0441d13017846040d0b4014010081c0606100700d04001220303aa11944030903400041010381450303034401040044da400b90308521744030307554500e0b00d5075102c2c0d288880400400d004518007800b40610305c00030f201c442c40e03803203580e00c225002c80000302d400c00c0000100e105a440040d45100500500100b4001601c4550480124421220b003050310070007242c0492a417914168020000080e000c803c0c404d07662504001c680030b849802d50408a240d498a40c0e581c41d41c81a210450f25056013407040248903a400f081d000783c8400d00034800c1c8881182c81d01000840c2d8141c001e007444582c02030811400151521400031462080d400001c40c0c401059210584000303800d0b4040e201c4050815841c4000d4501400942180c0c503c896026500041c00d441c004c08601c1480c030f0890050340182c0f07004010a008200c00d441c2034503682c0c005015640c071032500501a420401007100e081d03003000e8a8600f1458818604a01c18400c1e46d4460145031034948000b0242c00e80b50802c0480d8000c54203614050b07102d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 709890980 1250 709889730 709889743
    0xb030903221e03021509040204030210180609061706031905160608090a11130903020c0f12060601031a06030103050607140301061202070602090d0506041b050609060c01020408 77
    0x50904040c0301c1c1c0c6103444641581e401500c2c56042c01c0c042009414801aa14600321200e40f61a100c80a81c84e2001c00004c10002d10543d00041d60041c0000404a4140c0c0d000702c0011107141e02c01c440c0000146e40e40000d941502543c0100700128030b5a14600c0c2c40901c082d400785134002001400c85040c0361843c418600c010b450083d0580d02c1d038004000c8144060302d44078221000304041d181281e000e142c00b035800b50301c8140d1200010074030150800e0b504040d81e07c0b031980340c080da982c814081010343c40034034002e55105650110140200041304000a441c40c100c0b0f20540707020103050103082640d8591004600400901d5012074001101a00c031500c070740c43d104003641c040c611500081c9120f00300410040c006801c01d080952002600700014402d150344042e415829205032100903031181e08600e407c00190254010441e0030018000000090050001d0280d00807030080b23102011078100f81c0d40901217086980580350300107404004056071030418000624068941c800010709094455801030309048 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 709892086 1106 709890980 709891027
    0x20c0607050a081209010501140d033f110406120504020d29090105090714030709050c071e02090a15150c150e06010b030903 55
    0x3041000b2208203074041c4803107483d00400d100310144510200d0700c140040d13081200020f401441a6201101e060000c0c2c40e81020031000c1c1c90079120b01405d00080610308003641042c3c450710540c24000b0000d50513420010040074441d030b21440a4074003000c0c0d80e0249680420080001c0794000400b0005007141040106482d40c407400000c51009641d0006082c1100c813010020380d0b4081c5200c62086502203985001803511081500c80c00c803001190020356076444080244408a644103040d801d224009007110340e600c0e21001c0301001d40d202902da001071400042503034030400041000e140441c046001c1c80e6000184103400140b14040090031084540350740c0e049000450b91000078040241c000d4020b00d000707258001030000c20260b0916400d0b80e00c0c445211152a00203400c2c02098101082403000301046e07400c00ca01560645e00c06054829148800c0140c0c014010408040c1c5000c0c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 709712230 709892086 := by
  have h0 := BRFrame.cov_init 709712230
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709712230 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 709712230 ≤ n) (h2 : n < 709892086) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
