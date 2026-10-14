-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1147
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:26:54.535666+00:00
-- url     : https://prove2.me/submissions/ed0cdeda-af66-4fff-9668-4f9184970960

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 206115107 ≤ n < 206294964 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 206116357 1250 206115107 206115113
    0x30a0b04031404031e110f010804020909031c0c020601050a030503030c0307110a1a0601020d2c030d03061a0906071203060f0e090105070810060f0203090d050f0c0306010f0909 77
    0x1514042c5400c004214600617000306002c407031281186041d109030440014103100d901e00711180c030b249964182d68075025621182c0c00d00641d40c8006d00000940c7c08240107807041410081440d85169500040200700c110100303a0207420b0440680159008840100c01400410303000411030790000080200c0359504e81c0c400c00200da008410306d12000040c02411645000c1c007001180214440c8040101c0c40c49640303480c4c0059994540d082030f084040750b1a5040c208403990300400744003030000160602c0381000c151400081c1020420841100402d56400040c005c03060b40c914540c2090409034041d519050074031001400a00a12800804c0c2511102c41c032900742d031003900440002e01105080c00c02c1e454403403400400d107800454070700c1010b40c600f070b000070b0b45144108100c0340030b84100ca01100c00e5608004045908892180c0c1c902c041d0b02c000c121000090f100c0d068090300c094041c1c0060404001840485410158000a114440c3d8044001400901440016403088130070010000802940034a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 206117607 1250 206116357 206116397
    0x519020102121303050a0806131a0a060914040207060e070b0c071208030408030a090503030a0c0206060406050a0e2208040602010b0f09011203020f03070c06110703081c0b130c030b030a0b0403 84
    0x200d02070401e4140301405020352b1130301e8802d19070010101d40180d002a104d560441c1d600310b40c4d102d900c0340720b0b81040b00441c403414240c1c0245140342c012480400c4020038007102502d00a540e50006034100c1000401005c002810310080d070141031381909515012400e80c403640b0b420302011300040d199040003c041075913400c283d801f40c16201e51007002e494032890109205401011100f20400c054010580003440d141390902c00c1c80145d45004203d0b555807820100b2403c40c5000003018000f11600b09916050403104000100c1405441580581e44c6c83c0c1c00e010000b42981c1020401a0280035864401819596a4101241500d18000e90480808101c0c18201c1c540300042c42500000e0100146038010700c0341420444003a80c050391214441c0140b4110025a43c808601c0f000d0041c0800380140881001d140981c1e5000071041680070601c0d111500001d500d061300c0380d00700d9444554070110808400e0301400744102c18a0210090a83c81c4040e480d1060140001000142048401c410b101e801d91410707 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 206118857 1250 206117607 206117629
    0x110d03050c0c010911030c190b031f080102250b010302040506030109080f03070201050c070f11010c1a0103060b06040810230106030509120703021506010519020102121303050a0806 79
    0x2c0e00081c00900c84a0070408000307000954028081d006400c200242400e060b400b03806d181c1300c440c40c1000194509100000a900003918050b2200013000f00340d1700c0d40f8a10318403a4040c00c5002c00050740d440c1e40c1121100d8101c5417400f101d501c9408610b820000c241459902411a0f8055a001c100f564072000001d00400c9014002000e4400101d81c203160456840c001e540304091603002004a0744610a5028840c0100c00000304000a101340060005088050181200c0010304006240c0c5100d5662419014880d2a6919000d00300c90010824030025014206107900c09842d047d00c0d0604080321103895101c0002c1402045469004210030ba940210215500307424144054800b56101c140081c00707010113481c150ba0911501d018103a80d103080c00304894601d40d1680042100e0b0b5042e1071183e00031000184103a06204050100d00f2006020b40c02601115201341d00060383c4000e100036070080600c3c09803840c0c2c503001003182d01d900002c0e0013104981e410502c9007004402a0385d40d0700003500040c19 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 206120107 1250 206118857 206118877
    0x14011101021e03010f0f031e0c05060c03030a0f050c0909100b070c03050c040b06070f0203120406030f1d0d0c08270f040b09070513030813080d110d03050c 68
    0x2c1c10080d60041612180594140c0e2800f100307900402d6a41d50b403600540328240000341c441c452950810600300c202c003100300840b5120f80103d0b45200e55610009455400c80b11400019400000800208140074400c0503d85c0300003181c100402d00b00168100003a000708042c0e03900840c03000c0c011400c0302c40c000500a006040384014243c0d9801d05140688080d02c040c032040b2281d1150300650f142604c2c0900594800d00005070003d8180315080e01c4d00308a50041d5138050f6090f000e030844008185214000038806482c080d180800c2240450711440308656600091510404a46e2020031481f4008201079284031060b00d01101d243c156414942caa070701c5a01004030000010840c44e8064080b40d2004103441c0908031400c0c6403c400603014030007038600400d00d40368400120300020f2241030180010341410250b0551803129142c1301ea07074507426580046581200b12020100800862004104e180c000d4801484e00340310244140b2500390b41c4079120900002419100d40015818000d014240e0310300b010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 206121357 1250 206120107 206120137
    0x60d06090c0201020702090a050c07020904030e0910140d0b010605030615130f090504050a0b090c040e01090b01050d0b190b060a0e15070c120305090a080705040c0305011401110102 79
    0x54181d01034001c0d80b003188102e025098900c0010308070801c9102e001e12403010072800e0341c50301d42c2075406c0108003140100220103001e50320861020589070b4113111807150003d150b6410007142400c0d028001001058299403280d00b01024050000340d400032101d0440340c4a042c920745a84900d40090081102500070b102440004111405a840d280c100d010448013046402503005072141c0503041943c50459005e4143d5004281010008810444d2503a0000010068400010a2000050035070b50303202c8141c4696134645d0020000e11807041255030060070201d03130982180307025039a038000b80440101142d032030410544802c00c9462554100c1e07905d5450051420b552001143c5c00902000081c5260034001c1e0080340b01c01051400d42c0040781e8105811420845141e0b1512030f43c91907102034010200c00f0802e040c002400780c2d84800d00b10802030074051001e0004513050400b844129a1642c207035000b050704104c0100502800900160498a0203103844d9034100c203010b481c40d01920559180502d40e40f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 206122607 1250 206121357 206121371
    0x6040b130f060b0c0a0b0406061a071211100908090a080d033c020409090b0a0c020a1a0709080d0e0111010b03070e1b07060b01022109060d0609 63
    0x420341c0c440d40c42014004820060181c079030a00100300d000f80a400b01107540010100404590511036080c0d02a20454020604a480c3c00d43d0900860050000c0c0c5803180000c84c0324000c104c2080d4104001c45000d00d40685061041410241e0f210701280f5655010750f514400c0d03c0c1400386040445140c7d00c1d0241020003065a5861295600c001c1400e541c00024940450b001c580c031039032040c0c00c1c81032003081118081407090902100c0300e02d0075064005007440c0c2c06c00002900c2034850080c01c8030340d4060365a030019441c01000500c04d0b2010310708803404542092010380001640310301100b03154104051503090715a00e008042d1000030541e00010854810413103210701c2944d0150025410132000e90b51200d0307840340e00841500340c5504288045e45600081030500901c00c1d04041664007660390f0740d6554450b8003860b01da2001d0340c40b000c800e03a44a038660171262869601002442107003c0d48414401c0206d03500d02c070740d80d1103000d09086c2c50f00c100c0c03002807001c9150b41c0c81c0d00000301401201c1000c200f04 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 206123857 1250 206122607 206122639
    0x20f0a0c03050105100302031e010b0a030b061e0307060309030c0b270703080a140d0905070617060f040518010e0d23040303030c0c080a0908120f09060306040b 70
    0xd00c0140c8070884070341d82001d001442c031107405950348046030b9010700180841140c640a101400c203242814201640d62280c06034101c0d076907141000020b501840071100d01e8188841030000c078500b0180d0840e201c003c0d205841d122520006481021284149000039000c1014075040382d049000002c05000066a4810f101c060b03120700320a21803410031040280061a6140c50054441c1007620000c1c0c103c01c404e1100c0c417100740c001c0310181c0b0b0131313014010880e2602d01e29803818011200b0400055030300d0f42c449041485441d800403855118060701d4a41d40030b46160040004007500610108a80500e8071503002ca9001d0214402c400c0c40e1111603c020721071000149030040d40d03124009000c000156030030540444254181000341701801e5081c0324180b900d0b05585041d0040c0c801050503c0030015040c1e44500402c0b2120090708260926550315941689800780305403401c0601c181071701c02840f0422000d050318420f00c003142c01480d0f054404685035556040068000c0103041f00d01d07600b00d21084c42c141d1903 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 206125107 1250 206123857 206123873
    0xc020402210907270e070806040c050a0f121214070812070302030708070f0917010507030e03040807030318030203010e0604050f0109030c06021309150602101515020f0a 74
    0x440c0704501c00f00c56441d07076141008400e4029510440c100b60300c070b01c2070a104402041d0414450141082e0840e5503690342e80040d42d107480011141070b580f00301503e49c18005071a000d100789008200400c40307048264104005010a821030380c600810003c40c0c900042011802904000c1044540404907a04c80c0d150341841400b6a0126140c501001c0c0900001040540a40b0a880c0260025a2603035207543d5106015101040e100d500070007880714960f000212504001404040042c014001150b00d0405040103010ba43c0c0104122500d0b070018001400310b502c0014062046039090b10b401e43c6c0d0391070b200c001480f2000c440e80029426500b05501c1000762070000600714040d40c4a00100d484a000d505100e600b01c0303c0b500c10040000b0f03c44015800440c003140c02405601c10300c85a4800980c0c4e4a09191703040329403012600e03504032900c0c202000550340501030039120f0114000d090203410030f40c20121132150610b00500160628000f11354000c18420080c5151902a8104540342c0d07421a041200c6 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 206126357 1250 206125107 206125111
    0x140103240303080c0c0601260109031106130809010c0303020415020a03080c070c180219091703030606030c0a090f03080409110c06060405090a0f140d0c0f02010c02040221 75
    0x7020a4500c030205803070403e044d04840300c21900e00d0141c0210307400e002c402a044107070003aa41c0c40c810030422480351030520030311402a4a610a4a50002a9140b0303014941007040050180b40c05c0d034000c00010000c602c0e00c404881544a003440c04608807002468290028007403074015040c00c2c03a0900c40018401d8001030a00d10300c6020b0745584000d0703590300c80c01c017100384a03001c001428410208000c010480d004440c99a040c03c8034071001d41040c03035806a4041c6150000300190019008200c200000702080f84c050360345ca50310303101070340c0b030f525011001c54102d20019001850301d00000030714110a03803041080102a00309096a400c0302903032400c1c0720441c6e4103d4050700c19510f03c0c01c0d10414010107e80e0844003c1a1814007070715003903544204000003007200401d2500b0b107000c0ea00183c000118440e8090010354811441c0803420b10301c0300366032441e101d0440c40e400d0600040440140c0032603410040b8070701c0c9580c24a0865464503803440840c000c5c0c011040c0f504122544003414940200003480528 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 206127607 1250 206126357 206126363
    0x1823060a05090c0a0602070504020703030207060e061b090102120307021609020301030201030b01030b09191d060f06120304120c090218041419090203030f130e010506131401032403 79
    0xc07181c4001c101000441d000d54802e00015031f112400401a0f801d00d0703000f4182c024001d0400509001164aa80c42aa281850b460545422150400c0043c915004806001c500c1120b07240b801c0800351b800103036894030301000d00040481e020000400701d0741300b040f4072b84808101c42d04445c905903440301418081d4000303000817400703e4200070b0700f042e60754403900c603d0142c44401000d00f03800d0740300d01e060000103031a07010015242c40c0c0c03680800d08038044200f106101c11040c001c000c0010349454a1050101c42d80a40024814000008401e022520000540d0f091b10880383c403120100080d85400c40b00415a5440a149180040b4140e03003080075101e01c0c03440b0340704290b8040c0803142c12440700309450030080710100c004103100100b1030095490b03a44a04100c1d4805021680b818842003150f02194104401485001c03503064014064104680100b50040506446050030700142d840c070071000800c2c1c3d00a0302d010841c0e890490710782ea0302c60f800954000043c01ca0600c0400c00301c5a4440704c00b0901e020135 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 206128857 1250 206127607 206127613
    0xa030e0102010c050319090b070507060b0307030f1202071e03140c060a050a0509060d091b03080304030305040317010905100e01080c060304030c1a0406060602011823060a0509 77
    0x14009650041c05803014403216680c80510750f5403200021014004500e60a95800b40c0d992a600002814240054021a201e440380c646854a41c6001d1040d600d401c04c101740250030003941000007402c4490003c5041e40d1101602c9280c2521030740407468018281d2004800e41c118800c141445050103078840c040c0c9005030a0301c11130a9141c030415a4910040180130341041c41040309209082c814000380c210313501340f0314000349408540b80000710903410031017542c11303a20740d5007211808021361001c1c01056550350302c2009001c1455912408058000180094185074603000000c0c01c0600c5048011000f00d82000441c4085d61208070210092108446504000e02030034070115541113442001390403900c07590300400a8403400410b001082e00301810440900c100208000009113214180c18160f9113001e103010158509400d0070415a80158020f2066903d0b042e06a01100c803486000690507400541c0e0500c18a06056909100c200107408155107014500074800102200d400090054602c5412 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 206130107 1250 206128857 206128877
    0x10030605090f060403050c030f0c07060f0c0803040b1302041b0306121713080f01020c1605130b0f03011a090114060a080903070609060203040c0e01080705010e130e0a03 74
    0x4082c0d40750140141d41240358841c50000700024400d00c01003c600c1e8400003520308052038601000b000e0b8000e01c5210055401180e014002c00c4e41c044050034104003140b03064101d80d00a502c0300070042c8030180c0094918802203000900300b81d06080010005680580b0407c1040c0b020703205a40c4024126210000003030421380005912582a104204419008049d80d2482141c1c07403440a0f0590190003510110640b6250011304c03514280051100201180001750752003071182400ad0a100424402603030110488009101c10703164109010100d030301482000489003031044c00203141001d400c95450b4950b0900031000c5036400c80c0f1800c080344d11425141003101c1d0741ca404590300d1a496400405400032800d114840c074040c451041a600720101009803407801c1002d84031082034601002d4140e072100d0700042404208056120b80c8030003882d0311480107056504101c421500d88010744241e131304002206500c1c60741940c403c1489402c2140d076010030000b5001c9c3d884419110b030b8030305005901161079085 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 206131357 1250 206130107 206130121
    0x41701140a140f07090e0a0603020a0e0103031e050f1809071211030c030402010522031a1302060f0703020c0612070f05070f060507050d09060506040c030e1902150310030605 76
    0x12402419107480d11700c0c9107403c109501a224800600e802d0405440d00000805038a6070503402000c1c1c242c0000285003581181000303000f030801003041044035065003d25600140d880303001d8038074005042c24895078a6028420b00d24420307000f00081d69001c80480107203c240303178001e4021009080c290b9414031070040c43d02003120060000710303807070b120303441007080007400543c0f16000409040d00302c00615581c1f40780c00c402c5500300d9251a001101c1800700c0100c002c1460190321402c80d880303015900d1305000c04e060380e80811018001d01c100100c074190042028020140240207144142c200a44950f44625101c00e000303d070007000307071284000700f05803103602c00c0028800c40403035034000e40180080c81a80019501e41c0000e050003881e44d0100300080c070081c40c1e161928010b98910701d0155001089608090302004111140300005c44103242ca40241000189400b089402c0598101000d8058003a25030004c194282c00030b0f155854410000020000a0000300740e0050a036030003202c0800869032000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 206132607 1250 206131357 206131381
    0x10e031e0d09080118021912060c08280203090111030903040e06150315061b070305070609060206160908030d020409060e010308090411130306050603150c041701140a14 74
    0x105d00e0202c8282250500098241215000c42c0441032910f054074150f928090000b00e80440380040b0740041d142c1c4080180207605c403032900d0704888041140f000c0f076900288620752030800b200f00e130312940d40c0110018022400a42c840809401c40c07400b056960326001203119129072060040c005895400c80200e912805c10001d11220035400e580c0d0700d49107861303640034035111a403007080c0c455109004003e42c0112601225400c00960540c60051041d40d0462901604040c0781d600b10508129460400b084815400175402e50002503681c1134034541c0400c10304c2214602d502c2d40107200c50740300006200308032907540d85c000c100325a20f484040285030b031a00400016983c0070300c0060102d11083c060a0040d141c1035008010640c00440a5460046180c0803085403c0c42a0300545080d640c400030000182410702004680c11402000305201d45860445000940284d024004140b6030380c00141503011025403003010034071101240c40c0807a2800580c0c1d42e015000c0c107103a80b94400820743c0401c1540c8000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 206133857 1250 206132607 206132621
    0x1211503140c0303071104060b040b0c10020a020d0c0c0302091018110405090603072301020705040510030b2a04150905101b08030103060209011403070e010e031e0d090801 75
    0x140518500017080d00c07103000c5a24200c40f81644555070340d0000512280d0000100003c00780d608016886071901044030b810074415007841691580104107041820740d01007604004000f960400002540039400d0805c00c900b8035800c000e402030109014402045040c2960703004031521800c1c100000c070705d40304140d420f031504503000c0c041c142000e100174001860181047c580c000e40141c2260056035848840c000040481509450040322440a00040b942d0500410001d8001070f14107100c641005480c04002030380610002d4a540912008a1821406590910400d66500442c1c1840702c40c5201d4100299006200c1c10f10600e031101041c0c00901c0c040e07042d9100302c82c40240003150480d07000100307580800750b640d55840c1007000001100001501e03400514003a60003802c00589502d072000015100520301014084044018420454510b42c46940020b510000386445c01088401d02c0106e85000041040700441c0b05c82d480d00e488005100203224035500f103990b511040030564500c4410300303e07004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 206135107 1250 206133857 206133859
    0xf0803030112151d1b06040302150403120203090f0102150a0e0322050114030f061005090405040605271002070203031306020706080604060e040201211503140c 70
    0x20600040145101c24140d64120900642442d1801544080501c1c1120702e0030120003042d02007828036003503000e010055103144604008010780308602580c0000c6180c0124840244184500d100d2040941d40e903105840040d64008030a0b500b662204c10080e440382c120300399150140703480d011903550f03d40c80000c00904031080b000720b030107039519411041d4014007032120a200907440200b060b0400b034915028032080d100314601c0c00245142c01c000004000f02d81a0540520b215818400c0c00015480c0f20044c5030808400c840906981420b0801641c45001d01210305a100d481c180400c818040340e034004901c240681c0941c1c1041d003104a514103a48420017001e038003d07a00c0714900d2107031818294014000340b030008089904013100098500507034581508503000507000328404000043d00f0620172500103078103e0b0180f10f0340d4200407001c21240c900610280c1000154003600c24040c0305044220a0283c290f0000c2c84403500d98012640c00600780c2c0700c200c0307026000c955400c03800c5a001c10a1110044c1c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 206136357 1250 206135107 206135113
    0x6030a0209032811040b1809060703061a2203060c0305091b01110309041e0605010c030507020105030a14100501080f01060207030b0712020a0816080106020c0111030c1e070f08 77
    0x80c1e124002110501c007105500142d54046071006c50342d89403002d580c8801c1d0070001d800c403454404c4140d410f090015002506141c01e0074014020900049558000214241c070307210340f2100d000840714814100320180300d202d0001307640d0201c01e001d0103070000a42c03070105880038060750711400011075607100d1203254824034009201d010780f602d6100e401e200c21441954821241800d444030000f80403108200717000c20b504100fa082c000700c84038540c002c00e4001d0109080444c05c0c1d400c15100030340544a580d00081c10801c0000010f1200d1100f98082d18000428030854003541c40d01c00c0c4030100c2507a080c001c690204202400050510341320741201410380e0ba05502407e0414a541d4403c0d100c004043c004500b4011a090700f044800c59070300c0504940d00e840d540f1002c1d030381000400c40c0382c01207031855401c003000668001404034540029011141d05020311f40701455682240005040d03000ea0309030706240c2e005000810494512821074501e004280e8415100055038801120031603110741c0c400c000c0e20f60 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 206137607 1250 206136357 206136433
    0x50c220311041107020306150109060507021f020307050f010f110405061605030c0a03090e0711070501050c0709020418050c030907032306090d03050c040509010306020c0c06030a020903 81
    0x801d090b00003500300c14090f90701c01d040400c0e590020f030604a04540407400704070030302c00034071056a00c040514024540c90505a1516180350041141d01160a00c03286e46e40d5186022290018400c10440c1d6245030000d050365041c5080c0396107a401303030000d039807110311720b60130300190341c08a50115080780c00320395000740034070328040c0105840b4001c0d402c00315080e1803601003480000c20b010000d0115052051103690790070398650400143d0380b00032901a01034410031403100807021074058005101c50944000342845138407104680c164610f40000341e0070550b0720702d00121b000980b02c03d0f9202802c0180803032050501840d6550101c00100740000c6a0b0340460743e2082030104081a18807008a0f00c14040340035980d4011a4400000d20703058055070080d003954450404901e0885d414440c2075000003290021390715042c40c007400030f003000c4010f00000d02203560014091984160402103408100400340500e40c80e481c102050350002d42000c2e10050003805000507911a080c1920000f201d44005180e215082c0303 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 206138857 1250 206137607 206137609
    0x1b0a06051b0c19020105040b03010b09090a0c020624030a150e01021c0b0d081611090601021203130b090607030e0106050d03030b03010b060c0c011704110d0c0504050c220311 76
    0x100e8507410013a81803100030000420901d004030011400b80120000c4181d0303400526050000b52a0001d00e0b40c0b10700c41c87d0000d0070a80560200e41c05070000e200228254410103803034691660445000d080503814842e4842c102d08001c0c0c0070100400c0000c0080c010000001c100c402c03282032307103e00001c0c0d000c906410707400c2c031401c07420ba50300c400070f012000740540780d400e0701a9460302d002ba44407400121181551041000801c0451071800ca0040e4080c1c8419956080140020307641c0c45d502303010094030b03543c040700042044040900c03c2c07211940000c400300450400140d1103862340416214100002d0502d2150038450805015840880e200609a21160403032a10200e0060001101b1542d00d0f54036000c1909c456034425000d4211007140c3d1000d080c1103988e00c0009040b854550890000010a2108100101c0c0c03403480c00c600405003d0751803034805080d5142c1f40b07000c0311194001940c414a0001440001345d00b42d070151040c80c52595a490b61a2000c1a1004420714944002445100040b06444203 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 206140107 1250 206138857 206138893
    0x20604030f140f0d182402160609050f0102030108070911130f05040b040501030218101203021c021501060302130806011e050907141b0a06051b0c 64
    0x10741046850034066601c40c0c8500d410b965030180100c11001c03000828000528070b014801c80301a80240c1c0030411291400da40c4040135130740040c010192080d00845d00b8048801150102c0b6540300c245002d5134442d20851906c04000c0c400510300b40c075688201958078050240510840741601c03044401844000e20f031607410405804d40300c8020340c0381101440b400d28180c47d034040080c090420001040419070902c018041140c01480583e40324500f0f0800401c0580c0750f120f09005468000307010705070300b0380da044c1a030b803280c64480c1e00581c1540740c282401420305034041000c1c2c219699003000c25941d2820b001c001c0ba1b80c0d2001540314100001c0354030040040b01e002c6c1e07005054940034103848040080c0d49000e030307604010090740000d00641d00244810810030a007018980549411141500d8508140304000c015245180850308804000114080c40c0d1000d5514404070305030080847ea0207101900e03115002d07000a90322000c82c6c0b0b80c40d801117203002107004c4c00d03550310b940c20600805002841d10165a6 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 206141357 1250 206140107 206140127
    0x101a030a0b01170a0509100b0f100302041203093b0901110408010b0a050105040e040b040f0f051b1507030c1e0f121b0605090c03010f09021c0302060403 67
    0x1051002c1c0f1503581600402c420803d42c82807104403c000303650302d00440000c0c01c2101c0c1b0860355142901e0401030900ba0341c0c400c041591000d0050740c0c402e4a400c4c5001d02a4000d100350781040c8444140c0c071807028205584440c082095a45600042881e504c0440d510f1800c003182010841541e011002074030100b42c7d1100b26690301410070000810102c81d01c440c0d42d8203d03070142e00a200765035152500c41404d4142079884100601007840c4c440d182c1464030841d40c5003007030040c1c8000d00003445500032600744510380c0b0b07035104859006558002182c02c940751803543c03800803118909000f03009941c440d500341380c411849445d4a0080041c6071920300c3c1c541c0c04031012000c60702c003110142440900b180181c40012400c01144d0710a02001204185030b0402032005004104c1d22410812300e108810440c46030040701424055214001058586a00c20038504188441c0031050301980b030302c03096034590680ba41040000d40c1c025504504814694408480005114100500561b0010020800083c41115080 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 206142607 1250 206141357 206141359
    0x7031803110405070c23070e0114100e030102030106030209041b020715020a0501050c0903060a0513080a051603050910020604080f0a0915020d110c03150606040e090105101a030a0b 79
    0x3100c0c0701e0940e117141c102060002d6080441940c2521801c0124040100001070064184290b40380d42c940340345040cac100c8226903035038080c502110f01c40090b103000d541455074030b40c80240250344075a1160b0000f03000790001044144640d0814008a0341607a51610039004005c00707501905950f41000505c40c00954103040c05c600714840c4060700400303e0000c2c8509805052580306655840b241c41e01010710f483c40191103002010714010a104c0b040007540414a8541e80c0180320a0b00c0b40300c9028169414010319010203401d848810b5148109903016000303000d5108126280ca0310450100400c0380e580c1000c903401041c2c06404c000d8a584c50303402c50007070000c0c84128900542e0321070311035071440c4420780a0000f03880964480c0c01540701168010f2030007002010a040100001e101c4100040da81d9007605240f28511000000881c0940c0c44070011100130302100000074800d0f04003151094020202100c0c1d03040d41c50409400441d4002c4c90300070220b40c01d0310030403d03203041d615001031071b40050040c01f6805d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 206143857 1250 206142607 206142617
    0x21c0804142130040b0301031208091f090b0907080f03040b040b0c0a020303042408161d030a05030d0c0806130203190914060c04050a0605160609080703180311040507 73
    0x1156490a508011310103880071000c2161a03502d1854800c0c1048142c40d2008103100b00c0e00308000c4002c0e000111403000891003006503c40701e042e89540e50007800e60113400b03001c004514040040c45140000e401c0100c401c1d4200701c071f03042c040001c115070b1680500c1c020148a10801c10003002480c142c400944a409080310540322400080e500103403460340705134001c080c606903c1b961500c8058448a01400c1c110050500d50054608120010078184045040e2014000140c00c00e071240c0c105140201ca01d048041c089030040f00c1c46061481d600d80000710140c100d00e050840410104d40318603069401040c2c064046140c91882000e19000fa400043c0202c00b0080d442c055500d03c0da410b4042d8014041c047d482c0e20010b0000809603a00b401d60081c81e00e002450100000c002c03e444502d0400d00311509450301545a0303a42c540d0103035030691100d001410143c02c1c10300c420248a41c400080c820244280c0f5003034501907044a90b44001c003480d100160402200c20000302e000d0406400071503000101c4d1904c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 206145107 1250 206143857 206143933
    0x20f0d05220c0e10151b17040e01090b21010b0603040b011e0302030c040e070503070f15090b0d111201080d030c08040807021c08041421 60
    0x10000918a2031006440203249880300308a03040081540035001200700c1c800641041c14000d101c0801c04030b40d10800c0410502044440101d030280400d5001b20b5403011420400c9107558424000f190058010684603030f01c00800062212003074441c0e502d0201c3c000d00045445c1b01c6020056403000c442000201c029520340404d03510b1903403800d00440c42244106010103080d4102140c10ba00c5441400c00b5071a804440c50051000d60f400003441c00c06074008031000301c0c540c2410000e050614005500954042c81403070804661455811104e13826240b2820701c000d01c801102d801101c40444910070750901c03100400c0740010805854002c20707640b03182500c0c04c914060020204000c0c1143c241d0142e0a40e400c41650004042d506005032139203081a4a051800c03400d00b9200c20340345105143c4000d00c1800d403140002644113001026400541c2c004100b82d4440ea9642602681800c0d00740035944500c030385822000d4030f00141d07030583c905600107500400c42a920b45c400089081141040c110140043d500 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 206146357 1250 206145107 206145151
    0xf030a0b06060f0d05150d03080a021605070306020702040513030e13020c0d0306090509011109100905030d02030a14070302030712120f091b0806070305040f0c061d010201020f0d05 79
    0x2000313000c0c0d03da0321100000e0518140e188034480e00403411001d40b040520f0201280402d03800010140c20518400005075a42420500e003004454007050017001402400000002d21031954050903446009580c14000c80d600c0515002e1481302d000001000300d20890801552802d010a400850f12100d0b0f2006140c40e03404100c0d245032801c0550050002500c415040c0300e08034540c05260740001065000703001e0782007544403080c040e010b04a465801030549641d240107251144454100924019007651030044010340c00a40303d41c0044485000f0583e905400c0c020340750305800300c0346900d805a010790704210741e90b92140104e03107418030f4000030003410791011101c40a503807254044289589000145500207454030035440d032012445100c0ba21494041000f490302c1c00300301950b00090528000655580310b24010000c0c4040c00c0024019400c1100003081964200040600000d006400e2020007010500120300f0b0388100000346009180511285951200c0d0b80c00854224482c114040c00394050b4403 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 206147607 1250 206146357 206146387
    0x105030115140414041103010c020303090c0d0606330504060c020108070e090108070f0503010203060130110c0c040515122407080709030201050304110609040f1a0f030a0b0606 77
    0x1d02c058440c898a4051b00155140c00d11507110810001d0014500710300d0300c190210745981d016801540206050b400980800445903c6040580584545c240204410805001c400c9540603503e101c504011490b0100050080080e60200d90640ea00c0b084000c0460f8011600158041c0a02c0103011002d03000c2c143e01e41d03903190b51301e000c0c15400004010b1907207010201c04020116030711140c001e901c10000d11017140d074040040700200842010503c0100c6034051810242d8540d042c0f420302c40d030725058180d00c828074064010a28668204116007154402408000440700e054550350000e550100e095086820403001a0300616154000e4601040c4c40d20f105190480306005412039400e80d510030054000d03041680035401130303501c0c504000010b0840d80068801c3c07002410181042e0b40b41c8025601e5555200d007295a441009041400006020703104400a400b8856442c0340c503030800030102c400b6040c091420f140d0388000400404c029181a1680110a200a450b40e90407400800010910491030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 206148857 1250 206147607 206147611
    0xc060c0a0606060f03060509090a0201320706060518190207080f070506010e010305100b0d05030a02010903020c01030902090a090302010b090711061b031605040f030303050109050105030115140414 86
    0x50381382c80d025a40020001011124070341c1002d4850780c5034400b0700c008043c0024642038050360a08050704c03030031046000409070380304410312000c248125480300c0124009400241c01751902c182c0b4140403150300c41041001035841c03410119145106400020300b02134084501030300354000381d0310051400b202c40d140c07100541c1c00300d0720003000d410f00000d01808101040002c54010000001e4200895045641e815224a0811a1070100540700c40c13640103140d498a40e042c0b41c01c2e90000031295561440c14002e40600500d00060f40540154000c03040c1550080c0142c040c9c0641c0100a49100e0340d0308034502006040d440c00035003c40d0740c1d814403e21541c403a914018050102d90312202c7c0500c8010981030316015004061400c1482911320751104c51105009580e04010040d203d005880891541107582d401580c1c01580b802d000514000107040c1c00d54459410f80f480c201d01800603a0303d03002410300307980f1041c4034002d4410002508002039231092007107100310b05008201144406082c14982c4096a003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 206150107 1250 206148857 206148869
    0x7032406030617030a080403050c011e0c08010905191104050910081207023111040612060b0f0706060e012303160b0706150b0703120504050c060c0a0606 67
    0x2c0c4840c00d000d0240311030b989403061400400154501995000300601822002c0c00c01418410040380c41e0428036000c0d0003030707920500c0141c10051502c6940c200c2801901c1036070032110100b1245000802c1d0341100e03000302407140b240b541407022181c0b04082600002c015071815010141d1007840081843e65401c0c1d401c0340030300002d981f404c001034100f06c480760a00354000d58003800701408203d5180140c0700c2220201c1c031101441105030503214099101000f550310700032420f0b03c1c0740c0b44c1400141a018180b0280080d1803a0780d4a903003000b0080341d0b1500803070f1030901030704406040920001016001c020001d00016109034404501c0030f949101d4400042c02c207801501c200b80305d103114126a0811420b081e83c881c80d044005141800c09200b140300c040c4050300891500d010f0000d41c602c00e01c40203810160402d003003000e50303402180c1c3e0340c41c1c03910784c03a000001d041700081e2513100a4a408000e03030081600568005010b02201c0c181e100400c8a65440350710082038034060301000c43c001c929a44101402420 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 206151357 1250 206150107 206150111
    0x221091009061722060b04050f011d190506011101090302010b01031a0a050418050f0a0c080604030e06072a14100801030605090a0f030c0308070302040b030703240603 73
    0x4240540601a110081802007090303c0035010000540d0704440710022102900e004a90400e155091040c054034100010315003042c244011b000e413010b0720b161075604840c0151f00e4042e80c5c80034161125042c04064440030030900110442641455140d84901d8009030141003a803207008001e01500d0035512581426805030359a40081111540c150003000121150340c0303140a0858444070020780c0d2141c0d50b00074640030b00c1da984d0045195000415040d840980c115040701ca401c0441030b5002daa4510ba510200d407040e44500000440c0380c40090380a0183d60705846101c0340440c098240115074020752404e1307450403048248810304800004030002d1030000c034001100400c0c10540311186000c0d101c12202d0107440f200342c0310045207600010441c150f1f5444440400e85803100c0c40e016242640c40304000e0306840a009000d000c068000740c04842d0305220762921819a590081d00398124000c80c40385c154006800c00004101d81e10a51100d48010039000c0c00c9000040c0140b00341c100e00c2c0486c4c00050101e5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 206152607 1250 206151357 206151359
    0x12060f1210090303060909081b0316080319020702060d0908070b150901081f111b06010905090303010f030f02041b02010b150705070303050315041a0111010501060221091009 76
    0x198135005010142810304400d22901d5560759a812080c481c0005801d946c1101c3c10743c15010b1601481210840030302d0100c86a0300c100c040c1403904c0b090340141c80c42e1410705001e5000c2030340c203421402a5640710780c000f80168104900c040c07090001d0074190a04403007088041106000040502940ca800340005101d02d000010701c540a0210308401030b041100c0a50054a01c480300c6102c0e0206085100c1454070041802a041e40d9804018002e07145082c020004901482e40d904400194060407a1205c0100b8484e50b103070490b219032a440280031b9041c500710102c03400c0c0b000c0703051511a03c803580d1025000250840c0c04141ca101c1400303d400e54003005035100e0ba1108164900102d450404c0b210744c2142511700210b030380c0e500e59101054032005051100c0400041e4003031550025640ba06240070f4001c0c0001242c03001440620402c40c0d82c0c00380070602c1c40e01c840114020521925060b560300d80c0041c0003112100803880d65500c0c0c1459200c070030807010084001e59403540061901d10314016200c801041e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 206153857 1250 206152607 206152613
    0xe0d0807021215011a0d0c170a0b13020a1209050c0a081b0f030a06140402041404030c14010f090c050a0e13020d1703070c0209010b12060f121009 64
    0xe0624901c880340c50f80c0c85045802010202441c1003811154290b201c50401c0c1040001504240904145a070a0501d80b010110403103400561003110445180d80b07004455490340c2100044441c580c00c1d0580008015450f40445040c0c0d0740107110050300e50a11741c4818002c7c49052043e2440c10f6000c440d181c03c103900d81c40580c00d086901c4009030001c8403782510728a01482d46804c0400d445410f40304002c16080d403001d41c2c0b03050000888254112109101058100d01c00403555101903400320f00603440c01181100f0481c88046490113143d1650321729462a180d500c8650040d01c5070785400c0300303a560f0340780b031184e629017a0f10a1031070051107019a201028a00020410300d4a49644500126061102001034604056841341c41c2d055040f12212400d85050414055840e0705140b030f021400c00000c14018a660451040480305208480d41d02640e1388885291410340203445100c8821080d11000c20903610701000522124031001e0500c0ca8403158448116142003920400c20340c84540d244508418 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 206155107 1250 206153857 206153869
    0x103092a0501050c03190905060706140105060c060a050726090606060310030f03030f020c010e2b0c020303070c031202150c040b031807080106080f012a0e0d080702 72
    0x41109003003c1d0300740b016003145281c90348105141c02c076812410740180c040080c09410140064a0080e210ba504d03003500e46082001080051084554010762000000701454510100c4101118510260100d601c48840355005000007034000028082c1d015040a03100f0245c0c401654800d80a080910301c03420288031103070602034090140c2d80030315002c10812040f000f520414004407940012948a80350090070204e00518000e6540ca2000f0b00000fa0710065550540001c54144020015a28400801c00010b4400c064011040d51880311400c0300040c0d003030048980038002800075050f640380000300d070b94595030700c03800ba001142c036900003500d0340d94040d41c100400c5056141c4d07002c80810504041c08440e051f40a50b1142d0220680c00100094440c41008220ba80024200080300c40746511f4045146c06012140540741c020300c2004400303d4050014000c1e00082805c20741c050350f2000d1104618545038060b610620180625824840c02c80d88602616401090040c0f407055141c42c140c2c810891 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 206156357 1250 206155107 206155109
    0xf020705120102120c090906090c070803010f06023a0302040906030503130b0a171e010b04051008011a160507090f1103040b0a0b030f1603060b01080408180103092a 72
    0x3410703001d018206d1562181c80e51280c002c002100c40b90102c2c2d03245414503286100f519030041c10038201000008643d248080d41801307640d1242c0954103c8420018013840c04a505085115440d00d095581c1440014000e13502d801811705140140c500382e111703020502999000d07441240c9585c4001500401e51134031000100c090058950761f14541804400002c0001e50703103103c400c01d5a92a1800310303610240b41202c0038421003503490101c0256a40e40e0320060240c100d0702c200317401000302c110503038500c5102d650541c0c1a52003030300d00c441407031003c2d1500c01440d4008060301a03003000c0003000d01c80415401c002e1040100114100402c000480d0746071101900e04c1c002c1440d201c02014814840041c00387c0030140d50100c50340c80c0021b40f0042d4500002d29018a0003606100c1c0c0c000c17604140072000c080700100301564022403050120008032001181e0070502214040d100460600940002035220050000c04480526021401c820039484500c07140c90010b00c441e080d2115494440c01c50031103491480 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 206157607 1250 206156357 206156371
    0x1c0803250203180d0203060a14070c0b150414092b0e040b040216030c0506060f0102190503040f0602010b090601050a09030f02120f0607140306010504060f02070512010212 75
    0x20000c4800303902a40e81e00a441c504646400800865519078881e41903010083c0d400500702c0307010b410320484400040c164080074880980718100003071a030728010b001d1120400d900010620715a80c1c0c20b49124285440c0c165a10b0b8455250034085404200b1401020300801c0408007400410a0009544400d0403221a0309620700365905800c180640c0c105040f20305100b0b0036034000c16200b0350100000c000348282200c1c0c00e207082404d02e12106142c0c3c80b011a24519125000311901c6458440800501150780c500c2c50703005038000f0b41040c84c07030080440003083c5d061080c011241031035202c03806405403906a80110780142e54822000d02d442c83d0100413290002e8080c01c190b80b51201105d4000c02e001c0303d038040a440210700c03450789800c42d114040c2210042c503008007503800c0c05c401b8200a03512440141c5840c07001450310115103031030031070344402c03680518030503101c0314902840c020090b00c01424000c2c014042d800350b48000100350726444030f0045114110000181d03925145403400c4034449000d007001d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 206158857 1250 206157607 206157661
    0x2032e0e010e0a09051207020108010b16080d09020a030b06130509060105060c1c090806010e130b18060108070609080601080a060b13090804090b0306070c020f1c0803 73
    0x4010300d400301410241940c20580040303009603a0003142d0f0b000313440c09030002045e600c40c03448140d00c2a0580313000341600f117200340d03201c510a90740c1c0d86a403404d9008001d030054212800200d07910019100c0c100070308035070342c0e040004243d0444070b03000142ca00480d41c0c401e55107040d00000300b020516046820031400d05c0c0f19003040140342032a4050654031001401294010030f8000340c2810000e0040041c61804050b9a00c44030050000170001816080e16104542e803a00c10f5100100b0f0035600301c40c01034400d00c0911a084040002501c400300340301c0c0c024011001082c1019200c50511a0901005020308005002460303e20f261400003044210303140c1c030001e40c2d034104100501404c403002c02d10b9201c1c160007420210340c846074070f0006400100f00c82203840341586445520300400000202a0080f1b46020408100204c0e2100525490700d000b1214100041c481240b444e0042c60543c207201441e200c0507008081443c02d4840c4160741c64205a003c0e00e001e4000700401405001c007615a00030840c4280e00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 206160107 1250 206158857 206158859
    0x2a030a0e0a11060a0909020f0c070803210402040e0307030e0a080a2301020405030d020705030c010f081b04050310272321030403020d110a230102032e 66
    0x5a040d0020b9198900c510503a07000450f1420148201144806041e00c0201150f81c0c2000c80410155a0b2108041c0c807210b004500340001d4044011055070700b00d507250703140700d44074100a42840502075402441240c1c0a96181901001302c8010070207040860320a40b075078107803407021008101030071000d6071100b44103500960142000815080c0102c4681d5212030600003030307441b030400701e90181c0104c3e08515014800d50264a140683c0024208200c82042d8117544961401b00f00450398a1400103a80011070080400700b203503404c3c0102e040c12500e40c40a034180c10907848200003400c200000032001c00c0c03107444a9201d120080103442929120341110a5a880079080e981c0310f0000003580c40f0340d80d8901554000b0601201010700c020206114007840c5035819610070584912190800e41741680188201c0d0110b0042502482d0f0030700d00d07403a01d04010181001c0640d200e4a80100343c0411801c2c0f02d000e5044030b240c600090000d10300440440c8640341c1d4844c200c10102188002c00030a80d2042c140740740d4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 206161357 1250 206160107 206160113
    0x403120605150705030403021503070f08010608010b0703020c0405151207060e121501060507120914040b060f0c011b02010c080f13020306040c08070609050307050105032a030a0e0a 79
    0x104561400c007119401920f031545814550300b11b00960303001079000b11520012403220406100118482c1e0955190b2180740b400d030601c103c0d03402c10240240c4010803138490050000f000b0000241211303500c2441280c1c90810001c02180940303005031000d401140c803c6510099618100c480c03000c2c65904030b4014041c141ca00580200f8800341212280d029852903030f608211140f090041d07030051a803180c40805956500e0304000c01c142e1044134191150320008007102549481000b00901b00d0303030700b501100f01c54248003042100070194010350f00d034466410040c1200002d04074016061314911500000303203641c559402040314000002e038020859140000d418a20358001c51200d40100702951112020f0740c4401e04880c030800101c401a5142c4100c43c2080200240144000103a400c103405881c0c02e5555003400f6900c21516015440d459002001c061006500c260041d59200d105120884806080780c031140c1052000601d2041403510000108400309490b4001c2031890001a4014031500c10390742c07 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 206162607 1250 206161357 206161369
    0x62006040605060a08010c020d0e010201140103080c030913060509060306071205100e090d0e060f071511040b0c0705060304110915040e0f1504030f12110c01050403120605 75
    0xe1000306050380e00e1002c502c0a45500c802c02001d482507500812120104a401a41c0c450741034040000017404122107031316551040c011315114441c80751401c03001c0c0c0d007143d80e40d1450b5001040c02d5080b502c4140059030040e507a104000303000b469001c10002d080d600381001c0c010340400042c9014080d0340703e042400071040d4800c040c002440008880080c007505d840145040045895003e98000c4142c1c030180690307100701007003403c810103171074032070500000c02032040c0300050180d5160850003000074407204000c10004400c001840d0090341c1c0001b10030040498068035600981c00003865101d000ca90701d0000c90040107480054542140c21605500d0980ea842c00c6103007860900c2402100c8040206a040601c1c091078a00d03103800030400d024003212a001140c1c1c442d40d2030380040c03180c8507808110700030303031401601180602e40641d07030072940e407610320010b6a921a180458040b095504c1c0c94040c0f1500746227000d0246454164008940c504050800a01018200b44280e44480c41c02070b0410440e0389130 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 206163857 1250 206162607 206162611
    0x5061f140303040e010e0f070f0c0b09010605060403121b150b04060512010c031803020606010c05120304120e01110607031505060c060105090a020306010c02120319050301062006 78
    0x104201102000c040c001090442c002c640c403050405040c0c9001162001c580c180851003482da0b003000880561f00e0b100200c600c1ca8907400a0300114455061850114024100d6a40d004503880e002042040d038400c08078a05901c05c2d40240c2d00c0202294806903002c1d0f01c00084541e803e49125115400341494803824981000384040d2610180c0da050340381125140c541005004050080a4015a0306802c0d030040c0600a8002c03000700107032074070480e203e10481b004846c0100e16016030051200ea0744410040d1588405690151464030408000500c8084910001d6105070b201e0807802401902440c03010303052080a141c514103104441c2ca260114440000c0d00c1907001103545408100c0e81210400e0090390a47c3e501300c0c80c3c1081c00051080d00050000522504981064a5282d9141c0e5141c0901c004c0340000d035102400203955014220252400c2c0184180c0b00103a5000d80e464a1070102c0749080b01c601901100c80412004030040001a4120b00d182d00c81c000004000c04210a04010030358440c040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 206165107 1250 206163857 206163869
    0xc10080405010b030604050f0c0901140d170703020c040c0c032f0f07031208010f060c1106030f040201140c120a11030d090b160f030509160308040305061f 68
    0x140800103041c0715094024800940c07028095920604050400315140c0c40700c080c41d0b940922410600c402d903800c2280100f41210751401030303a00044001402c010144881050a5075860303070000d0001404910b0301d005002c91442500201030710b034070302018401501c0c5290078040c1400515107100f40400d4205141b50050812004490401c10300c0d40c088103a11014180d00c04494440d604a20184800c001b0f04203050341c0c020040407040c5038071801e0803141140709000300020992400d2040003498020800c6a40d8540303d03019004600d0030101c045070a64004688010100462030103000965812500034000c1f0071140011514082c02d6a4807165501e1522000741c0c05002c0000e041381ca11441880e58006100865064954464a80c0160800f4142c5d03054250740302d8042c0004241c00c00b40100040030b8000403901c0c0d42d0011521510305400800c00204502d485000f1014a03090002609414902442c880e000c0b0a841c6c60450401910f4444020031002680541002c50410300c00200e48042c102d80c4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 206166357 1250 206165107 206165117
    0x14210a093210060306050105030606030316030c0b040501020306040b040236030d02070e06030d140904240911030f01120501090506010f031e0c0b070602040e0108030c07080c10 77
    0x1030140011480040c0000c90814240262545111607052030f03000700049038090581402142d0302d420416442e130b5010f07188164581d10802014461003151051a544140a03051180e4500603a441e04003040804880403246a54008104003440c40d262103000c10b0540141c60441c280343d98100741c881c070214100070584039144600d42420b00c06240b141c001e800e41e480a0103541c0e241c0b502100103950303080c00740108104454200000754182c2400189608030000c21796668023514402000c0f060b41d9880300000540058071400c5203029a0021a01c811068140d61304111701145004034540407955107402c24104140200244800c0d09910b40ca01e40c150b840f00b01c400e190f4614a854018010300850700c00411501524000050020f03581000404403801050241101c0d004915408805140010000c1144040100030311145c0000000350807840e100d40001072030a501e43c2c2c4000e0a12034241c1c40503189134400a140092580b007131140c440103100050082c40e1000808000036442c40300c107088102084 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 206167607 1250 206166357 206166413
    0xb1903090804091a04090b060315060604030b15030d180f080303040803061801092c1c03090204050a021809090c0405101502060103060e07050f06090114210a09 70
    0x8078124209815403007008000708031081b040d20f890000c4400c11910140300340182e14038001e010401c1c6000070b2184000a00451a241c1565540951290080d106080392040810b450351644c904002074000c1c61041d40326060200760003003c00d010902c0030780024800788000c0c101000a544004140c1e80c010398850103c0c2e85940e52540420401444203105041c6d00810000004900d15660302052003920a04d901c40e000d02c00d07084158012300b240700e411f104a0380c80221443d1030400022040300701c894480ca40400d0700e01a5400060555800b650480100d5500250000d441090f51700c2c1c40800000940301c4448231f1902a404075129981c940302c8071700139a201c0380081d402e1594050104090400300c01d40780540303070700d640c802550740fa400d0000322007003480d00b403144030b000c0c400103000e50480382d0041c600318061040300c007884400d40080c035807e41403044060b51720720014811006081080320391102e1080700c0384207480e03100300c11700090404d1440b24a4850010049000d0441b04500b98219543c090743ca0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 206168857 1250 206167607 206167631
    0x1703040609050d06150b070b0c0304050606090601021011040f0f0b2d0d1407020f0d050912060106020a110d0807020103181e0201111b1002030408070b190309080409 72
    0x90810185c1650710740c8000600440d401d85c102010300701e040d0245a0710b00380303a03403000003840341880180c03806400780d400000055807902d4480c1880b80d001e00103205560a0314032020211080d1000d083c1c0c4200c1d0207a0115050014000c0e0007078030740051a0a080b00d014043c501104140f0f40c0c4100d103020400c03040c00f0602850344d10305007000c000e2051244205d0541c1c9410040e8250010081459403081103508100803421142c40000c0549038801e81030082d000240c07003400165982d5010748c9038580c1000503076403400d400e08000e0200c10b00802c40780e000340600f0000c0d458613008004030f000e20300e4464216002c4c4031000c038845d04141e4004540c2801d0004ea00d980000302040d60600c9110001c018a401c016003000d459aa281e501004a100323803510304113003040d14020758941100800200250740500804451854280e041001250044c01a00c1c50f1945035034881d4100710a41d000400c01200018495180b05180d50081c4140c0059160400c0359480e182d895081c00d1165100d240d10064581c0c2c410703220 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 206170107 1250 206168857 206168861
    0x30903040803120402090a050919030e13092102030a08061f050913050c071707060e0a0c0605270609030a14060601081306020a030b03030a08011703040609050d06 71
    0x16007074810860b0b80b41d407035283c24249020b000b2034080340100c1c41003011a0820880303000300e0b80209200d5025220000c109140d0502904011400750204190103040c01800d45840c03210080495980002046141048c144107840c115482103074010444002c242c0c004595011050341ea4040c000c3c5130410f056129000058188500e011211f00900c0d0209200c0910a0300040241850a07060b9410440c200010707050100b04c4600315120303441e01100700000c030f001078003d8002c00586081c9540c03060420b481d94075158120780700d01c801c074002340c2d201b201d0960900c88901c05150003032202d407403c01d00c0c104580130910001681100940d0b80301c2c2489400442a031788004c10703902c5042c8007804032184403035181070410f10707002a01d09920950061902245003544182c400718803a145000074501d1020095482c5802503104041f050209aa11a03011420381e41c18402440d9041784c65480c02200c0d4100b09600d0703540103100b840b21007581d00c1000100080e680041013002219411941403c8000d2207043c8a00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 206171357 1250 206170107 206170109
    0x3030e030307031e140a09080d02070b09040504060603080403030503060f0906010c0b04020112020f0913060b1804092003010b030c010e04050c0d021c14100b161718090112030503090304 81
    0x15845c00c02040d86400305501c4484801152040c00c00c880703a0216100c01070b81c441a842c003400704242010008180305003400e400c080d4010f40700c2d4000081099036500c46e00e20383d420507003046000690020601c05e1901d0943c00762000100103c87d03080305402c058001a0401c081c40c0c0c40100040800f200013015a1700500e10300001c07270001c440c10340d41c030034409560070903d41c0310219281c890a82d551840c030304403406100341c2050741c055650305480d118011400d0704090000643d07155106480b600040005880720500481a00644c2c2c8000080090341c800c15084d2408150320307a01a50054200f22aa6a4004038129a280069400240c3c0c0d450f50000300c410341c07042060ba080001e00004400162a1041005482004940104110015421420000c0c40c8026100520105a01c607018000c6005003002013003c02c00010180a08a10950b40c00424a0201c0005541d485d000700390012080958000c0f168504001c40d100c100a43c18044031a2a008481e007001d000c10401000150040b0410030440d0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 206172607 1250 206171357 206171387
    0xb0f10030902130216230c09100f090501050405130519080d060b03060328080c0109020a060503090c0409080a050903071205010923070302060d020904090c03030e030307031e 76
    0x55601c0c0b11710b4070030079002c4082c100c0860f40a00501c415607080217003845140c0d2402c2107203020700701803401c001c10082c2d05940070b814008100c840c5200003a03440041b00c1036034002d0410b070602103515032400d4200012500010320b0b81024101400030364000a00c041215512a06441c40740780c1e8100c0107060580641c01500c010009907483c017030004c01c0d601d4044010798810001241210640612848018084401c5200104914038000395640008001d10050902d401240b40005086ca0a0b50009052028540d000c44082400041801010501440420403c070130545051040d48090340d10503240344101c080120070000040741448043d81c060103190014100b01500a40d220214180ba60003411241012070f0304910700c031002000b180b04001046008100c5401808403207107181c00380400e1750712002c0d00120503039080200d02c10b00d0f501d51145070045030107038588550490540c038010b01644088400035100e0f910910902000aa1051181880000707030b1405903959640a00c0681d80c08a01c44522 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 206173857 1250 206172607 206172611
    0x601050f0c070815091504020904080c39010804060207050109020604080312160e0108090c0d060905070503030f0f090a090c0c1a010f090b12030c070303030b0f1003090213 75
    0x507044400114140c0115a40004448175210281c88654440101584055500410b000640586005910b541d07009000d8210036140c6500c19004a040c000803520a00ca4040084600030342c06144070168042c001c0c0304904100500e0101c00060100c4e0b00003003005001c55000900c1c1c004001d802e40201d4101c4c0d0b0301400003900c031911541c0054481d00004c0505014041c0203000680303542c10380aa440002d01d40351155503001025100444546000600c00090703403141e02c8007003049484110030302c400c282c01a0030014944400d8078189043c0906540014840c0e401401040f510343e0365030044842291115000d107680b5068803020610030140c1d94803031444a0303d013841d0b00e202c2a40003161050710500c40d0010507042145c40ca0a516444001e0054402c2c0000e03015091001c0409030f807000c2c3e2800c50082c41d1900b0305010005141c07440d48552804400c81e00b02a004004054260040786000b200c11160300c01c81d0300407e008203c1e10450103041c50200750702c80b000a4155160f403006011141c0080e81d01b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 206175107 1250 206173857 206173859
    0x20603010303020303040311070e070503060d120521090c130e010c1d010f05090f0406080a0528021e0d061b020f0610030f0c0b030103051608150601050f0c07 69
    0x4065245e8104840c00c2c0c02003082c6954031501c003100411400c080c2c49850b4034440c0903407220341c001c80705070300010040d6420980140da1100802c4608203040702c1d0082603602c03583d440e60008446803811550030000c400e42051001401039101000c00d400d0414407060311310302004166820440003400c140007007480b030b5510340100e014401e940007180a80406480d0b03000514100c4003401101c2500a01e8200d0300081ca003407019552600e4508102c403284000240701040c030035155504039041040794030341241c180d8081c0501119002e80701d09802c50b00c510364980c00d100300f00942c0215001c070072511107010080109020008a030f80c1e9440410009030b400c070004101461141003ca078000d1001018a00136101e00410303619040070010b1140e10603240044416456441c0d55030314110036203101c0d011180044482c20100f11305242401442c000e40c0203a000b0816681ea41d00480350714861031304001c071150000302031440c1115800c06003e030420806e29116a444540001d03100035400344552818850240d000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 206176357 1250 206175107 206175113
    0x40e010b0d0803070504150305010302210a0602030c04030501050c0307030c080c2d03040501480c0b1f050d0210200a0c0510030213141807020a050f060903040504180206030103 77
    0x10227241601c0c802d55038810001c1c140201240701500d2640656031aa00050b0710000280c080e402450f001100e8100382c80c00c2c2a284c5e81c3d55425184200c408842038800481041149540742c0104000d002490521404038100f203804160a0300c202c441c68600d034178400c56058110f0302420500282d451008d21155103905051400ca8044c00c00b4504101c409550070245440c0f50815580341442c66070740d031007103c44003e08007181926214000c4e4200b420300120b40e002101050111a2051103054001020300b40c031480750b54075001e082d030f913500024041c904000e208001a1a4108103001cbc1c0c8160b41045a103003040d10803245038075120200305032903501401500b07104000c60840e102003601e20482c1c0002c40103c400100703e0481c0200d5850611841140c1802c000b50b0f810b26a20026428016100081d0f81c400c3c40304403043d20f6000d4550000681c0500844402c0c01024040400300044940c0504a41c0c01c120841035aa40142d028151140b0b5a039084110380300c21000c1c40512b02540905103948035a0760b41 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 206177607 1250 206176357 206176361
    0x60506010e0d0312110f04120804030615030b0903341707030e031227040212070206360c09091f060e070f050c0703060b040e010b0d08030705041503 65
    0x280344c21580c0c00c1050500510320340c042903590103000074000e10b04041c90b00c05da04104980e00c0000391503207001003101201144c160f029180d070f100040404800300302c4c51447c00c141c402e54001c0454865030424021012500c00b4042070b019200014400c0700d082e45c0040310101c00c3d0141c04000200701c803d00303c5440d01e480f11464040d140f0305000e52110458000f07514241610b03400c560314a40300c504010048185040d690606d09007414001041c408103004405e4042003c980c8418110181a00100100841c01d5030421606901c00201c000c101e1004003412070500000f02c0a03040d41140c0b174080081803d0703060040011070594000207102c02d2003800d1940700c1d5034460009994114154000d504280d0f803010343c50080008607419000403001d0b90381e95a000300e03160005034074814100300c02041008000401000a0405140903220014883d5015800c000444d0440402c860869052900b40f005980c5da540c040e02c01140c00042d00c540c1d03a5903030351040701e1b98803480c3c11070030801d822a100c00000b5030b40b603 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 206178857 1250 206177607 206177627
    0x702030c090a051512030901030905031905040510030b0f0f0607051501080c03070f06030218040903120b0d151802030d0905090a020c061302120d03090c050d0807060506010e0d03 78
    0x550071340380f64401c1c00e200e114061200d10042c258410817116003a03500c690300400150b40100c06890900c2070849801d02104e1014a01400195012800b482180ba01d040903400840003070404100c0051340c88081280c4109642203c0e110f0f058113140e001c034036200d0000f01c071210355010050b2840030740500000c404e041020b0107400d00610442440089500b400581170f4181c6441d8803281705268039260045010b0750140300b601400044419800e41161900d008110103d442510b4035040b490f0500b44035004c40300b082d0780c128441d4009042030b801040200b43d001e40d645a90880104030044107501d055203001e01014000d4040c8a002036103420560302003105015507008440401c49610b039801c80e0400e900405008410f40d40041011520410f565a0586509132003d4845c0702c00400078500941040c500e04d0320784020030b4954101e4810041015000c81c0649400c54803c100541c0b180c4a000300c5000d143d40c01000342d55288045803203680218040131010740d00901014000c0c42604e8014142005 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 206180107 1250 206178857 206178871
    0x1031a1c033b090601080f07030908041d0703020a0903021e06040308040f1203270b0a031413030903030c110405010b040e060906100c0c080d21020a0203030604020702030c090a05 78
    0x1032201c2d803003103914150500500601059480407595160b42c0d0b0030f40101d0383c0c0600003005243e80c40711614001500b01e4080c0008202020226480240c1007262441c1b80800500f0351003018410000ea44d030701da4210003900142c1e9019198401491a400c0036951691890a082a032208011030b000040015080003030060718401d01c112401144d035a5441314504221000c000c001c6600c00070304580fa600c001c5084002440d0500041d4259659032480700c256034080e034640c0000a8035505003000b900d00181c030003504114440380088441d815034500829442850000038100f1075440000c0c1c0170b10011300c40c6032900380300090042056503512119000c0c5580248150b00c105c104100000d0443c1ca0130f11001845100040c081d045030040d0391900320361821544904840b10302080d94041600c1100b0850004003100541341d0014007094202902e203070b0749883c1c603441c103010300410541040da07034044113070380d00a042a1005a119641d0340300190409405010f03282e0401c03803c0d02080250340b4103800042c02044 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 206181357 1250 206180107 206180207
    0x170424060513020a110c01140f07021f0f080402090c16050102040b0a1403130b0901020706230105060309100b010c12080703110a050910020a0f030e01031a1c03 70
    0x4641c030301094841201c59606d6011400c99210344007800540c0004005201d00366904614052055001640321034607a01c00e4920044c6852203030450913040b580548400017141001d001c0f030719040d8002108920020003a2041e6500852a1080aa501d0072520340856210b0001d64550fa16449801140e4100002d0350000910390700e1255600c24440c0d0482c1e0140100e5142c103010011145c890b5604448007818400c81990708000d0740010401ca07210b00101001c1150301054035006248001d40c400030306811681c800d603020014030055210014088c0401080fa21010420403803000040c5d44100c400740002c2c0c81d480141581a0802d980641803070720070056514100032810b03c10f421b0010310f0241e800e0171004140104031f0440701d45841b480307a600c2310a17640b045903113100c0141c1c0c6400219906402c12404906c566035165610747c2c05028410500102c07036034100d044120700001070403030001500c030080c4000d2002010814903224504400c502c0c0000a04a1056080c440c42c84045a580d1003628bc0c4620f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 206182607 1250 206181357 206181377
    0xe0a050703080c010506010903081209070f0f05040f0b0d0b0903070803040b0603060702070f060e0d05012d15060e0102010e0706180e0c0405060f0403050703060c170424060513020a 79
    0x50b018003211030a030ad801040560400705001200120284c02401d005001c2c450b1000001d010031200c80c500000d0606040f04050403440c000602059650b5050b0410f0b6207414075040007640e031504029030342103d402c142c104029407038450041c1d0451103a604080d0000030004100003d020000850794084d01066089524a1340d90407412a01d5100314018030802e40540f18040021521892034078180e400014807011b9a44207a6486a007141c041918a80c08a9409840804081c0107060988120011b507030f014000300c0b407000c1e400180852a8010201804411007040380907034400d610904031406800116003030140c81d030101130f01e0b49101c824075120381c1241d0310001c01d489500030000b03401a03c1400d644d6081500304020000a0b030030090141100c14000c1c040000482d0f020481d000045001da41c2c002a039101206000b843e5501c030110509031402040284800100850440b4a41070407a44100390032218580f0041e01a02984e488190300100c104d840e01c4031400f1329030061000a00f03a40b941d41200c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 206183857 1250 206182607 206182609
    0x1051002070b1b010b040c020a05070608010b07031d0a030c05030d05070b1816090501090605060702010c020105032205102a0c02040e03071a15130e0a050703080c010506 74
    0x5110070380100e1509107410700545490b640d41003840e9000d500305500100b0341c8900d400100e0106c450340403408005074068001001800b0061100f01d01804051034a08015030400c0741c207040d0380c4074a0310005c0800000500402d01e1003400c01c0800c2020700000c0c1015a45035881c141000103910303900440e8400d024800d6100e990b24011811102d0305a44098000002d5466890000c42005040c2112840d4000c40e8041420102c0c4a40c1010240180060018295050008000031034015400c0507005100070443d800143c0e13084800f21010b10341c24a0036a68a50314503800050280c840e06100790724801d0b00300118200140843d140c1002110700d070040150f02d030180180241000400c60905c00c1c1c07034204001101aa01c6565220740c0340f40040e00c081241100c01546501e1540030f0902518914071803042540000014110303140c0044444050303000e907000030340001d000c40318400b540612107503a900807010f0203a418882000529009001d40701c0040d030740d0904001e02c2c0d0121400c000035519200000e811 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 206185107 1250 206183857 206183863
    0x4020f22050a1415010903020a080d0806010f0516060b0406060903020f2e0512010608060f04050705250c03050a06050105030619020a0905030718060f031a040804090504060501051002 80
    0x8030220081100f82e191101c1012090410004204070304014507400040301503111200c2843c001c0510070000c0c0240c0c00429001002c1d40c401401c864100043ca001814401e5406002c1c2d031950401420f0724540c01004d4581100100502004203070000d040030400124103030031480e1002128000e40d02010f084125500300100001c0f160100d07c50301d04080c1401c2552046442c540f00c2c250744a040c9030b450000b190f009000300070070981c007080008034210204405820000014000c1c14070540707091045040091010b07180e0300401c5003141407d004001c0f411903c1d0540341d94888444d8118840102152f100e06000d034032402020001c2d900c09050200000e03041c100050b8452084082c01101401460091005000380d40000e1000c02004040000800c8030380d0144500d200070448121442d6440b0f090075082015140f003a8400082c1e0402c3c010304002048501d0000c0345400040d810003100350781d4a1918a030742d03005d9a0805e595062a080400c0708020442d88140d040c4c0710b084490000301d00078118201d036 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 206186357 1250 206185107 206185121
    0xf240810050130050102040e041e0b070c030504030b0a05040209090d0905040f0b150a0207090b090c1c020d090b0f13030f0306170a1b0f0e04020f22050a 67
    0x204000f08550707a120300107000340d802803141010140500281007034440c1d0b401d9802640001645c1c0070f040c414401001403d903811100620140c000c000144110380f600203040c2d1000b4049820720500c1d100050406204508403030203503510181c0d01e8294105a000b140c0248000c940c124004e580c1240402c02844001642d003402d40c03d40d58903c151175040c0303030a0001500c008240080c0042d10352084480b943d8880d200703074002030154402580c91740314410000345841c10b6607200d04480c4e85441c44501c030685541500303a9110403201001a0703905140303240c280c0c0f801000516070f8003051000c1946d4281c2810340d0440c10340b6a00519000c540b0b17440b2016120582d203000d0b00c0341c288031b60f1280f20b580300007400b0304d10f16a08803a45043c00204255104400e000d8240402c500c1c0407540c201034200004c11030700c80700c10b000640704103c2031043c01d07040501d000e0540c481806210344250b01c1e100041c04543d20500c010718a01e20180001601004481428080c43c0902803112034140c01c10000480b03e58a600c41c1003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 206187607 1250 206186357 206186369
    0xc170918091e03090f01050408060a05040302010b04090b010b09150d0204060e06031306090203010213030b060a061707030911040c030f0b010f09090e0f0d120b0f0d060f2408100501 79
    0x6180c01c4d4414104100d146000a40f64140074003800000348a04041c0050f62007039002c0f10000c24149040d02d002401c4804084546100c1c0c0c5c904001c0c20040f4800c406400d05450917050759503074030814200002e20030400e0300440038000d41c00051980f2545503e4011300102c8080b81c07900e04480d44583c04011003408211016200d01080031204804a0b03125040305940d580050300041c6401d00060f03842000b00c6481d001621704046100a101590406800c120018003051605103a03035140300d00511070400b070281001c005c15484000035424803000380c88074280ea000080c0204500c0c03c250134058050002c64001400d01e52030710b600820194001c0e88803819003103055445540150800451500a0034030410b1440c141c0b0030341c041010304600800c20360b4a01a001d44600d07041d00640203000007501c04034490340740030b40358861268100c1e032075242900900c01d502c00c0b408196004080ea260b40245036402e004400259031a001c020010f998059000070307200742505a03641041c4562a4070180e170000e210350 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 206188857 1250 206187607 206187613
    0x506120a05060d0203060a061703071a1e011410030b0f1c050a0305030103150605061611190602010b040b06090103090302150408040e0f070c170918091e 67
    0x510300c400315a0216078000c200503c1210b0580440e004203180c1042202c01003000740d5584010301205210207200590b030f0300340314015031510a8594609902040c48403061410746042808119051035850b2402c021985040708005a583d44a001e03c80260315909900c0c0602c54500407880258401c0c0208403007030384007504c108081c07100b40d024845220840640090740007400034030140000d00602c80c08040038002d43e82c841d113a50641c107218582c0c6c940456584401854084200f01988a0f4010ba4005065200080008a074541440c1c0c000c101c10400c041c3c1e0100c403801d100056410000428010744603240e000700004031052060004031200710307070299840702003842081402d40c0310b0740080250300d100b0b1054480c280364108112000300c00589d0106e0349007001103014841031070523018155001c0e042c403130f039034243e4144004080c00400c00fa4001806140d08025403030410280001142c4201380c029190701b9810b0850600e9101d12601a1120041409103143c40314010700c40b04000300e8440060b0000e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 206190107 1250 206188857 206188861
    0x111903050708060904170a11011104050315040b0103060b0a1706070917061f050d0f06110906030a050a0230070504050109090e010f0e0607020c150d0e030c0106080a0c050612 76
    0x4074810b87e004119507808002203c0b01085208a00f03009042d100700c180c640054449003454101070038000f01c0305040c164902071800b0040460316001e919411650400c40c001075a882030750100fa24100c560704481040003103030071f003000d6010300003070140d101781c00030341e40c15036100c0c9c0307810008140c40000701401910f5407062000c9810740c000004a070701c0310145041880080c0ea40d8102183d108219404203a030500c05002800d820702c096401040e4030500c0c00310034203240080d038034009407960102901c891000d03035450000842005541d41291590300c400c04800004c0b03070a4514503035810407001d00200d0220a1600898507050143e4251026600705864004609080a41d100c0003002e5082d42130921b5900c450744030040c0c01240c42041d0781703c14098080c101c0d500c0e1109e4040d00c2d00901078a0f040c0a01081003c0f017008081001c02c0e10502c0e540e0070404100840709000480c40c6004400606c54654071b0800001051a8001066162144107001010209642d10108800c1d0300443d8a045214019040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 206191357 1250 206190107 206190143
    0x30314100512030904152409090b031f0b1203040e060105030403140a050d150f0614040f080c090901090b01030f0f0c060905010212041503111903050708060904 70
    0x8401d002856080c2c00c490800d404040042c003034841c08901d00c0e000c0d0a0301c1009100180140c41914450b80d408401082e045007060301c014030b210b85520940c3c01311581c0e40d400944580d0140311150000c9416a036400703100c402e90340d2050081c034090084601ca06052040300301c841300e002c02a282210043c9042210941c0e41030010360306648002e2040302000321000c10318070098454800f0f492540e0465031450780301e42c10310595904a4000b80200d0000407421041004039001c2d0807030041c1a80c44910340076142500001c0c1d02c41d00c1c3d006135089400c81000c103100201e02c82e500052108404d040c00c480c0c046d4a0b403140000b1608a640980014001c26060401031010401c01e00d69041003900c250a1112041280d0b1140c1c00410701981040000a42e501010461980c0c100040401504d1418541d032505180c200c0702410504258103540505d0386a08107445030401203401e441d032001c840c40c02002c0e01180303000020028141280e40c1000724141001047c1c450500500c528800da501020301410780810351 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 206192607 1250 206191357 206191369
    0x8060f0604090206070c031110031e0c030b120f06010e151c06020c0109030305070905130506010e0a03120f030e151b04060c020a060309051b01020c06040e040303141005 74
    0x3007090b40c00c013104110f060b0015010b050300800640c000c0101d2410b60508504200102844521500401d4245804004e615121000110926020303207000683c10020281c294094a0302d11140350340000c03c480d40f0b2501c81d2000c521010030006403001d0b035040340e0b25155040700c00d230803d40d007422959a0b195944a540d0400040400344c08010900b090741c81b0b4455a1282c0c280d83c8041a108035170b0b5100d075940000c058050262507007140c1c41d401c1a0080a0909010450400c00305400e0030b10503171508007146060340200310000c0c41c030001901c0c8201d91903d9062840c0b11401e5941345d00002203000a014035407503c60310801080803020806002c44002541080c640801c0140440d2454108265800300d08910079005000500d02521041c2900440d40100318070300710301d54010014141000003000002e14086a05030381f404449009011007104c0d200101d00e000c6500164075001080010b010490448926500348030b248240e07001d001c022000081650084000c1e10b1040c0045002c4c002031229207400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 206193857 1250 206192607 206192621
    0x1020406020a03030e120319062405220611060901050402060a050a02101a0f0d0b01061d0907050910030b0f0105090f0409030503040311030a0e060d0e010507031508060f0604 76
    0x4a045500000c0c14091b80d151030b40c01070760440724051104644c0742694603580507040040c0001162540e050140b00b0b282112000d01100d034070304018000540100d41c190995584c0c4560359240091a0601d48510028103031a0380851003440c0d900c079100c001142c030354050040302d100d142c0c0500207500780344920000340c603a030f00504044415030240c001d24241c942d842c0d100301010320402c1410140c1c2c4100c503900348290814110103082c09403841c055200042111012141c0c1125502e01c0c2c0034400000e00c18100070301200840301c043c0d10504803000c0c1b205441d4030002500744440200c0d20040c0303c82441074141e00700c6141c0784406401078240b01c1c44209560184010300000a400b502c1601d00c09100c00000c0c0844048200440c042040070042c0414164000421169a095107005516290400304081c1044220703080c40340c440c140000b0380b43c150b4901030f00106207a17941c3c03c000b80100c0c00d01e610041d002d41030362a204409009280c100041802c00041d44500448103a141401240c40d09002e2101030410 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 206195107 1250 206193857 206193881
    0x40f060215090f0c0d11042405031501050609010909050a0c080f0609190e0a0804260a020f06071209170321090106051305040605010e071e020c03070b130801020406020a0303 76
    0x1d01c201c405240c4803409840b641210b2120b05c00310381c21240c44408c21100194102602952042c280e0781c800d98400111241034074001c076111515019000b0040703402e501f403600200c000a042c84240004041290403100e0507580c0390700d44080303642e9078aa11449114003254000e610080e80d034085110040c031501c0d415030140034048081000ca1840122074030f4800c1c1c03044102c070f400c403001404001540c08091103056000c42544085050300412200c2c9585002c4c4400181c820708800018502c550b4070030086440070359100c00c07802800c2d414610081d000e07501c80c0c0b0480e4a100b20b5807920080490001c001c860b100c0007803401106581890340c2c01e81c08048030092408110b5036a03984e001c41c543d030b036a103c40c811401c510100031605290600c0e140c000d0781c0c010b034010903d0212000c00d228820b07030403d01c0620350b40b000b414042030b46507204004230b241c11051002c0d103415008003000030601091500091218032018401059402e85e01d01002d801c034804c501c076900058001140000000c0d10a402ca40b002c140c0c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 206196357 1250 206195107 206195123
    0x3070b0907121a06150f0a090e090f01060510020a06090f0f1202011104030b0f130606060e030f061005090a09150501031214030714040f060215090f0c0d 67
    0x2d25840c0c0e691444405401c182d4462105602040300c1140e6100d981c0e600a2003922a1303004682c400b52011103600032075440031350400c00480c1100c1b03458411101c4600510b01000b4001315820003015240d11915485a485219420700c200030405041024020825043e654000e00c0300e200d190321001c00800818108881d141d0b158020000452220b401172004140a0500105801818900642114020b203811061020240700400106540081c0d40d0f0340100750a500c000e0035599001a10190360381084010426860b04002040e045c1d0320441e09181550280c04035080464203c0300c4680d5030208441c20b030600761400d0402c1c01701e414410021500200c00001c046040c00f05d07036a030b0072600300e80b14695604d03c0e9600d80041003400020100c5041046650078510581d417001e0400d0612488000d008109100d01c41c06044c4010131060115002403220b80c216800281d10b90300001e460b01c074000100b180038194003001c40c1410101050f00540210010010701d00f0702c2c3c520090008c003008900041d100b80c1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 206197607 1250 206196357 206196359
    0x8060d1a0406020a02061008071701020c1002030114010908070b0a110105130201090504020a170613150f080730050a050d02010c020d020703020f0f10030204090f09020303070b0907 79
    0x605440c100340d0166104450244e16004004402403034650010075203828002c10346020001c60b0000310781601a2040d2052100ca600d816000c218068031078039a803644a4410f030354158040421a41c05541613035141c004486520040400440b071441c0c1c00d000c0c0c59031640104408121500c07910004215066060800d90b07690039a100401d400c484045038010511240b00302c1800c1150707484140140608001c4404604103011a60300600302c00c0f0100502c9426221703e00800d1460350340c842c07546083c1100c030000340300b4000820543d41010040c1d204082074500d07401004590740c9400315402040c0c440740d54615811100340f080070707060000c0f1501d00b0006805807040300c101066083c00040383e00ca0058006160b02c1054105c000d003140e00c075042400c1190003542e05104429404104001100c2c2c048a2500c120314051001820a0010551465116080b03009000030b00d80c040d0090011154050301c20408084036880017004e030b8888010003913054000701f00003000141c00f108071340c0d044158a01140d00711 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 206198857 1250 206197607 206197643
    0x90f0415051801030606090c0c060b031011090405010902091e13020d1a0604060c03080924040606090902060301032306011806051206010b0705010b19031505060108060d 74
    0xd224101c80070b0900c0310000043c0700344103150062200900500c030007042503070081074009204424020004228a03102e69146002d55820003116070440703911030007000300300c40380030780701205600c022582806242031400000d82e4821a01c2540e00710400a04550450403071101d000d0a5100c080c103505601404000f00e04104011500c0945014404050000788808195608080c00c9260000003413280350108800d02040c2d52029000f040c49505080c15446034039800d0659044c00000e0011a400080c0a02d03170b12a011036400b000340c007580c02020204061915009000c01f40c0343c1c41c0c030011390402c404100400004020990150603500499041d800804040030321038100700087c0d01841c5203548a0342c8480e801101481400003d10f40cc45001e07241580c070840d4161280030510566405440106105041c42021b410a2100500c010b0007140800781c408603002d044038039400152020f001000300c85c1c6490506118950082105844064036a91500100582800d105c001240c4da00e100402102c18 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 206200107 1250 206198857 206198869
    0x1c050f071a01090b45040b06100201061d0a09020d080306182a0c1606080c121906050301050415051608040209220c06020d0203090f041505 61
    0xa50710003840104100d514143c03e40080d0b03285030140d14401c1e40503401400c800e100012624032410a9040d0701c04100740b0007640303c885680408803c25071500a04100300c100a10540018400c00301200d020225400220089080718580d02542c0243d400541406519600015035540d0001490780c001c43c0d40107255010034246001d4110481c1d468101009000c5680381c5803500321204002660a0303102031070405501e8944405082e1030003000f0907000c3c5003100d008906011a50b501d0000c0c0d080350402080080c41c1c00e141d808911074180007440890100310b148074046c003110320641c1e121408050343e440c1c454804200d40c0c2100101c000040d030b00c080c00551a1030038080d042c82203000300618180c03400c1d0031315000280e50380103000140061119034013901036600045403c0c0c100d41c05461a51090307407240d15894a480c80030402c9005d84450280c150104080080c070a000d8429560940e41a0801000f040e6500e00031013042c1584000052105402824541d2000c4d5a81500d1200c1e102d0141d81c0f0004590 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 206201357 1250 206200107 206200133
    0xc02030c07230d12081305030306041104050904031106060901051e01020319080402030c030607081b0d09051b0a1206090602090a080d080c0a0903080c0f0607030c0305091c050f07 78
    0x42e4031664031020700d42072900700c10b205034086d040c029581000d010a81d5400c0d200d100050003148515070342d00302000003049030010303100540300250400d4840d080504003c0c11a2035020045001407040c00000b4901d4180603d25504858025160001541c0f41a0210008109a03c1035904600c400d102c0c4036103092120203900c40106640d2507607c0e02e42007a0042c1801c7c050034010003800307035112000380b1104607800221a80d00003907040031004081c0d01494031181e18464001e2000c0003a0525013600d0912901150301c000da014030300300854a88084000380500000b07a48214071642c140e80b00124040380c45a04450b403c0c03841010010301d003624403000600b906100f908000115132085000c8507016810002e12034021094503401420a802400d00400303160050000821003c004110030301c6583c01000a50485001c100a07207240386031281e4010300910521211800281c20800400e030060340c04955607010182c503c1c00042c2440c521082541c181c0d0295028030391000b810800c0b000801c040c0b000c3e4035 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 206202607 1250 206201357 206201363
    0x3040f060e03040f030c08070608160509030a0809040e01050402131505090c0405100809030403120c05100f060b040b0a0e012303041101211e0f09060c02030c07230d 72
    0x20b01c4840c290b00701036043e80000c2d0003072180c1d0340c081002030062075088561950700bc4088848000c1c0c145e90180c1c201c7c0c16008032040140c1500c80c2e40e003190304000100d0007038248264290b034200400554800500e00784d49090f02c0107500a42c020402a0f018107003030300448180d0b1515544d031040982d40e140170034250a01283c0d1803c8021000c60140028604034101d200b4140403840d0402e0135003030540d156501da10551000800d0007222100098030706001d403407540d403043d42000a40702180100303071521010b00010030b140306009103880d0010400030402c0f0155420394590052650a000703e070b440941d071400c003100300581400702034820b40b00c2d000045114004818240c4860030f8403410a440c0c2281e404103050360550500c01a034681811540100d40e0f03944079003214900104148083e02d001e0040b40c400c1c0c402c241d044508080c0f21070754101054108441d080c1c4500010010038200c081c04a0b124000c0c1d00e800381175074001c244100500e2006010b48008403902e9141802240052130015101c00083c41d012 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 206203857 1250 206202607 206202629
    0x90b061009030c120b06030304030302121c05091b03070f090509011d0114060109120b25020304080601060509010c080d290103060b130b130302040e1b041103040f060e0304 75
    0x10342c05c000600760b000381c1220302a0b000b981041d04640d80a03440f5083c80c0484d81318218081404100f8010307030354200038558080c0c1010055820503d11071a00c418210040034506600c149502006040019208044501c100ca200602904040c03401c1c0c0030b40b20203042c8518940d01c41c0c04082c1c504100660212502022100000f44154141200316481c00002e100700c0c18012010030800940c0d0b00382d0307000ca422981c01800414150ba070044480f00010301d00c00c071042107000c81c00c2511176281d0008014403e41e0450b070112055a130b80e9201c211080d1040c3d00d040f50004032801d01e1031002800c00400f501700d060203c0703008160307429045c0b015209103000302c8500007414180c1c10000140d50301841250003a140360306029242180901c0106a00d102601c82d0160284000480c48210006c1c02084800340d98001c1003405420f010f541c0c5103170b8500341b03071b50100c0c01d4003442c0600c090301c0d113401d2141100422059554900f1aa21601e0b246501903030140c041d54a10349404a50351154030601c001c0024040360211 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 206205107 1250 206203857 206203889
    0x302040e150c09010c03030b04060f080d08010801180201050d0608010c03060e070801051f030e0a060203010609061806031a0910061b08191101020d020d0506010201090b061009030c 79
    0x7030400c0d003040a4480c6184510401c01c45000341d078051000d0503055054140820112000c0c5c021500418056101080440740c040001c580600d011440141100950740d4803441641c81e50341d01c5080701e00704e40e4111310020040d407940380154040c2011700343d10008444002882a516041d07135003900c3c010640280065560780040c4480b00c40b00300c407031f0703000056440c00340c80301c1d81001c0100b14000300003d40d45120b4800c01d0301c030200c954469004010440029400d807102c0d8011407501c03001a41081c02400041100440080f40c4140701c0c0000c182d400c800104d2a0302150302e051010f40040c030303807a600741080c100e401500020319160024901d008001d624103c584d02440c0080051450030300030548611540f0440310300c0d02144451090b18009032825000c80e040350b010b0042500c2006c65124076190035400414603600860380341d4040d00d0780000f010024031240d80c6650049080fa54031010041c4019010804201c2a0504c101001c2c0910303c40c0c1004408151640c0b210000301c41194400301c052214428 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 206206357 1250 206205107 206205133
    0x20d06020d0c0f0206040312021803030d05070f02060c0f1c020304051e01060b031801200702041a06030a0b010e060f1e030103050a110d0812070f21090602040302040e 73
    0x194450f03050000c0c1c40908200d08140d0b400928444d4907649907000703260040340402c81005040c11040c0003030300040c22643c0d20704071000d540b400740c81e04441d4440403840a00c01c503480e481c000310351180305503c1c4000181c40e00c041c1e440614a80e8000031000820a291000d001411202c544002c60155025400a202c1503d90412010154580120312421641405010010103500300140e0781c00c1a0781108280c00284d1250616005001222400c0c1490040b0f5031441500c00502000740170f03160081c1e50901004000001100032003814a4805070000002c200250325080e6592040141500514044180966100000b01d07103401c41409240e40c120001001c000c2c940c0c1c807001c4000c1104600c41841e04640c550f445003602e60b151400050100c000000c2a0001c6030b403a020410131441c2c1c00b010039a240c081e1000103241c40d640890f1298045180103c41184090107010f4213181021010f0080d09030f155030900001c0904880c3c6002c9440e19002d0001000680d42c07401007000e0810303210b000785441c0c403a000e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 206207607 1250 206206357 206206367
    0x8030a0c020304180b030319110f070308030402040b0d020a0605040905150105040303051309050a020703020d080609060f010c06020d0b0a0f0b070602070317071e18030f020d06020d0c 80
    0x1824038019540700700070030440100a8000020310500c03059000a00031001c60100382184202000400e1200b8417660b4445207030b4000c080301c8200100982100c4ca6022018000c9030380f411a0301000c0e18006090001400514180e000340c029a01e028000601103101540403800c2e8204981040021400105003032003031442c2d0344120303503020b0b00b854640e85804055400180c2035125a00000d420081c00250170759200200e021000000e01c20400d0800262400f48071607002908185001c4005018800c01c800701c03a031180c1c0595006036002420292180c40303450400c04800c0240400380e051007110500900400d03a1440981105a01510003140e28845841003091001040d0004100f0000d100414005c11035040265aa05680f101005aa824079070909941049400801c8503e58140d6000c010500782c0c4410342c04044000c40c0746801e03a181b14494151500140500d140d141c203c0b83c000100003041c80034080e44401400031f00340c09148c0c0e0164030303004141d07400061110300f10307615040d010110a03808 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 206208857 1250 206207607 206207621
    0x206070210060e0109090c0f030c14030606090f28060e010819120504080d0306051003020c0a0204020721020705011e081503011b0305061206041a0705070c0308030a 72
    0x203140100000b5080c540c41000390700303040c000d083e00b0a5032451404108203512000801819210480d2000e030303540d0b403401e45081081405054076452007a6a0f080040c280040c425004100041c000c030b04a039a921074203d9211401007904011050b001d184051140000403007910f442d6070102c02042982c141421603180c4603040c2e0206100b6031010600b29141a8412801c0301456030007030036502403101828049809000c1c0340c2168980340500c020348442550541d0000c030441d0300660341c24a80c07139845441a4201d0089000c22400c0760401450350b4014501a801403040c0e038130409450318140068082c490602d8980048080543d00000081c8034568000481d115224208080f49100e07120710400140b00035406000c031803420036404a900e006540c01e4000d000c0b007821684820250440e007880040c080c110607a6402d000c2d401400d680c82c20543c01040c010b2040750802569407443c102406521120b5100030b003080208031003488450b00084d08041100002c601841520340c50341003071034100040ba480 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 206210107 1250 206208857 206208883
    0xa05010609030317090a1211100c1b02150309030301030507050607021020060c0d050c0408060c03040305070203030409090210030606080106200d18120804090902040f090302060702 79
    0x140008000091344803420502e03c00c2400c0d040b1505071508404286804440180107240107102c042c0340688540c407201801c1000d400c442120402031b408608a02200c1c0c1c907425601c00989044403546250020404280119102504030028040248981140ea0300140c0d02c440f1940c10010042080c410304008103806001d0445500c0c1c038200c40d44d4002500a03040f50005010700407070440301e01180d15006074030088440b0a00a0300c41d185418101c000361a071103400c288036180d1030540400c066403440015101510030403c0104840e0b107a1200d450b002d0f80004104608216041080c50010b840c18400b9000034071000c503003c602464507104001d0300881003a00e40c0300b090310744101008065400303a0078504507004d03401d003031244044210300d03000303943d5195041a00502c2030a11086080d5844869601c100d90740808126190381c5445002420040c0d6640150402c001440103100941e855403100380c14920003000010070108565858068034500002500903030040c1081020443c0c040c0202c80e01415 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 206211357 1250 206210107 206210117
    0x6230f030f060301021b01060911070503030106050306030a060e010b04143309040f02030c011107260a0b01050109050307030b0a020a0516240501060c030309020406120b0a050106 78
    0x2648625100a0100515540a00100034081042901c2c00c2d4101e1758043c1920b0007910351480e4441c40d4134083c0c2010720842075076515101c2503c110503221420340e040580d0150155256034601b10088a041d080030302020390600030610f496000070700600c51042d0010701c02001080700480b0310308100031541ca41c001d00300101401810083c4000c55040403c51160354480c80c800d0b90a80520110040d001000310603421656a0080c80306014500340180034891086007201d042030341400c01112041c20a20004143e40e004003c240110007100c802e800503864080030b400e096802c825100351800004120688030781c606500107105a5a1001c00d010181c0303815001480b25618590b40c911206000912281401e0742c0441c2090707289205000701c41445e541d8070340d81081d5503540d0a01030058506a8510901d0a411110313451100ba21030040c58101d070450380b00d586048440b0b0310240d018010082080b0780c02a0f890750081900c400c1c014400750094002d004050141c41d0003860001141c030103820100c1441 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 206212607 1250 206211357 206211367
    0x2401050a02100905010f0f09060e0f03040e0c19051b0c030307030e0a0308030708011d270703080a030f06050319020105071a07050309060601080601090b0a0e09010623 73
    0x41d0700001c15a51070003007182c1c00900c000c1035041c420b00516a080282c1d82c40e50812410260507411a0841c0104500802e410040d40b2020403030980e4500300c00205141c0c580003480100b0050b60074100e01603101c2c0002c25880d00d0403039044076094a00c07241b65162400302e5008503624441007010f2501040c2e03800241d0040140220300030002e5a40d0140000040c2008031003039614581d600c03200c0e000750003194419056074481c00e00c40000303018031209004a1806c80e98500166400c030541c2309403a401480030203600c2003c2a11a8400e0754a8543c020343c2030030b144a001400030000d01c88034000c06058480d90740018001e0503405000c0e09aa0050344010f204c4e6102d010003d800000c61201515520780c2400d0881d07680806180c104030b025034807085035513001085403c00032515089001140301f150440c003501c256030350b050010349022806440a84c0022030010f07003401140352080041090780e0709820060004d0800308000f51004100b42c004030300003180450000c11604092801504041c1407015030b509003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 206213857 1250 206212607 206212627
    0xb090c09010506030c0a020304080706020303010e0c03061e0103090212011d0f060109150801150f05040c0206070f050c1c030e1504060b0d0f0b010320010507060b1503240105 76
    0x603000140c485509080001591980791f402041200c004001308402d031401d80c0d98541c0042d44a4100744222400c3c00c0c026400950240702c81411244502401088040c116052030103c8910b80380c8007030050b040c15665030764000940c3c1c8486030b072000c1c0700c400e400214040c0d00d103100078000618a00f03401045a80500d01d620b108440119003e41940c10310301c00040d940300381242c40e501060455001f0b00740e40d464034841c206455180c49240e410341c1c1004c641c4a0840703645000340001c494000304407200682214000c1442c540c4910169003038400145010303405d201603403402c1c0e803d140e6041a2164100840c03c010f000c0c8607014015048018201c50140c148810400c40180e40341900400c000c3c030b00c990300c81d50440c1030355440a400700b500340c00c0700550480100c0303850014a0313117101780010303151105150650325003491250344800008074180d552909210140c0d80c0d120240a511601ea80d2081c4141203000030b10f10b1a0002e948511388030100100803500c01c8110340300040700705410780c1c10040100000107030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 206215107 1250 206213857 206213869
    0x6070203060112031716091a0702010c03091503050901050f0112080903101407031b02070b03190c12060f03030e01080718091a0f0d080a0e04090b090c090105 69
    0x112542c940300e00f211000903180844044c0f004456030100072081c401404144142070703268810881c0c1c15224803011980b02d40301b10719904503d059160052100b001440010f5109103030701450207203c0d003062180303651900c0d1411600c060003401140080c0d507e20420141160034001d094001001218202140d410521070250074084a00068200c0c01c00158030715503914200200303800d80340384902c20044a002d0881243d000c1d2416242100000d0901d02d00d800c2205c0342c0c100e86900151706800070440d15182c003d171110030f5000289150385079400e01c0c940d4811070816021382040d00342c55a46130b41c83d2840c04140c16085442e01d030412000c04c0240c1030107100094102c08019400c61090802010a6a801200303c8849010034034180c800498442c0000e00ca054075001205400c00007140180b03803d4105090100d1500503096156003d8801d403250004900c0b0742c03009000e40c0c03000e451f08042c0385542c04042402d48105c07020848020508408112404c2024086203c0c403540450b07090405500d890300041c8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 206216357 1250 206215107 206215109
    0x1505030a020d031806091d010e07110109060e0601170a08070f0219030510060e091b060c030a090312030c0210241d060603010305030d090614180c060702030601 70
    0x4040d41c0080d0b1034000b030600508000350f2000d81500b42580f016241e01c40188440724600c5592490307490001c0c60303035810703181041e50b505a1f41d05800c14203040d580c0072000c4807024001d80762002c0c1703950f85d01058404102c040c002e000d94890603100405086d403521920454100d0702590200680d0401200b0000040c00d40c0c046171022038000d600c02c0ca0b03e040b2800001c43c0c42101001d200071002c1028800820080d0208031403d0140c2c10703030020001035035284801011200100c0741d45140e5080303510744c00c180351203a000b00254000e000e04a079081c4101c20803070500c1c55201d040c212000c05d140c81020420801c8000b40414040d180b882c0621114080110207541c911070703002081c265a845d90402d4070a09189103000c4200506001d11080c0d1956590307254800302a0050300c0034003000311100081e51410a1000c4074102ea030f204005500d0b004158454800400a00c8001ca844946540b8043c0300d1a03404d48401c0d0081280034000360042c07011911552400c044158400e001d05001e20010001d60741c04200b0700c1c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 206217607 1250 206216357 206216359
    0x209011b0b070804031b050c031009020a120501020c030c0313090b180919030c0501050601030501030b0406090303110301080c10090501090e040c0506030c0406020c0d0b16030906020c030702041505030a02 89
    0x40002c1c0c131986002d0f01c40b41256008044103a00c8050984184580000c1030f002d9084141c050703c0052003a100c070074085c0c840d02c1101030b401c5402905c4c2000f808200392000031850b806400010f0800034044001800c0d50310040c88200e480c0e02c007060070240310751180000c100500040404200101d072403004039050111a00700810003004d2140080e90000c0f0034803605018512a0002400385100c40c5006000c07003912280a0710395628080000304a0750082c0f2803141a00e4101d001d44407141c4c1c803581d9000c0500420403040b8101500c900c815043d440c2c041c0007541c06084464058041c140b00701301400803524002c1080320400501c0542007000380d800a880b40103441844662072025900d40c01c20614101c0d46910860f0072800005c02c05c040d5542040182c000d6039881d50a8130004e480004c100181c02035048806000c40413840040f81f0002202100d2003500304944c200841c0c140e0b40342e15100308a8000180d807d0f030070740000a202003149400d105a9802500000038818024200b0703001c03c1d034402c4170700300003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 206218857 1250 206217607 206217617
    0x31b0e01020705090c1210030f14012007050f0c0105030a0e0c060403110a08010c081512120301080c0103061d1009020309010f0b062712030d0209011b0b07 68
    0x1200069209200003406040c000e403501e803890400000b01034040d4480f1904002c20000706010440c41031020103900c0469030400d000c40e0b801541e6841300c400b0440450038040c0340d03642e10b41811003201c800003401003020724681a03a0380c50728002e00700b16040128030701c00740138030360080500c01d03070740e03031307004030590b178003c4105400041c455240c402c01c9d91804145480143d4840c0000c100041003250010080d40c42d03220559201010543c0c801c0075600f66510400128046586040040c170100f21001c200006000003c140522109a00e4050f601300052070130911003d141c000014001050100b140c1641c400081c81d0401500b4640004c11542d1a680d8104c21001200880411000030b0b040c41c4a01c0605034a032802c642e241003103a0170318004d04869088c0c6071007504001c1c8010041c0b50078801c0e00c3c500364000d51140c0b0754102903104241a0b03031104100a6108040500e20340c0c1200040010f004843c80c1e565005941d0155000003401ca001089090050801c4164040300003503114200316401400d107041c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 206220107 1250 206218857 206218877
    0x30c0c0215031906090b240f2107080901060518041202030f0c010b10030605181015020f06090c060703030c020309101e0e150702040e03121006031b 65
    0x2164004803803914282c80c3d1a051081c0428001c4030b0303138488612560100d4001b00d50b90080e17001e8480f114404090055440424400780007203102240041094114000c2600e600401a8210511034901600c7c1180054100070400c06200024403079000601800c40d00031142e110b407010007600c1c1840c0100000d00d0748862156207403031a4000c0080c0c406d40c0e100f10a40e41d03110125aa0054001c101d0210001c1c81148100704240c0c0c40d9009124480550b0380c042c0120081c541e2180d201d03a07041d140a000c005e00181460f10000d0340321400303608010116259070140618180103402640750480180811020350080e0048400c0c1d640c1d02d0007294a45070340f6040105000741600801da003107021307200341c83d03400c0f041b0901401901640a0f440c24074540c0058500031680011040443e80c0c5803010300c0c3c840e00b0003a04850540000c0c6ca1601901c42d15200800c04244a80741030350b414111b800c18407104003075001200c14450650402c44d4220f0182240c0c2c6020080d11100c41100a031110092400a0500c460096 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 206221357 1250 206220107 206220121
    0xa03031215080a0506010603060e01050103020a090e07111204050d030c060603020904140f010c2703140f12030c030109090f3507050607180e04050d030c0c021503 71
    0x8003001d40101c0c1e14069540307982ea06250b032248107010044815003d0000041080c5000e803060310705551401510099907828940150000d602440390b000c06c0c021b0b0140c000600001c40040c081c8a418181e81c1c114207080040a114078044003142402e40703a80061200303010903103904108101c020342500d00001c0317000715810150300400c900e0704082d4102c501c0c00e04000901641c01a105c04064400044640300700141c0e00d082c0c02c96980600d010300081c201c0c7c01a080721840c5a03e612000c92105040e101295a00d0352460b41d40355901552030002e41000700c43c0541140180140005290a41042c902c3c1d882c1600c20310015100500604c01010758400d401014040c0c9445280c5c4101d5200102101e082d001d01c405102c10b00c2031440e000411807503072210101c2c2c480304800b900c3c1074036400001400903072100d80040e901c11f0134403000710000044104e0000b46500400f000b0f18052801031002e4060107050100c014165503c010810052141c00b90803400103844000100d600609000309854885d00c03804 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 206222607 1250 206221357 206221361
    0x23a0513080a0f03080108010b01090e0907050a09060504060807120204020711030d11010e031309180203030d0531020d21031407030c05040603051518040b010906050a030312 76
    0xd00030035540c0c414a12402d00b045100c5904221960183d191203071a81c0c1e85205007420385510825880c0060300c084410045200f555041c0c0790003803518800d9540440c0c49101041701202e841d84030201e41034440e0010405400e0030301c100000b82c22503a0103000203508040000d0721134104644001d014a03400200b190500c2591130b150108004010140c03856011240d90050181408414901d1a075280c40d4020741c0c200d800000720360f00c46c2005038101c9011813500800400411100070020342040b07081c0310400c010b81c0e0a01c01441002c6500500240a0500708080b8924444502032600c903c03000d81e081c4640301c05200814030800350304a8044000482501c0c02294819980f00300d901224040d400118000750180c01c018810161024500000da80b8443d0440c01c0e02d610514030004284100014043c180c425002141e000e900b1800310841680042c01107840d03540442c0d0306500030b000c030b1001d2204020b4a4802107004144101342800024101f200160250045100007018413a20210502c00c00340c850b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 206223857 1250 206222607 206222609
    0xf030908030c0702030f011b08060301090503030103150c030b0a17070f0807030b0a15050114071b0e060f060a0f0c0203030c0a03110d200a12023a0513 66
    0x4814219200e080c240e05400b0250860380c1c0403486800f500c01c1d2000b613154140b1440104c2c3c42914003000c105c802440040d141d441c0040c2040303416540300d041103008940704100540c000d51040200b030881c211029040c00c2182e031055001010103080c618040050340d41c02610b40c0556010180c04014480e122850b61720f000e52940c0700c010054a00d030b0000030048804110101103e018507600d03946955a4400c160858000502422745400204d0003484294810100c420201c101154a207103061115100c4442418907201e08180c1c12000311018410300340710041c25500075000740d441c00400380c0d09200254030b9006800c3e82c4000c0280c1c0c41080300ca640d00c504034186003641c0260540c2d6844500c5003caa490310101075094010a100484800f18064000340c40c0c92200040d03a2600003c1c0711800c880e4400c903078800381d103410501c41d026200740480c800d100d181207031031116002046416078040c2c1a0fa0b44800761304034080c0308007200c2126020a2092000b50214001618042e40d4880502021801e4810031f = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 206225107 1250 206223857 206223863
    0x9120c01140f13090e0c0307050a030b07020f031611010f0c060e0c04020c0705030c0a080304180e0d020105010f08030c030f03040f080a021f051509060103060504110304150b030d0f0309 81
    0xf0b003240c00108400c00d40e1100d00e44214050544013424500b0040c10765a108501c290303500a505220b0420214040030101600481c1500c10340341a4002c04102d03501d903410100000b2096050300c0d030b00350308000c1e0b1419800c40c6010282010800c02c24041405400040c100501a00e040d07114031a0380100c010601202c610000020402c548406200d2552030f560f404a0103a00c0c040c1c806c00340400070f42e2900b0854903003140c03451001180b4103410a00340440350550380042c0510319882c3c104e0296900014001444070324540d42c00041c0c250f1402e0700d01807000b10540d01420040e082004810000c0501204440c1e580f441c0c0da4249503a503c0b10304d014507800c0c0310340102408006000c144044c809501080f1f840151200080300e1020400594104044603410f540d454155041d4078006241414032514840e030007001410005580e903038613400b18090b60182c0a1601034008004108001c01002a018902288086004001020003940800d540d55071415040782803002c0180e641050900c2600045044c0f54 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 206226357 1250 206225107 206225137
    0x60e0c0303040e0a05060d050d1101110d09030906081905040c0801140f100501210b0901120303180b060d081c0605010f0201050705041a07021509120c01140f 69
    0x56100c40f0408484000d0703620508003420304d00030416500c1c000c503120400d60303040000340c00e103c51500c0003a0380c070344200d025102d615503c980d000d2001440d0003014100e07010050502180c510420f00e4000d118010603008142072020039000d01c6840c80004d642c024102030b160340d000609807210300308803911001aa200c40410742c02c207a40d010301e626074090420b004191060004100340c55080ba41c003511400c9006e483e0000311200c0050b482c3e80c00070f4a020600450189001419603012000310f110712009800a110078504043e842c0c0406505109044900c0341d060b0503080700d090715680c3d00400250144c40702d07104544998078a000d002c400402c6502e402174080224514101000c01800030700814410107011138070008049401e5401070040c0382c41500c2c261b56482c907050501d842140140100350343c44041c1d0074240040c20050701d40312020742070700000700203031a100c03051407007004442e240c00103410f40d4681200041c4119a608140720005c0d0343c980741525a140c41a0341030400c4540038100c11000418 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 206227607 1250 206226357 206226359
    0xf070608010b090402040e1f06050a02150c07051614060903120318060a1b0c1203020a0e0402031009110a0f0e041407081009141b04030f14010f0c050304060e0c030304 73
    0x55440e4032035107000710220030009007527071900103541500031000b1790005078004003c4070084012044029500a80c0407030700740d08000715516828a030194121a070a600c0e220a00107100083e03180c18007440c1c0390381c220f0345540382000310703404261a030322142c10800800308007001007900400000441100808140104d800074684180043c001d450234074000c2c815090728001c044400e41c400c04600c0c045540011212640c80d400c0700c801c40080d44100446000c002c80611203175225034590008500500295001e00d01060905100320221042401c2e0403d2801081002154081e0050b0412003121050300f000c128000786600498081c21000784691100c400c0304041016454105031110b004241c0b04403503c1040707403151211402c5a0b110440040c83c80703919400141202e0080da6030a820200c1c5000b82400d05c0ea682c1d880c2c44861940000858039400c0a40807890001002d100d034400c90300018a0500001107160005000c0b0320000c0d102401003502da00075680b15003410840307005d41c1c40000d01283da0355 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 206228857 1250 206227607 206227621
    0x40512061e04020609190f08010e0d051201060e01051c02180301051b030901020c0304180c05041a07050c030f01021317030313050c100c02030f070608010b090402040e 73
    0x96501107410148010078108521a001c404414842c452075000e040949040002030400441191000d100104910100320102d0301c001742990381801445024004500704091004c3c5a0520044000080810205011704c10960141100860440386036003010310b110246080100d403a84540c00c4003481a00d0b4003040312101500a80c010080424212240703c5884001010182030300c038281c0c0c90728419881200343d1780701b2041c003178015600700103540f000500d0800c1100341c0c1411a002035000d9900803544440044c0f07142094000e42c61261041d141442c5444d050805540052503038808010310250003040840400c54104007020003940002c0c115401d140c00729107418040d510500010100300c004201c00030b01d1510302c100c00c3c204204003030051400c6580d01d03100a401c01c07900c8241030382c240c841d1903203d02207502c5404500d03410004980d140751684856005052818012098240842e8001e1004108242d805080780d03040d14070b15803502d96500e6012000601a004640200e481c00200c0300c140406 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 206230107 1250 206228857 206228863
    0x20402040b0403060b0f10050901020313060206040b0f040b0a0906200414060715090c09090503070c0b1603030e0a0c0e010509090304151b15090507090c0e090903040512 74
    0xc99201d8001400161708201c01d1060103003001d064507400c00b19001c070140d80c960142002c0d004000c3c041c8116420214203503d0049217400540c00358002d41c01100a01007400458200103522038a0541180d5540c20642d1f03c055404138000d050a440d80e40d42d001550400000303400100d444070b02704810092010501504291036880351003180c031400007504100c0d4450030f000c42503d24454020103485104201074900d44058252400d0403100c541621101203120480d5110700e25009000303200664550b90b5601d03242c4505401d64100300042041400909054254814001401a414900400e0140804051074502005040001c0035180b48030300109461541d086d10300c1c100c8074102c40074411a00c41e20f00b42d40e1607100b81c0c0500d40420b00314140ca151420301a14404440f200401c0760000d50001070b0f2284242c000e1100c0303000080380c2d107607030b04030041c41410003c4d00c01070b1078200403c10503018001340243c107009207000d0043c041c0e9a0300f800164001000d1060782c0c000e103005411011164103500e55251 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 206231357 1250 206230107 206230109
    0xd0f0e03010903080f100506040909030c05030304050d020d0809061303050c03040803032a180a03080309030307030b0a05010504030f080408160303030609020702011b05011b05040806150901061803020402040b04 92
    0x1c1d01c5d511003000910541c40e00124804441c00078142d1450302d82428500300203860080c100741e080c421440e6441000460400c0110301c554042d00c060001355226080081c107107412048003604100a01c2c0502c090000003084594110898403400c2c044011035140582d00b40c05440403a035a1804003290005001101000840c07013550015400d005402c08081070200c0801d05100031a1010824002003042000300490040c1002008140010042d038aa9a00700d2944c01100c1c290f82d42c2d00044140402180c15000b000d4010808403a01c100903424800002c0280c00740748009884c0086861844d01800101d8040310060a00301c410f03100d1070b56542600c2c040b4020548001c0303001a15007000010b42108501c244d0720300e158169180c8411507400c4000d5a610001940140c80359507954064031250a8000443c00b0a11803580380c6548940c07502e802242840b60080000d582240d095076100c8503940c9840c056815202942091441040301452404041005801c0203401610019011800c0400c84d00030780 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 206232607 1250 206231357 206231371
    0x10030902030705060a05030708040f050706030f050f06090606070c030228060302090d0210120c0e030c030c031e070f08160b130501121e02130e04050d0f0e0301090308 73
    0x45545030f4a07402e001e280c0c0310f08401440090320610202da040d9101700ca9841c1c209004d0b11500d40854a0384d00c0e1181069103640c441808650baa8421315003c2100c0e000f515400410081031200790b24081c0003040e01d241001340070038400c0304001003560070404002120006503402a0603101460500c1c0c1030303103a5400e1200c5094243c00410715001910301e12034000c0314200140030b00503850005d9140d09201612046012040034081c80340e003084061203040c401d0a0a514403540c2d200d08103242c1400345404c003807a0170421400fa8000318070010705510009110706a038081d20344d055242c04400f5410340c1c1807100320f800c007403200100c8840019078001d000840c038000c02e900c4003c0114507a61026284410700c00c408180c10744602c42081001258002c405944d04a5004d84020500364a0b0340f0320700c41d801000e00042000640c0c003146500c01c85404910740d40c0646400c0b400410345051503210507550300b21044440702044041c25031030084600c10800e215144102600910495011345406426800c04503040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 206233857 1250 206232607 206232613
    0x1e0816050909060114150408061303031a09040b06060c1b01020d0806030c090a0605210105070e01050d0b041803020a03020f0304260a0218190b0a0e040f021003090203 73
    0x1080c0d007060081941030490303d1040003200743c0584c840602064111b03912100c42002410302000454060900649204600002d0038060401d90b0746006411034420304030b00c0c809084070700c0c1c02c030001d0344842c240e154000b034002450034019513908001507041d00c25283c0400c00ca00070005052a140c0307450740203003c440800d030203480101d07816240490f200300041314a01e030b0503445400a001035003000807140d90810360034000890300756120300103d10b9661001c8045600d0422114101891120a1007030903044a0245009140408032200003400c500401008402250f51000c0084803075456501003502d080a508104d004075540d400e02a4480390050001d50140c054035540341403414010084800b86d074600032000b0310b9405091304a0321150344240707034000144518000400075a5910492082c1405015083d943c07500e0b000b0500700d0910701ca00e174844209400c2401d07841055036165404401e5504407008065243e0b15420f080701c24081c4801c01135045126030304501581c5071305800c03d002550090b012 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 206235107 1250 206233857 206233861
    0xd1205010e0606041202010909182d080d090f1104150503060a020a021212070909020403030e0f0f190501031107050c010e1906090e07020a0c1e08160509 67
    0xa201a00c011240d403584110104824405c030200c1a014011444c0103241400c42a0b480300c4031202100c0c0e02540c1c02a2007031442c003405003003100290354044113181880b155041c0210705d403403d402034121040010410300020030240e07918100e039806400382c1a04600e0050000701d084c20305101c0e00303a0b0900c80c1030040f814203184e1801142280546021280e000d00200910798500c070f1114005c5d00090300d07040450188081000c020f40440c40502420300aa1000b20202d0615510240000000e9071022100c01d005000401c08070342c0000f0702641311641911a409080700130400a000d080502014581c4001c4401c0c41950b50b240280300001611001c0e2010886101800340c0c89915018189000f00035902505450b0300d1944980703881d10300d160020f4002107220b5911045140a04565000750001a10403c81000b10006419040703810183d0b5002621548806496907818040704d1f0140350320b00e000c040d440364007100d074807030004c002080f42805039014080380061001303400c9101d100d1603100d180c142c00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 206236357 1250 206235107 206235119
    0x20406050303071101030f0216140d110d0f120c0e01030b010306121403070b09030903010606050406020a230a0c0e0f06060d0c03090b04210503070f08090705030d120501 74
    0x2c12101c000c1d800c40d0480c0082410b0400460244c0701e6030001081154007807012541c0d0f209480c1c100c80500e4403030000018503008020b0b07650f00c0c01000994100030000c19200040d048800486d002021101524040600c0d09004c0e900340c42d5052080c01c41c814080c0381c204141c40030307580107040150a01090f83c050007a40800001141520b0141c055600e200207803180c0100020013443c3c25801104c20b84054904000c210744518003540002c440c801d6694100042c0510f180c40d0a1003543c01030040c500b020b03030030b150920000035500c0f06c80b0080108182040501140c0442d20100280003401d0441c00f00c408440c01c030300d8003c051214a00c140c00d40c00c18164045018501805403261042c1c102030101d40c145101c42d02141c01a043e071035144c20500d82d58a20a00101d03105424240c4614001c100f1500b01e07081122807030441041d076920410400c401070091254042e03100500909050361894500810307200c403040c040c1001840d9100e694903110303103400203442c950803000111403451120010807d0b40e82c0c0380 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 206237607 1250 206236357 206236363
    0x607060e03041d0a060e061e1305070c0501060909111908061603050a1b0503040303150311010e010806010f030b0102030d0527010c0507080f190207050f0d050a1712010608040204060503 81
    0xe21f01d42d030300c454155a2401000c60300f8505c000c01120040503804901c0102c1d041d00c080394000c0d02c0e000c0008140000c20020710400340600d500804506800300b180c071340982c039007aa002e001348444610960040d02004880121031a02601802020003921511f050008040200c2404103203100b0100c2c1c20304000809200b4a8802c085a10000408080d5600d0042c0800c654640c03004000310240340c0d80c0c01031000400a0504401e019512800d08040400700e45800901152210a00c042c100300041c410002141d0f808601c0b1a001c5501e420045004080303000140d045000b01005424414680030411480f010300c2e0b07001c454041d118001290046d031004404031300b0783e41d2140082021070010032820300028022030040045090056026040000c2c0e81262031071114606c0d2018010303400380740140b1003464061064a030440046171407040d400d14543d24281c80c0d05040e070340540f2a41c407826903c45a060803100f250402c0449284010301c6607155080540500750070381c2c0c1170313008514001000c14581400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 206238857 1250 206237607 206237611
    0xb03041b180b0415030305130e0703020d14130b060301180f0c050907020601030b060f060c0105010614091809010902091003050715051801090506160b150607060e03041d0a060e 77
    0x788400034162811070710300b50741d2548480880b234008141e03d440010a102c4000e02175006000b9036401581d5030621260a4054070070200d010000803105000340040d90310340c0c40304420200c1e4040181d000c16515200024010100c0d0820b8030185c403d00401c100400106100c010360042c0b10722a5a201c007502c0d1814001c588004403844070240c1d00000040c40400c01c15405c079980b2a070000d040d152042c081c40c01241c120340000c078a11440381c3d110401400034680000d0210f03080c1101544035410105460001402da0140c3d800854212074500d01040b420f69080d00414519a000780c141d540e0703400c04d81c103110500d01d0107100030380b050300a200e07011503007034804d40644885140e150743e80c6007005554040050104035402e07095040c1725040f07600103440d8484801401894101c0148001408402c2c2405801d101000700031801c081401c040da00b149544103c203a030714464001d440007131080d814802007451842142c100055080658040f04100742614540612804400070248a0309681d034030304480007802 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 206240107 1250 206238857 206238881
    0x20322050607050903280b091f02131a07030e01021614010c0222110703090b0f0403020a0906031407030c06230a0201050103051b0105040b03041b180b04 67
    0x1c00c4010401280c03003034020340080354009040d030702e0341c1c0448004280000040c00900783e00d030002c00d40c8403041c85007000c0d069038481d040c00c0140000038000d407951b0b2400c050059507102030320303808200ba078500714010049401408000c281e42c4082944000e10510304e80040900b00c0003c2c110710902c0d002d5501c0441c11030303d0030301784400e040916403c00c01c4960740109000e80240c100310902070441c002d80c0e0340d92241c88c103002a1140d4100b0103c206174802c815100f0001410a43c24000c010078400030303600a84100c11103548813400b81d1074008222410b40c25120301c2e40040e60020381c01d1400304042c80e00e0382c055021248a501540d12000c013254070b0300c0c2c0703030780380c9200c068420640401c0400483e801044200c040300702e91203588440c464811044206034005552003c010f0307644400510400038108090000000b0f072100c000d510f061a1800209a4411030290030400000072001c1820084c400c00d000501c2c6001c0030052a540c0d8481c82c05440c09401100010030190410340211010f003403901c00d0f03450342c002e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 206241357 1250 206240107 206240113
    0x9020f040209030f011104080118080a03050c04030f06020901080a0b0f0405070302090306040614071713080412060c0305010b250f050703080310060519110106050307030602032205 79
    0x9904020000250000e0500c42d4160240050f510b030038210070300c10285a1b24000842d9900d035810021401d084a8010f0504c20391002507145800201c0d00000a48401005520380411a6901d03800c402d10140110740c4000c2681c114401710000300402d54001c0d00b100c4801b0b0361034103041e64510104500355450028245d4100e01300e005d4000701414103401182d40a01c4908000d03280091500100749807460445042d5240c2d69915502c54000c0c510f62039407a0407480c0343c544119640d10401c40e1004118000d400d81000b003c0d00341d4404200290603040c0c400805203146003101488440c24000301514080d25440d00081c540000032400c3c00354a800c1e60b41ca03403a82104c032800980c3c1020030702d90001e03405405642c04114180d401300020740c2044030030041c1d4800c0c902c65880c2d0403e40351100345844560404010300a0501550700181182d6691544007060391030541680c1e070b82c001025005120b43c3e00600e8050003256408402e001054000f140250900110380c0c1c1c01140341600c200e900608500002e01c650 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 206242607 1250 206241357 206241379
    0x80c0d1b0f15060b07080403020301051f0e0601020a060c050a140a020706120f020406050a080f011208090a080607020304050f0f06041206020d090b04120206090309190b0c011e0902 79
    0x1032a00d840c0e5582c01c4040300c40040d40c43d0720380c51441d40940002c50708540c0b01c500011700780110f0400780200d42d00b04d1103020600001c8020191594402c600714050b00d000602040c00143da140c0c42000301141140c0c01000811800e1324000f0008c001c0c0c1c3c4004e1203000402d69246103400402c68440072a080c0d41050750262420a0600d00100c8044a15030500101d40303071268a1190116924030040005000c240c641c0c0da510034681d2070240c04480300800f81c03814050200010001d4007000c1d80f004074007561100e0383d250351b4015280000d400700419041000213100d010200000b580d0000020300613103a080341c02483c01c0d4000001c22669850302c0c1041c41d002203042c4020054455803002ca03c102c5031042c41d0140c1042041c004410888080b0f91069a200c1040c078280414040541804032000032a440500140c1c0740000445569214040ea824000c0d40d0070350415086000b0f2a0040b809400082441380d9900180c0060741e000e400754000c50720301025880641c21085070144501140c02c1c1d800f41203410a4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 206243857 1250 206242607 206242613
    0x907090b0d020c0313060306030201090f080601050105071e060605121609050709030501090f02041112150303040f0f0608220201050d090602071b060212030c0306010c080c0d1b0f 78
    0xa0340200d0b004114a10042c020f00400705c0740d03502031001400441c0d0300010042d19600005120511903402002c080c42e842c40140b0645a0100715541555000c3c02c0080d510901440c140340343c54404500c4000c880c041c1c0460340100481c44d0000d85c200c4200711285082d10040b20090381e03c8499100c0302c000000f91482081000c2c04590304855841407131414001002ca41d203480f641e080d251107034421a64020802e583e80210310b420b1040010900c000742e5110300344000e801c081840c40b48050300268403c0d20300b0485a40950341041140c2c0640700c0415000100ca0703850024800d00308403401503101044500740050b040c8424810303070b206441d20611070800c0307441d403d400645007a808031062003404c80e2035030801404620ba81c001400d50a00c1900c0d0445c20080310786030a04d902e80e891300403808641101c640a10303081a10b600307580c0c12607038030180186d0320744401c401a2806001d0b0a0014609100032821010015000c129807940440b0364070b404a09064511030640042482c0100800003400d400051000c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 206245107 1250 206243857 206243861
    0x10905150d05040201020c09090606090a0b010c061e110403150e0a1103072114010e1f0914030d050601020601150c0311030c0f0c0d0c0b0c070e0f04020907090b0d 71
    0x800d006005486541400300003040708e80e2000c440407013190384010300b071281c20b06007030342c007564040e5104408000c0c400320000002c06440000d01c0182105440f0303400380380132451050541d1110b000392101001488522405100203070421711055411500c615625031a0300e00e90700401e502080c565000d00030020843da501a4507240040c14550184181080460805407240b8641240f254000c2c2d2210020b8131440c041d51103a01316580c3d142c0e0741c1d0418155910509000070070028244540a906400000d8420064014404000f000d4120072455104134441e10b8080010403402d103240d401403110f81c2e111001a40d59800c01c0c80b44204c12160b90a000301d41d0b42c41040310302c0c4158802d00d8a03400b40c018060910b0f18541140001c0003194009421460f40d6010801c50020845001d0301c03031480c42052512004e030910b0075440754054003000002c6040e0230080038403405000c0c0c844591219000d0a0401140100d100300700c03012400b0381812004104154020441c00b004c4130381c000c6c013843c9811680024100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 206246357 1250 206245107 206245111
    0x6030c030901090507030b010819150c02030d051e010f0e07050a020c03071401230703111c05070c050103020313110109050d0b070306121a130204021206010905150d05 73
    0x201e07655864942d00700089007840041e0007140078005110766941400261410000c1001001c105650b0022903030002410b0b00342580c0002c012140001404090484140d095200d07114400d04080e03e040100300c08011242c680310340341d020500707903100e99a8030f40c4450481000d1902560400410351800619414440c0000f80a686440d1043c1c400c41e29a42e03011a02d000c4039034225030a0520010941065541d03c0b031101d01e43d40c10740307003000070504c108810758241a01c10315030054104042e0b825036100048082100300341013180d1035080030413009041c0000b8041c2d001000e084800c2ca1890078005820341c440c0c001c7c0c90080601c9140303402c886a0554540c0c01c02c4040b00c116a040c080166000a040d540d207000d4120068007c0300b00d95002e04e06041c000b41224290741002c810045851042000303c2d0001c2122706041c04540d5180c8203130b403261900e83c00d0505000c2002584a0700000e01480c1c413000a6820f640203620a882e5031a909480b9002c22100300007401150b40312400074010060480c3c1c05800541e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 206247607 1250 206246357 206246371
    0x302060c0d0609020706050a0c0f1e050f0a0801091406010206060909010b06040308030405060105030d08040605100b22062c0f040c0801080c06030f0106050c012409050c0906030c03 79
    0x42c81c00d50b68010307141607070040e0740e00340d6050b5600c1041000c07040440c082c12450301d02910f890106c248440d800540f8040405039000e400132301c504681c0d903489020740221011803460300340c002d40760003d2820091214509004031001103007002d00100016a8400040c1d01030784c0b058010b400c40307940c1c030300c10b02000c0301000f441d1001035034941d401c1070150703155a0000d0010754003410b0703915a03d241a0410a1a01d881030303100c54000d611160255852590154100d6002984100007140c2c1d602c2d00030443d52000690b80000c0004d0f000010004590201031415142a440c075480d880c0c50031b070b590700c420f6600034803000d10700040d0f0744043c0e52640e00000c03100c0d01008122008155850070000c00c0b01007811101100f010602144d02e000060144450030005901507841c1240e002d440d43c031b082851031592000c10b03c03808040c002c0c04209106001005c0d0029010441c200725558518402144854103d4801c5c3c4a00d0180038a44008030340d000310034000b1900d800c007016000c41d18544441c0b9800140780c2c4014071301 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 206248857 1250 206247607 206247611
    0x1110f0307020c0a06050403020111060105060702120705190e070201050601020601050f040e011815090201120f1404030909060803041a090316080312062e0903080304051b06070302060c0d 82
    0xf0580503030382c2c004d68801a05c6296201901e80d421440054240d000d69103404e1041e0303011000410541d924042281c04442d8142c90700425241c50380c030170626000301900131030340c042c50142d80903c156514151040c2101c8203808440d950340c540840c1a0308176042a500d81340160801d500500080c1040c855003030142c0000f4000184821100303100c64211045048c100e1061103203044103109200801c6a0740c000c00e140501c04002490340c42d030000e07201a01d81c0104030040c541310f0019000180036a804401c02c1010103040280c3c80c40d043c90002c140303500f20b004400368075141010104504c9800001e0b142a500d01ba024150180710310b42c0703454841d40249000940c10701c1101d554140031180f0144800007040520b004584404020b00390701039081c8010201030103414200305000054032081d0101a0011030030070111000101044110354003011500050b2403148004180000c101c00020b10509134103e0306840d02170240f40c402001428401c400303024005a0002001c0754511600c0801415a0000c0c4a40 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 206250107 1250 206248857 206248873
    0x80417061b0a170603150a05070e0a060f0e06070b040302150112050604020618030d050c0105010b18042007050303270d0509010e041406030c01260604020c0601030b04031101110f030702 81
    0x851b1400c150480b580362100b07490304280100710740c200518880d08102200c0038061036042001c0105134802e400c200c402044403c100e8080151691401c0714001ca800503113040d1a4609800e02a41e00c0050000d0803030f4032102c3c14000681c85240409040c05154014040c10481e2115000c004807a004038000080340b0b407012642d0040c5550801a0300d002c85000d454054a43d445d282d4500d0840702c0591090003104420007040440030504004108800d07001c8070700161510059100c0e9008030050040174841210002e2420140200000a51320405220b4003009803029a80d9050040602c2200181e0256110f0383e0151070603801030000e4001c140061521021820039080000c051301d4900a0042c250441041400424103080c003185a01d640203080440e000f0410812841000c41090100e85101082c0804103000f43c0d05c580480751840421412901596103d04018080d0358041d03404030041182005203406c08501800f8004420001c0d8031a142410145280038a4a41c8002c1c0070100311300882c01 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 206251357 1250 206250107 206250133
    0x203040e060612040b0f0a05131e0803240a12030c11060a050c010e0d120e010f0203041101092c071209050610060212090d080417061b0a170603 63
    0x103d40b1a60151000012070b04008090044401c0040c1a020a035410300c4100026803d01d02c5400010a81c03100d00f01c001e103060003000ca034004503003200080c40502d002041c00540c084141c03030381c1103101d20030796140559240d002c10840d4254943c07180044441307040d003810003c00e016105500255000e0b085054540c0052000108070b58007008000000c10804070304100c80300824810400312030700c800e0092268078010308003d0000d01c1c4202c02c1e01616a2031390004c0200000a4103c1031a4141000065407242004d2030301340300c0307460707a904643e0000d21215400a200340d100802a601100402c07480b48204080b004449807000340180b0710700501087d04201455907000e80f01c1c00a003103010310050142818903101c8000c0d50501d69025204660105031190b021803d1042101e411400440300701050202a1a0400c854007490b13000c0314140c40442c0044010740c50201d031272849200c101c45102600303449541024081e002d80b95141c0d000030381d242908001a1403850740150032000040071501401c603408 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 206252607 1250 206251357 206251387
    0x406091506030f0c06020a030e040507020c1c03080601050708030c03220b01030c050303071722060c06050a05011d04030509060a090302031002031605090d060612140309010203040e0606 81
    0x250003150320f003152288880070b1061440e440303c0503050751301c06403d0060741070302d006105007103118a031449203a54401192a1034000c1217002842e00005c0d00005507088540401d654001030020146c001c40c2019001903c150700c11011100c01d030350300922081c10754807404c00e4a011608001c1803d50312154945041c004e100703602e680182028460000d403902503055203403144484586a0060b0300030f91083c03010704002100e10030340c5502c3d4085000d031140c44060180140310b0b951401e18070042c200b9000c1c0b0000c0b03042507020824034581c41c0290b8040c025038541500030003c540b824405c0d40f2058001c2554201ca000d800101641c000780285000346c14091440001382c0750394096010b00e00456800d400400450a0601005010031110401142145030a140c0640c050501030420300c10050000344945843d80c0324500030103420341010b41041865154480e0174500050340409896805008032111100140042183e5010006a000d541044e16103421040120030203499941c0c807400600528082007040703 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 206253857 1250 206252607 206252609
    0xb18011803081c020412080c0c09090d020d020a02060702090703060308040906050108010909030509210a060204331b05010515011e0c1112060a1b03090b0406091506 72
    0x81c0b404a40d1010002c018184403000761608019050052004001c04a4000783c03401c4040e8005000595400c91059007074101a80e25520301ea0000400c42804804507000950368a6460550201c40c0000d0107500c050365102d1070464020350080301003041d0390060801e444080d800a00606000c03c1c0395440f0743d901c102035041a00300a0f80b62359103c6040016687c0b101002d80100b049180c200022082501c005007648900610075000342c41404001e485e1911503c001014000170f501070340c120032060300d00f01d0041c1d4454071801c5188080f80d0b10f401c078415a1131030170380d00e41490000102ea00036100d036020f55a1151481c48207003008200084200444c200780200340c0b188058203001d1440294503000508500e90049880b43e411106c4c0360444480c1341c02c40300641c10703d44c0240504c3d01d00404800064800000c0d0610100e40740950411301c180700c005504908084840c482c4031842040c00c59004400315250804050101e030780b80e1000c60045a503550052110602418407039609802c044c00c0d04080c2e80503 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 206255107 1250 206253857 206253863
    0x1e020c1e030d060f0f0e0907080303040501050604110307020601090b0a0513050105030607180b0706021b2107030206010b0703110318010306091e0e010605030111090414010b18011803 80
    0x1002980310407045840c4110b03405040d040181c402d886081c81c0405080170b543c0c3c060a480503500c403021645907013003000300c400240101411650b0b00e14091400c580a0201507680034000c0b400c040340c020103644080140d078070030326240c4e005041030380c606400386000e00000350005402c81072804002c2256290301e042c8c000721020b1450045482d514120030f052a00000074881d1040100b41c200142c120384510515204031444d010141c1c2c0c5490351420910000d02c00c0005019124150a4100140440100b0120100e0301603e147c02e6a18185451900031803144c00d00003401070708a0001480b902d40074501a2034814080c0c986030624001204a4074590f070300c0300c082c0010386600e650701c0140541e418002c00010b4000d412003400300060000e03401660b2080c4a40081410380c40300c0820090300c5003548040300030314004000340710001508174000e69550101884a004904103c0d4446180160041c1c0504a0344440c1013030345842d203590789441c8000320100c4480d042082c2c5542d08200c4806c06c201c1c003005940 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 206256357 1250 206255107 206255113
    0x1802091614160b060f0607082119060501050c10050c0408010c09090c0201090201050d1e110901030b0901030b040f0f080a0504080c040605060a0e040906020c0604050d02011e020c1e 79
    0x1650424265246000b813141c0c2c820301c0348001209942c3ca40ea402d07a8285030b400411140c6801c4100c01002038500d0b8010422407550803141000402910a00f29005140300704008018858544004462038800d4080a15250f44502800c203040c201c40d038002da6020300741c50940341c11b15444507005429125a810b5003000900100c100b13001103a154820941610410b00080040001c00c2d400a0301c0b601450300709448681ea80d030520390250b070340ca8a07264105080e5a0f070401001c03402d0051070100303130022041140000d140c0300141e160740c1405104c07641660b0b040b2207400b10f40e50301c5640c0c660380440c00250846006000d4000e00b000580440c010741003861098413a141c585081c00949450000e6a0062520450502004003c0c94440c1400c40e18500c240303282c1800c0c2000100c000c20042c10060b00003d12042c800100288e00000226000b4043c41c490815655036640d8a141242607403e8005c0142007484121070034400d07903026a0080041c4106070342a1151500c00403094205040405001e61890f0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 206257607 1250 206256357 206256397
    0x21091509030b0705070f081602150d0f02040f090b06070b04050c01080a15050609030f0f0318031f0b0a120302060610090803071103011803030f1802091614 68
    0x103035012070a0f500c18100c4c5403150802901740c407181404911864090b043c180001210b038142100100724140150b000b03800d907030504071000704190700c03644100380b400152460031007100b0304c101c410700840d001c8518145034104410300740b46008004081005a05038004000c104110020380b004415920a5000720301902817008a0300002d00b02c440d00400d850002c91601c045464110303850508074044c5c0d0000c2c0c0d229525448200086460030701018803108861042d9480840b030352000000401d58107184000c420034840003032061555800400e464a100b0307148a00451a058480c0e900c6100c000c0d0000303106040c0d550382ca04410401240068080d40181c1001080140c00c3c1000340d840c400010103850040001c07490001100d0f2640540d40c80141382c0c41b455034500d0180d9409402660117940c0001d00312240c070750351303140c0030b070040c4414071190307040d1f609180454024035800c0c0c1c412a411500641f490465641c2c40e24000d010b40c620304a06014442d00104a80784001c0b500d026101c0c41c52042c000507005 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 206258857 1250 206257607 206257613
    0x304170106050312030c0316090504020708190f050a0503040c12050a062909092d07050102011b08090708100b01090e010501020d210c0e040b030a2109150903 69
    0x2140100304c0e0040456002c10510035070380d00380070840c0ea1010761401801840441c10b20221040030f0250720003980039001040005c02d21006000802d041c6042e0043d038029030166890507a50510950030140102d2400c1c0a50031800f80104000c40c0c0c42032160a07a250119200c11034800f10031680703401030303503164800c019030070030098240f00f01e080000c010035400085c0301c4001355805240e10038542c1e40e40074072403100110750461000c000c0c01401154040040354128083c0410522406200340b94510f9485128030000d0294010300c00e103680800c021207981d095a486060544105001400070542d40c030411a000954807000c1c0890550060244004240e03c031003030b400108180800e40018685001c85c0c00104842e0381c00154020101126081c4844050059034040c401e04118540d82c60840c2e0400e02c0707007000700e540440b0200c080c040c200e50030403034442481c0c00d1590320f50b03042e800240310140070301d040070985800070400000005185002c01d02141c584842c8500d12100441280210340d09032002d100f0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 206260107 1250 206258857 206258863
    0xb03070f0e0a050d02040b0306070206090d03050c03160507060615110303010b0a0f0915080402040c08060d02130f0603060515010206070c080d0902030613140a020609090903041701060503 82
    0x40e50518a080c41210804a000507880d4040c0c0c07094034850451042864119100e03500818003041d00203058800700c8c0380200c4080d4035a04100c0b901c007480d02680203205145402031181c42e001d21800403403581075035907a80c400d240100c0c0c1580400184076047c441800001c0450040310081c00c110358008183d0b070b000c02c2d00a8445002c00e1040c140c40e41003840140310313480d00041900d5600701d072490515454001100140ca1915450300305400e003050418203d41604d801000d4180110b101303030340c00c06c0700d0050b0100840340144140c403310fa00c440800100b0b0007600c1c014203919400f96110800054102640e00c940b005c45104da48200d80c00c40d210000c100d800000600b086050306001c1c00984440c0c9001400140940f11441c4001c1c00c511000c220a0882212544204410781c0e010b4103e440c1801c0c1f0241040d402c003c91002100c1c0002c0e010070310031030004007280dd06070302c03540a0202410300143e4410000031000c01051036020344400c0c000010341003207221015011210b84400025481e05020034541 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 206261357 1250 206260107 206260127
    0x90409030e120106050609060901050c16030b0a0c02150709170c040b03010b090c0d14010602010203060901230111010e03040b1c0522020f130609050f0f071211040b0307 74
    0xb5649450300400c582d440d40011a02c1c2d00c001115025034032100355005071820300034058107020754803030032091031000b0001e8025182924001c2900c0e03010741e40c0b140110700a407000342c0d075170000580204441d14104214821415000b9001c0e051050f41d00e41c07a200d812141d04012102c042c16540000364110b0307a07044c64803c1c131a032480f0540c0203100b40c14505020030303080000030300300414983c000030b15040308401552203a0102d900d2a0007400c100e50355000f009010750429100d007445100e80400000700032540513468590031700c6111882e0384001e05c4d0750040d660307000d17040f6010109540714984260511400d2004201802d1048030382500c440305040340901000c040902402440d151800b8802d20115001c105003007449140d0300c00744424000c0c4045803080120200d01e54001da0a11185070640045811050607907841b82020440313aa5076500b240e00208041c0c62010b4a000356801141d140d03442444036580f011700444010038410b6010217010103580c03103a03010072a051000310a0040143d40a46505c07 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 206262607 1250 206261357 206261389
    0x1201140a020708030612010f0c0806090604050127021303030215070509030604110d021816050304080f0c0a0b07090303090801020304020a2702040b130618030611090409030e 76
    0x6042004036612a04503220150000c6d2141d003030510741c503d0201003500100c4400c00012000e2043c540e03008005800400240c0b60540302d0000c080025105082c1407003607504135a10b03682e1240e41c4c112104506520040100d81c00312715107408100e0303c0c540300c03600d03060341d802144694020440c0e941000c81c0442d001c5c2c0c003c1d03e02c80c10403070108071030300c115a03000440e540c0041d0042c0b2005640b803820b10014040146200009401007400c0042d458802107015031144507000203044400070080702c0d5021580e0344000c03030380105103010600c58801410300c503c2c00b5060f07a0030134104455590a2640f00c030b01200d00201d800c8000200f0861040c0308050744040c000c002021144002e5081d81440d9001540c1e0f4207039800303854003000c443c0d104101c02e03140d011070081081c00d880318119512070f00d8600000080e4854030b01019091400c0300c0026402e80b05203402c103e21860030100314016070a603541c01002c3c020044080e005008144a4403030a5076840c0b2507201d034940b05e5150040d0300c041c81800d001e18003210385061 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 206263857 1250 206262607 206262611
    0xf040305060601111c032c010608161e12110f040e031210092a050702180403090302090711010b0f030d0e120a2405060a05060a030b1201140a 62
    0x1401e54580b000420404016100300c8100401172518011030081103004407841241e800e030f00c540b440680260b03c8401c0102224402806025102d20207160748001514003041285039003d810070101c03201c41030055421100566140720150b881103104c1c0c54801c0008103032a04003040c030704101146482d10b40c1266400e4140c90074001141d44019141d1071740039030200c01c007c56184800244100c2c2004c580040541a0070804002018503003030200b0103105000f81c15110700701c0b10f0b1308080340280902d080e04d241c10b030700611441ca07050041800ca400f4900182c421010702446034008001680e81000580c440c031115070b9116060000d4504440c251031350314520b50700503564980d0b81182e54030042030b0060038610303030305141e1305424001e40840c0850002c0c0080d00518000d20301c8040c01c10019805650f9074400286088006d440388000030005c95405840342588100100402c0143c2d0900078041c25601240c0d0400003607100b110004102400360412112080ea595276514240c1d184100c071109400842450003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 206265107 1250 206263857 206263877
    0x180f091a010f03150902121c12150605070602040803040905060f0901030506070521010303030903020f070501020a030c020415090b13090506040215040b0c010203070908010e0601050f1201020f040305060601 90
    0x144c640d13107002c10840c0c91685a1503109180039510340200100000e0901011140141c00c0210030010301e0401140340000541d4103201100e100d00caa0080c102d118040329002850741d0326103401a1141c0e809650219002c680074000022115002d01c007400003845031003004103e52401c001048595541d1050462007008207900500c0403c000143c1c2540c00310b1203003400340e50307080741c40320070340c03407000800350306280e00350b9500004c0101a455000005080e00c260203c0d02c01c0000070a040382c0f2000b150080d54016480002d2501c042407040036009180c0380003620000b442030421200580340b403020381028140da81c0310700c1c04040b103080203400e205200400c440d040002c0d100716039400f0703100d40015001900c551003444085455107201c0040394001c000040c016503039020081c0c0d03081d010f50021518000410241080003070189010b00804400b0030303281d0003802c07050307081100f04510003007818009900610401003002e211340091008200d05083e000c00991030b18618a401c0723240c840c00a1006041004c0c80074 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 206266357 1250 206265107 206265113
    0x6180c080405100b0607060e1006050108040519030314040609141501030605062b06050c0a02100f06050d0510051506160f020618091f180f091a010f03 66
    0xb0f10380034a0000424003246240c0c007040020854003e07034601820030351811003120328014001489000c0114112404c0c00341030b540e403005540b56941150060305d150070aa070301081080110078090100762007820001041415074080444c901400c80301107a2003030382c4031006410301040150851415041d40003d100d901c403000302c840034048040c80020629500c0d075010590507618034107003042c69207522030384800c00380c50442112825441d0000683d1010b02d030101180b80c2e0980502140d10814090300102107080205c0c044800401020840498095481c440410075566070400d0003c1940218000c04207502c244250341c044450103040300c6091140707048a00640e80b00c503030175074550941007840194034041c10f08022000c1c800c0031000942c859030020300e90540c0d1189580c02483c6840c141e641c074206a4540c100b28072019001203103c1c0001c0083c0c601003020311800703546209004107806011640c00b5440b04044251075084000325000a64038006201c5110326100407070040c410813060040980ca0b6032 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 206267607 1250 206266357 206266363
    0x51e010e0714040f020a05070b060402070f0803070c050d1101050901090c120507030b010320120705040b06090307140112020a080105040504030e030f07080c18150a0906180c080405 79
    0x84102d100c80351203156400703001c1d55990312003501e50440c05000d42d034a00c0811001000390340000700440f0480d144402082e12400d03d4400da038461640035004190250858842e45000d4100420710010029901282c1c00000d409000d40740040701e5988440f102c0a0000e68000c0c03c3d590300815000712a8942480c41004c941091101422129002c1440c20550b54a0070200c0c00c00105400142c99855001e0000080040c6500200c180540c3d1403041c1c10f07009814001c116903c220300c0300030f1200742c0c08001d0078007041c546540f03d041c2e012002803203145040c0c3c102d0007282c00d140680c1c0c403441d0000607401070b400311940c000c460842c007892010750452030709000301c0d00078140704418043d441c0216900d4001400b0140030300119a41d92a00a0495121030b8929952503541c641a010359441070161260504171401c1000841c0009520618807480c0e50ba03445603007151030044c0c5005181e0081d41e010b400204141d044c4a080e001d030048240282c01c112503500c0c05c03400c0d038150620910820503c002000b01040c404 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 206268857 1250 206267607 206267609
    0x90515160206060f060304080d0213030314070c1a07050f1e06010f090b0609030307050c040f0908040b160b012c01080c041109181f05130203100f03051e010e07 70
    0x205d592035201d440f541000074841c0a1a00b10400444c030000b40032645248188109084074440d5540fa11a1601c481c00400c0300c0c080c82100610984540b40e003400030f04403107641880e950f211a01c8071404c080e45a00c480b8070b02140d41d07420210799042410344070b1410b07180c0d0710040462003084005050652401918600d02c3c0b12510824400503034481080c41c80d9a00c01003191004000241141e868088a04115456501c04083d0034492883d00144120307858541c0180035015806c200600c0c00c2924004440140d580030841c402c08100c030740305c03201000071006420280038000d06c000003800350b0782a20044444040c0410701e1244128840c004000d240c07c005101e00c1d4a9005480c04641501c1007544190035004e50b01c40c595010b6900b50528074204080028140304a5108201e02000003004d18040900d1019004217500500f41e00030350b0f624080c040d0000c1d5040f218416020892a0791510034003410159500304807a50f4003d0448000d4048a01001034000b1100c00b00030800c150141081580d1140341d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 206270107 1250 206268857 206268859
    0x110a120e01021e07050c0607060f0b040c020703030e1801080610120f0f140607050a14090901031b120602120a050f01060f0c051e0d020c01050d050a090515160206060f 73
    0x920204103c0240000740e103410b1b000e88043c1d140d07030492400c3c2c1c0182030150140400d907494020b40b5941c1d858140100300d0702100c83e40190808034119201155001030011807030f9008801001d4885140c220725540300e000300100c8000d010305081000e101103410041d5800030034042c50001482020880b840100c4090540c4006140c0b11080107251443c201c03003400c0e1002d4190b008003810480f0980c1c0100081a0311071311951401e07002034140c012005a40940380304c461700050103030010700018801244004c210600405005085c0756100303807151054511850458846030041045100003142d5804150400c1c01e0680500071803a02009610300d900c81480345804000303c1d070301c0250005026036405146a90013801fa190400185881d03a0700c0d034420000c40102ca4880c0c1d05011045620100302c400c481e00301656014580405036091102070440509610801c40e55100d810b40060002c01c4804880403051103844120726040d1440140c3c16507540010007950005020840c440d40e84840030122007038 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 206271357 1250 206270107 206270167
    0x60d020d0e0a060e1509060c0a09080d0c0c0b030f0c0913020d050117030a0906050d1b02011401050f01120c09030b01030804030c0b0408030d0c03110a120e0102 70
    0x600c001a140500001c901c1c0701c0103030082c281c03500240181d42d004105000b00040885e41030350003410054603441c0d01112409840d0b0400c80201d800d00c40c0c180c0080c12a18981d1814240f00381c0c941010a040042d81071180b000301d00c3e003141002c00c2000701c051800c0208100019242185845074410820301d80081c41c900018800041d10a00c980c0c4140d0390100c0020004421500c0341d0030190071500901d42070050440b4807100d07560141280500108403200e880007555401283c614116050303070250088561b140800c0c0d03c2c0c54100640d51400d1128050721b45041e070010605680a1002c140c0c08201070304024081e60702e4001003421079130400400d40404028070030004014141d0441250001505d4200920f580c20b00030000003440b90b10000703081900c0c081e01d030345c1c1056583c400b000051441144903102803508148a0817030f00b06895807114042c095a814013140b103182e05c00700003040350301c000b47d4100032a406502e0110b101c0e0740ba210b01c0000b500c459008614010207195203840160442c1d41c0800c69130 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 206272607 1250 206271357 206271367
    0xa0201030f0204320f0a0303030b030c04050c0909012102150c1f0f090209010509090709020a03020705010f05010e041707021e0108060a140d1a040804080d030b060d02 73
    0x41c420b80e040b10b0040c128045407106811880032406145424884018400003150026020924001c082204c41081c020300c5400081e24665007034000d07041c80c2c100d41d6810b000b8607024060719200d5004482c0710345c03000d1030a99034402d003400070008003d40c1038000e0b0020400718141c2c51980b0011002e54140c05404507a2045004000702c8209032038450b03500a10b00c24021442480480d80d21011a044918013044060003000b00350b50030314040b1422004040e43c844860300042009090074003003150449408026a008a900c61b614441030368446035008002a50000309201800400e04ca04041a00301030014000755152011036011044090809440d0840a1214241c40c40300101120710043c1d0142c20800d071036500e92500100e080b4407003240c03800b00701e6440025045107040a407a0043d140710211034010141e21005100c1108810701040f03414261517681c00480f0400403030000d22480c404c242080c2d945060201590070240e51352800d605050030550031203120355030724003500d41c2c0c510040001130300c0d2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 206273857 1250 206272607 206272631
    0xd0f14010f270903052703030901111009050c010e03120d020a090e07020a0b010909200103020403052b170105010516021c020a060f050f0c010b0603130b180a020103 72
    0x10702400d1100c100954506240a0304045c0c02101603e14110701c5402540708040000d110502035011030b80507a450340080001602d41e43c041c682030b090706512402141c1e141000d0908072002c40348a040196102c2d4402d800480e91507030b011140c0203240c00f013a005451003072203204900a040c00b404444200058020960754155440b54032a10010044901a0101e40c1403e0302c0c007030345134440c1540640306100700d0700000c20b07410301d0f0b4058054150380c0b16003008983d080c00003000c0300304400c4902d0241007540030480000861400c10104840302c100300c65002984180345062085140000701c0c4c401071048456060f00364101403050a41101c800f0308245a403a0000c0034119a5130140000003948090140a40b4050414450128215034401d0394500d44440d1184001d03603240442060b41d030001102001030300451156000542134101005d0b0000c112000404006280c0ea00210b50b60707080a1000f10710b41c420b0210a9524130b421140b0400c2c4107a181041d002c0702c0c1c0d15100d960030040d0507d91030300031041d40 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 206275107 1250 206273857 206273909
    0x201021b06070b01030c090c0c050d0819020a050405130b030a03110a140f10050903040506070c031425050d3f080115080609070509060d0f14010f 64
    0xb403554003030b0018903d5a100d01d00443e1000841c0170b5040762921303202942c046940610340000000d600704000b4404411800c100711203406c1c0040560525425092514480c40a0780c006000c034410759031031341c0703444500f0541440300034a94105404405030410240c100c0741c0d1800b0480c03c10951f01860201007030342201c01d8051a04200303041c000c0c90004042d90039802c405020ac1c4140307003800ca6505950803c1036269564040e118150303540403268008100402c11450200b00a025540c41603850184690303983e15801c9d24204003020011007601300c141c056400c40200d040001000102d02c103403502c080d0030321000c05c8032030040200c001d080e95901999240350030914010b00c80302c020841000d0071004440e0400100c01503085e00d504011511100c00403500c6d8203096a5207021400ca9602d440c0305603554820058090400b40801c0d0034000100002400c1c3d440310340c003e203410b01303a0010110300c51810000d840204c415031291500d5a0007150018002c41403191501d0003101d05030038002c1d244080d90600451 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 206276357 1250 206275107 206275117
    0x6050903102309012304020108060405040302030423090406090b0f0408160206090301060f06030c17151f08010e0109021207110111071407060206090a021005120f06030d05070201021b06 81
    0x3c28580002c03002e00c0020004170a40c41070b4400e0340e1f090b84949400c024003050301d00640e4001c000d03070020700c410b10030405140076160002500445404144000c4004144034035000d0700cac00d944050300e44101ca824040102855500051154503011b224a05034444811502462910400c0b00f00c4130607803c820356442c1300a4030b50b00c03a0006c0c02000495503413171038200e441d0401c0c4941800301f03007840346c0c3d841154055801580c1d001c010b100c460b903d540d5003c885801842601c0701d01a8044041d1355200b0103034003d1103104698407100c0c0c40c2d1802c2541041d4068403920416801280750f1801086252086141c00c82c3ea1078000070039051109800f940e030408540074040e1140da00390002d402003050300501042e0991801c00d1a890000d80741c1090f01c80208985610007215010680d0740500600c90050903c00f0000d9424180c1d40317055800c04410510007520b951003a101e502090111b40d0a0003064527083c0001c0c40d024005082980c0762041940c0080c0d10f580240c407042250102c11418a00c494540c081200d03 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 206277607 1250 206276357 206276381
    0x5030a1a1008040201121a060f070b0c030415050103030516060204051206040212010b0102120d1506030213050a051e0a030501020c03030f0718090b03160605090310230901 75
    0x3101c103849100d0020640c01d02290103038002400c408101e80791005512a0941000c0c4512080035418141018002154440100403140f020100010f8020850360b1f80d460740103810614000e540ea08141c10034440c100141915825440c2c178080041000941180c101c40c6000010030710308510245074100301c0d0003030141e507011a400030600c00305014151800b00d01d0500c6680b0032510ba40321301e0f080200e064200e60b90601e55034050317840306400d20b554540501c0580300794001e0423408100040302e00c16044010485911410120341c000c04d0b510f00c21041c130365115028003016206001c515280000250340d4007420002080005640d000401c010b4490741c1c00c00001e560014020742d41e501a12403650360b0390348221040700d0560308000224000034441e015622118400b4001c1d00c01c464241808000103028424076190f241c81600c1e5900a0303581c9101c03100000b841aa16800c3d110400d020030f041c200b101204103850b20700c0c541184002c4070700e507a82030112405882c40c800c0ea0555980b5110f00d00406624100f0307 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 206278857 1250 206277607 206277619
    0xe010c050d020106052103071b031a040203010516020706030c02030403060c1809060315052701051906180213030c1401090801050906070e010e060f0307020f030a05030a1a 75
    0x81201c241d01508030104030fa8096508141c0035080c0002036148039800c8000000a0b0001c01042c4086030760054800a041034040145541d00c1c0d40741d036038140c00b90022000301d4680c1820800c1105524080c881c0e0b56014500302401e240d1703003140480080d120002405400241980d031001c608400b4420804d032409554000c0040120301800031015202d146000441a0180c01c011130200b001c80ca280a410200d0750b01001e04490403c800180744040c140060210f00b0b48002c041a02807110004962401c40352010000056180ad01e005002d1510342c1c0303107801c2004541000f4007008442c1c806030055414108801c40140c03142c0418800b00f11020f0240e0010f000d00f000680c010400307010345040206859000d03200c810307a240d078545441e826142d00301c0e0000380d29041400000c09031406034400d0020b051051515110114600001a00030b030041c6040b00051a07000c0100030700140c04010b080d580310f4903c0e00650034201c01480c01011480010080020180c03100310020302d84a161003400f40c107013002840c1d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 206280107 1250 206278857 206278873
    0x706031103041a071818110c06010b07060207150507030f0c0212031e040303060e10030f17040b120103020301060501020f0d03020d090c03030309110f0609120f1e06061f0e010c05 78
    0x3d41207940c4440d48111002c6d901d4a916851005a01302c1200c81034102070001e042c0680c0781c007505044a070007086060700e403940c00300000e00001e07806114080a07015a40c2e00045c25040036080102110061f240008031607180003807000f1b026030002404114121407148091b0743ea6100e02d8540c610301c8202309600e14414104081c03104040d00360b000102950256400d015290791402c2c00c0e0848150544400340003210000b0480340800c00c202e03807072021552944d0303807d49010742c0c500507411250700100d01340b0091112080107100710301d820f016003002400240300900306456460700060f2111010201d82042c540e0000726004925669044808100e82001300c01c4000c0e0b54074140030707002c1c0281000132a030396940c060100c1540d1404805003002110040c0809007840080002c0c45190000e0000e00c0c0d071548034011013440e800b007003084841c141c9200f800301c0c1c035401d0b841c20a40310725008010780242e01c1008a43e03030440180d00e283c084111542214541032200d20300c1d040042e1074074590410060940d0155401c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 206281357 1250 206280107 206280119
    0x10b031003200306070c050111090a0506090d02030303130204060f06020c060c01060f030803070e0d1101141201120308070201020702030d140910270803040302040902130e0706031103041a0718 84
    0x86d46940d8030b025000030703c0b08000f0105104054031034002069031000300b10320103110a0502101411103800003070301c441c6246c11707035400092030354100710741400c1c010304000c801d001181400c1c040e55005201c034020070f0b0181414544040e4485c034070104420302400f4040391102c6449000d42001c0c0c000c10800201c404500e841381880d0490784d10459440340443d0903035006982d24202003a070380680c0c60b01b2582079401c0310581d10044030007068145000f150590240301e600098000210114020404031100d0001c01503503240213881b400004211034203592050103600007684010609104100e21407810841d800030f42860f915144c01000d92340354201900301c44403010641c010703100310301d80141200a1030000040149001d00c1400f640118102074005020030801418103411190319688001d0680142d10f42102c01d04044034540401c140359a4001b507410005583c1500c01c4540b100000006030b859071030161030f000e40b15a0002c0d9a0700c0105581000122114030601403070300b00f4407030030129040840e6211 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 206282607 1250 206281357 206281367
    0x1206050609010e04170319060f030308130305070b061f17150a03110109030f0609020a05180f0c0f0a110705192709060f05010b03100320030607 63
    0x1524540104441e60011901c401010001d0340308941c0300c5c0350003918102c0c80e60460442d0f00080c0a00302e4074004c0c5850145032a074180030307500c09400b0080160051601d1418000c0420f83c0103401101d00c0c1c1101c0501002082d030040032250707c2c6401c43c003405080d4403584081b4000c4c9181040c07030021103032076070b42c90110190b000504141303400342905150887d40b1000ca81030b160490303d819aa034043c01401c0c04000040050302c462110202c14140040800e5603a111038a102041c00011100d03966030301000e5003186410b2070313a90f0140c9002e84844840071450190000c0b0741c0d00c00741141c2503840d021000034001c40d14540449060b19840f005203921559101030142000c6141c0b5031a855074002c0000201e4a420140381d02c0d11035544001c00c000609148c88102426100a046100c00c02c030000305503054076952602131810000c2c4101000a280c0c400b460010b030441d681070b0080c202c451030400500c00503490f00c0d0340c80742c00c0c0c070782088200b0f100380a501d6140604e00e68a81d9126094000d001c20883c541c1c2d005 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 206283857 1250 206282607 206282611
    0x33030f090c0a150c020301060f030c031218030308090c120c181512030903060f01080f0a05100f0209040f092d030e040e0105091605150906090307120605 67
    0x31011104148500c00c1000030424140c010150349441000b030000c091442190044003090001d00006215a140e6004840b6000346410507200030051a50420800c641c440e0803964024952808140c0480d500000380c80c101c0741c9200c003404008850004c200c9004050185500b42d283c000c1860056200340c560b9a0b4540804401403031080014105c08800d5401c01038400340310341050040c05040e084000100480f0752207208038400288010321041209413401c200c0b00380111114400c1e06069854100b01920f8000124200910350308581c0340000042e00000c0c40e04901a142c400c0490240f03483c4040d540240588040c1607030181c01e114100741c442ca461740c05854024001c1c100034030940241031110242c48425503100900072881c80c1c0445c0482d124910000d220940104003190020000e20b034103081d590107030f82c007c080d60010042031050322140300000004142c10344441420248115081b41280521854980200400030360b40c0341903035040c40720134040c200031a600c0400c80441d00b4644028082 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 206285107 1250 206283857 206283871
    0x5010f0c09050612070c12031b05090108011809050102070b060307060810210203010207030215011703030f15030f0124121202010b15070c0603050633030f 68
    0x902401810390511031156003056941c0609140e207003020b01803d6003d007200040c8840100020190820006094a88a00b282e01031952300030501200010f00100b010800080c100f06001d07040200902c1640c00042883c11143e49070010140c001300c40d08403c1c060001681d0041281d44000741441c01c00c07802c010f440740282c10a404036000140ca4000585040c681911510790a00c0e2403601000864803032103121103400302003400f40c10502e01a0380841c1c01c1ea0004882140960800c0541e00350b500c0464181ea401090010b4200d8100e2500c070600030340340d00c00501754590015018001031030b41d00013480c80d03440c6804046c045400030380301c004000e8024600d02e2143c10b80259480a5a00d0b250a411412010b40e800e860b1840300c00410380c0e0300c8241040718200410255500c0fa100515280d490b6400b040d20a0320b10190550f64403190700e4905040c0c5000c1c0c0100007030506e8201884800c0d100e900075085c48056201d4014600d00e041b4030315144491242204888000001040191124250a43c5409802 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 206286357 1250 206285107 206285111
    0x70302100b0306010518060a0902040308030702010b061c0e150c22061202090a0308040f0e0a0e0c0123040b0711030d0e010c0606080a06090b0a0606020a0b09100905010f 74
    0x114000b09a00d41c0030070b210b20743c0e0040700580c07480420002c510015070410402043c000c030580d40d0f031108406980042e4010b41e200c20703001c41084226502805000019042100c00f1031403c100901c50700c2d1200141021081c520380d580200d611521001c02482e0710106030030103998040d140c00010b03c05207905c0000c80303030340e812984075007000090b0700c040400c41900e109440c0c240b036440d400d000030802074011504d2075a10124515000012848503001030000e0304c0c4d15602c0300e101d542800703072030001d4000241041c86940c0c641682d0681e442c41c0403c00703d014030001d10b0044013900c11002c035414844c582041c6403000303203400103002a500744010000e0500710310526808554140c0202010703100c10403030034101d0200314184030005143d881004042501403107001c00103046600c1e907004074908911100f085840071b80d6200307010103125400c400590b128a007000240605402c0c000000d448144400c0300500c440711a00c0072417105101408143c1c42c080303030b442b010404903c2505003076028010444040621034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 206287607 1250 206286357 206286371
    0xc262412011d0303040807110102011e150506030c0f0a020a0510060e061002070b1e1303030806031b040f0b040507090f060306050303091201060803030c090a050f010c02040e011107030210 82
    0x100000c41901d01c11740d04840614101101c0b41c9564000000341c000707480c119580c2e188001c20050681c00c0340419448040c0002503c02341c940c126500038002600410b00c110024810071190b05290340842e024031202c0c44a44c0c0d11051035002c00e030f192401e4202e0041a41c0030b540c00070440310300719030310000c1191420103a03004103031240e8080c0032408080c0301c07221005800c02c01003840500219801813030101c5501000488140c001181c842c925081940c800021162a1804000340340c0d2102c20503800c01e40482c0900203582d01c464900015446040d00c06000c0d58464440004185803030b44421010701c00500306200516184000410008040c007500070303e00d84503c1d01003001ca110b031003a001a244064011441c0990b000b08208a8120110401c00250f4070b8642c0030075150030034005103008000d000e040700e885802d810100419070a80c2d80003180178010f1a9024030990ba400074041c081c00d90192070010701030408070085805000004603a540c0c200001400c071040543c0050605150028030200304002 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 206288857 1250 206287607 206287661
    0xb0411030624090421030e07061119020a21050d020c0f0d06020c01020f0414030d12150503060106052113240f0c26241201 54
    0x190091400b0001c04048252101c41c00c180074000c0c1c01a0042d1650030340e400a40c1d02d045000ca4444000c0c00000762a1044801409800c00140000c0e0155003001e10080440c4d45e501665400f9117040d9440c0700c41400790403000d545a1910350b5000e480f50104103003503034084082c4414000880c01d03040b141803050100d0004011310105211428510090445004c28010420041d800011050644101d5402c01607403510b188244020008900c8141e021600c891070100840c040601c0305111030b000750000e00e04800310550003c41e00c201c0010301c1c440002c40c04070981580b59400c0594204640522a8500100d4200d8000d0702810422584902140036032048400242c031440702a9103030040c03042d10b201c0950021340d418503492021403c4004400e0010b400070118001e0b2996020380d030a41d255225411020190f0026004200322400d00c1501100d42c01448410486031000f0034078084103803100c0003603c1d20b90b64025612641200100540300c041a2401c0850092541d001d07564031701225182c9032410 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 206290107 1250 206288857 206288881
    0x9041406010e090412050c010f0c0903021903031e020c030d2109080301030303090822090507110a031809090b010e010f03050a082a0d0e0a0b04050d020d0b04110306 72
    0x131450344402d112041030400001503480d6041000c85515075500d41c0000c107503c801c58441c4521805590b522618000d2550040c055020b50305140c44880030302030706091000c40d80000450050300707101e0384d400c046a110450200d08007852246c900d84e150042206545906621014403256480c003411011850b13040c00910b42c040300c000c100700411406090004001181c002c0e80426401801400f061b890030b1101d04403c0f8403500501000009080072407820f21036140e08cc89030070341c8189107003080c82c104c0e11403c0c41240c2e5000c0440c8000d00b00414954405c0400c161500b0490027042c0840090120180071315081000460034051540d8000044000050080300c00b42030f241180d800a0182100c002d4548600c1c10361360005600c2c1003051141200c0a04007010454016460300598014003d02d80600700000d02854030002c2c2c440c81844003030f10500402d100c240440f0b080380c0341201c40c24074244031341c808120300c1c0308903000140c0740e458540204014040845601c040d4100120150342442d42c81d85c4406203 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 206291357 1250 206290107 206290111
    0x403050312061309150b151306031a011e09150903060b09130821090a150501260f1603051002030c03010302120703050d0f0e09010b07120509041406010e09 68
    0xa07120300700f1510741800d07005c6d484040b40e4140607210a812100e14a0209002c2d406400d80c483c0c0354041020401c404c0c0d41c180f00d910a10200d55102182501c100d200080c41d242c1d4010304950280c484d1002c46404034040c64400c0c005010300c035248d5031131040c01c500c0031b410120184410b46141e401c5c011080305500d0301f402424415a0809110001c51001d030b198450301d070f0040780c070b080e02c180480301a03e0b032500315014000d481051102c00030144150145420703e2180046402c1c500903505010041c418141150003126034580c0a000104d56003048207805880e050342c1c1e0000c0c10711801100c07100a4901043c070003460940780100c0489805020400c8644102d20088455002d9004144018001864520000c0d01c0180702c200403150b1003a2a40c9810f404c060440c6950804a142d040703400d1119a009a501c02c01600304940200381585410881e01c001e221310710340182a8140c1c0d03064041c15500803029910327400300140081004074003007c200e2101c240141c0341035000c6283d110340c021551a003055154 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 206292607 1250 206291357 206291363
    0x601170d0804050a06060902041d071e05220f0611030729070503090d0504121112060708070e030606150c07050d050a03170403080f0c0403050312061309 67
    0x10140000c0c00100c1d0303003038030181003182c40d07004180034140411501e005250103400c01307050043e522841e0101914041c4250020382800310084c0c1c080040407a0440141c2080340510880c96001400001048070380c4d100b01408040150505010024038a41c0c10400f00c095407204402c00300060744076a000e0700c0703803004c144050a883d4800c10039500014580382c440d03012900074414a0024903010000294000001c48400300018400310800203008801c01210040b0f000c0350034840e150500307007640643c540e14aa0000307030601d00c45116540480e2204090703008802c245105807516410840401010300d04251003240000c0d090810300789891034046600d5000300d50080103454240c202e40b0740da070303201d400c41c01e001601030007003007400078468440d140c00c0c4100300d200380084e050300c1c000d915025105412210071a5840c400680c2080700190708501c0c01c54200941d1035075500107980b00c225074000c501c02e903040289103010100f0f603528401c004140c0c15015040849030382d45185501da0f280000c4610071500a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 206293857 1250 206292607 206292613
    0xa08060904050a0f0c0b0d0b04061508060409021210090515061f03060504020703090503010e03131e0314030d0b060906120a02160b040501060501090f0902030604090b010611060117 79
    0x80013844c54001c01d1491449807081d44111640e4007481d42094001540e1f50125907100d882d0b2040c145481d02c25480902011145607000900b480c100070504c05009106501a83d503803c07081c015580c0f00403131440c2c500000403c07140c10642001c2d040d006010074007821501440340000c080300100002800b107104040142c1442a10540c1002185180804c1ca410b10309050ba500c601081580321b600040c41c0e4a80a40c4a0005192510080c1800c55100e822030800941050004e10018900320038107804507080d0307441880308503102105040040110394802040780c2200941c08c03501c040080064803012050b05410403000c0100b40a2020a206803545264056002c02101101e42d6070443d580b81c00c042a003000500f40400d616445540312004481034030485030075020001000800d0260b42c01403c800e00c2c01d4040e162500c410045601014003c01800c01e401100141003621a0b6002540c4180c002e03012024650f03603500080d02c84026018140441d0203490004a00040103602c0b00b001c0022010007 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 206294964 1107 206293857 206293873
    0xe09150f01060905010c030e1903050d08090d0c060902060a110d030603020f0603040305130b0a02070b030c120c1b0105070f02010b01090306020a030b03030d020a0806090405 76
    0x200e1034040c5105001031001c2c5521510040c1150701c2030920107906019440c0a8460000000d000c03030b00a10204258031f14401c240a035202260700038815201e940e40c08000403151080d0854203804294841d40243c01902e1040c19586d104a004410004216030a980051190f9101904400c00140d001200070440c0c0400e01c0b14610044032400e0800042c2c0c55640418100344000c4c1c240e52041c1d43c040001002d050140b001c43d68400d801d209034074400b03a256a05240d00303400c004054001417041140100d001e10b24823080360b02408000c60b01d1403c0c0b1402002680021200030609908100c047c0701f0115020106040e60002500200000c501382c5050392000b403480e000702c282d92045a040c10070501c09640c1008540055a400c182d0159980b50500001c3d00504041c007100e03601888000341d64184c040190b806008400120341c0d81290b00d44804081003062130042d80c026249400c0303010 = true := by decide +kernel

theorem cover : BRFrame.Cov 206115107 206294964 := by
  have h0 := BRFrame.cov_init 206115107
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 206115107 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 206115107 ≤ n) (h2 : n < 206294964) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
