-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5318
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:28:43.727924+00:00
-- url     : https://prove2.me/submissions/b8e05997-f4ee-46fb-9969-08b8a5646f31

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 956294964 ≤ n < 956474820 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 956296214 1250 956294964 956295001
    0x5091905030316020f100c081302030c0f01050706060f050f040e0d080601050c060109021c0207030f2f0c03010c020a0507031b05040c200a03201c082409 67
    0x11790b1135020f03143c0512030420400b9885211400e4590b19554401036114080c1903000015240004030607005402280d9141100074403a07004001e6000841c2d20350780114261807103940c0c000c0041c05219100c840c42c094401d0306100c0c0900480171500c5005aa10f814007d41c1c0d0422a15402411045945101181e410401400705814070100b044901200101404a40e018044000380541d640710081c208000c140d08075103200c81501c0c4140404e000081d803001001c90400ca0924004c100640340d0481401e003441214605200001c0f65882e03040c00040c0800c4904602c00c003200200541304140506070f03151309101200800d02d4202034022310009001030105070148130750000400046481c3d00c0420100c4981d00d20700404581c61201c40c0b01d01c0e1804061500304060004050321481d40d66a5016010781d107555540c2c4150640142e09080000d000c003e66210324006c3c54030856a10003d0034060140300040d9004c0890704412045800801d4110b41d1049960030041c01c100c001da580c60410b0300001c058007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 956297464 1250 956296214 956296217
    0x4060507030905061503070603090305120441061003141e06040c081606120b0d08040311010c0803040f03020a0b0109060e100305030906030c1c05091905030316 70
    0x4030140c50214801304443d6103e207542c5520329850200c018201403070f00c4080d034000000c0508102c080000640d03c041583e81e860000070150180703441d40e00e45001000c40300c42c0c42101ca115401000c80449032030350200d40c420842070300403d094100608400d03843d80c00880c2c80c2c040071035190008000081607543c950b200380710744009442d01044819a0002c071013580f41000449940510305120034081c1c9511940010942d00b001032104101b40403c801401c1c1d091b1059a050210340c106203000c0340441d03001759590090040001c140b0b13001034907081103550003034003003617440c240701c48210203095020340b0106640f2034101080c1c9080d0740d81d940d00e01c00b404074106021070841c010420204002503014036540e02030400392201140c3d00341081c0024140000c000d0015041016045003007000c24800300071522507100698440713940780d40700c2d80d2000b0f2070b110b01d42c1ca03510042d1400c00030884d01c5806a0115020380c0110341603845061880a0080340040e04d414090040d400800110340d648070305100601c80310303005 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 956298714 1250 956297464 956297471
    0xc1203030e0601181a031e01111321020a030215070b25020601030804090c170403120b0603151924020c120601060f05071b050915090406050703 63
    0x100a9050180a034803130f03c400b40305403c0310101040240659501c2940c1038039650340c0000c04200280c0e460011a1256060000f05026515008400c0d0032582d00300750008003d942c0c4510305800900710000601c108c142000034aa50214040281e0700c624151a0300100844921030550b001c002c401020911030301c070002d81c00c001280000300c1e00c13040e03140315a80c96141012020510f1004e09644190b00f602c8000315041200180300183c0d00c00700351025a1881000000c1044072174406482c120b800240c0704c00e84411040804c0101640715501251400c0032042c148903c404000600025010a42d040e050100c61481c03040110b042004c2c2c490026907401c1701c000b000d03d9a540241c038891030018040111407103180c40c000381e401d40402c4000484001034500701c0c03c4c1580b01c0c090503100ca02c1070060a0410180f800d040301554030401c1543d00302500044a944014400f082c107034030041c2103100f014000c01c3e440d400a0a422440b41d008021442c010700a1001e40d07859a407144000c2500400007810f06a4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 956299964 1250 956298714 956298731
    0x1804020d090501050a0b04060602060c220e161d10140a09031a0c0d0b03071715070504050f0d02180405100605040203060f0405041403030c04060e06070c120303 70
    0x10a019400c41c00b03010701c0000074141004041c0d442070b68000c640301c07401603041280400c00340d5800608540e201118019013600c0b0310854400088814204a460f03403a455145004180304d00403e0000d402005628210a401d12608209440302c0d41c420990002ca165120981161801e10780c001c500400030b5807800340140070742d035100448280c001c044024005540c511040c0100040f6204012140060800001c49444d0000d0849164491222001c100e95100c400d003001a860801640003c0c289515a80740c1d0020418a0780d0f999810006000782c60a8540c000328201500800444d030646401500400d004042841070014880e550b01d8100e810a009101035249407148403075082c022445a0b01402100c949d0101050613120107030031142c4110320400030f100d81036035601c039042000302d0203a03070108003030707031941403425008800020035031007804000304024000d58408000c1003624000e85030b0696a91403141409114080d00d480100100e200100078842c000500c1756100b030a0344030380340125103c03d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 956301214 1250 956299964 956299987
    0x30903190e014a040b090f190b060f120a060503030a180e01060c0203060c03010e0f06040906090302060601270b0f1603030204030204050f1314030d29090903180402 72
    0x25007000c0d00c3d60454400049030300c0340d840d160145034826a0211124601804c016152901500000e0036994403240d142804442c0e69600303400c0740e0460a0b009060f19250261302020300c0741d030350142c0182c01039590000c0002d00381c00301d28455131050b180068000e44c1058005c03d0140c44000c3e0880746602c1c8444040c4c40090344101d44c500b1030307000c2c00b00341e564400603a200e4414186001000341c036650707488170140014002840342c0d070089540240703807a086803610b807550000300307000300060300e40980054140509501419000120b55019032020781e00c0e104c46200700b000000f068034040040c012140082c0e18100143c0c1c6202004c0c0c551880c01032034107841d00f45420108540b800411400710003282e0080b03400c1095141078418564002000d19008c64980340c00c1c6054000d24a003201b0003421440c034400c00040003c0b0070420758000746450001003110320141d01e0700305940250040b4415046124400120ae541070100c80140102c403140010b5080040715a0400100000c004403603070041c0e82070000c6c80105 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 956302464 1250 956301214 956301317
    0x30d0c0b13170c1608060a1e240801111803150f0a050c0406021f0209040f0e1b06030f1504020a030212010f0f050607020402040506030903190e01 64
    0x2d1180d0107030364038400501070070308180ca40c0c15140c14000c4c4c400400c01100002244813680705a10080000d120000d00341710900f00f142604411a09525140c4c80d4100344410680b4010340c61a011a0082c00c1c03135076003803030500381c43c00400c0c9d10303039020740601000100c114450720410440f28020b003601d1f50301005d072701c8121101404890740f5500d65129000d0040f1440c5520409070840100d2580c40c1c50b041c01c25034081e5442d001d031a0144641c4103030400742da0000155034162502920001d109201006480340d200000d071846004d42161405480c0041c2141da03420000001004d10140100e03081d0ba494030041d500c4c4000043c020384104030700248280036543c1e18401040c40c0c000356100181c85460b030500080300078005821507459440f207035406000303000207107210710b040380d00854980d5502c210500c081006401551b020a4000c034002c010310012000102c040c0204031445a584a1742207031540e0700b200d510403810061408141c2e80040d50700c00140c5810048030400c8504610b0f0f604500c400f5071000035 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 956303714 1250 956302464 956302493
    0x11031209030711040903140d141501080a090b18010f090803070e0d0203030f0922020304120311030f130b0a05100b07051207020a0b04140a05030d0c0b13 67
    0x603420014990081044110820740c0300d500c281c070200004a410313a03011f04405210200c08140401c04203078403075034010036001034401a51845101903c5c3c02d102c4450010301c14074002c150f01042d03500000503003001c03091142d503c0980c0c0100d10208a5112250241981c03200c10400740200c0d5200d100c1450214128020004481e01c202502d982d01c1c508120010280d83c2000807403032103800141416000761754000160703000c0f010003040c125960300b05d00e000500038503240340403c600c2007071440820300c0c0c01c50035074003461113a4040e608519030000c060100314220b94010380b25040100d0180042090a080d0b040541d80c0200700c01e0b02c400100d001d5444044d450070013203800c100240d440d5801c2003195420206000000c24408840e641840310795551562616011401c2c1c940030f48001c03800d9419599006a01c100904040303014030383e601d444030448100c05030b4070540d15000d00303200b4000180908001542c95100c0c00569190265018540c2d40e48030092405400c1e2080f0031841c4040f08085645101129170 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 956304964 1250 956303714 956303731
    0x7091e090f0f230f1e0a0c090f0c020d0207090c03270312180204050408090a030c0608060105070f15020f1309050901090f0308040c09020d0203100e0c0406110312 71
    0x2800e8008501400c840c514003c0f03005401008100402120000b05003c0380c04040c001209128445241d5620303000c00c0010280402952280c0003070400e42c56844088248a2600c1c1442004c54030b150580c1e990302c3d8030a2860040e84401c404000000096001c0070080032940b07000b14542c003108003a00703107024034002c11400c0701c0e030200c216004050304160032000e000c2030060309122a0340c0c81d0b400f60304180b18854010380280e4649000504000301c0c841212480b0748010890341145449007012a9101d246000307800c00b10395a1401309281c2e41c012400d0700c0300b0540c003040c81d0b0041c100356036801c2e40702d0442074182c00319250203004038503051070407002030009801106910243c83d45081c2c9280241c0b1400b030a1010700707915084004010800302d10404203003e406040005c0c06843c0e51030101a80b40455004400d654801309400c680c503003094000318002c10128000b07104e503036254440c85403551025160301e421038108010400840d400355203448030121600b82541d04094100c0741914100008581d41107 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 956306214 1250 956304964 956304983
    0x20f03160f022a0607121d010504030b10090c09140316090218120c130b100f050706061409070f0806010e0a030803011d130b0f0405011b08060307091e090f0f 69
    0x1c0c10076480001c7d214250307003400a40d40d8800d4080b0018002c0d208900014107540078480016a404400c40403402c010032054400b048800100301004006207014054519490a0156840780c0781c0740003d95814800403d80064003881d10f030419103002540501c06400701c440850140400715940c41c040c1d004030400704005030000d034214804102c40020301d83d03c01ca00040c90101280c415071920140140c2d000b110707042c074088140302090140c03818050281c1c0103120604200000c644050400c0d000f580c0c001060b02e110710075131103013041a1009003101e4100790000d40b00400145031584551803080c1c0300b41d000350038201115100d881d6001e050b4002d03000711011254074060a05040d5590009680c001c03002d0807004e410390340340c3c4d03525043c000c400341030254154100000b190a22074290300c000304501111120301c2c00203036450400313171443c5000c03a00745100c2d02a20200040d02030150140c0200001c1081130000400111344c800c00007400d0000c02a99004030020119000803e844641c0442900803050b02 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 956307464 1250 956306214 956306243
    0x1e0309052d060103150903020a0b01030c242703020414060f060c100c1101020c010603050c010f090e0406110a08090106050a03050a02120f01020f03160f022a0607 71
    0x51032118116540070070300da024200400108401c0d9030441109468807102080742001d905041780340203034000d800742a8078492000002000000c4070444101e920100f0040b102003204080c51101500c000c000c0f4011640c00c44c1da814001161038945000b00501029240c00a81c494000c04c003244c01c0e1500040110422006204451800202d04d202e00c000c1201c00da132524402a40140d1220400242d050409450303820110b2500d0080c011150140a450b000315110316404d100d4501900c410705c030039516070180d00f860300501d52040b11082507843c0c1c04e84a5498280c6004041ca14818000304280d0701c0ca43d072085c407045c140ca90b8000421100b8603ea66041d030908001d901c02e401c4565660120384a031032915010170001c0c6011905d14030f50360f0100d90b081c0c408222a0f0240d800c112a02100e41031075403002800100c0c4a0840000e5802502c1034241c01030070400c95101a030305e0f9154440c600e1b0160703001042c9009820290220901a03440442c00541d100040501003281908010000c640740d000e0741081 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 956308714 1250 956307464 956307523
    0x110c121201050306090d1b0602160c090b240c030c0d0806010201150b0c07083705030906130504141f06140702010309120302281e030905 60
    0x305805080c04401400c40390401c079443e0380e40c42c0000c0351240244007084500c624000c0c0100d5030141c0742900080203550702c0031803001d5a29900170520045a41641403c8081a00000c2e407107800d454035070290041045c049030808140704202d070303000e524001640c1084041c05000c82440600740084812000b045041d140004c007a12034180107182c2c5046a16024800380305508080803281242c2c0340c0c24000b507640c00441038403420000706801c40c0309144514505103003008480c0c40032070400461607240710b04800306003012142110001c20040c101c0d5200340008609860148010140c0d000746203103074000186d1713600220381520102030b40402000340b242c080155401e51a00403206107480c5885103d1000d0800802800d082ca0f02c0d203000c150940c3c04111b010840e400307944004119500450250052444a10b0040296002e40c0a0540028045803103146010480302540340c0c003c001c0e00c0d80e042d100d2000c0c80240c060314401140720308042c0c031403030280c010540511031500d00200f004400300b9004d41c91b001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 956309964 1250 956308714 956308747
    0x25050d08120a020901020703030e011106091c023403150f0f02030402030d0f02010e120a0207230904020406090f0c110703020a03020d1113020a02060c07020d0204110c12 74
    0x20502c165401008515160383c1e0114601055950609114044030060b80048851015004410300301c1c1c030400303040c04201c00b80018446550071442030700980d2084807150490701c5a00808040081140c1118140b991800d000e514281c1e2151929214851a607691a500c2c3d0a8110f100c42c25447e542d40c1054008a010f1809065028210b8002c107600d10b00b00303640801d60311751114201104001001401ca000103100390040c540c140321034012203000c0443c0700b40e5100d4aa2040325103901501c42d5480001d4040b1218140440340d941c040780b56108203401100744205150024004c9902907500c0c0401301e0040c07494451504501880c200015105d00180c002a05d2501e4075086140241e20500007000181d41d1140c6050130750398141e40542004044d80352840c0c02d05d00244049900c204680c10800015a041e409407840301d54941c00c4803865102d11203450308612683d0800303504100a66050005410a0f4215980c01d24130b0812840c58a404223000a05040d1800342c0104655000600c0003003990748080c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 956311214 1250 956309964 956309971
    0x15020f0415081b0d0e1e010605120f060a27060b0f060301121b030f030c1203020a0801050609031c050408060906250c0227070c0525050d0812 62
    0x15401d0080010707186142000780580c1c00c0411044e40c450b00c405c0a4610300f84600c09011300740190f4851001040c81207140a4640d500502d402114042600b0070808000910a4001030a40000d8072550315030740b051070050210003450f041040d159240340880d50101162000d030f07450041c0e01c00154440010704100031100c030714a21310304c1214240010300400b0541c0b1125200141c0c000742d01c03099180c070a0000d200c40d000650024008112013a1000c0a05400080e006c201300c0c42220580080203140c0b07000d900b00e000d80000b120005801e600107224a04080004001d0004003d086800c0d0345420601d50450340c00c40745c4071000190b00850308005521040140a801c00c280001605062400d10381c1c68400070b4600d4039406071076650200c4400e82d940200d220202c6c154001e41603044103000021031410321130314206190750318056075000030180c0d48522901981c1542c00006004411180703419803018209142d003444410034141000240b43d031ba100d40b04d0400d02d1041c0c0c0c2c2c81c1c0d00c500580b90a46c03c45038005 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 956312464 1250 956311214 956311231
    0xf050c060c04210206040603150b0a030608060703150312020a14070503010c02010b030d140f0c0d080609070c23010f0e0f0604150f0b0d03020703060c020a05070315020f041508 77
    0x10003510005a641030292800e40c4c0d07031841d00194030380c42c5100000703109c0700c0383c0d003c1c2600710030008160700d44561640022041e00c0e102002c9030141c1d11036545c201d0885500030710204160007142c1c3c0500000d111140030a290030310714811622240c08644400254294144200c501da5002c50010021410203019003a00801c060008101210284000c262600d451070a6082008416040d00d00c0c5d040c03805040d502210040c080e1603440d000d4200d40340307988405800030000800c45c600c00081d0103260000c2000d125000030755400c070752000c0654803a07001d80c201690b0103412071a04c103074201482da000d2007600070180d0f10040200356131750003498250800c41c0b1402102e003540c016800f0080400c0c20549480f8415090500005140108020090040c01041e03403190b4401041002d03d010b03d98000f0720f040507030b4060742e42000719030070054050307907228041c0000512a81081d0810800b050b420b40401103a03141203180540340443c0c00c600c82c00e0303981c426000b844c07072000723281c50208041ba40800d00580c00307201d9 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 956313714 1250 956312464 956312519
    0x70503060a0c12020a03110a0203130b030c0910091710050c0c1c0e0913060c030231030b0c03011e050f0609190b090405061f0f050c060c04 61
    0x705400030300240060601c0c2c0519a00010705a0203503106c5e0b44084050011050581d4485c104200003e462f1b81c0081c59074034480e07100c02d101280d00c0148070202c901900c07810000c5482c0000380c2d070a0110516031000160144580840d0004116008003480303448140c1c03000203070030654000d03c01c0d141103c03c00340000303e004c0c0c0c0603c4440000200020140709803251800ca0b80d00c1d41d40c0e0514116121070f80d106005400003007190074002006481340410b080c2d0703489540188840d0000308011800c9000760414031700e480103a040609048481240302004a5940c1034285c40d4082d00c80d25031880c401820754149050b610004010092a5a0020341c10b602c00602c4d010101c0c85468800050f0601200d81d1510303105000010b1006215900c43d4181e00451048130400002d090703031401d056a030398110180b514029420600050258074084504641190340c8001009060b01c00180856110100b003c01c1c4040c841d0402c404021200100032561084030040d82c2d140e9150708200004900448190707155004000703 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 956314964 1250 956313714 956313731
    0x2010c1b1412061308030a0f0f09050124050d05070f0e040203060901090b06100203090d03091406041d130b04080a11030901080403140f0706020c07170304060c1112070503060a 77
    0x380f00854413403030380100a02c0d840b525192204c0c07006101c4031640051080c0b1b00054030784041c60701d03044500c6003400352000304000200303801e4202c10a44281c00c0d10003d041c1040040c807541c41d05020580040d03016004030362141d80c50f4031406d80700b07082d80d030006820410004200001c500c0d0070030000340e0004419000b071028804079036071111010409085280726a9052902c400301030f00c02c00c292000f070480100604158022800d01405c400d55500942c003c0940d05000d044041c1000e00c00c850031a0740c3c6581d056000000101c0040d901d030406008041c1196030003030710344045440044043d0090307000e13401155580ca100308000c0c140c1e030001c144482c219001480303240750b16a00241c40b01d034001d8150a00d45e403607075403154560010748560580f11485070b00c040752410034400301c2d0b8060310707100b0580012592007070784070b9035041d510041c81d40c0720b08400d41c020070041c0019031144510707903102c6224015402c000040840001c1500c84404540861680000401c2007580340800185400c595030348010450b108 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 956316214 1250 956314964 956314981
    0x4170a05070f0f440702040c08010303031a01050912011803080114040513111504090920060f0901180909020f12030706150b0403030f030e1902010c1b141206 69
    0x1300b00300c1c01c02030034502d500300074250104000881e8007059000b88104806071003d00c016060708420300013a00001d240c089060404800a115101407160584903507040881d820100400300304100359040305075480c3c4000d4030f6031f400803a03051004c0502c00d4444c001658140b01d640308803c240c00d5203481c4528140341c05e001656910140d03042e00344d6041004044803480310400700c5d000c100002c1c0b800712002c0b000240051140080d82c40300116512400524140c03852074400c05404048c2046c905a01800410004950b06d4685004000d40361042c10020070007140c03000c0850594861390710050810391141e00101c214500720407100e608100c2200c0c090b050580d4124021754900512800804203135840c811440030b00c1b104441031000b8903122004603a103503281d00d40106200249001800440d04122800c20001c50100d4210044464085200d244050a03001110142c40d040310035104118140c64000241248210f00c07000360503c80312824031110a40180b1503004bd100c445080c3c0d81c0c01050034030a807013 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 956317464 1250 956316214 956316293
    0x70504050108102309060d11060a110d0f0305070f091203020c040f020915030601140d090c0305030405011b1101030522121704170a05070f0f 62
    0x140d0080c6000c0355940c0d00d990f0020b80a105640068806504001009001c44071901035032032141825110107a2581b9241e05001c100209100024114003980300c20150074207064029011800389441c007180301d80100102e05080c01d0803502c0100005140080c200c6c5c0d0703103402d801403e8100311640b070504461510501d009200742036600407940e0441c00fa03400c0809140c401c0146044800c4003c0040104104d404a004002e512100c11390380030721900c8079025220b00581d01540e01c502010f03106e80000000000c00c0040300d501c0072007030411090740c4022810101d0465103001d000b55200d80c00a45d40c5900344000501925685845083e1040203c000040002c50503440d0001c0820207080c0460b0f940c0b90b005c1c440e020101e182020070b070304045071a40c41003409842061000042916210310a0004c003102c030407980c060080b00c0c0035010003107900c51440a00c00041c0149009092440c0860920300c0700e542d0b950310241c022030152003020036040c420040c045408001c032040152540081c013503800c1606030b118003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 956318714 1250 956317464 956317469
    0x9031205012106110d062409030b04081e07031206050604030f060e12130e0a020307020a030c02010e0a03030305090c0d151a100809012f0f0705030c030301031406070504 74
    0x140b03894000c018030342140e0130181c88041d03c8260051121a40303656542005910752400701d17428100141c40c0440890056521800380c9030860451a40b44c0d9881c0ca544503507600070101c8440d80e0740c00710805c01c81c03414a40041d0400a110783d481c0030000e41000540825609103412803441440304110400000320500182c011003a0b00c03032008185a0b843c4460725043c6820000c00c00d800700d4001500c080070500c0411014180ea0250b80c0c10303c00c544401903400224082141c5000c003683c0b080c81d148000c680070305145856944145407031040e04180c4008100b40620603807046020075281c1081c00544541400400010709090365001903a620740d40340e50864640da2103040c0011030390351300590012194042e82c00f402d04005403e072030720428011401440700100b111840f415501c2c2c040f220381d0003401409208041504807403586e9000301c2007107a0b0f054650042000c0f84294008002c6d07000081e1f010310142c01c0c11032031000a1340d140e40c03440c18404240c80404010901a8002e4010000c171f240d000b605a805 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 956319964 1250 956318714 956318723
    0x501090b0d060e0c062206030614120f1608190f0b0a11190201050a0b150a020309040f090c0f0b04150c020a0801150509060607030f0909090312050121 66
    0x1045004000e01d00e050144884c94240c200e00300240780303d0140380800c0054084c4d8054501003000d195a104200c2c1180c809000784428241d0300c00900322240b800381e260050820600742518030040c1c01001007407400403908124040901246010064001e0501c50807440081c1c4108514618585a54510300404c440d10010803146c00f00340401d00005c030380c0e8002e610512404d000d19a490b81180c51000421a080300d07904019030034031002401e9050b6500494107241005030541d0031400014454010719084541d440086110034400204540d0b914040d158940324130540024400040b07041c00c040780b0b44a40c105141070301241c00d0400c0041c0d40a0115000c55102e0f1665404560030248101c07114001e14034040e600402940e40401c200c54190b10500c19105a0308116003c9680c803801d0101d0a102140c90651101040c0201408a1701480800010070b0042c40c00085143d154001d40088500c0c204043e00003d0010714460901b403004e1040f117014110281e10300420b103100031001103000121000c000c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 956321214 1250 956319964 956319971
    0x503010603120324030501020310060c030906030b2b02150a020c041806021b1011190c0c03121d030604020d062711090408160f1a0a0501090b0d06 64
    0x440f5002403094075540d54400f413034014507a0303030406601035007040d0749100070701064401c0000c07268018080d48840c00d0b07164840005540ca40314050340101400d203040c036040500c50b912407621413481c4142c001100403065888507004030f640113002600000c0159041e0070305080218648090300002d0f0484080005c0320041250011017000440c10012044024081c03400400c5c070388007501202107155031003ea0306007221b0100c01510001826034803400852884520200011110f2444800a01d080340d212420310230300c101030316a925445a074a0340d006031480540d241d4004001c0e6030145041e451312070503c3d030501c403015480000a03181c2c1e41c0134000074440c3e10110520020405d403600b1203407440004004104883c03606506a65140070304410464420800b0030340040309140462481d4000e540001c00ca40c203200d000f041e807440400644030140c41841111503010002840e0100000c10480001e54200c040d041480c1004169034040e00a8141c00741000080203140d2245441e14a203c4c0c0c2240020 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 956322464 1250 956321214 956321231
    0x61707030c0e0f0a052a0d11031905060609031509070e160c020127030b0a02070b07211a0117190b0612160206090303070203040902072906030705030106031203 70
    0x95204188140c503074010b06c1c000d0036455400103181c040e11007035040d01030601c142c1c8581400202c0d2032104035200c107072004603006540081c4985900140e031100c0302810b030900e003004980001e8540110f008210300010420010401ca80d1824003803000204242d2078018010b0400030038170507030401c2c0340201c0803c02401f00c5000080da0322503c00312407562003001050b201c3c010a201b4508410a0500041c3d44150321100404d410685a1080300c1540760418404807258a40810840303950302d881d040302180e250100c06107840c14201e80309070543c01070480300301c1d40350b1892400013400b0b1a060300b0070900c5d0700d0485000c100c2c0300745541c8000011f81c04038100000d0211040c01c0094064041d6140c4203514075840c6080003170705c0d46c039041000e480007015021105583e54080109507139100886d0040c0050704140300401c0040d0054001e030003610301c0364404074020540000041c54680280c46072000401c2c04400b801440d05080c40100e0260030150000d0100343d09548a5210010020030f02008243c1d8440f541c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 956323714 1250 956322464 956322481
    0xa031e02042a17070f0c05013803190222020c28020306070302161a0103050c03030313020f04021b0106030606060e0d1b08250f050102100e01061707030c0e0f0a05 71
    0x14015807131405003a01c44402114146c082d02103c6d44c51200c1d1862089c15042940390001d0301e01355804d058010031402c1c501d1035003031101c1d014018095400b1440502c003000205113450019200c4052640f00619a880d185680d00c002c043d4070012a00c0d11210203185400542c40c0800d01c0c65004009041c0941d0b56614210907800c001303800305018088041c401c0420301c3d40031000150604880c001e000711003000340c4a00815407684403d6a0115405460006000050901c2d94482c0302c1281d0080c001428118424040c130601c86901140c1c160a0355690420300c10040310303101d0100038010740c0c50800c1d0a44203601c0403d5141540e03160203000d201016180e4102108140c0b1642c000e4281d010585464544002c803c0e42c884070702c195861141200000b0100d031040019820204851050b4002e03c0e80283c1000f428000384281821007000d55241d45000c42d00382290110464072400c0c0100810038503185061110309415140c0100c155030010704103124045000074041a0040c01d0b00c540000c00c0e44071280b0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 956324964 1250 956323714 956323721
    0xd051303171f0b091003060807030308060607060501030303090b070206010602030a0813020a06170c030601050301031407150203040f09110301031b0e01090b0f0a031e02042a17070f0c0501 82
    0x41602c8407030724603404102d00c0007100107000c40c0d64040c0d41d0030b84110074203403068095039a980110b034496800407104001003849861025000440504441c0c50a01c458a0f0142518000d030026008a510340516204001c10420903550080151000d0075455042c140b0007901c9103d405174900400418001080c07180406a10700440345074020724138103101e6503450700038007055201d2007007240760303081c0740c00080710030758144100c0348140b105a48e040d195a00f50354408400c002136110040c0588201c1e60302140300b117111030708903030b40781100d40003992039618200303caa920101d25003000e00d0403805d000402007115620001d41c0c0c103480d4000e40750180600003401200c00c40896030f0008801c0b508120000518140b03541c0704400c988000e0b074000200c5241c000500c010b004142c480280054800710300d8200351206250b42c0e10034035100410204241d0700000400c2c3d1404561240070481e00700c024010741c2280d400805448100c80c01c6079940c525403801c1c240140c508100003072500d091100700002602080400c0d803 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 956326214 1250 956324964 956325001
    0x110d08011505041509082413080c0a0606050f120a0807080c03030a1b0806030709021803010509010b0a080a0c0b070c210203071d1803071203020d05130317 68
    0x1000880d50101c0790b80010300d106183d00c61806c042c09504035140403221030f05044004501d40440182c00c45d112800b24881d0032120803401d41303800409104a004140003444206400c50181c00701107a85400c000c104440c40500441c2c2d40d116022020700c03190018800714014100301c0d04406c40e19181d01c41414040000d01c240b860045541c0400020401951003a83c00340001e0101d46041b86441d80b410300c401e451048050740c009900d5400302004000910039600100602c5561000c0d581c0a00301182c0460300751182500c800341540d440d9050302e400d0303040c04400200100206001003020841d0743d10317000d01403009030065a202c14030001d441700c00c0c02212100f440c018000c03401050300513400039000403083ca502c82800c034400c5c050340200252f51100c1440c0705480da1b0596410404507100c00c5440a41c82d00098071000c1140014441c08010420700101d5100c00b0005490169446080b6002603049603c01016042103074040320401c0003190b4420203201d81030b420700001190a440f40b026500000381d914 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 956327464 1250 956326214 956326229
    0xa02060a18030303050403020d0c1e06060503010e1b150f0304060207020901290c0705061c15030b07140d0c0309050d05120105030a0203031c060909060c110d0801150504 74
    0x40301c0082015450707840688140d0180d400d503014140da0060454460f80c0ca07850152007030052803550200c0708003007001c484e04e1502c20900000c07001e42d42c1e0080390948244600320f1b80d068015010944030107250300181003148408403210400c81c0d0308010565154000d107643e96520103c0400003408100041d0b0440d014a600140708a00540e992140c200da00d0140300045804a90b1011150f441c100214041d1940700503804094541281014284051500000011b1040007045c02d241e078007082062262031400180c050039414050b0a42c2070412100034040c0c100c204005030a031020042200301000d988a2019042c0007085980800130300724041c1a044201901740c5c00342502e0b0745180e60704071000b000d121584030203902032a0b9a90003010b4680d05d40d144043e406820030001c0071912107150130202d010841c0400d00152540d141c0c240b4601310340784104110358450b904c00050210940202880c41c8031060303440103044c0038146140043c840341040c41000117042c1500416040320313000300d054401070b1001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 956328714 1250 956327464 956327507
    0xc0601120f301d1203120a0207030f0c02090f25020105191107030809070e0703020711220f0b090a0203061017011401090b0d09060605120a02060a 64
    0x820402c1d04595100b4088480500c541d04241455107005030b80702039981080e0b0306249082c40480003072003000305000184590034041005a08503a41d00d211045014080e880c0300161640b5252030050440c00300c0f000000c051100b00703542c0c41c00584d1800041c540c44800c07818004010f40307034800c4052100c5416070a50612000c2e50b240945051ba05502c001d10600c401c1000b00b0142070b6180780c00381100e4602c3c4515a04100070022076020a0003010019000b9692104480b1110383e5052585c0108d141039074040c00194001134920284a01c00d82d03003040e44281111045050384407010012008003034800041d00080c1ca5500d020307070b0015141d02c812900100a081c1c40300c9482d1040c0280002d6200321080d52140780d900e100c490313038140304082c41590300c102544062103a90a0050900f140c0260064990421101c1c103808038440d4074610140c52011402140440da48400345045801c3d2040e54020034003480018100c1c021031200002d100f21903c1d015982940d0f506100b01b0304441101901c0c40700700b21281c1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 956329964 1250 956328714 956328743
    0x30207080c011b09170a06020f040e0907050a060e03060a0911060d02040504110304030f0305150a170105070e0307120203101b02100c08011e08070b0c0c060c0601120f 73
    0x2820f00400050101c0703a03885424080d220b499054000d4080e105000440d40101071100024100c1d90040100c8907034542601c0c245035403580e100c026208202d6405000b608130410402650a00441d41c3c000b901490403d0201100c400700400c2d9100e4005048500d0f058440d4252000d00c01c807410b0302c400c40c6101038a41030b503440840c0c0c9030401039407241c400c850050b80b91201c1c0a10740400f10007660301a560540e1429003070902d88000303c001e01000341082000d04060710b000780040c1d40c0e00c901c41d0010b08440c1c80d90030311429056049030031608010007990078803824050b251000d42d0007083e102c064400425a280300c01205002003442d11152180c140754031454054544c0b104140103000c6050b50006508880d0400205104030050f602039581c00d40100d40070000600500200150032413a2014416003841c110b56101c940500d01990350703001c806200d20028181c0e042d00e4081c00f9810030f0600a86103d840c00080388c42d11030b51244140708043c040c80e030f00748d0710303001304030305250140d55003a040070084000c0d01 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 956331214 1250 956329964 956329991
    0xb040303150b1e041a0d020904020406110d0906082404051302030706030605010c0b09030c0a0c090e15040813031514150a2106090b09060603030316030207080c01 71
    0x6102545004040210b5034004010702440d0f41110140c40c042010311428243c24500c005094104201d50000b00d82c0902002d11141c60b544050300051082d544e6090009400c018180d0600c0c6000702d0740000c0110300d0070103003c5035401c250110303002411240203411105a9900070181200440c0c6141d0f4003900300030034014428006031109181034022410748040350782d22041507040b200544902c03404100c0ba50404404a045120b000e90720444c40800e491402e4800f0001e135003440054001101d1000c80031900b4090b09400b841031100d04034480008010722070644aa50315003040080c401810311400068114410ba27081b0608030003198883c00070205070341140b080c2c0000c0c140c07034841d035148090814006502c00c20581d0811480c06030141003210300e2418801110b01840100c40d0315212815540354400016a02d4030070b8001e028040d9400c1c1d0b510381031404050341052400341145110b030b4414001c1c081d00e07a4107881c50045420860034016950301661602c02203502841c00003c00d154a8444041c4454 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 956332464 1250 956331214 956331217
    0x312070e370b0a2a0b07081902160809220c02101a0405060a0b0d060f05030f030307180f06080907090c0c03051305060304120224040b040303150b 64
    0x1800c00c0707660075240381c0d22203220348128020401614009440d0000300354030312045101d4800118403480310311042c0000d5481d14003400000362142c4000510100400c200e0390825003844030748070384190f0194a4616008019041845400c8000e00301d08000102e58810366a1880c0045004d02ea4030800010300ea20107450100901116140c00054080c0313080d01c0c4a00e41d440c0c45a8200c84010760514100910220140801410010b1056801c00d40c412004100242410702030700644040380408034a6a04141e540b61744680c440c0e001074040e40c004a4511405c11001c4162a4820340c0c3e0300d0240804404010740904500d25903009041054150030b02141940d402019a80714400001c21203141c00e644000a0088841200c4d103032002402080020380000c1c0724a0042c035580032840d4580d000d560721000043c2e01da03032040c2c8080324650b0a00c030310f05401340e406200e00b480034103601c3c0c1c00e030702040e641c00d045c0500c2c00d200400040c901c14044001800f054001e5109a41c0c0250a0000042c040c1d11609440300a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 956333714 1250 956332464 956332549
    0x4050105060103050c030a02030403140d02070606090b220603150603030e030a02031b01030b0418120c0f030f02030d05270313090b0310020d0b040e0312070e 69
    0x65080c9400100c1550103801140e019031840c044a074a03603a00c445594000b504060000c60402014098511284080c4809440308100c03403400160b85104900d0960122072090703100c01d201e18141302c020000c59075031407100f41d480c0c0d02b10145c855004089800c04801001c1507000203044410790003030303c55006c240d54401e000741d0b4403139102c4c14180130a000030155244c074001c02c000d40c1684000108001000440250100050107040100b41234a0b07010002d8180d880c0c0070004044800800704883c28003070800207070b10b02d0300120f081204612400341c848036034007030f05040c2c054140412106680c020702d200b00200c3d480080005802c005504028909010f00d203025940074510b4202d4611498441101100310b41c1c102d041030751310501041c0303031800840180240b00501941401113560003103950005000070f00c84028044800a40030012100700320450f091000c07242c0440c1d000384882540c01289850381d07078100c0c3c900e040911716040c01c1c1d00000c84442d02003214405a4070201041d400062100514102 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 956334964 1250 956333714 956333723
    0xc0307240f0e060c0a020a02060d020a0e0a0b0415140310150f1b050703050d02072102130b0a0803040e0f13030903030507171b011401180b0f1804 64
    0x1e403915000000140c424500c030004243e00034502180d004c0004900030440c10215006960303180b102500011070070303008072920f40802c1e900010180c50b01d07540101e0f40380d407143d411202c0380000c03400c004903582203000d0ba00800b42028800f02a03070a02c42c0c0149008145584000d900c150341340b034405510300c01e5070714511440741110740c110503000c002801002e602c401065695182c0c0d683c011a4001d1242c04c0302e11280c02e5409001c2d082e40400411018030503a080c0000c03940003000c00d00c1c5400c13501004140020b0300400030408119060300140c0c0e071102895000c2c1840200420300100040c00100e00c09000e5000d2400c80c8800900040c2208042151328030a206078280340050f5594845112024030700240001c001941c3c807030003440004d001c3c0d0094200d00d405030704c0320048000d40015070b120f154403411610400c948990b024220070780c402d000307030b4009858080d100041d6500d4800070f1984c201825118042d0300d915072840048644880799001610003008210014000d00e01202e215a00030640c1c0a54 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 956336214 1250 956334964 956334971
    0xc02010509010203060d1b0302030d020303070e030607140a0e0a290c03090d060b1003051618050f1302031003140a050a02040902060c010c0513141003020c030724 71
    0x181d40780010310a4034480e007806000381003002625520003142109444001581c00c04c079038400f10250700c0400031602c0c406860b80003107a41c0c1c1001c14002c1c04810310300c0980f034403a80c408002c000b8101e038000703019601c07011500000b0361603e43d0028180c5000c00c400201a401205036200056903c4039401c6104080c56501280c0480c50010700c2c1c02440b130f200f031425507160f581c000c0104240e1414180080d42c545809014006102035501d0001b51560000140c0b4800007610383c2c1c144810791000710481c0b04609460304008e81d2000585040d110000707620711445100780e001d01c10b002e4003500c0e00082c82c10b000705902400c65507494112503400440f29140016143c01c240420b51900980c4000703000d10010f03811400908195000c0c1d0b007008084c04403000c04a070825414081c0c401035800c02d004c1e00c0340512254450503116080f907001d1b0b0401540c1540003d03040340100d8031920550312141c03500340426025180c0981c1d43e045044000340345118030880140b000030300030001c00c03a4074065100180c0c0325146010a0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 956337464 1250 956336214 956336221
    0x260a060603060608090a14030f1305013c11060a32010b07030903140f0606010302250c152705030318131a0f030d08040b091f0c020105 59
    0xf00c4d00880100d400b07a03d40d9000710600004180100b1001150301241c0b01100c0c0b92100c54600c1d84842d8200a400b14030f0109110030900840d80c00c0f41032800c10010681d90410b80c01d403d41d20760000b1011011006003004111070100341c800d0b200d0326820b4041a070003c00c070751040c00c207010858002e1070a031009903111007010414442d15101d1281c80d424844104028221590901080c9042648004807c905000110754000005480140362a40d00d41c031102c042c1403244110008241000b800a11150400d8810040c454042c10a24540740710030f54901c1c40c0942440d51440c0460403075030740e60400c044809650003482a0307980c3c024060840500c0c035004114602d01029000c51030515140502c60303064106018404046004851040640c1801055100d602c0c921504020444140240481420000300705000050410081ca030849000990003801c004080c00801058840041d0004006026200c04101c10f03110400c840321780c1300e0071580c12100e1542030745444402414450b454002650815000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 956338714 1250 956337464 956337467
    0x91005030403090317070f080c0607030e031602040e1522330507051e0c0d0f0c050607050403021f05090d03050c03070f020a0e0610260a0606030606 65
    0xe4034011541512420042c6046981d15402405041810511007000340002e4012802440f1000051170081051a54800c214a401303804c10f10010011b1085c50304180e0070403520348000045849070303411200201c0c3e000c0f43d41c0c800070307002e8540c0119640c06480764800960b10340b16402403880c06040d064682d01c0d11401007a02d600048a00c40001911400155214000c860b0707101e40c07840600d00301c14804802e104544000309044540070340324070780080e0022850410100d21580c1685615080309003040c01e00c1c202000341c030380e18082c56000004000108141c100407500442031115048d92110694000745800c910050030390b000b33440f00340d2007109040503443e031290040040c00301d034a080f590354516203071044051092081141c1c1c0100d080041c10081c954182d00207201074181c0b18815590301c400c1c101e69004004901449800c03005010074210248603440d982d1640051a0480c2410106104034900d0010410078003150b42040100c0da14500300080c018255010b9000c1d50a552020084262500d00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 956339964 1250 956338714 956338717
    0x512010b0913020d0b042103020c0705040213030305130b0703020a0b0601050a020706054e0c09010e0a050d05061f0602030409050901150801060f0e0c07020904050f0a0503091005 78
    0x74065001960b1003404c0d0040782ca40c0000f0f0358018096215144004c444d4403001201020545031140069400310313a1070b039110028810100100000c4906500f41401c10350034070000d01441c40000c081c82800110050300f54602c0340c41c0d00003003d1009100d52203002608003e5111440300000b2150740e000240000d0b101c1d80681c055801e00d04d0740768010f1640e01d050407c02c0d01d647d800320700e0b0560030f0740c20418020110441c0384c10f00344c034081150015006107540340306482d11f91100c1031100513401d8003240c10455200201e50644802c10424038141d10680b00c29401f00d040c00f40b241d040250814055a403400c01d00100044160099045220007000ca81410101c806056910701400005810800c010040304003203402450704040e16000000740c03007502c01c1c1246144001640154002d075100c00042012450104055000b0200d500c00f2041034038004660111600c20100000e1103440e140010809000040064031640b41400c4101d6100d080c0c2810082e0362a0014101c0034800c0c0d099070003d6030260b03c07450 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 956341214 1250 956339964 956340001
    0x1c15080c190e13030e040e1c140a140409020c06040b01050f130e2d100b010816030908031021030206070c03020c0a0e070e04060b040512070512010b09 66
    0x210b01a80a80350102100c08452a00405800304101600600c807117a03210310914501036400ea0040154480d90080c40000100f50500c1c0300510000802d0980c900c044d4074112040f80101d032401007064005008000254080c0e030700000c81c000c0c400b0401090310140020f040f0b025034061125903000e07a81e01c00801c01e203030b08002100b54100c400640f4175006211250000f0300c0d022071050a40e03a003900500759100c41c0240a01804103032656103002c0100452040c42141d203513401c000414050707049603000180c19400d02a024802d41c48c00004210744103403107a0300c46066a0790144d449556402c1001024036001d62500945412494140f005404080b9101a08880c198560090200c0c2d80d0b500d00300b13554040c40b40c0d400b681580915510300580d50b96181c2d03050f002c1d21500942c0e66003800e00e10001030040b40c0f154130184c0902d18160051045420000c1a42d0441c2c00132075607050006800c2400c141800307040e6000782e400110079503541480300c1c0103411020f024503081d42c6800d226034034010720112414004c07 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 956342464 1250 956341214 956341229
    0x3011412190c0308070b0f0705070c0608090f120919081e15010e0a050105040e120d020c06040f0317040c231008010e09030903031c15080c19 62
    0x1040402200303030104501402036000b0b2003529520b8582000700e920201084400070400000c1004403c09a8102600103810b4034250f1308015540d07456004e109040c0c01001c0c1407200820014400d4101000603441003101d950030b480e01416500385408854100c0c4888611841c0c00d60030300103a05082c04029012510440d00a0101d940f00502c2d00c803070000c000700e03941c625005070750850083d020030011320b0f4001c0c03071a10b44080552a001201c04100d03081070304014071072824200384880e41000043c0c0b007102912004811603861042e52403180007882410320747c00c02400b0308020401407096801c51960114040c1e03d5014120202e10f21940300300303200316802011014414800e200740c2505a50402d900c0701081e03007500b1010301da140010f1008401c01d2200c0c000854404c01031081d4104424181d4010058000650030500c051002980b07a0080c4442c0300b00c4030802e580400402c1246e41c100070b038191040041203800319281c26401c0d4990765010001d070300036013100003129a00c80e60300c2d151004640c901e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 956343714 1250 956342464 956342473
    0x60c02060901150e04081b07030c05060301080c120c10080117120a030b030c060d0207170f07060515220b010207050f22020d1401150509100903051203011412 69
    0x34249004c3c5201006072080d10500f0003800400500c0e26191501030300c40d40094002d0282900d1460310074440643c540040d405810144010848041e0020703c0d22200c120841da406c06942018040398a4a40245039296100b00110724120444c0c3e00500000c0c1a2170800320b4000c1c1a501b010400f550303411107003040010703590040004580c850700c030364402c1e078840900406842c2010810303000580a03401c0104e04007807040d400280d0740308008600b10000d44440500c0405030070100318021113450741c080d480001d4240354452000900000010603d40010318008000442ea462400d40c3c0e042914150041d00c03101605d0031034069600d41c0001401d80840e4802040f00b5681d2000c82d062110580342c034082e014086141c05150b40d0358188ca40064440000e07890000605801c1c2004c8403001444180d00908140143c5045054000c3e401012201c010b0410380b0350402e0000c0c9010102e41e084166400030700580907480100000041d900c00a504842d032400b0384106004c0e80204100481603900300c060250b600 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 956344964 1250 956343714 956343719
    0xf01050708040b040f0501111801090b04060311040314030c060a060305030406030c050d050415200d0c0c0803041a07081009050603030c0f0a020321031b090d060c0206090115 76
    0xc3c2c40030302d580d00030711800280910310354503a1503034255480c80c00303074140940300032803004651050a6840c15460100740380c408042481c0c038030340715512b1081d40143c508040e25124000741000390003085800070740d0721271040080719402c20a0581c8030f03001200c1c405c01d1801a5004109a100c130307030085405032034100c2c01944ca054580700041c1c0c018615416860244042441400302d8180c00e841100e2150b03015090950400e004541c0c44401c5400700c80c402d65031120300d40c000b584000911005e80b10030781200440000c2d590810b200030750305100903120040c0f44000c000304010401402c003890307801d11044502c1c5c80815440e0040140d408420850781d0800c852011172007080110015040540c0203d00901505c2c50302d07801041749410b1200504482200c2d9100345000b10071401c00300070700e00786404000d11140c00c02c407403403410481c40d21015003c2040d41d44030b8a000e1030074480d00780c21684032400003010401301480c2c0c0d00d40741340904040341410307016004940000d0390108060040c00e20361440491702102250 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 956346214 1250 956344964 956344973
    0x7081209150604050a06091b081806041209050303130e010b1207200a230a0c0b1c020c150708130b19060f080c060a0801090207030c050106170f0105070804 68
    0x44c0180301248050700c5103000a40c1c9155446018503041400f51002c0010450510240040b80041c1030b9109440012600c618002c41c0032554035040707a405201200301034100882101e040700d00350042c035418080050f40d0360b0000002402002211075280d45401c881e0703610840242c281c000c000100c08208c2c0120f001a1026200c0c4403e8902c0319025807003c25001c0c03900f082c40e890304d495241d0489420640080c0e000c00b0704518940324040e0702548000348940c103642d42c0d40000c00003240c42200340060001c10680144c4401e14200d004040c03c0c0345085440c5c03121610b5450f60b4440001032429106902d90100c0e204500c02c003440c61240303204480310141090700d0364900c0c81001000740424131006100218003034603a207a00511000f01081d40c00341341c64500b4040300508200e1910aa0b170f102e4801044188211500001365504580440c3d0006071650020304082c2c4880a04a4004006505c2e00d00d0104203102038502802c0319a1002d0200c505074100b21412074204c0c0c2e000d03030700d04011401c0e00d80001d0008c0d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 956347464 1250 956346214 956346221
    0x1101110307051c0603060614010e09040c0317040b13060f091a0901031b110f030901120b0d1401021e030f06090916060905011b1a130807081209150604 66
    0x4080740720f000800310398036103d0108941c00340e00011210b480c0803500c0005036921104030b113800c1d04100c81c10840d0341080c0d6541c540d102d016100043c030030380c050115401220b50b4201950028070030070700c1d0156951120f5682e81804481409860041903a0303280004000e032080a01d04203482501112052406601c2c9503c03071290000e5144904064440715941d40c07020444510316801c050076154010140381c02d40350a070038440394000d00d0045a100f80041c08c2d40e60b0f07112402c10100e518036032000800c0c50940d00800e4415800c0c030b001401060000d0b810035401d060560080041c0a200d010210101c10071070400d00030351100342c3e409008091442c000c030b281031500b218550b8201c031407442144ca00100001c0c03040244040c07540080d0100721440c01c100003a580000b0100565415000001c035590030a945121580d0030031800400c680b40030100041602205103a0101e085411050305911001986445005a071152822200c040158008a4107000000582c01400302e00c01d103440d89540d640e1010b01c0021b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 956348714 1250 956347464 956347507
    0x717070816020c150d020708070f050705030d050306210604050d080a060b1c090c0f0609060c080a08060a08101a0132120a09020102010518210f0406110111030705 71
    0x40c1d00308001400540108c00178090b0314800d2800c0c400001c05400d00301e040c0303405070340034601039000380d0244110150300c207084170f5000c130f03044840207130785031542014038042c2c41155407001181c49040d0034442413100001e1107031680754255581c41d4080d641c5038410b2041da00144110600842c00f80944407210b1140c42c03240b891a0364003d4005040d0b440c1380c9960360804140d0f4050302454069001c00d00025a1181e5840e01800e00d40c2022180c80c8826610346040e8407030f880208040201440100341c0c0350765a4400c01c801044003500b105c1a485924812000400d9040954060806003241d42103895010303401010402c200c03c185d015040005034803140003012409400c00384120100500c02c41d405a4070841400f03403101040020340c0e07100d1403002a0840b64094400d60711450595055102c88074001000c200302d110007021131000d81480541500f075801080414800d480010801080745c5071700048480d100801d5000034408040c0da6549243c05100036a50740d00042c0040100070340e03910b100010a80e8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 956349964 1250 956348714 956348737
    0x41a0c03160e031e15010f081c08041104110a030b03060f090703030f0e060f0909100509060d06020f0301090c021204030506060f0319060b04060504020315090717070816020c15 77
    0xb026148550580c0845c0240c200684450300002c050224036000c129040a8808052503840c41c280d4200000d45240130007000104a402503032140e590310303200c0d17401007c0e4040007504400d80750364442c54098044c04c01e604505c0c1c06031084500040e0035070303080380f807540c01424114040c0c00c4590650710300300c038056101181e10061000b42120303d00f160311850000c046506000a03e40d843d00840001c200c8101030142081c070520580e0b80d0244810707610301352402c0c1c11510031206031a07000c2c1c00b403400401034052040c15280f02c0c680840002284c040507003104154100f551709407840203001c1e00039030140f03020313a0002030f005501010001d59641040d400865661100404603104800780c11003e002c1c4000c500402c403542622500035445606190050901070601100c0035400c616041040d11840491010050700c100020404242c4590051000c0e6401c840c800d400f580c820300c1c100c00090310342c50094401200119541d880d0240481c4045881c40e41900e009113445000490b2509204207900a50340070345 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 956351214 1250 956349964 956349973
    0x31103120f0f07170a1701170c010503061305040c090605060f16021818010518150703090f031d04020306011e11031810050a0c0803041a0c03160e031e 66
    0x21000054000030303014550507030b9509458903403003a405a1586c8410307070066035200700c4004061016040443e8881d141c4400b07180040d100c0e40c402d0006494401107420225681c1d1a00040c4400d111420002805440d907440703040c00f0a03951401802445d11580350744c01102d0100340b2070001d00f035103210406040d05c0d0006202c45d04107d43c040c40e0340003660f0180c404d86000b5648000c0021070b07080038024594081c1c82d0203500c50340d008506076200d450326080c01039400f40c1c4a0050000e000c1a000fa401042c2c969000200b0be018070550b480c02400d5921613200d20f44941701c1000c0b900d5030130302d054000c80b4810201039403443e04c1503201c0f40055129a070010102001d000f48414008640c1c1020806000c02c0745e1400624840300b0000b00520509a1100b1940410090100080780c449500a890480000da001c070a5030340d25503031410404d485842e60350381c40300015410003e2241814900d809503009011940e81d1003440707121326a05450920f40c041403103800d500001ca8030540707290b00c5900300410306520001e99 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 956352464 1250 956351214 956351243
    0xa02011e03200304200a0605030c0c0f06190504080a0503091005130c09050417070c031704090b0915130f09030203040e0106020c0604050f0607020307031103120f0f07 73
    0x50b8042c01d403501404401d0100441007000b03000c000035460070302c1049403c02600344140c060204005151501680080c00400004101003d2424088501031754540c0103580d140a504241c403a140c200980315403441100d00c41c000d045110440c86454000c82e40300b1259450030800307002c03c0e1031541000b0050f078550f0003040c041c006030480601410740b08000354100c00100704043c0c83c01541d90302c101d4221900084c5031004010000f2110380032498010391104026440d90303000e140c8060a80440d030001406484149030501c03c50070715401600644580f54000d2091051000600410260488164080706007964407101c4c94200199070080c038424003000454a0000c8641040c2542c102d00400c070016440020304003e0600e1810b12180944210701c090300391704080d100010000e0040b400340302d00c200c10102510700a0f07078607071040742c0c66203501034280c85800f6940d0524404241407510094001e002d00052151440c140d075007202d465800c0418854203040841c03604101a400507034040b103041107554140d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 956353714 1250 956352464 956352491
    0x6030b0102100504140f010504020a120c03080a05040f060c02100e010c0c0e0f061f0e010309141f02040b040e0a090804150f110a030c05011e09050706020a02011e03 72
    0x2001d101d41c5c000d8050890b0411002d000d946403211a240c0144503074034203030500c40143e032885101021500751654421010445040800c0c0000c0030368401041d13401e00203400a80f16401c6400b42c41191100c500180c8c0070b0b0740d183d8040c0c54a105201000758816807040590260380d0040d000055498010700d0062940d9605964440407620309420600078582c5480800c01038600003450b8680c00076003580c104801c1c1d803650b118000014001201c00303050007141d11904040742d03c04d50100017040d8121000d00729a506698441c0e45411490f45001c0b4403840c031011140d410001c900846044411203019285000e01d002040380c0803200262500300c4c940d4032030043e14082074060028201030500c01400321422840032102400a96000046c0802e000c251100d01222141c040780030100305070503080000c03000900749007032070051454078003074030f2805a0901048407081c2103070f1018404c0c2d4030640403949095100c49007a655050410390090010780306095540000711030300c03660100010fa40c1000701721526410903 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 956354964 1250 956353714 956353721
    0x5090f100506070c0801060b04050a140d0b070c0c0512031602041515080901050103211817011521240f050f0606030a150f0b031e010f06030b010210 65
    0x101030383e40110018041c07181180c01e00c00c1f9001080c80010041c82d02c0c0c50900442e102c0c0c0103901c54400d26582071901d82c05c00b619151400c00220340d0000041410380703004540035002100c0c00c1002ea4110504200200306800d00c1c0d846d083d4007a200e60000d41c02c201d034403084042010a1050b01702c6e0855100c4010740d0100c4c024030518009040b18640f05440c801c03007030744014035401e002400b03035105a040400400101c2c00c5510501000112a98403420b9480c003844151403103104c4c4003409120341c807000d400044840b0014201c04a05000200a001d000d500c401010004980c0340030b0a0b00d01a0082c9604481c0c481021505569a1203240c210240a841489004202c80c080b00074060580e150030003032054103078034420903511030200030bc10003a03805c0c2140031030814000140510300e016520340c580d0000c54108030168004000000c03980d0041a225400910301d40c01c156040c00f510003916128068200c00f601480e8161804d01e074010b190145880c10440182c03d0707144941c0d040d070140a984400d90251400b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 956356214 1250 956354964 956354977
    0xa0f030201200412020f0d02030d0f020c040e0c061606140103110103090f080309070b042c07020a0210210e0606060a0905040506010e060313030e06030105090f100506 73
    0xc000040411000a40716060300d420311450403190400c01c4280402500044502d0031144c055907004540034504003c1081c035028208003039898412426221031040d80005004010110780e42501c003480413100500054509602903561540c21100d04d80c0c07240e00b00344001e880700307031441c080341a0b410f4a40e0f160041160500001030400c019100014401d01c004540300201000c02880d042280700c1b0b0301d4503018400500c524005080d81000004501200f5040091401400080c000d542c0e0303c81c1d6518405850700c003440f0040e4600940046c000911840301d0b601e80f80724008a0300a042c00416903402c106000e81400094001e21004d060003e9020f0282006203542d20043c010004400d41000000c40c40e18400400452242c00c0411032050800c0c3d0040381c10007194000d0380c0214084d11030000580b00c2004440c041c5410500100800c44000c00d41042000d03143c1c0281c4501548011000a02580e40702c24021943c10110140100f08982e4144c1040c03640045801554110350f030300d403c006519607000340d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 956357464 1250 956356214 956356217
    0x20a23062a061006080108031905090a090501050f030102190c06470d11030f0d0c1a010605031314030c150604020403020d0f0f24180308180a0f03 64
    0x204002415010fa2030281c00741034141011021507142424013950381c42203078414106840305100c0c1403030003802002680d4441c00020030b180060342e00c401c420002004244a0b01e482001089030001050138107100b250002c1103030307601480d40700090210035a500c540c0f141c0216185030761081c4045880180911a021601c0c482c1c40000c404070082501e1514404180210b0311840d1054918031210350f101015007518030f0340000820980d2000100003410962030070064001409401304031540c0350752281c14090141e01ca89130481c414080c1d011041c1d490b400901600300403403000c0022a41e40c41901c60b00c0042984140c0581b090131200003515421a0001a18070b0300f15845803505400d00000000c0c01035000400f6542181068510340009548103d00c00c80940a80381d18000d01c0148013229400160081e0441c40240d446800c000c09842001c5607011002c81a42ca04054035061100e901050306a690f00b51303a64215070340b122911144c0440c9842c0116025201d0803402c200003940308483d10380d245019 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 956358714 1250 956357464 956357473
    0x8070c1103060c0702010807110718020d020a050c12121306150e09010c08041e0302070b040f0302010306140d0b190e060a060506070b0c0d180b04020a23062a 69
    0x348005800030354007034201400d0019034221181a1100080d0441c00ca41034401c0701416580d0807c0f0620081c801c144102c00c04c0d4ec000215215a0742d08400106008117004c0c08403040d040160408070134a00944242c10100d110341c4020071400103201c003112504034001e403c0020016212146107207003a03100e030b0000b0711102101c010451000003c0c820407132944072a00780007a0302c6c03030643d48082000c1c0741030081012504610b189401414400c000c1100600016020a07640701d84410f001005255103100490010317040c2140403070b0188910a00c440d6420f00a0300301942201d00340d0350304e00d00072001007040f060854050b0046c01c51142d07074065684c078080b41a0103014035042c603000384410740b02c10350001802450200021130004d9020b110003544154513009154a13000c2c1218040c020b0410721404800e0324501ca2008010300c1544443c0703130f005a00c01c5580780c0703100d0354442100e2070034066208610000031031b40048404504100000308102c1411080501c3c04800c2d5000702100340c4030f91030000200390321 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 956359964 1250 956358714 956358727
    0xe010c030507031a01051b0a020915090a0c0e0d080f0d0501030c09050106021c02072c07030c1202090d0b0c030a050105031b0f030f2e02090108070c1103060c 69
    0x1010301c01e60007140ca01d035400010013214900044d00500c0b441543c405590a01021070000b00028005005030a078010711081d0903080822603d24046803100c001d0303110b001103030080394006203180b2480700303038443c0e07621a001800400c0c0200481a007650358203840c0d5503820001c203411409000c1c0205500c00510000042c65411810010103415464119005242c0780c40d0050000f942c0005600b604610081c03c514541c00c1d03001c40403420603c2a602c884115040401540303201003451300003100021900280c01801e80d100c1808a0a941c80101800e010034100384c00c6441c01e01d00340d0010400240090007484606407036688600c0f1190b022221b03011140c00100902241203a01d000300f03801400120010300f2004070034140c01c5203290b5121115440769600005040302030701c007484140080d55a60b4155504c10400810b03000780003020508034601d800c0d4607107041c07913006007500c02d540c8008010f9490b080903a80703a10080e5403601c0c40c01420758020b045101d01e403000b5a420070209104d146200e03107172501c0d000f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 956361214 1250 956359964 956359967
    0x5070c0312140310060e030307020105092b03030c08070c11060f0c0a050307140106231f030f24030311030c070807060e090f071d091005270a0504060e010c030507 71
    0x1c46e0905424400c1d0401c001c4400984c0e448012b51b429004200d6890410207103000c1404185070500c0c48001d64208102401c00515416920910443d60a0789507049250b443c140c040310004400c0d0802024041088043d80b06070821001030511245034001c000d180c104010202d514016542804682a030310000b482c10420124034440c03289042d90070000e01515003400300c40d244180c030148038a00340000400d071014403030b610307034004c080c410b041000741c000d0188524100401500e110015518007a05001141b40c400404104084540c5000c95251010318150750b81100c9188849465848600c424440c2328602d98060000100900d10304000782062481c0c13100250805c4a000803040c030a0b03100004001152020307918003680300c0710602d00081e1940841050070301d241000f0020310380224a01e010044140c0c006c2d0314010903180110313041d100e0700d04040000440714182c0c1d650103100000c1c4070085140d0311003d400c11900188141c8000c0b07002c00e008003001c2e0031104090703641c40c00251208103010109 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 956362464 1250 956361214 956361227
    0x5060f01090c1713080435030c1203100519090b100c3201060e090307050304061d0603070f030501090b03070b1b01050906090d05070c031214031006 65
    0x100c03140c2815502d01d1003201255120f00d034010030344d511490701c012107402084100780031240070b031003401c01001c0c20342105411040d0105003c2500a500c0400c1d06c510304103c5000815940c010001100401c08401283e080200a1b00040c0c18560004012040030615948442c40340d017074070301000b03c2ca01c3d00c0344c035100c0520107583d2001090b9009584d0b0950070f40c4520b5002da420240e003500241c401c0341c010710300c2c44c01c41c1882401c07174100d18503e0b00c00c3d41125060340d010340040048401c075008502154845400da60780700d106141c00140705a004000800c07405010b11800c41401501c1c3d000c008145030744502007800da500444a03140015090681e56010315054824580902140b1108004103928100401da549020740500031603100c01152600c2c4203810100c1441210b003142000b4811130600320300c00ca590341c206542c00b150a004200e80a000140308009851015411041811345240356807107190541d150f5054500070041484040c1215103020002980948000389241d03c00a15001005042 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 956363714 1250 956362464 956362481
    0x6050d140103030504050d151d1005130b090a020402030703091b050307260f01230610111c0206090706090b0f1b0a1514060307060e03010905060f0109 66
    0x125809030052021907403020582d41500da081e214401c0365005410103591850f03003d000d80d9881c5080600007503041602210750201350391b11400300c4041e041558210016610f044500b641c04261140c055004103607250b1141d5040100b400c20340b4550501500800c0c240ea20072200480880d0b100c0c0c028004104032001c0c85061075551802c500c0180382858006030315002c10384500c00030214000303d1405010604801c018400c04c4407021201c100442900090292034020003075182c0c2801040d10b040400e00711640e00b84116130060030a01a110080c1090724204007034440082c00b40704000c148580301081742d0318406607464503001002d240c80c28501741072405009401580400a0000040205a90f03401c16900c41589020005807900340c02107040146628008a48a9038810001d080003440f4108820850203008201c3c28400c4242c103640b02c015402050b40c0c42030300740d48100d404022241c07084415901e0124000c00101c1c201e60251103d901e0480140c848181c001a04401007191038130600c2039004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 956364964 1250 956363714 956363741
    0x90a0b030708070509120712030801050d110d080403080706090c08120301030605040f4b0204151208250c03120903062c06060319020301090c06050d 65
    0x40d5280441d402030540c0005031860050000200b0b200c061a990b0550100c0401c82c001c040f282000c1c8c0c1c40c22030a48084140e8000c0d0085200080003042901340540c2064810b0f400c010307942140c8103041c06100b9418007510094690b15814040440010700d08001004218080c6101084480550074480400030711640506196400561005884800c1205990450303070080400101f42d521030920511007084000002c141141080740b20f040d42250300000d03040300c220200ca01040c044d4003800407001c05007488043d124404140d451600521b803d400403c64507950280c0b034810243d48104003d043c2612a5007150300c0c4502040480d64020000740e0055000650ba02c5130096030307410340300c0310058a214000035001e44015100f80c03802d58080d42c6001e00466020ba07040000b00704180f021040d0b00201950171016410128244001d444000f440300e004803c014094041007040000411803118440c0d81280c2554071016000301003044034162400421080d26095514600e90181c41d0807201085802003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 956366214 1250 956364964 956364967
    0x8040503071518120908070f14040204090510060e0d020117062214060d020a120302010e0615010f0f080114010c020612010302150c0c0409021206280e10020f0c1002090a0b 75
    0xf803031108108c0340d011a609031004c03540c00000030380442c0182c8515001005a60308090600589407082280d150484103d65601c40c504010fa904010001c200c404000e400100032012882100045030840d50700100c0003042c03c200484961001201021325101820500d40c0c0c0700b508515043c41003c100c1d0b4402ca00303c82480018030780d980040c020070150f008010303402c6610160041054002d60081e01c200e45000b040303503c00e261050401000c100c80c41645400104d0301e001015210380140e0036020340301416161904160700302003004c01080803007481039040040805042c405615610000d1955185460f1640e52075030440c018440351216076442070b40e10700010005040c1c0600040b45600c0c1d40c0004903800719600707800c1c1c0000740726007040b0381c00c01116014940c14080841400c090340308901540207806483c5045a002040440d007070084214140d0700140c805084008050780200405204c3e00c0703019003041e4891055a25224031010f051803402d0340002c0c41c207150718045002900620615001703e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 956367464 1250 956366214 956366219
    0x501031b050a0c0602040905062106010510020307020a0f0905070504030c0e042f01030c020705010e0613081b010201180302030a180b07031e0804050307151812090807 73
    0x6042008030650420100000840c820480c14420309282e40d540750000f0043d9161078445000c0c0d002004255205440f844584030f030480396403900f41403802c103003401802504050703180909000305e4a8015240801b10300042045000580c2d459280d40c01a00c04c04028284042c01c104c1d1140440d00040c00d1241401001d100410000c4c0c82d1a441c0c005454481b1322000007900c443c5412403506503448612034541942080c6684444424030148268210980e820f10a114141034140e0303c2e415580141c0d4001154000140d806040050040070342d40c20182c490321020b80e44841190a10751014080c1040003410f52500500c1c3d80e09005862054610300b085451001140d0b80c00f82d40c0c2d11440914606201d0440404001c00a000c40c0400040c503e1303403402c0b83e58090918008282c400c40c5070301000948803038061140e005204001851203240d0041c001d500e4031219860302d1817410180403400960944030300200120080800c109121039118501d00c2000c1d1040020107030864031540c104060503413046004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 956368714 1250 956367464 956367491
    0x6270503041a090a09020a0315181d0a03091404060b03071b0519030306080a080901082505030103140619090c0902180a0b0f03060108090115080115050103 68
    0x4840468840456840e11582c000c90320080c0340c042e6012056101c8890780000690060a80062601003010f907000c102002c02e194203801c10901d940a801d0b90300e20810030740c03002c21000c0e51104100c0b10011444207009801036000d60301d00029200c00320001806000100701c1d1000401410717600501c1124207004045c1080600d081c035003c000c003000700304074000014844024200070544c0005801006076000d04803015020020400d000d00c040b03000928006001408c1e4102140100030150302050040c03811050100440d100d000c042d11904500b01120615902c00000719008100e0075403a450b81501c2e5803460400d108004501d56480500c2c1e044a0308202180846801c01e408016080d98000350500e264100801c100049402c030380860f9100241d451401140c9030404c80b1804000c03038580e42426103550b042c1c0c030140540548100410b1050000c9a03480d0b00966200e039010002d500001001d40702e04002c000ca0209079032112001c0d95407640780b0310400310f90b1481ea1015010030308040c84014101c082 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 956369964 1250 956368714 956368717
    0xa1b1a0115021018020301151a090a0510170108060406050f1003030f03110c010b030f19021c06020d0b04050723070507080714100e0d02040f0b0301020706270503 71
    0x1c03d000d0440e6200b0072107a104102d14040c0451a4015000308400901c00d800e50220094501400d441c100b450058141c45a03143c000f182d6043c01c003d4001c0c02c00c5e9213844140418555445001814440d80a40380d00741e0b0318808642c54000c0c141c0c1e200500035401c0504085044a001400b21b20b0704020181c200040000f4825010044075494034020b040f94070070301c40c00c400516211070b0011b03450324000b951400d028815004012000021400e84401d0f03c51041c4280d03440210700900948500d149403540094540302c201080d411420b590148655403403955000d080f0b900007000c000c07840b40d8415019045003028401c40d54401220f040c4543e40005507110b21412000600302c940e85560300240a40402106201410060190790101e032890f80d1900403040300c0050380c1900c0c600403403541481d51000d40c80b0310040d1410020190641075107400340d409110180045c907480b005010780380c10708007a5544091000300b03041409140c1c0090302404180503039801c03140c000480a0741001424441002c42c00100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 956371214 1250 956369964 956369983
    0xf050405090f0912040f030b070206070f0c02060d020c010519020307050d090515090f0607080105060f073201050c0301050303093102041e0810020a1b1a011502 70
    0x10355120b50f0740d0746100b03240040360030a207041c41303c010400140090081c840101034070b120362840881235407003400c100d0742d0715012102c3d10002849004030900d0140191050014070380042d050a2030072941248800507071b40501140c58050b956941040780d2018162081c0264a81480c07003075156040c80f003c02070040c060641c601241b586e82c0c2080e9801c00038208245580150315201c0c40409240c5503c005032251205020700059004000010324168815640d05041e200f00428407824900503584103502c0350402901140c1d150407881c401c100311607000e0144007040321452003040e09072038811240d5003035803009810b000815034188010722680d0b5001c002d56100e02816a003800c01081c01926070b035944040e00d01d5044c80400075117107042c98420260000c105880301c649030b807130181c54260344040030781003248244506600203800c0d04805603201e4004180d83c400d60301d08079007084124100b02c6e01c688030b0004121040e4410314000c1e80100c0141041d1801041c0c83d040301c4062800e94140a501c0d0000b00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 956372464 1250 956371214 956371231
    0x270b010e1003140103030503041202030901142a01020306030106080c030607050c28140a03080a0c03061e08060c030103032712030206150a0f140427030f05040509 71
    0x80d5030a45254030991008249840302e4881c480613595a040181c0b050340191000d071491000e0310743c0e140310076000104a90400302c0c181e5408140308103286010055821000b02c0c8524031aa698020100d40703041141c94040b01c0607580010f9032401d010f010182125644d034408407c0b42c0141110000594001c01ca20340d00c88018100f85a680310b160710002d082101c00b9803944510b030001c810001e035002c0264100500d00d8420362040b600c40c4a2507403140d40d10000480300900040000001940114080c0c00a03030b000c100c1414041035450321000001c11600d46c09010549c00c100d4007130200417407142001031607000400345001a2455046440003445c070709202c0020380d5400e44104001c21a260394600f040020f00c4c9203080c40d04c6040b030510300203445841c159004603001b0384884000f059490003d0244086408006581018900c0c01c484102e5590045c7d040311790041d07031803a1405034041441e03102280308000d0115500f0030740846c600508642d000254030400c0100c2400103200c951218140d113504850070707 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 956373714 1250 956372464 956372479
    0x603070f0b0f0d0b09130b0a0e030304350d0515010807050c1005010902031008010c12091406041202010e120a050904060b1303050f0627030c07270b010e 67
    0x11240c4102800d0b28000c003a8101d217001e4208001c0140403200c0d041d40a114203419a1940c54400102c0c00f5603862081043c42d5810030000318002038013030031501624013807100311003845545d00700228602c00c09080c020140c980c000a00d07814095082d10030b45034484002114400400c642c3d000007085800d0040001c003c1c000c001900e40d900d06800c02032040200a041024001e039a1185080d40194000b5a0203d035425200c030b1010a4000040c02081000c50719640c424464128050343e017400740000f01c4068403894030341d03404060700aa0601c00c1903c118094000508080d01ca00002400c4402c0100c818505800ca09045410041b02d03004403070f0b10032a00d1801070f454280e0b00c000034000301503039440064000c2001070850b440c141c4000d81e132012203020b00161000341315001c81040c1c444900b118550107003018900c0320002886c2c0d410100001013021000c4030b0914080c120b4452900e002c5d40c000505100e003149454000b82240c5000812001e0b409005010b001c40c0c1e000081c00065440c1921445402c2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 956374964 1250 956373714 956373727
    0x8182407030315210c0e010f03150b03030a200a060e070f03030207051002190c090b0105090d060c05042d080a0f031b020d14070e0c04030602030711030309060603070f0b0f 75
    0x10781c0050000900148007071b07010b407569205080c0c4000805480f040316103e49100000c1504081e6200e070340d0040745d0240c05180f411200f034100302c5005421400800c81c0b00700540003010316410820005542d24443c0300c1c0045d1075205424410301d0102194054840440f221509000195000c98220101ea0081d103002240364400030069003030a00040720303118041d015840200c1840540f10041080780c3c200c0c24100010081400111418818102500d0300483c0e1400b071400002c215500802070302c0c0341c81c50300c42d003410b44070454450190300300e4000c01d01c8040418103500310280c6c90044c5071300070003144000f8164040380d43d9500190b49800c241c0503062111800c2d01900d40304400302c2c8034403615402171103000c080400c2e1901504611074441c0d000c909124105021960401c208200b500038490349508500301850b40e66110040e40c002030645041046103a01501124400c0000d94003a50a050107000240707070903814940b40242e191310400e80b800200d80200a2094a6021500411140340f82c4d1030b40e440 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 956376214 1250 956374964 956374973
    0x7020103050f1003060f0b1824061c0b03060f01091b1b020102070f0608010311030706020a0b0703112a0c0105120903090a23010504030818240703031521 67
    0x558035400316005508110303000341400010103205e1207501c0c081c3d1003140009c03a11205081c001002140c258200302c041121a40300e04a0144032000301c0040040861400305083c080381c1440415681c102414031408012321034500075004244200c07500d0b42904443d0103800600130701c1d0101c8507000c440c003a0644032803042075901c2404400083d00f4180d404e4541075613504001810b8000c00d03c401d80d0038403e00616200289000706500084414913070090070110180d8175400074482001d09914189039440c40494100340e2100c018210b8075460740c005499950003000d4107a681e17250b00c2007074441600256820100c90307801c42d09581c0c407088101a0180607541e4001c500d1b1451040d003000700c0c2e1011a6450000c1c1540c106a003465040c0307021810806500c40c004019504e40c000c40c00002c211120911004088040c20307072410010900040c030090400344c40856199a040c0c0d105a81c03011b070340000504205268141c0a5215400500310b20508040c0ca040784600a0710725145402e0300c0d4100b104018424070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 956377464 1250 956376214 956376221
    0x10902070606090e0a06150e1602030409110424120213050d0f03111504140a021002070f052b0510050a140924070203160807020103050f1003060f 64
    0x1811100020000c2c11609080c017984c4a5003900704861745803c181920031400918070200003100c002c00d01d2040700e40c480110680b203000b2038408250444c0700c2400002240c064a004100c00052980c00060707403142440c4028464642a0749003070a4003105044441c9003950081d944205070401c0a00182c52b21000c60880540340340581c455a806244011550188640e104a08940c1442034440a0303420344880e0b00142c584044100500320350a00e03c0000c0c0100750382a44145a00c0d41060945800040316400221541c03081c020303010041e8423018041c0407049214844902401049540d011104800704072082a4064500702c0c8403a02081c2c840b0504011040000342030502c1100c1c0c06200742c0c58060200302c018240034803503400c0952003102084e000c40e404a200d02d9404000006010314003800540740c0c02c3c10034007800d0030b0b08520003080141c1c48240c007042001e103203510a0344038550720070f0140001001da907400b03450140d4042d010010300100c0125144500308603a80500c000c00d230210602d44a0004 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 956378714 1250 956377464 956377469
    0x510170705041431032f150106020f07051201060b07060b0901092306030c0d0602120a2702010509060304050303060103110c0a0201050c10020406120f0209010503010902070606 77
    0x9040c12200348074440c0f5001828440c404400d00c00c00710711450f0014101520601e030780750506808a94811010a105090305050415a2008144c2049600f0301c00c10811185a2900d500754111005545170040c000454070700402a900c028180c520641d40c100d521810f83d84140c912034140c01ea1503558129080d00217100400300c88092607198000c0341840009451103c030030920514040d400403038840c042c0d01c0380ca02400059004142c0070304d07010805c00e20400000e014150700d441141c881d034285945039903804610b00c0c802c06004d80c889105158518441d840076000740d0099044c1030002140340043e800c5c54070440c10420f51496071072403034001030b1900d202e0000b140d5000b00c0f0000070001400f030000025030081c0000c0ea000c2048030066804581c481c000c00c250041d064003e2070b02600590b100e03001400404001c0b100b83c071001c7c0003441c20a8200d80c0103501c404c000c21040100f00407402e45510810703007200160b0f10251710704070110700001c0c020b20050040506599010030100140036481d8800b201 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 956379964 1250 956378714 956378719
    0x51309050f030c030406021c1e1709010b0306010503210a0306051903120306080c0f0f06070c080f030a090e0c070b0a02030117070b0331030507150510170705 69
    0x10b45240c140f0704152242d00c1401100d0140c404d6400105000355582c410b1f80c0030b14140d80d549551044425010721600d0003803918001041031035130020707031050403c1444901603568800002000456241410306014059114510075040380c02c9174a0b560054145001150200e89445540c0708680380c4241c0090034103410140d04014030303550254103542f41c10000000d40303009521a40d0f542c403240b001102074680900034003030560000c800d00c211a090101640e880c511000301243c502c004010007260a42c0c024641c00d644080c1c00329000c214161050200c005900c4000f0060340ca40201c1072409040c9020707600c540160020030741c0004640c45000000e85078042d5004003d407020f401c0089002010350401c0c052460307091081c0342e0111080e039000400704100c481d008845402c45c1d5030324131503411280041c07154ac00112a501280046014610040340d00c1600c6a1903080e00c40d11141842910885120000d50819281c6000d2000300c1607114500300440b0740d480042c101e024008410f6906109055200301d4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 956381214 1250 956379964 956379967
    0x3060d05100207030305010506070302070e07170c0d0b0d080406080c0708071a0907080615120f010903030f090b04020d2310110a081308120a0c02010b0406051309050f03 74
    0x20100700ca190000e1424901a640501c2a03903215010054580300300351009000d40d202c0c1408019120ba100000c0b98801c4050400c1401d4001c0702d1110301c100c400460b0034103403042c00042c0258040c2c200c1e104921500c2001d0395516011903a503601c401c124841e43c0a40b006028044002130303000022a001c4524855001e01c1d629203500d900d1034281100c1e401d0144001d106006180042d1a003440010f1410854610703200411441d216490011010003510080701e030400c402030340c2040c810400b04281803001c5540b1000165a480b1810003d04881004c1c00c00301080342003a1459000c201200b83c503507000350f0100c84103440e200d86494000c0c0303554002000402003409601c50102402000b042c03115107524004400d000f0480c40c03403814140e42c820822030401080e0721030041543e80e00000c4401910034441d5016a150040c0102e817464040c03012610040041d80307c0031008170ba00c0d42802419948042558140a03685c100360000d2050955803100c1c0166030b980700c0c0c82505000040180940301030814003501d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 956382464 1250 956381214 956381233
    0x40f0207030c020922081c060609060e09060a0b0904090b0106031406120304260726010504030e010e190e01050924010c21030f1d1203060d05 62
    0x10300b07039004120080e031180403c0b01c009150108014883c20500c1000341040e990480c90b942c94500c16041803416200c000179500603400c0702c0605124800c003a1181da12450b5030b05203020b00042c82c0f1100c2c00c1010380220850b070305000d02c3d038603155910302c00c0d02da01021458440702610701240c01040098405020301c540c1500014103150164802c0215007013102000303040307985030424040308141901c009401544100400c1107401d801c010340e200b40e1042103196501c0c480d0701264503890b1034502d400020b1000b00b002c0045c4150030074412508110300c4640020301203860152400740c07a588040c05a80c1c14854045800d40035a5940510060b4060b9060003034500c0d80c2d195104840441c0090003800e0281034000042506001412020070b4842c002c644440320b044680c03001103030000d00c600d1040711800c6001c941820510008258125100200c3d640014851800350100040d11348064000548a00f2070007a0201d01ca404103400c42c00210100c0c505559468410102d42d0341c0c0d03107581025000e801041a036 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 956383714 1250 956382464 956382467
    0xf0a050d0e131d011d0303041106130602070e061c110103060b04030506090d2c040915090501060605040b04171207030503040528060e190812010b04030c14040f020703 73
    0x4001407980c3c01c80081240b41d141c6403d03032201030407611450100d0307030051000034000303640502c48404407007005d0591402c00080c80f18848a40740580c12040158020113400c1c880c0f060520409a0301010444102d40403e61040104480a882c894040d20340907550458010903406038020800803c0b07000c0d4040c2c0e030355503a070030b0190b241e0710144d0399107030310303000310780c020042d081c0300da41801580c1c1c940e0300f1041c0c02e4039802c074a104851110002025007180e10ba41495006c110810a0011001d20480f00802c0c01c0a8516045007110015027265007803090600c0144895041c180a50b02516410301601d02401090040305180c94100b0302c444031001e90016903442016807010142d40901d10400442e00344943c08084842180208030300c40e041d444110040e1808260b8035000000652102d006130b4400e0709070440051060400c9550a4844070750006904401f030101440391401880340280a50600303007181c2d50050525024442d0807450524100c1c8890969141d23400345002c508044030466550096180 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 956384964 1250 956383714 956383751
    0x21c08160305041a0a0b06030f0708010f0b090411040b0301180609230411030111220501020d2006190506090910090303060b030a09050f0a050d0e13 65
    0x100034016104450160a0060090203198011a03000d080d01c54100c004011039490110010311406640340c983c40c290609807505401503018886000d181c10f290b00c4c094801800f82e00040e03000c403044d841d4011040060040e1101640c1c0000310440300490340d00702d5800091154010307030708600103450000000245100d0510444030695041c2c180600010755076101e01da00f240c02c06006c2c040000340311850707030380c42c119941d502e00c5c0d2042c4203501d803032070003840280800c0c2103a070110307000030b00f040d4009507105e00303070510140c00a413140d2402036402126042c040003d44506105084200384401081c061f1141e101c0e00920140c1c2000c800200c0d68289011222020000394100920040710f1501001c6820781c20560045c91183c22032100400f00e94261600203030082180501c10f07402c00d50385644c0400c101d896000203502500c004a80851401114100203042000d03903180d01c01907070b2141c1090400600c0216051103c91039a05114640c941000085203507841c10803e000102450143c0d50380420f9001203 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 956386214 1250 956384964 956384971
    0x100509270108070e010e04140a0b0a0b04050112080702030709110904110a0c020f03030405060706151203020a03180b0313051015051306031e21050d0c021c08 69
    0x85008141e0740d0303825660f40c440b4043d00620781d01c10201e20045c80140810b12203907800c07600c1601e032014803c40c1905414200194001b0445100d01510140040c03120755025014003814100d90802c600d514000858245240000b8000c00f038000201c3d541c0199030303051003402c0040451101c2849812081554200d660b400060700303600c202c1c50800040044c0d4000742c20b40e8a00b100a40300c65020211907000c000543d030110001c40d44c0f61004120105d500d03194040039144d0b8a214103008950414408040c814000294105c5902403444514020119500040540b025074040c00c1000750325032203460052496119070014914990000240920640407500d6107240e20b01560a0b140001d41215481d425180b00500346014016004010300540c98500c00c1301143e441010000203100ea42e950390b02c860b0407281442ca5000300d0b501096602484404104502c82751505800e43e81540701c0508080c045002e5024082d00441e621020340010f50f0081003550340141c0410b00007401c0c100c0e10000140f81d080200c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 956387464 1250 956386214 956386279
    0xd050309090a140c0301151107090903030f141006120b330a020d0509030304050d0b090d02010203190f06030b0a2403030915030f02160302010b0d030e100509 69
    0xb0f0b000a4103031500f034050724140d0b41005c01e0401400c4103180d00b1160812041d52900b01401007400011389403850303100c1c07902c80070302c280c07000720740071070b0100c141380c1207403078400312820125220010801100c4007071a82c04107496032400c0c0000d09540610a20b402064445a801c1c0c01c140041d098225184c00b01000003001750115610700008004001500301c03d0190315290301c05a4044e011f05005c05020b81301038a000c580180480341043d0b03031500028050405040269030910200d000e0203800f6005004806041201c1c0c0020351460134041c500003000800c1e050340c0c0b1541e40d52002c4c0c100b2200000d0f00301c0e00085800c41c1d03c020550522302610b8006140700d4125400f07070884220020800420005c2e0002140d4240d291400c400d0714045200c414196150040703420140c1d03035199170b1144101c3d4406070000460451840d151802d0320710340a821034010940807481011b40e8042c00e00080d60004501080e410306444031942600c820900790781602030314004d1540040540d85289000c0e591079001103040440c0d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 956388714 1250 956387464 956387501
    0x90218041506050901180f0c11100203010641031e1905040c0b070c050114281106090a0b01050d0f06110702060d050f0601050c07050d050309090a 64
    0x500181c000b120b00921849402c0882800100154003840071899140050a4000300e2a02180c2c1c9491044800302d201200c003144945118000000b420040b0003510741c00701e90110b1440d4142200900300d082031900e040d2682c41d060316040129880c03110002c0001d1310308008100340383c0c910b881089450704100c842a110080d4003945486003400001e40ca8043d0300444509485468105402000340c10010815166814803000004942002e98000c00c203850250503500c0e040d50410000508660380130808491901c01803049c145607182400001e503d004841080c4500c070f03101030740251005030b48182d000d9990300a280c10031148031700119461f0a12442494424116070f01d6404100c040c81040314041d100c4002c8011010020b21180c0c810001c55011441c0c42e801c048032036000886c5a4080f859603034541d6218402d100c40b20b0803501084e5084102400e00c6800d00e01200b8006030340748640e11030140300c0d1000c2c080500a06c241403048806845029002000c50703e8010070780c0c0c0142820005078407a0a40 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 956389964 1250 956388714 956388743
    0x1104021b01090b042a03060e0a050715140910210f051006020d080a0b01090f06020d1107051302070f0f0c0e06060703050405010807090806011710061a0d09021804 71
    0x41031003100c00c5c011529040990441d16000010301200d0407000480c03103407005c3c90020405c1040010300030a180305808280004c0603400524441d103003056031282d002c0500000b60256a5070b00310301c00e401c5c80c6181081c050b03d00110307200c18030700000c0c5e1403030101460107080c0140301045030001e038441c0042c905440e112540d40c17401240c0c0c0c3d0b02e4200088000505141c0865160350b030b990000315100205142041410340c07940398512000fa0941c4c000c1001d03074010040b14801e181c102d00003484208003017025004036454040030403400d6281c000c45111f8940d0000380d40c000c001b000b050101805421903071160b403002d041c0c602052252103030b0003a485441c00d4074001031610714181d03048840042c0e1540d5404c1c1800d203008010750714500302030400b02c00e118140d20081890755040142e0b600910400e00e0700509074150181c618100381960707080c0000f160034040b0912524810900c81c099407172003520500d80c0c6007030701134540b4000c1c200142c00a500c407502c661911618901003400a0051707000e1072903086800c6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 956391214 1250 956389964 956390003
    0x11d0703021215061c060c0f0315060f0c05070e04060b0a0906120b09010905121e090904170417070905010603050f01090b1504031b0506071104021b01090b04 69
    0x1001c1c0524002004000c4001030021705103050340c00c545e0061980301001502c45035482070180e483c0400000000f890102c200320744c00768113024014a9115102541c0c960741c1c10300000600160500c140c0c1c1d014403c0006001c42040010000003005100c108503100281c01c061800f42c0c003401c00c84108a200e6514840041401e80d02403294208403042021444286070981d50303190600700006090041a55a440f52080400c50501c50485000d4107002103d5480ea40c4c2d030780981404100c040001804201841f074042c80b030b180c464084c2d420a401034040c100c202d000b543e0048040c442c2c0d811244031481d2410102c624503400243c00780c2601d80b50f0301c0a01590f070321141e088040302d504490501076102c0ca000100300014841d840300031500c101800030b60072103074a24114400d43c2d101d640212510315500c54464a4886408d403148044e000c1282c0441c5010b20a4450b050341100980c1c02503c542e6000074841e0f40525440700800790100020020302141c1400d00b800c445a006c120b0f0142c40b21030104074401030740c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 956392464 1250 956391214 956391223
    0xf0907030606080a031821080d050f040b0709141309080a020d120209061b0c040e0c0a090c2a21110102040b041a040308131404051e0603011d07030212 66
    0x210342003400124104101c40003861507d42440064808040030001c3c51005032160081b148140d105020461442c14680f40a04210400070041020881d0030801400001d05288500900f1101120107a00207019007500d04010885120014216030300000c05420954000c2050402894a0380b2078140145221034a41d09034424603001682c410410068014400d4a2040f40c41100105004682c0b1080b20344000c20b084602c86551000c16922022044807030b0701d80381d06003101420703401e00148685903491001410090400403008414000503400ca90b1240884111400c07003500300040700262000d220108502090326000080000c02c52607490480cbc07103050084500315240c44540c00c2c90319240c448440049000009a41c1110204200c0000840e00241c080c0004894103240310000f245400e4841c200c0c0400d4800b550302070341c144010003801304503d1002081650b45040343d58025520080000e0051600700f03500c1d40a00c04000c0b020400745000036079041524804e075070040d40000b003d11b030030b42c1e01c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 956393714 1250 956392464 956392469
    0xf07030b03120a030c02150c040504061401080f04031101090308071d01050307180f090213091116080d06030320011109010c051005040b060f10080f0907030606080a0318 74
    0x1c6000030820083d100c2d02c00d51028040c0301c014416502042040017030840d0303840058400f500700c2d40c000f003024059443e0504c14080244007222140005090000c00039140c940000e141d1150001075200280606011791006c245150b103210007080b1040c142d10300078000c1c1c0340030340311100044c2e20000031101640a0180d41c002140050b114142581d66400c02110450000c4a98814158600c0b40000b010000c8000c141c019100e61000540c80b9107500e01101075100340c552003c9051400c201d802024068420201c401c062402a914803564209040800c0107110706e201810300c2602e01040001410391000380351610b22005509400c22281c84440c06080e180a0620720203102c0003040107280b13940c082c0181c600346070310a9040c0c540c0c28124004480c202c45003118107450300121a400c0040c20319024404030418182150089588040040024020400103095071540e4500201140212904111160045500580600c00d1585603034a8503100e0380c0c01c800403800302d6080d6006110f0305041c00c5800c130a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 956394964 1250 956393714 956393743
    0x1031b080a03080a0216151b05030c07060f0b28090b1e0a0312090e0c0414040506120706050c010e0c03060f13120305091e1b030f060f07030b03 63
    0x4990b114182c21034020f510440c0040c1550116402100c00201c41034a607c3c5400048000001c9210304030b0700c5444044083d4080e64104842082005400e00002080d2030a0540011001440014607009400200400e17078805501c43d20341c10003940401e00d03202006481c1c0081008802183c1da603125003070180c80a070980598407041d40c10401852500c01e28103031031740d58001040303490015aa030301d0312103415480d580003400040300c002040c000c80104510440d0007424074002d035031406e842d085508148690070f40320300c4e200b0358458002c5002c5a072803a00b182034010344081500d42440d030b40c50010309a64040c9925950359428681e06041c2180e0108200022003409800b401255583c0b000d0340000910051503001d502000c9003200011170400c81031421000700c561400100b03404d1204600e89402030300906117135400403900c50410360b8600030600b070100c030407840000305184114000090615480000c50780c1c09200d2002008501c0042c051103e003e801181c9040221200340300c140340d1a8000418800f0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 956396214 1250 956394964 956394977
    0xa11010c122003070503150a05090109020c0705060a050c070e1b07050a0b010e07110a032007032a0801021e0d09020d0b010501020f150115090b0301031b080a03 70
    0x900c0488250000c4007150303602c1180d0448441c0480d41003090f5001554060f001501c00300400101e8050352039100d1021000301c42c5668868500b00000742c1d04401401181071080e0007103551502030b0010014600030303060003850942c8500103160001c020350040c4904a000741b06011001079100b4904406600802d00da400c1c0020032549410071000701d81c0f04000444407807240c0e6072900082018116524060408002883c3c003a013040600107050840c100401561398101d1290b90300001e4100385c2c41162400f100180c22201100a007043c3e06003c01580090500101c0110301d140c20311000c0d14540340320000454031808152140c003d18201e0081c1051440091007000009112800b00000391140c0d00c0d0b401004200c03140e1642c049080740706820340460301c9001c8440107215035a01032050300160002080105803003d0711915092062206101d2031013039200301c0090240b82807188040b00041d0801070b8419580c0d59591420300034140c032030300c000c2d0301c00c0224080101c2c03140300c0030401c90000c503055074410 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 956397464 1250 956396214 956396237
    0xf0d1214060f090601090b0f0301060807030b0f1909022a1b0103090f05010e0a1103150105100306080d0504050f090403050d052203020a050c0409050d0c080d060801020a11010c 77
    0x1100c481c0b000b5200606006c0581400103d0202800090070305001c00c0c0e050b5910ba524000d406407600c00c001e803016040c1810003106138415140c40046081c0d01c5800ca8010141017001064190f040b0620b800242c41540005000520000f1000449241c4805005c020350802900d1440603212004c452072522203080203a803c481643c400d0f00040d50301801640d0842c2514650740c0d81382d003141c01051048010360030495210b020700480600061241d041540540280c060140c54040841814051184110b014102040310030f4484d80c400005030010f21304640701002c0e03814029100307400c0f80c441e03141305900c04003e003801401d0440d505400303198142c031031505007484109001c02801c40142903100704080d411501d4480020790f4003501c00c0600a8014202c030312000d0500034107069403020720174056400c05040c0c00002d1030015411002218030314142c0b16901082c41c2c41e0245c0d102d09041c807011035007080340c04190024198001d125170040c0c0d4071000755010924084a09854002081780081000d1060710f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 956398714 1250 956397464 956397469
    0x6070b10050105031018060b0a021f020903030a0c06110c0a1e080d09060f06090f0608010203010e070c050109050a03050a1d03030a180801020d0e0f030f03180f0d1214060f 75
    0x20710803e0141b0116900303884130400c12040d004010102c0060b804000c2c001d04490701484141700690002d0400d600c3d0010410201c0e55034070600c22540c040140c510031a900348030907070340304050f09410048101e640d0040010080d9030b503907800c8c0302919100341202025640c0c4460403120b1850b103a200700414101700006201000821001c0001c0c0c1780c8588035403220182c052a4882d203005006840c4001a1860f0541c48000c1219015040075903a613204000500c41854844d118a603c42180d10f0b215031707541418900786004d05103a035802481d500ca0011800201a0814060640580d0b0f560351001069076480e0050480301c0d00c0302e45103400d60020009506542d110314400e4000c00d88034603004c0102680c905070682203a001c2401c0404040e690304428100304000c3c03089001e046603080c000d5040c205480c504407100c3c03001404007003000440305060901d0080074001c20440d00284801d8810402c04258068002040102c903078185500c1c10100440c5541c08240043c0109005001c0c00441d6181205 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 956399964 1250 956398714 956398739
    0x309060a050f0a2f25020303071212060803181c080306040e100204051504063c031410030b0c030a151e05060403030c12090506070b100501050310 64
    0x10080400100c113a1070108041c500d04a00c0c00c0d5207120882c0c2540c4602400000300101000300100c0f0904502103081c01c00f42e50b000050f102410741214181c1085240c4401c140c4401102520114000d4142000011101d0300440a0201c101c2035000d071810010407a41003180440450703000b401020b0f1650b000c080840c2c012005168842c2d4041d00004840080c540f500c1d1a1400a411111000f900001d0074015802d054103078800740701449480504160030b14101601640209243c1d10550043c19104460225140343c607a504020040328481d0084144070028050301c07004411807004c01103840031440d811600002c50080b80d4105454091a844400c0410fa413684094690600c040c5ca130a604000c2400f814000c03001004856070807060152903000195001c02c2e198016881804140010800b29800105008006a01c04001040f581212109580083d100d40015810050200c2c001c01045481e00c0000d0082c8041040c200043c2e549400444161200b02c42c4400561a1040204080c000c0c0b0349 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 956401214 1250 956399964 956399981
    0x105010e0c0d05180f0a0212030a1d01050d1e110a0c0b060303041e0806070905090c0c1c11070504110714010b1801031a0405190321020309060a050f0a 66
    0x240251214801c0c12800d05d445a00c201846951700602e00d060210314200d03403155290304050f0095410202003140142c9800c010742c5070202001c040294441043e032140702256009611300301e003008046588900c101800254805044400c0d1501ca42c185600f6114415075048aa09036a401200ac1d582c0d55241c603540300c0900324a030584410b1201080e40e950442401c02e2000303d2040e0700d2001c1d4034044031a40b8211019101000b0f100da0014180400e803107250a1036807240600183d41d582d000351881091a242541203403100e00000081d2501d0143c1c0d016101d80322400f008012243c1d0103071a0000c000844028200070301f10008108820800145d49043c07941e48010400c3c00001c20007030748004500203000921030b9055000002c0010700400c081c0c02c02280080444001174000392070595901c59550311070b881d0541844c0c0110210104142c4030701c0c0780910042d011440302038500ca00707640300d0001c0e4200340d990b48414020f620000764907078414401c03248a10602c10307503051151a4030007c400103050a2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 956402464 1250 956401214 956401231
    0xa0e03030604020a1b03081e040c150203130f0911042105030705190606120b0106110f030d09050f030703050301030224070c0e340c05070902070201020105010e0c0d05 73
    0x401c401082c2d20301000b117101c1664002c4e00c0f20400e0b0300c2e010440f003001d45201021001c51054103014800818000e0880c1416544209001d280c0c41d40d140b202a45540920603201d40131a0705214041069240606200100c4500c25001d100084c2926400c8109006500401041d0340b0b1070100c058000c41c2d5818030101c01400b85003546d1800465864590415801c0d00d4038054039079001c61540208175503403155800034012080660304200b140c1c1d0f21005104418031824040000010048c500c5610501198203a1031400c01200d0b80c526a00680c000605051601643ca601905001c50641c09c000700849250740d51654030b40f451a8250350030040c480039503000415500c2c40c0b400b040d4000381606002001118068201c2004007860314101034070f1160700800103507010350f050b207080500d02c02c058241c0044010102101903407081d0444122400001c042020f023880c800c0313000000301d1034010750040001d203000f0b074002e0140d0b03030702c601c1940b10056064503144000b040230040c03e07050a165901403900074064 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 956403714 1250 956402464 956402477
    0x61106060d03172409040b040b060a0f12060e01020c0319020a0b040605042d110d081c06060804120f02160b0a030e0606010c2003010f0c080a0e03030604020a 69
    0x1c03050700c012204000c40341e441803a0410035903400d1074064229800c5045500b101c000e04a03281c10307907c04500010190009100d42031070030100c1c0d5136a40d50441750340a0072841056419a03552020000069014039009079030070740c42c10070910703034040c8107000b05c131040003441c801540b07001107181000046e28000c968500450080d0b007106000903402c45082ca000303d02030034020501303060509041d00707401607820010000150b100044041039614540200000f81c10900b04141000e5010200f0b602403000311004020090001d1342c16543d250a603a04196000204001c102071a298201500c2010b03084d00c002d007201c005180a20300c0c5911414003541000031030b10607541000030b01d01481d014a44e03150011010140003144c0c402d009036040c810944130096440050106052100000e402c0412052000d170080045081d00b00800d241c58580c2d4210b030741d01400810454602400403030007070a15480210020b040340300801e8580342d60b402003e20440d0f00e100551314607240c00c02004002d43c400c2100030b050016 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 956404964 1250 956403714 956403737
    0x1050a0504030b07110c0315010603090203150403110712020904080f091509010e0906130507051204050106060f020a0506180c0a0b090306100e01060e010c0204020a03060f061106060d03 81
    0x3c000b030340280141e4841c25520300785038004034244410100c40300d001c0d80c000b030703004505180c11000c07045c11208103003000941070032940086810260400d0510790841929802d02c820160b100a50b0514180150103440c091512800c41c0e1425092042c00650302190010215010440c04402000600d80d0a0025460aa82007000c50b46041c0d40c0f03800103c90000c003280410065030024840041031804855545244c40c1070030001f40c0301c11084410400540d5a06e0006480354041e604035202e41040b6194902c851a02e403604501038540f13400b680f0001890135004ac45558000110028000c0c0c0c4400603105941d210000300d482a13400c2c4005044a203d0800860f515403100c030036040c09410070315411075840240d84281450241d02805082c2012000401007080100e031041c11070541b07403a490030711815551100100c50b51941c0020180d40540700088034040709405034400e00c2184d01c0004a0418a551503109542000d04095005400d4020800003040d0780380c65000d07800d4440c4070b42000c026524 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 956406214 1250 956404964 956404973
    0x709031a16050c0604110d020307090501080d0302120a0509160308040e0f09100c02010605041404031e02032b051806010801060b070609060b040e0d12090203060601050a050403 77
    0x4022150204251032544184a070540712607a90751490710712824150720f46964410503503600d08008101500e50769406815041a50300d0f00c54201d0000d4008040b20105511420762900a20b000e11500c021481001c0448074954068002c1e24800d03104075000354200c1d0b498102600c05000300520256450280480b281406c2d441c080c2540050350003003910b25121401c110100d0b00c070440140c4500140000007042052084000424048d01900c0d03240118030a004c1c4002a03024000c6030704110780c001d040c03031300400300d00b810150301c0b600c181d000f41c0c0e80c1c0320407400752918100050400048480160401c01c507a845100031442801d0502c2c0400394141d10082d031042103141290403d80c3d0000c0210355000c82c550590604100c2103025001c1140204101490003041c54454407501600820342512a12107800b8403415a201300b038007640140080c030040c100e901c01c464440c1714498101000c155042e40183d491450741c400d00d40c1042d8068005c01c010b440d03010040d19103401c040c9400e800c00c1000c000100000303 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 956407464 1250 956406214 956406233
    0x2030706020c0906032b022d060601210908040b0c06040302212b060312171e04150e1c050a090905130b0405062707030803070903 57
    0x385610703800742680b04050003c110442da0301910442c42640900012401882140405800140710740b04080c11601d481005070304002d103000d0700741c1c0c1e0602c4000005888441c00d9440d160b0506400040d513040d541c034400155071001a00081c99002d400040c00d43d81d42030100c3d406042006d0040e030780740e81015540c10000d081b5034020444503400b60844414802011380400018102e4034007204000c0c2074a007100e69a03003a82c042d400780f2a202004941100b070040042e840c0004000c40c9414040c0411354680c2816805581300341050b00000303450400c0900070001a10407680502845c42d00c8030f00703c0b889442449054803000d0001e41f04182140c85034510040c8030b06c5000c2102c0a0305006e0100540b1aa207aa00c00340b00c0400c02c0c07000d00008020003004203038058400021341d0741c03100d00004d16441e02d00c65034161460155004010180c0302c0103000600030005409031017004481422801c00603864241030b25103001d000440c00a9011500900c00070b000280503540c46201c9d0b18003544010b0783c90300d484045 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 956408714 1250 956407464 956407469
    0x60304060b10090b030a02180306040c03170c03070f030525204209030601060c0c0b0f090402041220100e03120406200109030f050313020307 62
    0x320340c0e903441200114202039a000e144602c1900705605154a8501038a9452100500341c0485950004111107112402100c0c0d5420303100c042c045403c24039242c90440202403042c0420750310a12170394000171800c180c40084030030284032480075604009050350340154910303024204606000c0300b40003803504401c907617011070031050076955442e41541003400c01d00b1040420f00c418200c40241015002c9a54880c0a04446400c0e11008c1124070316589110050031102e447c08822182208690301c00e241510843c081c0244c4c4808a040c2c0f0803d903603620b0113450341f81410000409200345000c0800181c0c00341005072426208003a00c0a24180d00540060b080341e215410000725030007002c8035a803d20103441d421004c1140c80360000703c00c11015800084100e4007945a0f00200503020035064181d0302d084c000d161317101040d003007072580301c540f1880c0207840b060840003854040100c00310019840c060500600c4403094041e1103203190946415801c03203caa0006160510004d6000a0000182c40c00c0080200 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 956409964 1250 956408714 956408723
    0x60b070c06030c0c08040e040c18090614040f0825121706090109090f0804030308180303150907030b0901141908030904180b1f230f0a0302060304 64
    0x503003800c1110280c1141c2e201c50545081043e0202c2e1180058098400c03141512070764050030307180b075803545400d06030600b45400c0603920704042880c2d020954981d401440026210300d40502a03d07401655009407220100d03000f800350000700c13211101080700c50008142004c200ca840494048040c0c07864032a80602c40c02c04c032403181100d01d03004111503000c15103000c0400c5141d009030080c100300c2d0002e0a40301060003410096a5240c1c081000c00521940c0201c2999000345507941351a0340303080142c201102155202c05174081501052181a408011688100c4540480c2034880c0f204c9400d00412140c010000024580e075a851192a582c442c86101d00070f00e02d5540c060020284d54080c0580c00c00f007510f90440e1600410014407101c1c1c40070040d10001282602d00080154500d4034200d88550b0080025011600c0602840741c040c101c1c5060f041c074001c400d110b0a60031075848001d05044d00d0310381400c0e80c01d400e050410701441d180c049050721001070020024620305850307800041240d4800e80d81140c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 956411214 1250 956409964 956409983
    0x302060703110315102604050f1207060c052115060a0e0d23070311060403331a0a0801090b0a0b0d080d02090a050418060f060b07 57
    0x1810326803601a15000202d5101414103608200d092041000c10034665188196464800040120300c9080322085001c00c10f040c01d10803c0b0300e46000280410f0a45040d18140602c0018000e1201d0028001d0101030502059038544066601c907a401810304c0b8845608020041150105612001035441c180840350b0321010414181030b07404503d00352401c140d041c000c03181800f42104450308002207110200c03041c0d41d03031641d8103041c0c03400003000d030384610194400300c14803010811155000117203001582e00c0784a01201440c40c103020041c41c7c0c0100c0c0b05c0108031506944000142911403141e81c04d100c42c5c144403480b20390840070110810b60752104950420340390725620400302450059141c04c01442c20380001c01507160700d5100c0c0d121082c0300501000c11903803942060641a00c4400a0700001034101c198584c640d000f032201c0c500a50b2014040600c100706080000c20709160500c03c0108800d09007141c01c5070924980d407088003030005428000f50071a640c180000e1101280401401036510909501 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 956412464 1250 956411214 956411221
    0x41202040615050c010e0601150e0d06020a02060109050106090e0105121513290c030c0c0313061e0503071416030503060312040f0605072f0f060304020d030503090a0f030206 76
    0x110308403111b134040d05e03565502c540c0c01080b40103c00d20a031840c0d440245004a1040340d4400819200f1880e81401003101d41300190300ca0b451540460070340e0603200c4c40322092100e640d0314102202d291609001d80000c072541c10004100500c3d1030340d8296142c000c1071094403440c042d4011803400445c000c0310a0854901621030600c1048841c0b1040100800c000220280c01c00040040701290f1100510095960100001240c8001c50410944840e403080d0700403280d07070703103850211030017180003511620022500302c03150b541d800d211511007005600da031541d0715406e50360b41000881e82c0c01080c285400480d0000c2022030044100c0a00039020a8007980301d031039903030820800341071070405022030301311f0490b2041c0801e10181c000c1c1d09811013140e80503c1c00765201c10560500c001003192100700607030804400c43c4480c60440484911030101801140c1c55402c81c000541484818401210000d5009000000c00c0c80041d0144001d5074100754a88110f9102c0c078400d5039140085002c002c01500581d0044040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 956413714 1250 956412464 956412487
    0x1005041112060f060424030e0f060403080a060e0a140f100b03040c090e0a0516050a1a04051c0506060f06030412141305131104120204061505 62
    0x800003034182080540749040c0281807200603110707020307000603c190504039030340001c2e03612a010303034002d0602134070103074039001c58805100301991920349404c012a00b81842d80503054004110b44822807590005046556910340d400c4408100003400741421664506020404d000d0500c2180c2c801e03601340d1303c00150b00e090303240d0400b003c250082000742286095000c2020f1703d042a1095012500c42e00d5809450362981e14046941d80701c1a0044840c0713614003a460088240009241082e49006405441c85c0c001c848104003035214590050325003083c0036070420030144e1154031100305c2020f04400a00e00b8251940c0002c2e20109001e0368100c50100b440445900307015091180f60341142c4225a00b40354407000c180411114000107001601c911005d4203a800e03424041e84282551803440300d0121394070048110011000240c2d070082c01e004290404004014044d60321916220415007a009802d144c68804c0c25080e8403003007507003260802c0d00c0b8500001e042c0c0c043c5400f0030551200c0c1c0c8070705494403020100d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 956414964 1250 956413714 956413721
    0x12021b07030c050f2101020f2b15051309020301020c0303010f0909030903030c030c0b09030a02010509150105130b18010923070e01020a080406050c0f0d090905060f0405100504 77
    0x1100344a13a495400804955480d0032444040d104104603040c452000400821b009008050040c0c10ba048001820240540100001000780700018140316000e40b00c007034210115090a0000000b480d284002400701e46040420485a0301c0381d07103408514040306502081c02e9070040001c115403940040018005c1780c400341c2030200580a5241c1c1000b400220341c03402000740ca214400902440500310361070090510a0303417002c02e00c43e004400903050381046a049996940000901d90049d480d140100e144242c4c0400d00482040c0b45001d01400c0e40d00381010000c560031401c0c528404079a07038411032740e4141c0f200010030181007468011242c13190f00d442071200c183c886923240107042d6800311541a21030150100c5040c2c21003072501d00444043e1100005030700d0a004d4503030181c0050000b140014100c0e500c103000341381e10315040c020f80e1550895104080d9030f44030020003c00c0481e5040c80d0900180708143e00a40d40000c0090015210800c410b000c42c0850303030305642c2d10022481c04c1c1c00c144002c1c1480d01 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 956416214 1250 956414964 956414969
    0x60a200706020322080304032f030307020c01030e061803070605070c0c05270606120c0702012d050d0b12010b120a030504050609010302210103200102030a12021b07030c 74
    0x13000f80141d10602e5455218900c80104020305009021601800e100074401d0300d620f0880700c2c000c903a4203042c0c030030301000d980360021030f042c0340148038a1103020041c0d40710307000300c09031f580c0d1326001050180c690450200c1d2040c3d80d40e4441d00c8601c010b0004401140e100d01409005a885d43c07138001809440741481e0b404001650040c0340150010050401030030300e1000416180c02031111840038544078800024401e21400003e040e0801aa10600400121640007802c81e107100340c0f14011420034a1b0b00d454090380005500407481e41d801c500702007269004e840200011180c80000040410842000410b100c2c401d00503440c2d070741e56401503249682001c03003070030707050f4010000100006013142e0350003002031240b4061280160404200c049844e4065015203030341c050302c1c2540c030f0100305000c400b01924031404d20054920ba20a211022a000c0401040520790003041c0d0140d4074000707150906036580d903081e4823b0b070402903003023050040085a180c003c4904c200d80c03c01a145041c030310f09040301410719030f4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 956417464 1250 956416214 956416261
    0xf182004090803130201050d2409060303080708090c090405060720030405010c020409050d12050a02070201140a180801091401111b03040b030c07060c11060a2007060203 74
    0x40114804102c162040e01d0b03000345404100305040842e44012129400f485910288150400d6110042c0d000d114450110901d00840387c0342640c6d903038a01480554010344030190108040707002003103030103120f9410140d0041e414004c654640c16480040348a400c401c171030560f00c80c2c0240c401e014296500c00c41d10307081145e44c2ca140c155031aa40d83c2c6c2003622445240310303180c1408800c00540342103440d150080003659800401742c03914400c50280103080300c981003141b40b030a0351408001440c0c80d00706100350380800f601a03590721001c1d1600790610006500c004001c0c02030025280c1000303602d0340c0d00021031018151400000c29000e01ca40b40c52010415002c82450f56170341482141003401c03514030140c50201e1301c00c1b02028007148840e0740980c01d5104a0b00900004e402c000100000d15590b000204840c900c6145c0420001810398000c1700d0000303031000c0340350213504103002042c008642d0350009014910300e800110407645499510303155039407140c0d03011a04960040b003000507425030100321080d0724081 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 956418714 1250 956417464 956417471
    0xf12030b10051308030c0105010510050715020c01140403110f1906020307120e0717060f01030222150501020d020307030504060518040903082e05040f182004 69
    0x144000200100c010048207401c21002050201204007000541d0009280c114241c0781c0e10b05200e640c03140601003d014407809140a2040324020b81d200e003084a004a41104441c0e03087c144098003000a5408107803054070564840b50803441034501095100e0040307200740c0310395417203445030f240444c06c05291003590642604075403507a05404113000b0200b203c25031300c0240169280c0e1117a0055445000764032041c0c0304c840c0f030f203ca1460740b21000039520041c1d5071454403c000230142c20040e207075941c0040703c07524508820b1720700400042c1004400080b05000074802e4100076a81184850304070b5000b41100c1d20005207220701080302c4e58050000c25085005c51014500d080c41c3d9403400383c801d101c1c0b13110301d4081140010f4070481d10b0400c101c140841a5000304140710400107030600030480003081c0c41404058154408622001b9001d810307000c6200480300400e400c3c40e14040803c00240740c120103490141e44c4a030040c2c0910b005030000840d000784a240e00c0c4203500c4405521521904c4400070440c019840d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 956419964 1250 956418714 956418731
    0x405090f0a0f0b030a150207170403061d1b030106091104150c0807110301110d02030f010501021903050904110c07150203030c030412090f090609050c0f1e0c0a0f1203 73
    0x4c0100c0d1140744943c20600099004100e03c1150000344940500607111150000412062561000050040740e00410040c0002c0c0c00d00c440640d10290041042c144640c800c540d00500505c25141e0b0641140f0010000a6465580c1144c20161940f010f0301c00c80428001401348403d001181e502701806081e8a00a81c0207041c035502d250711845081005003000300c40081200b0550303000d41000907004000c0b8000341d21100c3c2c8841d42e8000c0e4101b0b803000582888401c0c00800d02e5440003c90088802d80410201c3c0140c4240d00c090306c044e402103003943e401c00d45460b101441c03140888001e2000482c42c00080ca1220300e025220900b580d29030794101d003150010001c0c060800c1c40c0c6015a03400c15003065103d403a12303044140c1076440783d140c1d61080b83c4115496a000604880d82d0303200340201d800700c1d4010f100aa607034890702e00c064403c40d2a4045421310138440c480c410011410907003910888071a8841c5032055000c001480c02c1d04040d0f0880301c032984803078424204449210035072000c020905040c000485c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 956421214 1250 956419964 956419969
    0xc010c18080703080f0c03040905060127170309270f0c0d0e1905011b0c0b04081312050d03061e1401030902060c0606011e14030c0405090f0a0f0b 64
    0x282d5100241100c140401c0030010175613100f044035038000200c1c0c200c0e1341d99907076800d9000117404201e40c0140820011080040201c0740c0940101d10410840c01140c034050800c98140382040c003c1414030f040f440b0500ca201100d880b00d0050b541648101602004619000824310340d0101000b0400c02c420603284050001741d01814040d1000c411051070041040d000355076190b458401a514242003100490381d03d01c05000043d07003c00c40181791070315080d0311640b81c8142134562082e6940b00510646981002034041045100a441c1c40348543c1a40c801050740c400c0c034418112280c080a0b00c00d0b4211104202d405901842074800400814061001035204000b042d0304045445c0728411080c2c6410501040680c071a6108680307045d4010455510303114000c1071290f071034004990340d41c0814220070103540043c2d9072000890f01e2441582d01c026000c00c4110740f4102580001c0e007040811082072001007007a5440e244110300c55440b00c0901905458012440e00a4034150310039078880c180f52080381c52094 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 956422464 1250 956421214 956421223
    0x507170f09280204090807240501050d083403030c020106060e1819061205070e0f040f02060706060303031e020a0905040b120d08070e040b0d0f15020c010c1808 70
    0x2141c04880c0003170714030454104101c052007800b800410340ba0301036000324200e1072030200a80100040e50340030040c980c2c8400902c110b840510501400181d8244000010101c50420b41c000c0a44008000c0d1880846222000030031030b1440c50442c042034075103512911840e82445103100900c25803501c81060300d210404600e01009817150804031208040000c0c074803211540c045d140d41582c1031000c1050b035607105c0a100c03101c072440c241141c00c0d005e007150001c0c403080e203289454014004440c50351340e80e13100c0e992031000304004450708980140741444100d000c10b040340314146c0254000e40300840c4828913201b1210340c03140c0300d96085015503c140810594540d000d06c01c4e01c1510002d40c3c002031281148030005480e5403440a4511161146040507000030303902110300c500540c0035031203c9400b40b803500100001e4421000040c0d41140015070b440d004604905540c045290050080c1e4408001c81041c4401341e9218625180003a9120000000903503400020800c1812412200366041810501c0c0e4070b032103 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 956423714 1250 956422464 956422543
    0x150705010b090f060402130b0a09050a050402031b1e1c0c0906200c03010c090303140313061e0504120e030303241908070f0503031207030507170f09 65
    0x510b60110700e01400402a9207c00094541210000d407030b922240002407512105006883c01803030500c80000300380c1802d0013035038040c200c1191101207218400348a407551342c005140d4000d076041d01c19014461030a08500828100c081d4048054000240340d81030000c0c1d52803220040100401d0803001c0111315440401f512404079180480d418800b08400312600e440000d0304900c0d0302d9403802e00c2c12241950842c510808583c4030b511070f0342e0041d525454100c613a003c219040c00001c0c5074103040f980043d19540c41032041c2144d0f004200030240461403400c084410448044680d942418001200c1c00d80245401009501c120b009501d54504080700040200d020303400e0b420458a548224102580c5400d0001300a1045106000784566504200c0342d840c90a803003641c080b0210124041002d08000c82128070ba90320002c02c10b2281e07286d0344000c07002020010700c004100624160300d03510180d081240e250042c40d510828560038104842d590307003044090044c91a1100151181d000030748030400c2e41400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 956424964 1250 956423714 956423719
    0x13142d010302030901060f0e04062a0e0109031b03050601151709030412030201151203020307030807120c0305190509070b0a2f0d08011a07060b150705010b090f06 71
    0x220fa44801d4040c2c1c3c050800c54000340000c5c0b00607480440c0d4580c00e5442c030391207240141c1b0240b09025801103d10701c0408000030000020480441c2d00060301c0c068819040d6800c0c041c9811040703a60399484001d4400c9900c031684100b00e5103448100184002003020034003420404100101c19040100c0103130151003412409803501041e000050030481090054078024071109001600700340d0189130007402001c07002400115403140d078070003140304031200c100b444442e03034550011494481c21f03490076a4203a00003000482001252400c2d01c4080c5404c6c0601244043c240d1008a242d040c8011041c11500a088a1503c1e80e0301e014104424500002641d6040b500c010f50388940d50745e2801c108a07061583e0800d2032424007500d8030421100034406100482c4c1c80001d609489160449080c00c60f4207e1007071242066400f003800503000407401c00c00051100b42e114410004143c4440e60228001c516058610280d5090100765941808ac00380243c0420308001c68183c021860210001180d040d005400d050 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 956426214 1250 956424964 956424967
    0x6070b0907051f02240a020903070b042309040503160302030c030a0905030c0315012705040809090f0f0f041e05060702070929030313142d010302 64
    0x1526800240704660260070041c01c0580701c403154110781c0802c0b09030448424010b100362840d01500c0d480220030509001c114145568850b15985d43d140b019420007080143e1502481c400001c2410050000300010a00002410040406408043d005586008009003c0d6035030b00200000200302000315040200c0320203555840d86424101240303103000352140010148030002d086c6000030b401410701d00c201da02c1242214591080d00007070644400412890740c81c4a00b9100060101d00da901081c207501d0000210400c200e0108203030f482c0309468040d10300b501c40b402c0018000c005800e0524042c0e500400c0ea010347c00441c140301d2003c3d44008070040580071040e0100020904100071078064004040002500400302045400c01a4840354190b5009001d849187e10026551445004502403010101103046440000022410030200d00c080802c0d0f143c041041045400f00984444501400340c02450b258181c2d130308801d218107254000e40950750704090300d200000d02414a8500355013a8130030728016 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 956427464 1250 956426214 956426221
    0xc052b1b2a0b030103083f0711070f09050c040e0a0f140a0606030b0f15070302030f0c060103120819090203010605030f0a060f1b03092d0203010c0e06070b 68
    0x1c5855145640100c00d03000000030002041c82503840142c01c0c4003400800410940840818481e00c1e03444815013001842d581c00050020b0080070300407981e02000500701380040141c84070f1400c3c24901c0c150000a40111001c1c814002c1c039001d031040d5170f03104942c0200c041c9001c2c02c0429010b90100c0c001d1003031421907280d05541040e19419005243c040f10b00c650318400c2418645000000380100780038a80c00030b031803c0c01113801841d00702540c4141502c003510418186000c004d00341c1403503200d10420f400b58070040200000203520b1500900028149401401240d41503150038030030340c2c252202080c10840040d05101e44685030f04681e11950301000320001d040903803480402d000d0006e03513110641c1801703802c0d00b000d0b00c01740215903901a18860b83c3e041205000104604044500031403086411808a07240820b1403070007036101c212040d02410b07542d0308ca17600844e001c0c03ea00ea212050b081c6482154006a411402c0074050400034124504100410906160108216004100014240d0a0090b020 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 956428714 1250 956427464 956427533
    0x230906030c15130b070c090c1b080703121b0503060d0b0405150901060e15031204140108060409030e1912030c120801080c2101060b0c060a05070c030c052b1b 69
    0x11728030081e0242710402040485003804101c80e0428102600803c0f50110550001a098070540e100100c00080d1520301c00400c0104680f40d4100400d200e40002c0c61208082c0498000705a0310300c502c2c0300da0000c2a00410012070021001000b07888003c041c0e0404001f4490700c5049440f0305d610080800c42c41d08101c0b80100000d14003080d000e2201040c0740006400302d00e42c0860940d921000a0070b0300c902d50642c1351642880b00310340d05002c02a000913821103031441d05103400030000041030690700c0c8600c40b081d202c851059000c0c112003402c4002c01c403101c405200b003041004800c0c01014050a0090456240000f0035407520b03420465548500c510641d11004481d80e0160040c1d51000e140c02002a03503201c44041e800d0307603c144040402881808006410036005003c0d841c82010555510b02c1b00020360f03a026140191005070454090142c551200711501160248140c0072501e424029030b94500c1a00c05443d008141c450503105203202480c2a010546004803400302074100c0408040d50903840c0b00c2c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 956429964 1250 956428714 956428727
    0xf05070c031205120406020a140f040e070c0c26030702091b0c0106260307030e01030519050f06040e0a02090c0307030e1f06230906030c15130b070c090c 67
    0x403082d030591310307400910090011640c040d203c82c1e60700782c4910009403c90035014203903003d5069054109101040b081c0724182310704d403400740c200704542070111920b00c09948080b135280098110510a81100c40758102000390341d5011400e03601030102440ca8895580c02051850350000c0c43d030000358220003400031000c59040d08039030860541030020440c15885200c0300c4110020810b00340d442400b04c280e110720290780030080760301050303040e121420403400703086c010f40c09402e000f042c0340100d0300100d0307440d4444030b064040e05104800301b503910251841c0c09000c11086030144000d4292a900062040b001038a0300011607420442083c0130540302d9407134402c00c034060701d003480d4411094000c000344180040c00441d001e0640c0d1200c0c1806100c8951240080c40e111040810300701c01c0c18240c480400b8440c10300c1c8098070380190018003540c0303103180c1020100e00d00613650b400901c045240000c058101d0307454010a030024040711055903151400301d880701450742d101401200c0340590380e80303480b070a40c0c0d01403007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 956431214 1250 956429964 956429977
    0x10c08090c0111120403050c130501240507060c020322080d08091006080f07141309030215100e0a0509030703180f180c0c050712060207061a010f05070c031205 70
    0x4c2c4e0b041d55a620f0340b410729100c0d1114250030b40241061014002011068090749040e1144180108003400342100d1000403840100d10b00c3c402d00904001080108a59014079060400740390029030381d0b074042134146504a4054800701c0032501c00303e8400d00201c5008580d0105003065403800c0959074581c003400e42c1c240241c441c03445481c0c42c90a60b001070b080e03601059420078140f4190a40c0c1d49030750345100720010151948192540324000c1e810803048403441d90701040183e4000d20480e01030080c4008400d40150003030700c405004d01c11418081091060410820754003c12000044c80b45081c1490031070740c1e9006050700101800140f10382900810b022003009070040c080d01803088a003c0c2e0703401c0180318500e181117220005030b06007600420220300801c03d400d2000d0307008005140c2140784c180255100000644201e540b88d40801a51300400c00c2400b03a20342c55549481151464085200090300038440c8580420901c070090006101080d00c42e450501280d0f0400390042129140450844841c441c04 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 956432464 1250 956431214 956431243
    0x40209040218030d0504121416090204180e030717070b0406021312021503100f0b0a08010f032117090c030c0d230708071403010c08090c0111 62
    0x10460a404455414032042d201e00e041c1d007942e40080c00c1c4001120284554000c01c00700425110000d00010380e10240d2507042d1004000382c5103100041c02040c1e104c0700c0280d0040c44080d40100c2e090150621081c81010302c0c8004080411803c400ca4070019201c0c000c09034098a01e105508003400d0042e00203080f24405d9a01c200500c0d06490585886e0f4001d400407914048030283d03140740840c0d0301c3c10458030030794001d4006007208500c854008050b107455000800d21010321280034000100445c2c44082000a0312810003103d45031501740a00500c6004160301140805c000c4100c2003022032201c0081507901d4001030038803012407481820a032169600356401a0306007175030318200f002c103110115002511042c110705491484213403408001c180d82445402800040204002114540204041c5c0a409080038151940395540e40849801d1100d940c0c0030007a00340b82c52101d00e1041c6000e1140c104021388030b00300a0401c2c200003180c643d89000003880f81d810310cc202000580740c81010400c842071244603 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 956433714 1250 956432464 956432467
    0x2040e0a1a06031e0a020301030f12020c10020f06090d14071a070c02041b020c0904060e03070b01030615031218051302070303060803071e030e0301050412080a0c1d0402090402 77
    0x1070340c03501c54410079400130342c1003026034011841c12041030080340c0c1260b400070985030a158194543c5802e1120075100342096119040c000c0c0b013143c0701d07040c0c03050b50008150040c00543c40c071500b00c01d090490040c4240d01503040050100303034444d0014140000e10b400d03a85165216140342c0f230004d0890b40100c402003440c11001c410000c403641d03c0b502c0340c45468402d0341c007444610362000c440180355a60001d68800340e04500e0031703807003c1d0038004401680b0500904000c2217040d031103c113050555103c080251410f05d807020042c0144001805024890303081c420090b44c005195480307544480c461010300e2800c200c008400b03c1c8c0c070300413a0b411403006890010180c903020084101031400070341c0954412000b0909280c80003c92600103c16a040560420701040d24a0805805403000c255040b0040701031140742d6503c0c0d0181e4500748075561003144a80320154a1080b414000313081100300410f62060b09040c0a22250882d41c00806501b4030200d082c1d1032501d021100001401a00405100a030030510 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 956434964 1250 956433714 956433721
    0x5060a06090329180f07050a180b0603090a021e0a0e0411130b0307050109051c14030f0315090402131805120d0b0603011410121404030e0402040e0a1a0603 68
    0x11604e0240d941c24940b10100d4000c00124110151980598400d00b944144250320402000c40c08500b138041c04054450b00081c52141030b80014843c1c1c005480c0308403030340e00c0010f0341011070501d02841010104c00788130548840340e10072300262a8444500582400001c0400800d00300014030b1419000000000d22442100001c44810310051400b035080030b209204040000425501404460040d1080a0710301050300700b20302c0c0c40c01c0520b00c628070103c86046e451b610581036950309001a04007000358003609035480c2492440c60354140109020548500851018080140d0380c5247c4251010f075041e41c042500d4110942d011041d000d940c80181441c06001e110400440c3c06000130480c048040c0b5042100c0713003450082c8a41c40c0000d000c1e40315003001d081c201c40800c1c50010a1946005001e02d00000d801e100c01c00000290380004004420750b02601702400109500005001c1a0003002d0720210709081c03910801e164101d40240c4415056591055111410640c80c5942c00c0100301c01342146030b0380e04 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 956436214 1250 956434964 956434981
    0x4030c080622030519181a0403120c021008090d11060f180d030501080f060417180406080d080105061602150409050c0c0706090f03240c020f0105060a06090329 70
    0x8400c0350061415071213081c0403c00e10306600d0200d1a005059621034106030271541ca070350140340d10455410070310140b02006001030f92000803a00ba040200c2c1d540078910f0501c1c40e0f94920340113100341c2d8030382800100303200c84154074000142d02d58088402d2403146880d44610b541003155100b20342100205010f030045440f08107800d5004141210861022110005003400d4580d0302e604d010b4400425001d090103205500c00011009030000240b508214051900c82c80c00143c204c032060381c0004031070303048401d9000c0e01640140200b801040292000f80c90201004040158150080e000a01c81c43c00c81041940b040848003c1d80d0140c0b202000030846400d0401000030150000014502c040c42580c01c049812403251003818121206650b000aa490660b40c9000b0030001070616a810725a948884410040340c84c0203c0d850841c40e9009048040f5101d4011400d507180200354038010354240c8401c0016030b901000b00c100310f80c0c100c15083d90300b00031100c0c4248400d002904090814020005000280 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 956437464 1250 956436214 956436227
    0x300f070c1b090e100c0c0308070318030c0605090105041130030702100906080c09041e0c030b011d04090f05061e01090509070b0c010b0a090204030c080622030519 71
    0x1080c01e103081343c2461485001c02404d41d881e044086001a201c00d0883c1d000038015450300e80c0004041c100882c40411040c4c5580d5002d0f00020140c0004d4442c039000c20170700c202c5210725504080810000d001030314081c0c43d1810881208c141c1240144c0d1110000d00c90002110106e01c0402406010f42428181030b240c02a0380303401450043c0d206d20f40c0c3c420000e0f180390007605010203e40498484000a503260a10801240c12615001d034006e0340710300d160040c0851081e0007018501e4404d00010300004002d000400300d400842c45141070201060650702500c0e011150303103001400c1100d010810030f0b1240f8208050310b11a1000070110701c500f0b01404054042c904c030541c45039024014000707040e0780e034408900c140c440503145445281c0040c2000c0c010418050020004102100c0001c03a41c00c403890003040441c01258404107200c0e502107000d10801004c54004002400c50a00a00080c100344101c0d003a001841c5c1d071200c0000c1045005042054012410b40e00a4030801c0302c29126480d40c100c000c2c011 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 956438714 1250 956437464 956437481
    0x2102060d0b04060b34060903030b030d11060a27050a170d05060904021f0509060406031e02072411041230080c0c03300f070c1b09 57
    0x22001d940c01039001c5e0308607401e03012a00d03401034811081d80690380d490320307401410140016020140c507140c10103559203042280d4200301e090b56036103a43d5544520710302818140040c011004403800c00d0180c100c2d40d01c04450403010700d4408411205100720503c1c00300d15010300c110006000d5001d4060300f2840004807005403a07040070100d002d0289a981d0020044440000c0302c0007584121120f0310501a180d07a18145230f1044024102107240c4500350001845540080d804440001e880c4c3c030502c84040c404a141c1c0005e0520508250309200c0c0c940e07100201c91a0f0f0600e210b2080c0c6c40640c4403090442103800c40b11f900104102d0b001c1e6584d40b1110070f40c84847d0b84000503144201a02400c000010440c0328601c447ca01004442500e0031055204564000024004038006c0c4401e0184041c540c006100a02c40d4500201000d420700c505d902c10890075a42005560f000003040300100042109031103401a40139405181120300e1100301d140810300c0301549035030507224500c580800318080580381d03c00b40780d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 956439964 1250 956438714 956438737
    0x10c23120d15051509030f062d0103081207090306110d230c0a0215010f03120f0210020904140108011e02040810150e07020d092102060d0b04060b 64
    0x56100d00c10030341032040c07500d115481c1c00c98182a1001603958000003e031a0081c00101511044080840c07d903107085ca01740d80d03481068402c5020140c417200c60300d090025070002480240441d624544802485009410444011290140001e00e46502c104032443c041d50b40030703004000d818446055226140c110764204245c00c1e01c0c054a59030080e0400d4503000c0011a0700010814a40e142030039407280303410582805095104820240c0c49480e00c52102d41c1c0a00708410104402510b541030040c0e04d048100031074000c1c0b18450540140b800d038081904141c00300409070169450401802042c0107100e102d0a443e142c0340303844001304072424103400c2201042c80043d0740c0c101d940141d9000700200d01c9507110382c142d0355000a26100000921350000415624400710104065598061070b0406500880742400103030440303200b034525590850b404201030151301d81a15401030051020116450090780080d216040101d1103d00914107908648030051025000780001590340d2112440354000340c04404 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 956441214 1250 956439964 956439971
    0x21210061505090a180902060d090b07170a2a0201050f0907050f1302040506030106020d02060705040509040b0901060810061d0609070c080f070317060f010c23120d 72
    0x40128800c0c2c050b18032400c0014604200c05140900b13061100c0400d610015020341c4642e10100582d40e500d0182c0400b41c80316001040824192421010365280103101d5070510000c01c02d213078040328400b100b0950142c500200050600301c0b0a031442c0c100209603400e0509015004814001030381e06402480c01040c100000c000c035034032401e011984550060150b96045a0143c4e42203d007881d0500703510300d0364184031200518081d00c0d01d0105505030310980203203015a10421405480350b80c10410903230b2045851030046e040508000004600c1007000e007010381951159404590006420361000f4020880e083c2210142d8034410410006442c003445154071840c401c540d8658080ba880480c0e52241c0c10003424217546941c0c022054500f144210390684000c076051080d8550654154000e050a9000f510b4454031510701000c91141060001e06c2a0302a01181d0000055a608031904007400d941c0580d180d007040c0680c18820000c3e40d100c00541030b0310b100d42d09001000f982c01c40c005121800c110007052 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 956442464 1250 956441214 956441249
    0x20702100e1e0411070c0e01050103060b180f10090e0c0301241206260f121803011103061f020c211506040612080306040902121006 58
    0x380c030358800803400d403034201c010803802200b00711412a82d140741440041c400503080b0744010400c001ca80014008a0310644a40c0d000c1c40b80c242101d0700d00c0d0045c01c09103010300c00e00d401d021806500340a860700d04050340c41c0c1041c1c0c4000507500c2030000300120402401070504002c50100c020030000040c4503030202c0d61609004140304c1505802104d040c0c5525005100c18619154206000f000030080780c1e808004030010340d0300b4040450b0213054000c010348803103c0d10805d6003a00049d10b020b010300e00c800e801c0d0700c41d0b0940c0b0801036011800743c900f900c0030035691b6114000780c10800c12500818006940c954079006441504000d01c4002d14001c940661302c040c0a40c25000480450b00111080040503a100e0034520324540341c80c800403404450001f50400200b01c40303001292400744400d44110300318004c04c0c100300c40f80c20284100c0300101160402a4000c01072a16042c20310311024085501403521303130f903104055485101d200341c1c50b20550703000c581d4080601c3c0d1540004280c00e00428250980c0c04080 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 956443714 1250 956442464 956442467
    0x60a08070e04051510031a0111072301140a020a080906090301060e010806060604120206031009290a0b0f07023d080403050a030504170409020903100c201f02070210 72
    0x1000c000c200e0310744030052044506001074864227000c0d07015002c03a200b8040c0110b900080c41c005100001307a04104590750f1a07601c000034159500391311040040150600000c0556540010501d000303d0300104000c1e0365800d50300120b109071150003c9650158200140010382000760400c1074100d07030a00b416215580c039103600b040707041d01c1288035001d0b03840c503070000380c0002d07180000042d40c00c44451740100405035942c903a00d0f400c0e02c00702c2d0b50f01c10704d0056003c40120f040c80b60241d0150410070031a800118030f170030300020b0307543c070302480c0444041c03004c01040395411500c4181080711580c20380000340100040600c451000d480c03040b060f0f500410030004480101c11b0040d10300c6801240c0c10b89481d800c200c1a10411002850000e00503070301005d007041c400780085c0c000070007400940b00321000581d50b60018802d09d843c1aa41c010700003241807401000f001e029034030110700910644103000f60040c1c0c0b0001c61703105240040d04d4001c06001145004111450308840d030003000321074801d030382c80d940800410a0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 956444964 1250 956443714 956443721
    0x12060f08010b04021c020c0307020a09140a200f04030204060e1e010b090d0c0302100c030201060806060a0317071704030b0906061012060b030106020706110a02060a08070e0405151003 80
    0x2012448110045d05208080881c0e0040c00024107004200d0781040c000e034000400a00180d40852111590b4210402683c0340ca02a140c0e401a0103c00034040c40c441200d40d800c07480c40c001c45c845003075480401e458040390985011035000b10340051003030004e5a261203c5000c081415104d45244806501000c003012082d065079504880b000140141400c030700f58140003060001c3c04c03044802080b42c10f00400141d41c1c40101c080e074401ca0b9558002c07003924a160280c05c4403403d4004400641c0301070f041111941e50b06121034107a80c1c1c030402003508031848803031034081401161130040c4401c94108818103064140d002074002c903405400c1e941090b0f03e80c11880383d00d80400743e41442d00804001050040300c0d004002026001003811000074034140e40d010f00d0852508280c02450040e041202d007002155402983c0c4200c45000b800940508c80c425030002e4203d06c204103e0304288072030b2000040026000300c3d1545501c2c8400740007441103290510304140c0c482619a031031072040b050501c036151800d21920 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 956446214 1250 956444964 956444977
    0x20d0c03050409050601030207120801060e191208071e060b0f010c030e0a12080c0609070806065a010918020f0d02130e0c0a030c12060f08010b0402 65
    0x4072114075107424039110707802500000f00114141502006442c000509043c2505550340195035400004c1d410440e001f130200030a0840e4902c540c002c0c0c80705200d04611100d40e58100c6095220711105d4042e0342c50100000e0041c50300140014400000910100100e44800381c00507100c0d104c10001000d8040030042024014000c4500041e005040613001074003883d0750a1013018010f007403911180da109070742e05480e10041c2c401c0325580804210840d41d1002005640c0c1c000b003104014000351070400e64030660b41c1a004011900c500701c042041102c03000781d602032900300146519480403860b91582c588044000f6007005c038031103a50500a81410010003a002d01048105035900480700349024000c03201a40044c16004066908100e8102031842c088004c10400000301e001684aa820101300301900300e40b41c0c00203000d40c105000308030194200e0350032904494040d040014a03d00030fa20100e40c1c01307213648280358409181890103d20f40c48586914412a104c040c001d00110301c2d18401d00041c0d00407130 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 956447464 1250 956446214 956446217
    0x20a0c090203090c09150a060c1509200619021c023c150a05060303070305070b070c0c1205250303050c100510051315060e0a121101020d0c03 62
    0x701108050f20b082d0702e5050700f19100300381c43c3c4040c1c0745407400500070340896400708c00403501c1840140204800100600315480d41e0341010880481107890320484030b4881d00f248000c10300845100380352303a501c1c0810703150001c1074184000c0d01002d48030006035482c400c0110852402c0048540c42014038400501105c1035016000c45510b00485284d2010815a00701d02c1030120240b02406030036201000c0151641003007076802d030b0940d40c0c2004030081c403c80d0000790542d402a042000610302194004040350140e507846042640585d90b481811151506140f80081640a00d45800070310113207242401e0410134040d030b0940e0300220140d69401c0c4c4080e41401c0580a0f94107450f410004a805403020384600340c41c42e81a11035101c507081012048520450740c01c0710f41c0d06882024801818040202400c00103460005c010110040c442101402240c0c4111001c010200c09003850a031541040403001302941c00d465050711500b8903251290a0346064545d0051088480140c00f1920841041c00c0c0103805 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 956448714 1250 956447464 956447473
    0xa0e0124050d030306081b1305010806041509020a03050d0f0207030f02150d050a06030c050102010506300a0c03051204120602130b0a021614030613110d03020a0c09020309 75
    0x9007400d200ca0b08000032800c1e010300d44c0c3c0c4d800000d00c00000b4448000210000c1440807072a14046003080955050306000907006d91500005003c8014006942da400c1904481d00243c0c5200d40440385000c0d00003200e000750403030b071809000020881c0000c4c61840102170307901c8541903000c48070070881e0394030780500c0040c099120400101c00035084c0004070f004038480e9004007924100c2447c0c0003100f511000d4071000b896590740c02c410003c2c0107a205070706010304003d1009103c14200b07540010101c40c0190040810b070f800010f111200c0d42c03c5101e900e0507a2152509494400000e42000880c00405200aaa0398004c014121030100680c0041300c007034904031412410b0446d696100d10009412440c82d43c3e0700c2c01427071080411204000342c00791455501a034000c09035110340040c0b10208103c2540600d81202c89018484010f82c0e011520720f5001203190b1100240c58164200003529560b00c1100a402005a40212062550105802039154000c00034122020360f9050301000b288421144441644c12 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 956449964 1250 956448714 956448719
    0x10b0109050405040204140408120a0c0518060408010603060b0a121707060b0d20010f0e0d11061909240804020a230901050a0f1e0e0a0e0124 62
    0x2c103684443d8125001030800100c20240481c903104880050741d0030b071100c45001c03803048a002c290300101580002500d100b4000c0d50342c1100041e02030f0041c2181030514011182c99211103485400a46005000310402403000d05d640b0300b00040140828030a49010707005154020506401c241e41d0695480d81c0000154000355209a4000c50354004007011141140c031074007041096625100c07503e6031640074039004a032419050f001001800e14130840076041c000701100580340b0641042809255040540e07000207020410310386003152040358110140e00407808502d081c20381c800400345281000b002c1c1c8914403004c1c2c44030f511844c0740800d142091220480f281080558034071404030107401604c00303030402ca4115110800b80380b0640d02c00b0200801d55800705141c400b1454440c1105004080c20340d0710b90029400d002d150b81008500740540d024201c0c03100c4900d45044018503d52004017030040c144c40c5282450904180a012007a0650304190b013445110100200e1040000171400c103101c0c0d860000c2403 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 956451214 1250 956449964 956449969
    0x90a080d140d09020901090e010b09150114091003060614090f061b0d021011040f030305090d170711180105010e0324071107060206150f120c040509010b010905 70
    0x50110030b01d4215140c8038410140181c5403081940d000c0c001800700405c440e4100e10000d42102d41c1c0c012424829802a800d200c003142c2c1200014040c81c80c28a0a024000c00d41d81c0d0111081c0301d07000d40c41d900030380192890b0070031650541c80070043c0ca14070b688600450200c100b0290481c00703001c07551540056070f00b004000602d0900011710248001e4002e10b415500382c1075406041c04001c21201e00540c00142100e290710303000c2e1042c00b1040c00c108180318200390610b0406402c03d015804000c060010024205000340e07502c070107080c8440c4e444035411a01072012200c1044980203400104e0340d0107100080c0c1c01680c40c2400c0c0d00c032541d09691500d40e40a80ca804011650b40c464a1082a014003a07031340002d2044c0746503052800310300c0c10039040800c0c0d0f040c005270040c403025003011002403d0700300321824071035954046070140d0001127400092042a601c003000424814a00d4803165108010504107187d919000c40d01d041401e80c111010030440e6181c850990a032022580c100c0e0000d814104180300c1c92 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 956452464 1250 956451214 956451217
    0x809030f090f0402031512070e0f070318121d060702010305041b03210804080406030e0c18190c020a06050c0702090c19030207171c020f090a080d14 65
    0xa201c014405540d00203400040740407079105480a40e0b81a031500d080c90b41c01e040000ca0030211222900062071100c1ca042500a010711001d00032000b98070710200480c15951094101e081070b80c20341300b01120114001c0c944400c1d10351003440703590041000e0744a0205110302d031452040c100c000c0038202030710703000f441c0c0d0045008210003041118201e00c00c0b881000c9025071400310312b01840c418040b8400c80740703084820801b41c040314080c803010044803108020000d030010044d90101c1c2c605050100d4984066400c1d581042140300c451500b12445190107050209040c4106000d031103080d00c8510912403e0703440c84141c4a128207900003591101e480b400004080d03510040c1c0c00915a0780c20b03400c00f03031640e0011ba508401130f03440b000e80e00b00200740035641e80038101034040c546100b410110314005140d540d1001040d41c45031004d4041e03002007410040405129400c40d01a0302850085549209001e089180c54001c4042c0c0c2e40500405280030a46a5000a40303070001000c546442c400344990012040d00c5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 956453714 1250 956452464 956452477
    0x601030f1211010e0304090b030a080912030d29011814040204180905061810090f02091819150510090e010f23010b130f030b10060809030f 61
    0x4000c141d0b540448607403400e04c80c1e4182c0410310009999540c1c50030300500281c4142150b820b01c42c4c2c002002c0800080e14030021507007003001c240d4008070718003c020000c0707045010b0124034003242800c19411440410340044440011002d00d0458420350951500465165946422000030350480386400d201c40e200150b5505001c82000b000585000c1e2240c400e141c0410f203604584144548440100040000620074103900000188030035500c03030720780c980096030356546118152030240c0c1c0e1a0b1100903c00f4150301e0b102900d4000c0c06021750b40c1403228229000c1408125020b40900995080c0e5a03080c8031580e500342d44a411905070801040d107803000d00300405029040100c29202c3c1c01c00092450464000d0003415002c000000070b414244210081c240e0304000c500d0a003000e991400f941881c1d01211903541036404010302103441d000320503030b602a005950b40001409040e20500007081041010a161164151003101c0f80c1d100d81c4c030326065031400c005851a8060390814484008001d05072009400c9 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 956454964 1250 956453714 956453717
    0x91d010e070c02030c091b07051005091603060b01300e030c1507020c030618060c0f16030513032001111216080a030f0e030301050a12060608071508090601030f12 71
    0x200c0042665002c1d180d03440410221703501d8016282000ac010f8040c0b2400750b12022101c003420440070f652a41d488048200e0100a0009a80f4071525580340d10403c000e882c0f1001c0c241d503090b288051400502000d82c0302030b00a401c55814000e1a032408180070094031030000310701c4010040e10000c0321404031541c0f0b00800d20000c600c100018400c440d6401c00402d40201d4024950700080000c1c120981c0c1044c8009021515402d0308202e0249484c41650031243d01c3c5003c158502207008161800b1034443c0304101001c5040b030012140803040c40a116207050205543c011400996a074200055a007003c407007134880665044001da0000100c03109004180d550091855007076455030a0303440f410076030400c44101000968940c100d08030031b40f03113110700d500b904070f600300071030a541c50f150009900d090a80070303488841401217403400401115400c0781014010300c000703441010344c68100f02c81c005021010701c000080d0300704010441003500030680074180c0e600110701401044c00d546030b000c00481c649200303d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 956456214 1250 956454964 956454991
    0xf1206050439210b032505010c0b220c080c0102101505010c0318170f0a05030a0e06040b030408070314030103030206040f02030a1202030c010e0c1e01091d010e070c02030c09 76
    0xc134550707024014007102d805018015180e0b55101814050004029003165052155080291002c41d45121070070343e120301e404d4011500300c0c0e400014404041100c540040c00104a05400300c0c600a011946a0b10581e00b81d00b251015090300821f941030302c201120303481031166051010700c440c0d4400c50350b06440f039001e42041076400070900b114440c00d400640c000019110301882041e0400010f000f10450141100000c00c420b028030703183c050b120700c25500441d09002242c48074800c00e40342d4200390340c000e100903141107450345820f0619018640c006041180002c10b4202101e030415007401c150384c10b0381e070180d00524003a81c5664666441059503c801d85c0d1610924a50000040308408000301c1ca10f800d5015640702c0b2000550282076903410440d40ba02500080108101e40d00c980a2204418030f644005035104210b200068405c0c0010350000100c480341e0b1443c125140c1e1102c06094103e0350316500e070240c95550074404403900c1407842d000a40c180c0012550003003620b4014011500000701c4400705 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 956457464 1250 956456214 956456231
    0x305090604170304060f03020a020d0807210203010608160c020f0d02130b010210090b06132c1b0d060b0a0b0c0105090606010903030f120605043921 65
    0xc038614941c810b0501ea1a4030000b028440654084a5400081d801d400c0540c28050880f001075290b880b030110396010015240300103504244141052090074005c10300380c035426440360014001030750090085c00d01044010002c5442d40e000710f09138642079001c556176410701013029820803072100c000030302c840d500c0f1982d0088034000d40d8581c541007a103081c0b401c1001071065580c10000e4100140c00428031940c5280c00700020201d0000c640165104104407560186101c0060255005109044100d4a80e0032220410350b0805d094007012544161008200d0b00c1c1c1c0d070700b5401440450b141c00e443c002d8000010309003002c001200d54000814000c0020302001070302c0e40720302d42c10341990070001d41098603a4491041c40440710003400000d82211003803900b03c147c1421902c0c007804650b01c2441340002c01800074410303500007107907a0108019150091091000c28441c0b4040500010020007a0142d9070980309004040321810038014a4400d00b5203500303050842c041c541c0685030107030301d0548a8868840c40320 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 956458714 1250 956457464 956457479
    0x1030b071e0206040203010b040e0c010c021f180504051b09030a140d0305010b21100801060611250501050708130306020304050f0d14090d1703180601050d0305090604 73
    0x1079501c049540c001c0802c0e28284c0101802d40c0c40007800f2600643c60400703a9081c0f00350102c3c9984200070203081c602101241803001c24030b803401ca0184c0c080419028580411072560084003040c515010803080c0c1070a5849400300002c8030f40030380d900b40040000380708100301c10003480c01500c62444002c0c2a5181038146441d40d00c4404c03010310200030b49810101c071855134190503105007800340401e20001401d1181090010440030007041c80c2981d20f01d444400960414800c200070300c05440c000c0024045140e0300e110282941075040e91290380e500602030358801c0a85140e1041c4581d40400d500d841005180030010f42d00ca40c420201a2845502040030380b048094104c10310340107502c10710340141c0e00d01e4a030030018108038904484e10300c6500f0030192440342aa22050265684502400d4503070348031282d10000d902240115401481045403c84030034002003000043c51142c0d4100c0700f1180c01c002c0c040070644e1920000d0003090b900c07119096110b0046440351004c1c083c21304002c0d0580c0d01d803d45035040d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 956459964 1250 956458714 956458757
    0x90626010308030702070801020c0604320109022b0213090b0112050f030f120c04120b040203010b030a021f021204030c0612020f070f03030f0c03050907050d0b01030b07 74
    0x2a940b8030000018400b131150704214000040c50071000850030115024416912400c01400243c9240e11216002c0c0c440c040d220008958110b07800b400c1e00201c44d800c20300c140a05440c900c1a4400c803100300360030385807691041c0c0d040020740c1c0b20224001c50862603400c00070000b05030382c41c1c20742465540d9802170026001c92881806801c81c65410107850350f462411f035140c003220340c1c09140745400c1071120740026000c2c6030070307a8a4440c51000c140c15654601850b84900d00480d4000d039802030340c1807214000e0110400540e40100e000b903000b44010302403002419941d070300412001b504444005800380314400c1c085258501c08005206036085050302031504002500144c02c10f9464070722220040001e03d400581014407405504415404c1a0b903901c40d1206901983d400940f00440c142ca80b0700c00c242c800d078404000010700c48020804010b018030f00500410045030003c0340c03071183d68000304403441c0410158030103550141090404e68250340d01c10956403805420b020034004100d8030580a51b55020 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 956461214 1250 956459964 956459969
    0x6051809150a1403210d05061909050f09011505060304050f062e3b10050a0902040b0703050c3901080106020318011b060b090c030709062601 62
    0x99502c008500f11200301828220a20342007078030000814881510505010b099541d02501e0380c000141c69643c0d080030a5600d004044504007070010200c2c0410380c03408039800180a00c80011117000c05580300a8001c2c00c0380c1d000400002c00710010b14003008503107407076001580e00601c114160744880c1201c400c0d5519281c4259400f84c011581d1242480016040e2640c0403007001000040b2402c1d10702d808040081525085200e48000840e641d400c9000700c0014500c11040c0782e412452000d61828060b040e110311307854010940f0404059030001013040f20390095501383c8814001c40b528000b0641d500341d0741513205401140c0c140c012840074100c0c10360319502e10040c00451040d03501100c80e090040070702c1d404501c4400c906000c07030740d00148840d5900000780c03191000c8842480c4a21204080181e60300f28000707189464818668001701c08200350ba4000c0c20a5000a03101e8144540368801d290360700b4001251004001484184d00300003ca00c2120801c5503030030310040205800200510001640c0803d8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 956462464 1250 956461214 956461229
    0x6061e060a051210120b0603030c0619060e04020612040203100c020d0806010f0f2a0c030c06050a051909080303040308150a062001060f170706051809150a 68
    0x2c1820420f00011400859100c414640309040703440c14a0714026128030300d040e0143c00044004002512920204120b5060048400c01c0b21100d18103902c01c0c0311040d40e0b00b2255003006051070300003e000710030008620301461b4001c10090400510013511225500001e10aa03171600c113140c3d044d0b500021a124000543c802036018103802044840702509c2800094005030400841103420044207500a050340ca00201c0381c5031031072000610386500700d100c03c022005846002002e0200d0070030071006900d0442228801d0810320100d03a59800c0507240750103500741c03100c0464420041d408080000391400c0c46100f2040c01c1030030303840e078503840c0d02c92460300100c50881c08034159074180b2a9003903902100f8074003400202c03051802c4d9400c20341c000782070240c04241c0c250046010304454140403000c0d00300c60050120350452407030345a910981c405a45445c0c800b0708020b03014512010848a100e9402c80340340082d00082c6941c003a8140307080c010090303c01000c0c04241c803151002d03441940e4408c0340210082454 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 956463714 1250 956462464 956462467
    0xc1e09090105060414071d2403180115060507050a0606230f0d1b0b0307080106030e0106061e140c0a1a15091008010609020406031b0206061e060a05 65
    0xf0009200c00c540c03000d01e503461000d40741c10420500947c4401c2030200074521441036841400c50310003003020000804020f4280c0c143d942d451441d0701d542203000c1d520514188200d0902058003c0c40741c0d0895602c2d444c0d461380f00c0b10600d801d0010398020310013416080e209504403038015281c0e45405c021190150848e0075240d41901001d140305e07402d501001d2501c1c208071440910070707200ca0001030100c29240401003041d00c05140f040101101200550020f08500f03500382e03664a048000144250400d005c0c0d1800b00e4600950f0014402e030501c20602911403e80b10540100701d00c10340036103201e039014001c00804c0340c00442c0e0480c1003c480e001d0440500001e00900e04018546000e052500c101805030381d201d080042004141070720044030072203a0600340c516079155219862040c90070380d00703074200341010742c2891000104641d00c0c0d8000d1041b980580d81c20011218814480c80d8141032040210005030301200c0410b030305262180b03100ca0030101094600141098400108645421404420020420 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 956464964 1250 956463714 956463721
    0x30a0b1807121112061305150702150a090c271d240604090507170705041406180a090606080604030e12150a111810020f0c1e09090105 59
    0x1510050700c03da40d044a102d000d07150304212041c2d550000802c3c55400090032015841800820b000800041214114079412450140740203541c1e1112175216002c04100c0f030000030400c80c400d00c241c0000d00d038032038000181c081c50140b1400400070709403c0581200c0288421100e41e540d24414901a001304a00c04901d9008a00340039080c4014400d580e2132908501f11103243c03489900410a910a50071a00000e140f02e01d401c2c41894907071903030406888100c510001d50806040003c0c00d40440740c08440610030700c19060214001c9280554480c0c2c1c0240d040b110102ca8000c2048a50b82d00c401d4800000070340f49066100c1c402034540c19440781d01c41d0381101e42404181030307020066a80200069626001580a101440c0c1c0d03a0010344510070180d90443c0c01280c040713000c0303070441703221001100f11054031494810a1601400c02c0500518407440c1c0351050801e0301070011962000f4204000041c0c07801500c004144454107804091a4100043c20114461641c2d104242940a1300c60040001003500d03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 956466214 1250 956464964 956464973
    0x9120317272b1407050309060a030614040b0108071101181b060206010f0b03090a0804150e0f1e0319030f03051f091509060b070611040302030a0b180712 67
    0x548509642c000450b0b4144010495004010340019a18810880d9903e850505010b8103500500c0c1107076500c031340005140000d00c0d90582044090303a101307040440c0000c0d05402004102d54000c1c52260108503c200080c3c0c00303500541100f01880709540010030800850200482140103580d4102c603d00c21000c083c070f00c4404032360340303450140801d070000f030450707504021185000720103501c01c1109005000000840c064414049108141e078001c0010340c0329503d03080034010580d40800038a000031041c4e01000c0861500d21629200140d025008154500f80e1001d50400c41c403100203100e805105921075880c030300c4085650500d2a50003982d80d074000600c07414004042c0c0b4005010305119860305840b003009001c4661110084074461200060001703221314804000c4d000356840340030010300e041c1000690041c090004c0121511607035041200e05e00c4030140301070340d004a010282d019488585100300046102c5548c84d0040c40c00d43c1c2680c403d44003400c0c41c519061094101025800d850a001800c01 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 956467464 1250 956466214 956466253
    0x609060b0703081803040b0a020c03010507030609180213020a0212120f07080115110c030706021b0603090303060904080d1a010f110d05160203120a0912031727 70
    0x1c04504d400c420742094022820381e49004501030350b00400000111f25170801c6c020050b698500380b001c0c0080c0070f94075201c400900286910700c9901b6889007480107090500c41c4005035078002c19801030400c035001d1004e00307541e4001c1d044030482c14294402c0481c00c1c480b85004001425404449000703032401c5142c503c0c83c80d0b0482c18090492741c00d000d40f400040c0003850310007440d01210b852525100c03074041d0720030209514200c004039005415001d5010040303070701540803401c00200303910800601444100501402603074403040352f0a4005400610100300c040c81d00c4508140c00070300400c0d0307260400c00e080e010b0808841c00140c0712190400c0c076120128865803c0821083c0c24034090600001c8481541001ea8903500500401020002d0020350300c01000050802c5101c09030300030781100c01140035641040c04d40d900c00b40c031103004100d403200000b401c040c0012041d022a64942d0302c2c040100d000c0312010080120150424075541202454240441200c2e104684001107403c01082003c3c480c0b030b48101e4a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 956468714 1250 956467464 956467471
    0x608010908181c1203110d0509121809040521090901050f060a0f110706390f110d08030406050c04051507020303120c0301240804080c010609060b070308 67
    0x3851000000f154a2882d00480c1c180307042d00501c440d011103400304811030003481d070302803040030014020580c2c900384901648140e1080c40440200d4070004076a0060340d03414082d2030b010f207280b0f00709541030254500b8110b02d0150032504c102c08a44c1100c1c50311158100c09d502c1000c0b200310a24001c82e5090551078181c40c0c1500400c1c003a5540847e44030248007044040c891076080c0001d0007000000c00511521a02d1b680425410f18020b488595403101c0006010031440d030b0100500d004c201540780e8600311780595040300c000d0109803075840314078290340d166031010010b8410307111f0900c1e81c2c40340300b6981c076141c82c0349600c1c03481800400d40d00e1629291080403200c3c040c24038200800140400c0c44140ca6421144601d8500b0220541c0c40300b1070340c40082d103075100b9000e409980c0c07074050081c80301c03020228000e50f068809900b40800c4c440c0101305018400c03000c8080035400240c1003000f08000c95460740042c480b07901d40e140041501605e07440d814050341e51507805862540000038400d014035904c080003640 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 956469964 1250 956468714 956468719
    0x50d09060f0e310b040e06090a03140702060a0f02060a06050a06111903080601140f030105040b04020d0e16210b0601091d10060f0f050d060801090818 66
    0x703414081800041c001001088010700a030303005100b4902c03e2041a101c030000d550000311610030410200c5500000d000c4010885020320300f41a00c150f42004049885441441c81750300615010702103450444540c0701940c9d10600c00b0504101d01005620390000a04200d074550312090140494060009d02c1c2c0280146403040092034540c051095550f0b1080d02c900721075140c601101c0140000d202c16040c140c4042241c80283c00440c20030b401c040d041083c0750312825090322098011080300d060b1030f0482c410300c42041e4002c1410401442945403a42c84440001c001810060609201090340030441e0b00394044080c0c00d030b00000814400c200c0003906607001d008004050f10540a80281003c28010765003001041704020400182c3d060340300300000390003406021901542c048031a801c1802c2031400741c3e210710100840e02404a510390080404500001c019034961402c02268842110280c006c0040311140c00c0d20388400044482c1c0c00d00a095065000c3e00e00366903620442000755510300e131190301913030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 956471214 1250 956469964 956469977
    0x6070201020a030e031216030f0c1505040312090312060501090f030b06060906030a05071805011d010224150a081002160b040506092a04091e050d0906 66
    0x100180d90100302e0000003030703042c1040e80f94220900c0c00603080820389400051854004aa010b6046420b406200e5006009403035010903500b510004441210515401822002c1d00d540c3c00100300d1003e40c0300641c0903009180050790340d4881c246640c180d070b4070710701c040c6c001038044400c0ba5400c06191140c0d00040009081003c0624035000d007240c2c50002c14440907042000580024800e81ca80c001110311016000308515602c1c68565003240081c0025110384000800c0207102c9880084415007450a4074070586498074601c0105180d900300300009400e80741180103a8400c1e0302101e1185141200046404040c4180fa02e00300c005059800c803400d81031403089a040504200c11103000c0307110314072104c05460160b41ca240001d000c200e5182c180b6001440705005038200b0003446000328442d4007070810201900d0072a100b0440a030403c0b8940c10390140040706040001e80d0a10701540100401441418115003400c0b00c0040c00b50611101c0b8000c1c0c80e140c001034500b111a0354414054405400360741400e1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 956472464 1250 956471214 956471227
    0x3070c151b1815090303080a0b062101050a050604092c250f050d03050f0d020912060c0a1116080f07080723010509210d031b180e0906011406 62
    0x61404d06035200240611140138003103807180c03001da00b0111502030007501c880c1e40c401ba500b41c3c2103588088521000c0d0bc070078102c00041820f05e442640142206c200134813450620781000c0000c8001d06119030055041c00c880c129400c41000409010745807209550080d0260b10115003406168540703085070451650030102c01400550607241d00e201c2910010b075001140320545140544080c490091012030441c40450252082001600203206081059a50031800c080c0340c130240b995080300340c4500c0300c0c003d014852035038050f20a43c80480c240004d038044404080008040700d10300a02500822600d811441ca09a4000004c202d1b4a0007014000010010a8549600410300da05001e5811518000c0e003e40b80d1016807040081d94102c500c000e00110b4000ca03010594070141a1408007101c8502034843e115032460300912a4006821190034030380c2c082c03036410320121844400c10301607614002c0d00b6017000c900903010511140c49100b82c1e4000303084a50401081c209801c08102840d0721500b4100100e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 956473714 1250 956472464 956472467
    0x1140f0609220c02150a380f040903020d180506040902191b1203020c0d030e010c110307060f020f030a1406041a01030e0c100203130501020303070c151b1815 69
    0x1080e50107842032000050001c0c11007035400e07140041004a0f25240d9075081d1f100100759030691210703c0c019089a04612800c40701091000b962020b000c09009600581c209580e014003900d8001804105010010040c81e1200002034168116810010481d980410b104d4004004010320b103d01c1c950758248241111540203101d05107000d03010005002c4684c0d51141110f85010350103543c0210318400c03e4618502030303618010010000c00310b0b409001d60038000d00c5a02e0303c0c01018402090541400503514000d102d848210140036100c0303d03042070076403c01207444910240b03005580071711042440482e4140740218000070b1810083d0441c0e1280c2c0c03a21003101c50f0380a13060084031032240d082c00c0c0400c40d460302c2014a801c2c042c0c0c100e100c07608554454200b84041d0303030107c000e1000905810f460610a03468100480c0e80e800308840d0407022074540090344012500903821480a0200b1003000f10301810300032206442042c030003c514010030120042404000a5203c1c40d9024040500b110640c01951100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 956474820 1106 956473714 956473753
    0x40605090607050a0909051807030b180705060a0813050105070216090e0729040308040e131709191508010e01140f0609220c02 56
    0x150b442402002a03464060150b528040f819091000d583d0080070060400d80b0818440d03d00c4043e080c1c41000b01001941c400c9144014074204802c007050344c045250528400c5800102051040d9140c62080d104078070001d250007080364030344c5291400e605900c500040c180d0b500340010080582d40008550741d02c4650030840402a0765101c070490219441004040680c0d045918100312407501d020103150810b01841202c402801d1203441c00c041640113078000c0300c4821340454104800c01c0c41880c040d0303210301200c0201440350131640e01d1203005003070b50588006280002c6509269501c0f030501d00c400198120f03d10144203501c8421003451503000366041c1d80015070f100000b250700b03800301044604a40f01100310004805543c010410705540b00f9684541100007407042e8011507980040c04600e1072507804001e0202d075103240c158070513154040700e031800303543c40000e2103c1c41c050340b1031 = true := by decide +kernel

theorem cover : BRFrame.Cov 956294964 956474820 := by
  have h0 := BRFrame.cov_init 956294964
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956294964 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 956294964 ≤ n) (h2 : n < 956474820) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
