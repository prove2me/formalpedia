-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1564
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:35:58.543985+00:00
-- url     : https://prove2.me/submissions/00dc3f54-faf6-485f-ae53-7896e6b4b150

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 281115107 ≤ n < 281294964 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 281116357 1250 281115107 281115113
    0x1080606180a230702010b090a05060d02011209170c0d0f0c0201120902041a180405030919050d0b1504050c0409020708040902040b04080d11030d23040813091109010813 74
    0x1510b903201300210341c00802d1811400f01030148002d0040d100131405814401081040c0e16800d039000041c1d0350a2130300c40c020606c00d01d101c00003003100210051151991012504a544010020b007141c00003c0c0207866440c01e2a410555001d0150002c5d03038040755401e00e82001643c081c05203942044c001010100d0184515400074044982203500d4145010500405c90503d041581c1440b0540003100544403190800da140c55507607000c2c9840350761143c82020260403220320000103140040030301030613071a941c90040c50140d040c4401181d5104c000c0c1d9800400c52410315017800b48601452890203184d00c2c02d410642d049020307500c81d020542e001e030410400012601d09920040c8010402c88150710f850b5030400d0b0301581801d200841c890100184614245010316011084a20390b0450030340c00108007207510207014440c25030620034005040e2840421083c001483e0003400603012640703a45414a45408188007110300515201c1079644003444204d540e5401703035001070340025401010713400d40307901d0350f03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 281117607 1250 281116357 281116421
    0x6060a030f0201050c120307021603080405060f0d060801021b1c0305070e03060a060e0903070c0e060d02040c020705010305070c030228020310020a1b02030a060504110d030801080606180a 82
    0x6c1d0100c045081c0010400540030390602250300c6040c1d42c003010172400c926589079800c07140210b0046070310906000a101412240660864600c400d44503000e011299440000900030340202448458000309580c100d80204008070326400746480ba9a81702c0400405a40c0490003070100904802c01e1000e9051603001c0ea40d420004548511810000451030300d0800392007a01d43d00c009040508503600901414001407101c1001d1030070f85018119803202c51b5103e600244001944041c069000b52400e44a547c40c2a800300c1d40c1816244281c8013403115456880c8101d4000f0107954010300143c0045071120048031186803914441403201b03200044500c1e02c2d0300080d05100d60454144025540028010481500201082d104030320380414858004e105401094aa00e0244802840c19545100040400442206000d914400900581d00448051501070325071a802e00440086205010001e01a0320f000d0300c00a100c0b02e200c002d994401e88031043e001000d850301401035a07a511034002c607220910400 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 281118857 1250 281117607 281117623
    0xa1101200319020307081f0906090f0c020c0f0105070501093302070c09090302100e031305030109121d04050406061401020d05030c07020a030f11090906060a030f0201050c 75
    0xc1016540c90801040311800581e0b100d46500040e030050003007007000d54018181c20f80c40016007030041c00c07240e146400004241c00b41e800462040303143c00404200341d00c05a012400300710071380c141080301d640e8400b010b030f176100386020549a1180141e20103041c25445003006c0c054542c40740c0008500d80026550340750401c17070391400072100312620b0004040c43c8007415005040d5415503171400c514181894550004d410003e00070840019102c541c003d080620800000c0e0120704030307001c10041c00e01401c00761a141d41c09208088c5030a45001350200e614076061003500d10f15a40041e07080c0901c60402c2041d105245081d020017210000d82d6104c0b88642c80764003c0c503104520402c40012558180024001d28400c6640310504540c0408401081150010110b03034021000f40103440c1c58000910010341900a1900010800191001c2d517400300917000039141c1491074222000d408a03034401c600241c1d1910129440ca9100e05810410008a90050404d0500c14010b150183c42e100814980794a0031000e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 281120107 1250 281118857 281118911
    0xd0b0a0e1305061308041502030c070f052404030b13080307020120070218090106080709020a081b07020913200f0301020a050405060d090f050a0201031508030a1101 72
    0x14200300c1070400c0303402d0040e19400031149204995800b60340d2548622402940155002c025022002028a500030819502c0c0c0a108004441b545525580740c031031031800602c51540151090b20002039486100c0c440d019001c20000d00407410280f96880b0000b0106c1d028081092981180544001040c03804000318820b00c490f40012031071031111f020102d02002032015044546500340603440c0103a0307030580a50003000c050310011280707444e00c0c0c80c03403801000e0643c000d04840c8550000010601c5841d005040781e260300f916119016035076042d03020f5131380e51810304000003a4010403800c40185803007510b281d04884280700580e900030407680c92a902c10032840000d0200c0c10100c00e484010f00d8040851403000200360300035401d002084402a100d40258010b01e0720980020682500142141c2d104107405500305010000c840441d050061b00c4030408542640001c1c24102c003501c203708200900411140f081c8000c624240c10b1800c11542d01401031903410300c0355202c88805c05103034110f000040103101 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 281121357 1250 281120107 281120131
    0x207050a11030c0402070b06040905010b13051503031317100f0e010c0e1003091a010e010609080d0c0b1503030a05090405060a15050a2307051b03030d0b0a0e 69
    0x1016010185401c032100000c52150340108411b41c00512605041900000c0503240420000b4807442d0031070144c0858403445402604103603214100d0002d582140b0f0003895001e40c18030b244e40c0400c007451f03103034400c070000e524121003469810460b0343e120100b0601c2d9041d01000f6a444044842450740580c1c5038061500ca450b51a04180f80d003655081c49070018159007803c101c243c02c201000400e00c488810386024090560756600c40080c082d403030002c284045c000c6000d1140d80d68641044500405080c001c210002d5400c5030049141840081c2441051191342c60302080080a90345800d0f8402c0014030402950400c9800e0540ba61020805080e0740f0300305407503890304d400490f42440121500180800d10820b00c0c42c0e002c000000d003803810240025030a00e00145d642c02c0c120403ea8040080c4070300f104510f201c4070240641160020003421000384610180c41004030070515214900501d03040803a815002001004100c04403030b4411049101c0107001c600c1d100d6600c0f52000148041240c031100403603 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 281122607 1250 281121357 281121383
    0x9090204061d03011e0c02010b030102130e150303070809030f0f030a18030f061d07062a120315030203010e0a020103051e010b0a0905120d140a021f0207050a 69
    0xb030745140100d0448042034000700400820000c8840260640e81c0032503208595514030104154803c3d00070101c00480540250350399014050b000036083e100c0d105429081a00c0c0c004154481c8080c036030351070f190030010025402d0501c41c1d1030b401000d0f4458540395515101e030802c0003405400a101d0030b40c44046030405103480d00b040a8001e0b03c50014071201181107040c511013480000c0380341044101040d041200021a0110016014440402240b48015a100d000400240954007620902450140316241e0b007000312110a01c202600d0f900600500111951084258403071080d8000044098007c40c04102165250042401c40704410100d50300360300a11010300a40d6090700489402c105202808003c50350071040c40d047c0110103005a6102103030001e1903041c3d0394401d03030a00024080080c030380b4498904403840c040c1e843c9602850200441c2602c2c4051114140440c140c2c0d08a03940c54026009041c0307c3d002046041d980100480f2400d5403d12500300450000c02c100d03020035100760305800c440 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 281123857 1250 281122607 281122637
    0x70f09030b07170919260315100c030e011103130905010e070207030b161e0503090115080d080a0e010c09090f05010501271505070201030501050a03050a080304030909020406 76
    0x28003000307143c3c80c44e55002d0284946a16610410400e540740c00c400390880042080107400c403400c0c603216000381c3c080d85c04014850b4020b40b5429811305400100c4045142e580c52310015900300d044820080c01284115041841707550040000c101d0042e8250280d81c40c0c8030126030300c50300842190b003100b50704a0382d4400500a4546211840703401003118002400380500c0c541d18120024001481441441c140c40070901c0c0060045107010b0001101d00e1030110320070b0f842c0038002c02070740040700d020030a0742c01c00f89070140c0700c0141c1d90248183c4007841301070300c020f4000346c41c19550300002030f05040c3e50b00d50351221402d515074280301b400240e44066039141d0fa403501d407a00c4542034991000b00c11107107500d4800100000da07005452144034412150400000c500f1104200c3c8010155074415650400c07404800c240080d4090000d1002900c01d8130108016605c81c0b00384400d0700b501b03009c024901c0c0c0c001d6800e0404030700007601039580240310f0f281a848154890040c281660010751040e0701003802c03c4041d18039 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 281125107 1250 281123857 281123897
    0x22080306040906020a021e070e22050307060e0c0915220204091d1b010f2c3303040f0c06080f01230111030409020f090f010c0308070f09030b07 63
    0x3004074a9005256090034489c8004d8060320241c403240c0403286000e846503801c0121058003036019008402d5036258111428540d0140500e40c0b424401c0d03004100e504280c500d0b08140081c0100360a03502104468145011700441840640d0320b9000c100a500e160791000650780018000b074220102c0209a00c1e504049540740000c030f620719148640c101c12039040b018085280c00f040301c403001746040d564070300250b6025545c01440c0e090303200300003611180007080c45800c100a4690303900c0c260f075004900318400720002c0018104203912440000300e42038501009840d40095a0030a021384c800500d4101943da40d43d401c003246030310000208402c50108820000200b41407070040c00c0c1030760500369038a100031701c2d005a001d00782c103e24144944c0c50942e4405e40420408d80d07005d401007200866544c15a5a0b94001c150007034141103108100d0403a848406511502042c24640d5242c0c4442da0382d500c45e00b0060394140e92656140041000d28800007005c00e08543c43c13071b400b0f80c8064550b80c410031301c11031040c05 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 281126357 1250 281125107 281125153
    0x60204150806030f100b010e04020a0305010501020f030a02070902130b1801030f0506090402010c06060f0e0a0f02090a0306020c0102120a090302060702010605060405091e160822080306040906020a02 87
    0x1203e504049540e84180303c0c0402d0780744241c00078110000740c4190030340043e203407003e03400d0102d0b4106102284481005415074003041c1a50b40907000c880400a08008031540c0b032007051100c41c01030b0001c9408104501d01a0082c005041c0d101d203000441c941c466044010300c0e003180c0e8850f0340d20994180d003004d42d540c161040c840c94044400c818001d03842c144000c500f16a06c040c1009040158480a00050090380d50010020706080e101c459800b81c0ea44c10303040c95100041d03e08540700c500d80070403a50020100c0c800c883c0940f0002d0541d0074618a10b40342c0800a40240c504014155003c1104000190280312528410190403000044051980c00c00034a04200109050305581c50702c01c0070700c215950710050300e049840c111000200f5954241c08004940c40b05044160540030308000c1c0208400f00700440081e506c0b19645031070300c9030f0729000407190011080e09501c49010300c001c10200812013a01c000e55201101520101b034060140d40c582c0300301d07400912181c5c01a00b03c1c655003140241c4a82d0541 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 281127607 1250 281126357 281126359
    0x2070507060e011805061605010e07080c0d0c0506030a0b061317010b01050405121c0206010501021005150114190509030c0604032a0f0308030f130c050609030703060204150806 77
    0x3010380310007502402003400075018251240c0d01c0810607401d03001043d08161f09040c0d008009000840720180e115564003d180118440c900405070f2260f480d0505541c41141c035074101115142d5145844144041944043c0100107046d1321400c24145d603844160007003002452400c01100034601d4010210304441e0401070041c456410242d041e19642e0f031000a6500b500c40c02c443c5418100c1c210307143c55280ca4040c02500303603070103030301d20700142c0702500450b01034101d4a00780c095890481400c1940b00440704200c5114010001d00c282294255101d844d070080000060f400710307441c003852505203801c40400604100000b80000400742e51505044c050b40c80c2c51740007907600e141441e0542d65808444004a00c450494109040140095114000d0701034010020301c80d400c1d03101030312403c1c076864507803080b0740e50392244100e40045212185c20080c54034800b90010040072601e424a410046144c1c0035488042e854032647ca000303c04070302e031840288003d01a802401201009600340545074040c004d0250f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 281128857 1250 281127607 281127617
    0x90c090c051306030f021b07030204051006090303080c040b1c110c0c040b030115060e090609010b1b011e020706050c12280e03130503030f070303050a090602070507060e01 75
    0x4503401c00050950b016502d243c24041703004041505610000e0054824039500c25001d03410003416141c0205842c01507900a441c01e100a0381c1e441c5003507484040070300c1540c0019440e01001c001003446a04c00030380016280e00a6860141da5030403942071500039511900c00301c0403407401c00f1000507081c40b81d02c010850755a002428906904443c0707840b407044450302801a44c60f25030243c20b640d001e51210000081620481351091345600c0d0091500039545a03036400342031082d0100b28113140601030541220dc89400d070300d2800d114101c40b0341d04410510400d1110350b40b03421842401440c24010322076829882c0b0340c01603e030003032400e04806a0700041c02c80d10382d054042080400400801e020168401040300000105107450244441491108000310f18001d2610300d651011450105c001c01200301d010a000075515120810103841e84520240b2100500c1d00704000000240290003455010321248070009a18400d92181401d03640124011a1250042c200034802ca6401103a00c0020b400c00b0f282c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 281130107 1250 281128857 281128867
    0x71b0c06201216110a03080703080109090f020d020a0509070c1506240207050301020304080c010c03110306011115010b0a080109090f030c02040f0e0607020705040207150b1201090c090c05 82
    0x20940da075208000310aa520742e0700c0c210309030070701400c1c0c07000360342c00080a0050155503981f0304000d1480d4118800850002c1c410b980000340070031850080401054001d680040c1c000180da08200810000982c2281c002c40c4078540010141d90351a54180306000c01d81711894102070b10702e8088000b19404800b6424907103458400d20281d50040342088184010718090881180300c446c0c10ba11f02302603984040d9241d80004104001c000409000e03048510019000b8055a00c1841c810b03800e41d141c1600603071041800b800051081e40c4602d206110444510301900e0350103242148190700342d90260003000001d00001091a00c06030b008114900501e01d040d400c01c060766007a9207489000790b8006015081004615400d011f40d503690340105a94462150104403160b03900011a480b20707812034200000d40101e00002905040600881e10350591258482400039541c0e28508010f0840e82030701c0d904840b0000428880380320074400e0340036290151100903115480e01036141d040d42d403103c2e40c0408000d07007885 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 281131357 1250 281130107 281130133
    0xe0a180b09040c050904080409020a02030d0b090f0a0b130f0506010206060d08030601030207060f05041505070e01090e09010623030c010c02010c060b040e10230c03071b0c0620 77
    0x144800380d8004417134203c4e40340c0300e0f41004c0c695401142c0022540c5480000c02180640d0000001c0010482e400d07030500002c0003803000c12454220446180d8502c80c00180001d581c210207500020b84404000d103101050610700d144c0304100c0f00300812180031595a0018858190b80401c40e05510040c102c031051003111080e501c044c040d00026108905141c0c01003213410030041c1a0b080143c0c803426581040105103814184a1780b03c1420340c000c1c0b0903642c40d00011a85940c41031182490414060319503a544900d04078828000030f00040807200343d0356942a000c45c000d201c491441d04070804200340d0000152007041054145a113000c0c07080e051009090003500180d801030325022039541c21a00018401c41c4810102c2e01802da028000c0103035014055032029441444d5001c10360200c0d1540c00205d034018901d0310f1120b0707041c09542045154105100044c01c20b407054615903251807102c0c4070030207450b600707507201071301000c0a411100100e000d5065100403460044440503000012900500d02d000a40d4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 281132607 1250 281131357 281131373
    0x1080102250609020d030210050702060112030c1106030709081014040605070903080d090b09030c0a0f030302120f1905190c1e0e10020703031b030e0a180b0904 70
    0x900d01c0024010030306000c00c103010940d88500c0d04035401900c2c0440b098074914000391030300d03000500b84040c02d1520b004030f0300044c400680c050580343c0c00c181c100954083d503101501c608010910807151010f42040116075500d80001441c0107000a4503120341d01801c011007141014940014014000c0ca030500001c082c0e0108000b032034002303130011000144c548645008461000058101411070304000541120213074041c3d0102a1761406006910110b03101c002105450f403184e0f440000700740d03004800100c080342d0220f406942c4288203080041c6000c03001442d0500f104401c0716980070201e1400100101c0c405c4090900803a00b428420410452406a528000701c002d02039203031043c1955000045021402500d072140003481c1e0008811241101040007001d80312007a40682c0261010031008032317124000185602640e5042d00c0340210032041044031010054852000c4d400c0014540a02034a40c640303009900280c40554014100c0341145510710307007520880200107005220102c00c10010900d61 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 281133857 1250 281132607 281132647
    0x40f0e04030210050a0b040903051b01050903030f0711010e010b280902090609090a050601090605070b0c1c141006110309131d0c0a0609060206060f03030c0106060c0b01080102 77
    0x245000134070f80e228000800014100c0c140d89a420500d40315174501890b422001070511820140c810b01114045000d681d421b03203000707441c085010307482400401c404044945411350300125501d4240d801c090301000300c9003510600c41030002540d6555513500307035504020419400224010a40c040900806050408140224880c0b09000c44d03000c0380c20295035851000302c585c4450001c148548604014410a00600040d82d110380414040c50001038103d000f5001c1d40c00b0503411106501c000d5589498880040d8091aa4100002c640d0618080480c1051180c4c2c4000404203400036400e1508482101c2040400c0d00024180940c55a00e8400d07102e00204075440283d05940040c1d0303101c80c0d000d03190043c008546299500401942c11003040c640001143c24810b90115449a20070340c0c0d1b1602610050180c2c000c8800581156001524509018182000d035640180c12a45050400504282114480d8021900040d80d00b85c0600c18051b1800541e4094a90b01000b1442e01308e03441e5000b1010255 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 281135107 1250 281133857 281133883
    0xe123402040e0f10020c150c0a030207020d230c040509030403080f0417060f0f070e04090f240608030f041509031e02010809010606080601051b12040f0e040302 70
    0xb40c0d84000c03140641446001d160245400407942490300614600000c1d400c1559150307010300c1180c02c1d10180185902031903001e44803551500d49480d105050450281d40080c00590700b00d140000c0c1c0000242c20a81400c20300041202c4410444000b45045403e00b1103070b1a180344214240340503c0103242010080703070102d07940076000990f14040c428103c0240e0059a0105882d0341c1d28408903219000007042d954810520009400c51aa0310f000e4054030b0344505131502000241d40350501d40d803a04103a03202c0c91400b40103c4020070040103540d01c0f4804002203105805a030b10400b581c2d2410741030076000380c6024010500c0070b141440d85840010351203000c0c85c49043d04142c2c5540b400301c070711400750a084010f0b580001d03a04100c000701c41e024803003511200208a00091040001130080b00062040e1416280190344010041e143c640c0111007503004000304070020300b04069a0205103604001c1c004020f02d810a1040d15586498090703000c0003e1a4001c910b03001c154000c201c0040c0c0c1c04186240c800f46 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 281136357 1250 281135107 281135111
    0x103020a060f02010b04021303050f071d090307020904060c030c02061e101203031a091317091306030b090303070e06030709080d03061e080c040c02010e12340204 71
    0x8501600f2405407000c200090741003440060110b00d540220007114003500d0061b82120010b043d000b1000d0745d101022720400103e5068590b441d50040640e0342d400e03402c0034200003200e00f06861600011446c60003a2011210540c0d1081c074001a2134140c000c0a070b1100180c0060720440ca04207244007080b10040c0a150760044400000400c0203003807107011030280a070300011505004040ca03018006012803090400900280805c24101d442d082c40241c0c4101c2046004060410055a5000340c1d1840603000c1d9504030340038801482c054860204004d88011030000105489185040400c0700b89809064040c082c3c004104024001d9040903141420080580c0c03499030360b44d50300030200d4007440d00b5044003649004604400d1800c642c190041000d440702c0515140d03a500306081d05801ca0f450a1150940e1604015601c0306240303840d601548150380365000110305403210610f02e508050942d40c07144000c00f0081008801640c40d0940700f50803512107003002c80c00d810356082d0100740300d24a00000740304030703 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 281137607 1250 281136357 281136377
    0x203040203071206050103060506150913181a0705030402010f0e0d080304060507021002090d02061602150a0e190e04060e070602030a14040b0f0c030c070306020d140103020a06 77
    0x240741001030030001c002c0b40301030650500301858080003030502840300752055414940491542e1500f11018150b0201030040285007100c44410701c00c3e500a54040100300702d07900d40c804031001803503982a0a400744a981b9080d00804560381404168001400780003c1010034000c002c01030342c03c642c900c0180c90190a02c00a010a5000040c0e0411100e40b0010401e1034080281700c00c0003101d1b0003035400307440f1a40035135940d80403241914040340100c105480d40114504184405414680024151184012407212640f0f00c01e03000f00d52890b90000340900340200008140c088240e1011000042c20000c81e150f58403880d2211aa0b00c14600e10300495103e008006c01080c10010140e00040c202424403040e01c0c019070361a031001e91240c00581e0301c1001300d400840145908042882202c043e1185540c110703080041c40b1102412a410070320790000d2900c01000b16104a00d0104205c600440c8160000360340c42c0300100f00c10007a00c1980480302d25440002c801440107070345408003582900c22503c0c141d9461 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 281138857 1250 281137607 281137609
    0x405010204091109010e010c171c0e06010602060a020412021c050703030807090b03040b0109050402030307061505011d03120d150b0405040c02030c1c09030510090c0807050303030a02030402 83
    0x80c8034580c0041111403404010b14884084240500b5403814241c035040c0c44508002d0056403040410007004045092207081c2482501c00c1c5270150680c400492000c0074030064031784446007290f00036185c1182c0d0303521185c010050705904109065101c4c3c600c40056050a25206006c2003070054050000d05c984c8590000c1040710711422134440307096400200310b494082d81ca00b0701629040064425400042c2e880381c0103d10414148210b0303000e250301c03d0403190030360f203049000780c0180006403089034580020016000424a540549103042c2e00e008002e1207138924080000d004801460143d008001c0c26100d030311016540480d4068581344404401070b514400301c0d101000408181103504000310209d00081004502c5502030f04c1581e4081d1002c101013080c081003682d49001e00260188a43c4c000d109000c108400c62014005101c12030820101403038690b5901070600160700d101d0062039a9900900301409443c168402c0145070381c07409000180e0078503010070f45a200091000b405d45400001003421 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 281140107 1250 281138857 281138861
    0x405060103020906070614010b270f03030406030e070501030b010509011805030f011b03090203190204020f160c050108060a121110110d0305060603010501113d05100509040501 77
    0x43d82e074000d02c036540e13520712031801e00b0041020b2803e0b42c07007059904002041c009640012680a90b2584600212107461b140e030640351041c2800d2001c2e0405403025040300716450400c0603101a044644011409100c0650011701d08800d907403000f410107080500a2420b070341c000c01259410300302841c1c0039001c41d400903410380b545031260340038580501c034000c6554040c2d5019800380055041c1010034030b8143c0400341089046da4003000020b58982c00c8001443d0018900700c1c00315084902c05000503080940354009407016400105881c0710188401e000881044440c2c0c61150151000342004242414003d000c80c0340880c0342c0c05102011000400b40806000504a0824000d00000c2c03806d030755000d80060041101e00340c0248030382e59202e07030784803c03107107600a0040c248a614042e2034141135031710b41401100c1c511508000d82e45079000b806850174000c2c1b5070b01c10315000008621484404105e40c0305039045140d059040030ba00143c41c00c000d0001d82c10111541408948c0c0890300d003c4640c80354104980 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 281141357 1250 281140107 281140117
    0xa080c040308180321070507050d0b0112050a080d06030b070c0302120c010b0901030503090916050a08190e0d1205010f0306110c030412060e0120180a0806011e080309040506010302 79
    0x440c0010706011185c0c14031450018030580e403142c41614801030303458090243c0d076442c03004010b04441080300140f0000d0340302010314904038016000c6485450b119154825250700a104d813034015500c0d024140f0038403042c4101940c02036124988021a40015100251160b0040c10059000100001d85200c441401d4120041c5200002c0030801a9652854915a254400c1846a000b0304804000910142d02001202e44a55581d103680317140004049085480c0e00e0010300c0480300740100c0e4000c0c0690a1503115182151840c1c0004182d80902c41034068012242803104e102004d043c00010b22400c9801819001201c1e400500468064103825051626000e9124000e039144008a00045c02080c00345e00d00044a0280104005c0b0300c107094034103400d84802008800002d07401c443c0c1c802017188a2002070401c28a043e13501c04807003c103c0001a040740040d48169010741c010001440784454280303c0c05010700d03000c0e1400e9481450302c0d500b81e489000b00b00714a0b00c11943c0f2000105c0507402901110 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 281142607 1250 281141357 281141383
    0x402031b0f222418020c010c0e010e061e0309030f0a020105011d040b070e0f0d03020f1c120903090504110a02010c050405060d0e01200a080c0403081803 67
    0x2c240c03641c14001c81882068400c0b400c4001c034104420400d07414440103200d194000d00b00f03400800c650901e404035640324000e03100344409580c20040800e99050038070a00d40e07501a5603440030340841031640014103c1d5414028070380300702820009103080801480d41001b000b0300e2060800d031a540c8090545065000d51080c502c241e100015203802055030650005058402031201c24003140c2020784021846201104c004100d040c00501091295000d0a6011104080144110a1425010081854070140311412401f50f84454454603e1036020f10003803504d90031a0b00135034845020510001c18091603031000780c880e01c0d5a50220000e052040c0720701000b03800c02500600042903082500e94180c0c0c0181d5502006510b00342040307681c14469002c440880704004d168600304408410314000400107010b900c0055941d8602d9070740c4403a401030885004401602c040c64842d041d4442c007414015005201c03442c02d160421041c00061511002e03200c03410002100050b0044e03000380440d10380a0290004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 281143857 1250 281142607 281142619
    0x80907120809032d0601181d100c140309030f0c0f06010e01030320060a0f0915060312021c0e28060201060e160302090d080301030c030c0e0402031b0f 66
    0x28210224400743c0304c08001910030000702c0c100c007180d2800d500d402d002e000c6d40c1d000c11940c80030204004030f10303005111300010b801d00b5030000e910301d840e1051a02195001d402c4002d92540c4200b082135030481450541c0c1c41c080d43e04245949030554120307490303110360001542c200e1008280440209410032131751420081003000c0b6103180d611880c21071100c0c4400d100c00c0300051007000c9010740e5685100c10200745c5440c800e008040548900d952200a0300700041011007050340c4640036000700380501c0301d101906680550000d20030b400d40c28202d0154003031581410655100b001030b404100c00401c0640381c010800d00c2e1801031050340c103000606900b6458035400e0300b20001c09886842107150542d101c1210019002002140d5840883d0124150b080700e01884048140a001c2d110a0280c2c008281043d07005020315083d511550f1303213161940088e08151412945134205008025424400070060804048103151610307040d40040d590750320280c00d0701c1ca4030380d155104106075100d86120b0480c0e42170042c0341d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 281145107 1250 281143857 281143873
    0x21303060e011b020f0a110420070201020c0d05071a071a0a0501060c080d200304031106070903110f040e150a1505090c09010e040603030309060c08090712080903 71
    0x1520b80640030b200031403010400b580d00c84502107030002560b040c1c0c40c00240040c00c90b170103017601c60201c03010045041d0354210b51519181040c181c445454080a040340908403074482106000082c580081c4909250003000d0505924012070800200c140c00c444444044101c8800140c081c8900d50240da8402811030307844120302501d4000c0407039018840c12400000308850307039031040221410212150050301200c0c00300f04540c2c134241c440c0c000f4801c40d4844c0c0b07441c00b40440c80d6101d050380c50788203c400f980020102100403000b0b003001e004841e00042149030080b5041c2c1181c0303d1030b4000524210b128401d502c1c0c1804180c054445030030580d2904100e000345d604001c40303165000d542120481e0b0b00054280380c42d0003400b0035400c1a1403002a80c10180250b40150ba130a0b1071b0b403425a00c4154054140000b04201d100241c4d00d90090340061032080d0780c04a01300016240410079100200b046200b8042000e0400100381400507141040b2803640c016400d000306c0c0d40c2842241c40c4200c00c03078507406000e0251 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 281146357 1250 281145107 281145131
    0x1706060702181920090d0222050c1e0d0f02030a0209090c070b0402011d03060403030f15150c020607020607060923061605090405090c01030b040207080a0302130306 72
    0x254490084880104020f841100b401002c0341c0d1980200350030b02c0880000d03103880302c0c1c011018105000015005900600e044d400241528864403a41040301010038007540d0307186103500035030f0381000d0100442401c000940c1c1038403004a8840401c0b110258001c6400340018110741c03c07403185507000d00411592400c1105849000c3d601074512140212039003004031340d205030118100d5418175084040c2c6a440c2d112640115a1045910f60b004a0008580c98002203545e043c403c440c0118883d880000e0b1080765003e103a0161005c440c0c1c0710255002c003401c10052450482403603030f41c1d820680f4008506100510014045004000b0040c4d048400440d0a10420840c0c1d03001071150381c05640c603c548507240d6842c6c1a0000f82c8400307868030030b4200001054102100f024084c05201142c14414286009100450308807401161043c2080c0d10900800c0b03682d580600c00c0030a034850584055181008030707114901e1a120f10002e16003010307400281e403220100300800c00000795621120622012031102 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 281147607 1250 281146357 281146399
    0x21031407021011030108030406030915020a0f090e1302270c07030908030f3009060a05100605042112020703050d080402030c041e0e07140108071706060702 68
    0x3032260850f0b00c0e00d907000360b0110451080d40d0417211210002c500c1c103070505c0d0b411000791110030707011144001c1640c101344501071680054003100740c45503542c040400300300740018111400c07a030000744080502c0c0305100c01c28002c1c0240f4a00290192041c0381d406c000d410000b41030b070070000c189401b03254450040c090840c800300010a00c0a01a594040711161680300070364991040300340ca602251800c0212007501a02c1c010030600c0314266201e004030040e4002c00c5101c7d1100c04843d0303040550042000c11801940c2c9105081c1c22440c1c0b42407a008442c00c2c071078040c0c01d6100e94052250064441822007030901040008490115031113940207070600d0749041e01030f584601a0000329201c2c0a03005a102c0c1e440c2c4150040351041d50010000c20359220b000081c070009210061418200900b04900740003020040d00070340d41c0482c2224010100d0364544070311900190605603d0a0401142509100f04d40da4082c9803200c2c41d0141e08901c24817600c2e180d0008007544640d620082d0406105895040000481 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 281148857 1250 281147607 281147623
    0x90406030510200301030609050102120a050f07030b0d0605270f0f0a11100c0209150333070216030303020a1101060f1211030601080109120503042103140702 69
    0x880c50500c520f465261644030400306040981402840500c01000828800d410940095008000044c9001c41030001c0032001d400441e20810150b0320b1f4028401010b55070810b0a5114001d8030741003269090756400228240a1800d0107800240c66001260f590320300e0403400590201c1c07130200b0b6202801da507007800d0303140c0012009030031040c001d8203445000650003051000c0743c2a07000e5852908140010f003000b40100c06900b016082024000e81c2400684468164900800030240c440e110784550f101003500d800c0300d0540003400214002c91801d407581ca0b0145090036159a000700e4000d82d81e600f98100c1c508202081e14126002010300c0010074543c05030300429070b090860f40c941c2e0403803401d0b05040d4217844061003050b03042c00646c0420001ca000c4100030580d018461400d0044511107600040d107401c5085c0c2045c50a130350344212507000c01c854624000c01154040c10118110b21301130721507a554910100010781c10012458210079101d1083c0e01003140c441440700ea00c00d85050010b00203581d40c0c02 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 281150107 1250 281148857 281148883
    0x5040c02011410081e03090a0f080f01140406020f1204060615050a1d060c0f01050a0b0a1401030515040c03090314121b0f0d05040201090504061d0603030904060305 72
    0x107203502148940008203201c3e004e032140400280001721000e81d12084050a01801c011a80400e006034580c0303565140d034034401404440c64410400341031a030b07000e00341505ca021900c001c1c0c1c0b404600441c0002e1000b0341d103034450b0b0000001a19503070b0070290300031688501e1802c5410400030108100810105070301603825640d542000100004031044140d80701e100360b0302400c0120711185011406860102c509030b1503804007800041c20f00e0300840700c561a1000384400c0e120165124402c005200c00184140000503d049501c40c11491034442c9180d1050924a16141055202c1c40080c3e0340045080f45080d03d480090300801c40803528050060013801da03001c04900080c000355420305c11a0449090301c060112090118450740c80b021000301c00001d0054001802200c240f00d0864150300503405400c043e6007401e0b02051500c0d0900c001082c54030b1a0700003d03c038a2400c1410320005c414950100360791410210305185503103503040001d145000d01c0312105d901a040400c04000c01802068025500314 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 281151357 1250 281150107 281150141
    0x9030f03030f1406030604230f010204080c0103020f1605070308030f0a060501031a0d020a090603050607030f02181c0206040f08190201020a020d0327061d03060106030209060405040c0201 82
    0xd100d040303400151016118280c5c160701140101e40811031030050301030000084d013445148440340c1d00819040c10f4000c0306e510300c281d60118080054103001c0c00007805200003403804518100c1d6613050145035019418401900c240401e0211041010801c600c102864212202c00d4aa20700071030581c2d00c0440c211070b12152139050101c0081c40354001e01545125005030104050010104401d003c0340d06940a4103a9100c5180030000030742d4005881104007850064014204070b01e03000c1c4c0003600b0b844c0004d00812020784108054405400750340070b40d003c1d2880032a900d950b000092000d590b4286480480654040000100000c0e0004280d18a00886180c2c1081d60035a903800c900220004d460480d002c1d001da00980704650042c40c00000c0130000d9482801c02001c10507107448079002030f10888800c0d1a1880440c001800350a400001c501600e0852517942e4010208040210b07455070810b100364000e15401082e181c15075900e00c410f81e07000d40806801000a680f030000020701130701300c0e0640301011034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 281152607 1250 281151357 281151371
    0x3060b040f0507080a0c0c0209090c1e030d050f07021306180e03030c0a1202130e090d090b0901110102031f0e04030f120207021206090d09050f1009030f03030f 70
    0x3107140280c0c0d100f00810780340c409850307440f011000060000a0204070402c10540540c20042e691504068042c06000c801802e41141c18024065103440c040340c0010001d848440351945540e000031a4900300c80300349031054450703d1403004510f090040d440025403015403481271f07034000b40c066801031044402c40c00d02c10103210310a0b901841220441000c0600c0b1703800400000742005403210091405079000d281c0a0103042c0290b04146c1260004001c03152a0000345008100d003030840040d894028440401600e400315001801800305030040c40384c0a900080450704c010580c1c0102c018142c07a0741c400d00295a80c1c900f6241420090300400183e654140c83c100c000708504050007000c621403070b40f6480340e01505d80c03040025519554006420800035408215040051b01c1c0d00110818402c0c0941c01003615040c13900c615800c4c411100020700400c95440420042955403507652261010300f6205404004e8203450101c4070001103801c00340480d00305c007501d1070030107a01d58032001b007005002408100403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 281153857 1250 281152607 281152631
    0x30e040b1f0813050c060a0e1c050706110a110a080307060f06080a08041e030f120201110a0f08090102040906080f0c0901061d0d02030106080c010314130b090c030703060b04 76
    0x580003143c001c1c1c800c1e8032131040070580e41880070003007045143c3e90406611124504000403240d244081c0f40c520250006402682040001c0183d080600707160b0811540d034849081c4000d650782e501680240009000315240700650701c0f6000e03500060b01002040d04d41e42e56803400d0150280450440ba6803049140620005101002082c5100460340c88101585020301d08080b030500c0040241102c3c0b98040d980c80008000f0702c20004175544184610300e003c2c0108107942000e821152148054102030130104088149503a11400550120741141000403554540742091402400f554006c0600e4503e0280b01080e0100002102644e912400040f12411441c4c1824800048020700c280303070100300b050007806200c1030079126115030440064621440481d481c1c002900350342c0315520654042e08080555529540c1c98000c000014001c0103902c0d14900303001010380c02581c0d800f000603280690b02004682445020300901180d158005d0444a1440d10380c2480b00050200100036841245072810764114 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 281155107 1250 281153857 281153881
    0x6090b0a0606090f0f031202010b1c0506060a0f09092d14010c140309160e1f1503050402061e030f07030c0903110310050a05040b0105030316030e040b1f08 68
    0x81c0d1305c42c00c0b40c0c009103618580d04c0d0020850254250340565480307109050075525030f66820801e201109425200e003014509010341805001b034082d9000301240842070042d203000c42d04400413240c0c14080000c031a00c281c01c000303c41c0c2e1000002c01160001250642e0b5001403c01400b5a010780518519004465008502d42c200c03505114620041108082080209040c800146034031014107010f450a060149068490085003500841412841c1d541400030020303040140c507000c0c0c24414000c0064038240340a9890110601030003404142d10780c0b00107011510390b081603c0940c1c040c41c082d800307012600c804100d07258100312090080e000c0f41c040001d512070700c40c2c050084d202c02d0a4a60f8110281141c603000c16000c010b02c10036416104114180352005c0d0913105280c4a40e064181c0000e09043c0361920349042d10040e0b1201f0310960085c01801102d11844d5852021990300d402e02c85d00340080302c40441c0150104410b0642c0c409800d06407c1c600410030f600f0390749801440d5803882c510f0381d07540160002c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 281156357 1250 281155107 281155109
    0x1614030711092e0b12090d09142701060c0605062704020415060c02040b03030703120e0a08160209070306150c050c0301230112020105031306090b0a0606090f 69
    0x16805a28541c1d8032480007032003404410010f8000074551500d0703100c0c0340206907070f84003030703034018409920b0f5041062039201482852101e080780c0c507202c010070b407034040800f600f03103c0a10242d01c900d02101100c91140c40e908841030a09241c41c260143c20340c2d541101404444940b68107030f41e17107414140003612901c3d203942d4048111303500c1c00041d2a016590b0380c604401c2c00000300201c0c1c00c25a07070300c0b07882c141f442018289130042c0714030b0b600c461480c95540b051200b506c40300e02d104c038026401842207200094110f21480d1b20010300b160006481e80b540c0001c00c0c0390145800029080010000c0c0c0300d105032104180c8008154001e43c4c0c00d05490b111600100c04403807241c800e00c0c070300b111480941c07240d1500c11240ca46502d4028000c907000c0b030344038000080c00c448400200c420a00302e182000d005204507400700c00d00500c5080c038141e90040487c2c0018215100007408418032030310075070b281d0041011544c0240160398103d075041e40b05191100d000402042c881c010764001c2030421038005400da40c82c0740604 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 281157607 1250 281156357 281156371
    0x20a1b0f121209210303110d0b0102120408030405060a0314040812090606060307031a101716020309010c02030a0b010306240506070210110d1707050901090506161403071109 76
    0x2a80c00303102140340503a0701c0d00d4500114201b645440b0307003601d00310a4070091f04404034440c5000425100d03040c00a40741c18204003560305400d40501003000026000b01c19075040741c005490403950b800b402c9008800a100e03010080851112040034070080c081c1d2903004c2c1000302c03003501c200c9216882d041105030b42e401c0c0465206074494010000541c616219400c0000e002981040801070f4603103d60008070084030122040c40000c0511510340761462269440c0f07070f04001075004402c418404000c00075124840d5980131414840760291100464804001d103120f000d41040d540c2c2d02c07e585a00e4800c010b0204e000603401941c003280100030322100040210001c40718010240c0345055402c0d820300c2800c0703c03111400e40078400d2800502440403014440c1907480910f59984007000c4500e09100040980c0c084c01d080b041000034040d004242e41c00c40e000209540048490359107c10024004095803200140010092182d085140f01da07038074008054a54288209508200108940280625941c2c01c0b100c1c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 281158857 1250 281157607 281157629
    0x501030e0c01050a050c0106080d02011407021207020a081c1805010914040e1510120302030a08040c230301050f13080c0106171b0f01020a1b0f121209 66
    0xc4a600443c0286064a4207041450405443c1454242180d00c59485008143c000c002c036044050f07420300c605e0090b020049200308941c10001002580c509960100340c03015400041d0700d800b5036603031412031390007062200c00715000b4540305449055041e00d59000e0300b011803003800c80d0818004032a042c1c0c1080e00c00681d15601c04500e448009032090300550342c0760b41c109030740700310380a41c14106002e52076181c100488103e4140c28140d1400d60b00c0700465100c00c41e14030740030108800213540402140c60150491404090546841c1019426500641d02111070121003043c0c2c0b50446d08800280c44130310740210003c00184d981c06041060712203045030451400359801ca101320000ba030303d01c0948483c1034420000184a40c96602044030155600c884405580c13000c07081d244544049116141d4003442030390b40c1030301c0d01141c0001035550210500c0003080030701d10409210340305040314111002440440f400c1200556185c009403800020800255072440c003141d100d510440c01100440c1c00c1b5081d000d94 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 281160107 1250 281158857 281158873
    0x13051e07031401092a480b0901180308060109170a060e0105010807030221010c09050306061509010309050c10030c0219030c06020307020102120c0301050a090e061303020f030c010204050a0501030e 86
    0xa075030000380301c21140e0001003514140222a2981d900c051100e01e4400c000b1601b240701d07060901014849004007490110780c1417403c0d00074410f541d0040a000260b050500e5069900c901740161a00426900b040320056001c002c2d82520350400545540701601034403080080c2c650308000d843c2660024040c07959242e009410030001803d20980c10010218001076112110700c10403e01d6007514003410b0060300145600d18144013a01d024003015411400895504030f036298000035003c0c540c090741c50100d0505548244060038400c0a2084150301100240700039040e2001c4800940140042001d0000610404003110000072049117030b8140c0e80d42549a4a6007891103a131168080e40c001400c030701c21550280b00c944500c5055540c110f011f5031161030503948942c10f10050000e895074a500c4504030b07a040c01c5411038030600110f80300d50044407001000410039070740d0405a1030800c84204004051000082e40110f211040d809030050310f108696024000b9a6000110b0070380e07494107901e9925400c1012 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 281161357 1250 281160107 281160137
    0xa05060606090a180903030c180302130b0913030e010801030f06150503010c0c1106090108150612040c140105070302060720030a050913051e07031401092a 68
    0x800b4001200006021605403519008001058460365007400586900d40711841c0c02c05406020b4a10100503614081c089511034000c0025514a03031b01c0041d000e00d909580000410700140c001218200000d410b45240d42082180382d001420880750640000310f480070720071040d41c03044010038101c070b4001d031240c0c0c801e462a844aa00a06251000c61020b003075101000507291400c2c080d81c05c45030304130303280c003100d400880c2440d070b108403444811940304841c100304140090380c00a0b89290400812078185d000d520500010401620828040f403a80e0700c03e03482007008120740d04940d0015112442c2caaa20b51820560041d161030148442c0140546c200000158020b84581001916031250000c01c0340f5001000031807505580c00721191304002800000c140d5400d0801010b20540140c100c43c4c100201c2c64138526001048614825804034400c85002192240d8407030303088040c1c0b060011380c00b1091540e5540b0400020002003512800000a9420740f81e07604441c83c00152810815031503041030300301100c0c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 281162607 1250 281161357 281161369
    0x5030a05060126090607090807090207050102120f011502030403020d0f020109030c0605070c0e01080c1e1306030312050405030a03200a0e010206100305030d0b040e011b030b01020a050606 82
    0x2481c060400c07110298500e80030b040c244045844641c668a400081c1c141580902c1c2042d000912440c140601c0c05403c1041c28400120740c2d088541440c070040e01c1e158a8a0b08a000e4850b01c0424070203042000240206980300c0098107040b10f80816025042c1c03030440d003060340c80c2c2c019480f0280d80300c024100b501d80031a11418800a4051051402c0d030700f0303e81ca9079988003601e642a0000e5002a6002c01d41104200000c11450f0142108280507030303096240c180c503d55a000900d0145003d0302a09071450707030380c40b40c603a40c840b111031700142103038406110519180d006040d0340c4001e800007042d5200389189070201e8440c09014582140c065031500704a1031055003d0444a00074807040284241902c0d401c410360b501070040f5080655070340030400201400285000006020a407100032148000c2002035030010803140c04243d000d8000c00c0d01000000014020305901c0304000465080180e082e80740c00c21111115181555a04e08000841410004a80d2031003410001480c070b901c130302c02141440c076040f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 281163857 1250 281162607 281162611
    0x10b0f0309030d050106030f0b09060a270501120614150907120908030a0c050a051801050403060912030c09050603010e0402040b1e0a1a12061914120a0305030a05 71
    0x52001c991400f00c41c0a1140300302d071401d81c0000c0c000395850143c820407000e14090780c2d0340b501088410a805091117400213000b08844c4c0314001d0039502103c408061700d07040e030082c0c1c040f90728041020405980d4034102c01132107405442044441518200c803030481c3c042c0d07581920340544541c4042010101c40c00061100c4240d019107400c0a00c0001c100701815040c3c40d000706c030806480307001c4c019101c1c10450b1200c1d040d0b44d402100744061000a11445c0c05442d806810b03200c0d00c010b00000031040c0d0109a005130358600c030301c0c0c10240606044c00161070500c1460b111207202201650390801000b01e01003000c40300d140e001d0103041d0380f011041004102100103001403581041c0010000035020b0310b0440040c1e0100340d03051182070341c005d04e10000d40d9036141881c0980b009162107403001612080b9103503040f42e184105207a100d00d03407000001186681d150302812400c7e44035440c0c07402c01703440d8440c0b07c1502d50100b0310701024451030035074034000a400c20100c0c1c103104880d81500c0b490305645070316000502070700d80 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 281165107 1250 281163857 281163871
    0x41106041814060901180228020d08090106081504060f1e0605010c1a151e09010b0c06010e13121d030d020619060e0c09030d08010b0f03 60
    0x14000414507200d4a003060403201c5444800240c04040b500840c510b40100800051040018100400401e1401c03002e450f03020410010059507542d04e91401707000389181028240d201303081080400300c2e03c0e80008804108a80e161140c009541d200f01c656826100c0d24002c2c210304e0b40201c46d2807101c01d03c1c446030300350b00944505e102290400300c004120084440414210040c0305000e4041d0054402501c5141c0180200303113454041e0540c9a10341140c140070030251000d000f54940c002401c004000304c80c43c9025a00145541929091500385023090761100c94514070890040c0b000003000140801100c0c2c3c1e1401c1ea001030300d200d0b8a81f010315000240010a655a40760700b20100364005030440101901145154130303100050140c000c0710105202886427540c4c040da10102e6101882a00021565444010218481902c0030300f01d1454020340078941c0040740c55000c24090100c481451006801141000c0e8105c480042030300c0822925841d0a204458480e5020003810120b07240d41401554401c2d4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 281166357 1250 281165107 281165119
    0xb030c33030408130e070c0b060102030d110c120309071406211608040b06060a110f0a0b09030307050412170d0b041505010509040f18050616030203010e0411 69
    0x1905a800c0300c00d5500480b01200c50a100080151000b20015180c01c06031000b1003103450280382502c40949401e0501002070246a4080d00251041e0300c2001103d99030480a90305114a245030030740190b0036000805c225a40740507040310700000350380030b40541e482000c00c04014482c040c0b40c00c010440c40c40302e50031803540100040103a003003c1e20312018060907102c0524404613081c46c150700c144c00c28440c1030211310b04020884040c0000b044034448000d802020468140356940001102503a400802102102440c080d80c0740c207980b9000040340742000f40d8000d1050140d01e0b52030307294554aa1100302c4d9100f022400c00d210521001140c0d841c20754403540308150102c00010b44803c3d80b40590001c80c40e01041c41d88400c0542003030f090034082d20302d440103200c1c440b038402800d10001034002c0c003c1c0c2c81c2d124080e964949281c0b00034540e540004034a403201c4c041c114a607102c41e040864071150100d40189641104c1d0f190031114501ca80308a81c100c418aa142c03007042e4595649a01541402d0025903038040e03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 281167607 1250 281166357 281166439
    0xa0e030f0d0b0a0e0103060b0904150e07120503040801060608040b04031d1509030c04060506071b120c03170a0807110f011505130504030c0f0f0f06050603010b030c 72
    0x500c030300c0160f1010b403183c00b030310026942c0f440c6810001c1d95841309031035000f005003005010015100c1005952010600c04000c60755424501059180841d07035481a002c8084010301c0e2400d20a003c8010000c0d6003a81000b40000c0c0d4a0780015078042a05940082200b03c1c9140018086071140e402f880702184150500141480e40c1c82c0028201a10000280d158190000e44015140b40400c10852010001e9500344802c62a10380061a039010f40b03500500740c071200510400c1484c00c441100d0024100301e40000f0001089400c10340c48040c018041141e41c0740001020b445040542029281d070b5661655490394141e9030350408451398031301090340c00351604c2041100c0e0202c00003030207040d640c0140031209500ca54900030030403070a6482030003040d40e100d2401d01031202181d880001840215005840040c292601d0301d031414a20561080240c5101030303c03070030842000440c0e00150301a9008800034084900a00e0400d500e9a50210340c060340302044070322215000d0b81140c81c000e1030300c1556000156078 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 281168857 1250 281167607 281167609
    0x140f0910090804090e060903191101020c01090c060504140d0812070f0e0915010c0203030403060c02150105180604050709170a12020d080403140c031602090a0e030f0d0b 74
    0x144011000840c0c0d40080800c0502908a03d84500540b00342c07414014201070a00516143d224030980c42725805c520709a07401e59001c240105003204c070100c0c20350001c40d522a6070b44d0010380200700000045940c40d8200000290007481041510217031354500b005c010b05540c1c0d60707003006000040e4070021140d81a00f80018440290080e1034203204101c9078070780d40026501400d0003800740c80700d440020700c41d03582c3c0c8040c4241c501034040a18291102070928641424440c000a80743d4050703940002c045a0070020b210310101d0f40481c039001e00644c45010b02c4420390321101040f4100302e11020507180c20203a440016014642030300100d4010b1290705080d411030391914100303171520a00d00d102c422241e001c10a1841001040e20b80081d11083c50300c042c01440c017101c034006050020181001e0200301c0d59100c90250b511184086440c042100c40413607907070300042d4020400c4a81e000c00141d2041b040d13040062020401402160b1082c0c5040d0041c5150400d40040c0c002c140c1c01c560200380c10561350f100c0c0c0001c9 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 281170107 1250 281168857 281168861
    0x11040b041e031a09010605100e040e15091f0c0503070c0204060f030602070b0c0c071802040f0e0603071a1c06080106030b040b07021501050904111003020403020310140f0910 76
    0x44000c082c00740c0c0d0f1071038011402400c0d540158050307802803d400800c2001d0940c8185401c4200e0340407900841c042c41012129071820754804003c01c2c43e180860305100662000007907182100c100c8050f090041554500311208444070401e00701c0c0803420030000600300602c2018103400691000b0310028442e500c03144030010441d8550000c0320b440707900207929014018074508071035000740b10070100c920703090002c034a1684951140c032512400b50b0b40c0500702040071032240c040d28042e0020391040300c01c140d23941c06400441e86090b10024003d0042c410041081d05041080c00701054099600e1480d14142c4040d6001d042801400d800d5076a41c0d9200100781d4080a0081e0b400a4bc01500844054142404d0401002c013000c0c1a01d4155400440340c80c81c1c119210300910304544040754003c0ea40e0303544e414a40302030310344194455480f5032401c6c0c01280f0190150701030b0069074001d50489180b10001d501ca1001c40704051f41288020725550002180301901c003808603408103d00c4180c50000c5200e49210301 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 281171357 1250 281170107 281170133
    0x10309081308070b0f070b0c070614041103011118030c06070f0b010b030402030a030f02100c0f02010e0c0604030204091506060e040e0a1a10032411040b041e03 70
    0xc26031420a010060000e08003c0c0f00c0c082c1401186945c9421104001c001844c403c4460040c4281580c00008010440301010341d090301da0030110901c607000590104c50784801040ba002c4402954902840e91a802c05100d81040c001c100b040c0ea07481c00110f042c100d2031800c0510b1000d5450b2145003100c0005449140190a107684a0310b0040c50200251400800b0014141c110b420b400e03806004000c05650300041c0420101e816091410544120302012402d0110008070452400c1c2004038116031554071502c401d07070b4108650700030061f907401e02c044942c89000d8884510741c4002c00780014809403806030722a54203103104e42111251050b0501894041d0303181a88401d012901a004190b081e0520703010315421a8003080251007840056078401d542d0303c429480d0700b0151400d801c00101c403242803501c6400070b540c2051071504d60805805000c2120100b00b41486042c50415908551210580065609458140094500307040c1060340201d03595850091340903030314254a800001003058128511 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 281172607 1250 281171357 281171377
    0xc0d1401090605120c01030c0309050d020c0f0a141009080f010f0f05040308040f050c041410090608030703080907170c03070f12020f0d051e15010e070e01030908 71
    0x544641c035001d00c9504681d4035034000c60240071481c910010341c000104040f02000401d085c0020fa00d500b02c04100c0003403804e000f00815900c1501074006404d5000a8990701c149030440d1640c0d84001803000b84036070000701c0c1c4514201c500b090200c0b24203c0c07500114584e4191aa4602203c03815941e0307410601d0f00c204c01e1081051a5981d050135000b2039150701500207080a124801e00c01400d007951b00610003040148042e001c08030349282ea900304102484214241a4018424000e10b00e118400b408105001d40c2c05e81146446008001a01e14082c06a4422514080080c6040550b940c800303482c0d030741c4001d08450190017105008a1044900301c00005004a210000e058566000302410314140207034000c040f44503007988081005100552006803007507815136001100107051350126400440940d00281140591095200c0ba0f00d000d481d0b252941c10800200c031034100d085440f910200701c080c0101d00540500100140030103016500340040c0350410701d400604114a910780340599000b2030300345 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 281173857 1250 281172607 281172641
    0x90911030703140c0105180d110a0815180309011101020c01060b0720100e010c05010504030e03070603020301050612040218010906180204052b170a171e0c0d 69
    0x1902407410f0400154000100a091440c500483c880044000450b841e00701c51040c10303030465100c02c012940100080c903420140041d1052900d42e41c01684880e10289111001081480014100000200a0b512480c030000203980342c060043c00440348440290002d6030361359020071149000c00000d00c0354034014048103c52a331506240c0c9407415200c01c00105212803c040300360303000c910b80d423801c0010345507a14906007603580c2d07001c1c03500690f46205500c8010b01507502c2c0504010501d50004824003001d01c040f0162180b281c0c17030704810b4080740820b001d100d0300070f041441142646581981c64580050000b000700e1b8803d088002000000c12098001e803400f50b880e000100900c801200c242008081c12400550903e81000046a5604c4106241c4115880400c0a5090b4415200c2c8180f2100345c1200986c2002c0da421030008860350310440301d840c0080c0354400c0350b80c018000042071601404408183c908038040324601c2c080c0a01010b41b415070b071140100040140900a4485c040281000d44030f0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 281175107 1250 281173857 281173883
    0x8041e0807021002030c070e060d21030b12100504020a03061d0c100c022407080405010e0904021c15090b04050105010e01030201090312140a021506040e07090911030703 74
    0x1480300d03014884443c4400d56200317000441d1010700102e039640958404a100d92082d5071204001540c0c2a800d480251040a2600a6078480b040410120058401c1341c0c405211070103004050214182650740e9a40454101d1148140816103941140b601300c2d000130a482c0310f81c0c2e00e030b40381e4200720b9031a100400000424144d02c0d24150500b80103046208000b2108500b100034070510280800c07460f003400034420440c800e070300720062040417914030100c1868800c403511204645001d101c103a009010752030104200500a2815180050920f44a19809002c40c1c0e03e000f00300e042c2c880345900b03110003210b031222030b6000c3e00002500ca116404902d40501292140741c2010305220b82101d01c10380004031058155001072026036004032450040320ba110300e900d100000301030004c48100022644000c1d2055001983c0801207600081c1003958102c203058880064440404210071511000b220f0340154010b40402c01100800307900030300b140d90094a40d010389520690020303061403903642046501a000d181 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 281176357 1250 281175107 281175109
    0x91e0e01140111010b060d0b0a0e130303140114100c060c09140a081e0106030215120601020c0a0911042606070c1505090c0d03050d0c05071208041e080702 68
    0x110450010070f00000700445080d00010440510802d03c05940d0036403586600301883e04e50707001802c01001064150f401904101010403100409500103a00007820610041084c10300300224074104d496544015986400340b4080c409070b2210003088109000d0240d44107030110708240210258801c0035921400000d0410000e151514900101e20740541c1e1200b20900c540640040e8146e4050382249200080c286000c1a05014001c03a4100075000407114103c651700c58110307405440d00e40c5200380c0c0d07480d0f1541c851004983d02d0361f600c50a50307407064595004000e038450700d0384a081008208064030f0b14054803000521040411200e040141030540030204010110902c80070f50400c02900d000c1105c0c1d90342c0c0d01c490303039600d8040441d42000b0f41c0e1107012940081040200c002e00001c00b40241442c044141800b5005030000301260300340b1420070440c50032040c8180211054168040da070b034841d050403607a0443da01407000704126080c100011128154130030810404122b1032040142c10b5a41c0310340d00c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 281177607 1250 281176357 281176367
    0x609060e0705040c050301030503070b0c1b28150f021e0a02010b0a03031e030e0610030309120203060f090307052a0402030103080d0504020103320c030403091e0e011401 74
    0x15404c104407050005000081d404411100d1994200031202e2035034588045000052084500e14200030908207200310f812030002c684042145109941c480400e0000d42021400401d0508002c080440c0403490401d9100c142c0e00c400605150004014208a04281a83d030040808440b681400202281407a0300c154240580400c0c86820b07141d00408529659014280074005106103580035900640c411001e8441c2d032000340301c50b2401049034030500385001072003a514200d020950000f84440d5000c152041038072004032405602600901840d600c03041e542c11005005060172917540810030864011400400c2141241d6030150b00f01d000e0000540807003a54403c031347d10f110f8000c5005100420104001805032200c0c00103002022032295907a2004030010404004442000c01c0c641c1078008600190b5828060100101c040d540003907140c00c03552200c28001203a000b0002850b080c0c05002c950001101019005901c020040c025625000704c41a1403009030050b40c91072852803481d41c595a800 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 281178857 1250 281177607 281177621
    0xf0b0d0506010906290a050d0915050a02040506120406060528050d110f030c0402160b090c031c09080d080708060a0305060a200a0302041a1303020d0609060e070504 72
    0xe20203960403001451480008174003402c89000401ca0105401d001903001c0c1c0125004032500c8101000f940442e440d0010b81000e01080c10150a0320300760021f41e22211038400c40b03050356401080c142c01c018810100042e80c3c0720040c0211582c949644001a80c0d840e100c141c2c80c84020034080c071002d1013030404010603c0c0308090340400d105104403030101010030281b00d291150407105a9401450790040070100c0c0c68040380d91034540c1c00610014814025178504950101070901c2101c80c41c10640b02d50b42003070755030a404d030700243d85504660481c02103c00e000700c0e109030720550b500701114130a03900d0200c103081c412000a42d0010600f14402c00c00644c1d4450041c07944180c00716000c1500c1c038115107076103035500c03002400052116507d8845019519415006621204d80025415520204400c004019402c24407800030446070001401d0b000d002100c06032901c0c40101080449400e28540030400992006001074030b015983c0d5990304081111402140040c12000e8000c150031482c1c4010f0008980c03138 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 281180107 1250 281178857 281178869
    0x2010501120212150a020d06060305040b0609060a0b0c0601031202160b0c07030f0507051503040b0a02030c0d24060f08010513020c03030906010618080a03030f0b0d0506010906 77
    0x14080040c048803268000c0301e05515016215621040c14902407a0f10f00b4100c43d1003161180c03508410070881450b690020200040002014400c00e565003205505841c01034600030031450742c0000140e80d5080641885074003550041594140c950b90f40340c50582c1d94089241c40380c046e04074100600c103002aa0540c100341d00802c0c801080302401b007103080d9543e648103000b03100800f0400124811003000c10456140a5a00b280c10003800301100d20744140c1d00c611900c00c4500502800d9201c0c841074592000381c0348a1500480c40001c80c2e0b6a40180034000e600040800040100034000080100101e11600c0c082d490f507030114448149100548540d0408c15a2041040110000c5010f400030750020600f81140d4055802100b06020512035601034014a81c4800c40380c40701004025900c0f40000d8114105d0351140c48440d0140f1685441c000e041815006a85d02d075804502e550700040c2c826441500503034800780000035603070030100018069000380300050f902c907409040180000030381341c0720340d40003000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 281181357 1250 281180107 281180111
    0x60506150f0901121e09051006060c060216170306090c030c04090e03280e0a050105030601260109060e2a07080f131401090302060f09060c070e160201 66
    0xc911044900c1d4441c0e154000e04010701c5000c408101501e40d0009161502510345501c0044a2060f03ca4020321051506652500c516403801b1303000070307852080c2d8080e10925030394060040340c03986640d8040c4d8800c1d0b00c605000101038000501141683c16003003d01c002c00246250789041400c10065160b8024084581c051003c00070b00982e09000c200b1107048441c90400441c3c0752503524105802c6019075a0f44e4000e180503140103070382218000f854000501c52a840340e4031180760170070600c00b5803500382c01006d001c200c0400200d0341a600404411055503c5000c011030f08200005200b160040e080e40b09103e81501e40c030302480300989a42c8003561014814032150061005018082c01d07000b846400c015076a0000a003080911540d6030841e03005030b40410290b5906d214102e91985110325901c030311944101c0f0200e00035080c1d0701c110300c5003049a800400545c1000f00306403c1c103000340d010850040e0300c590100001030180b03000740007200003440c10404240c1545884140c0b4404030b40c42003210300171a4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 281182607 1250 281181357 281181367
    0x12011203180b040909020607050111030f15030604140a021302090a05040b1003180f0506040c0806240f13021305030f0a0305072d030906020705010206040206070201030b060706050615 80
    0x40c0549060f01c040718210303070012036031000c0c500120354240304401001c3d00550802003a8001040316100550244410342081c01c015900d01da02481c02020301d01041d503142d005400442c0209022001524140c0380705c0c2c0075941c200710a50700144500c071040c03a49036007840d000b20340420304c0c0c5001c54950300100b80a8038207001c407100050018200301c1001b2000d500385941c901c0901c954040c1d100000401990080d010581109503007003184e0340d080208d500300c52880894a01240c540c20108245005411020040c912000e03031248200700301102d00501c41c0c0010176440c000314540d80300e10a640c2d00c3c0019101c0141d58400c82818060240d1050300818020341c031030020080c0883c0d0005003524100e4151070959140c80461411052503100031107050000c0b10b680e00c030014003140034500c904200348203440310350f041a0348180582e15000d9510407580542c20041c00a030260a01034020600c20b8414500015601006000184c07550444802a0f40c42a65141040030a0400c5d0980f520a22031042d5114104 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 281183857 1250 281182607 281182619
    0x70b0417130302060307020a02060c01020301051509030d21060303081602011518060306020301060f171b0304170316030c091203030b0a171f060302031903051201120318 74
    0x40c1c5410710009000341e40010024180d07174800d004c2a103100d503008005d5580c5085841503603010350001c4c02100d10a900c13140d800120210752004a60000e2406005080102c880071401d50300c00009002010401c41d1500076124024254810200a50b2180d203500c0100d05125070a2140e19282206020540e850006c201020446c078840c001c3c03c545104c0341501c080300c0040c2441c00509401e610040801d80003100201d0340d00e402000240c004a11750352442000681c0c41441c10b981c5a0a48041401c3c2003004c0c032400e141c1e07118070001c1d903100380103e0343d07040d8480b03003440c804440398800c031000000c000a041501004592602580f006e401d01d80c941041c44e5424081d00c01d204c030101d0b01740141410b640d5a0005c619840704400c1c2001418075a66070703c1e02c0141007a00c01d0702c1d4000902030340c26403454403055000742c0500b4410b500640ba00900103200794088445c440c0070700c041800094040c880c040c441400040070720108203000c0c1500382c40c0080c0011040c035010b071075901c1250810425102c8010301740a9 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 281185107 1250 281183857 281183887
    0x201050903070c180e0a060911220e01090203101409060405100b01020a050703050318030616050c031b030406200a060c270e07020706170a11070b0417 66
    0x2d03502c003500c280f1302c2e000748440c2c604003c100000035103560303000d10742c00710007400066030240c00701074007411408409214683c10446184130384281d0f09590410744140c13850741c40c9903500c091f1038200110000180720b950b03500001d00c0c09410008002c5095100d448100c040445400a247c120305060020406410281c2d2800d8862440c00e009104083d035600c415260b9030b10030894440c1194200d0700741c070503558890501c55220f6004d00540b1000c3c803402d940a0840382400a40c05100700c0800c055180d80c1a80b030380c02251260720402d161403180c0b006100080035500c50244070384d00450481d004507a56440e01e0f2002e00038041d0700f10320a000380004040a0146071003c00c0005126038000f000207480f040480e0300b6501d0a181490b074110406505184440100c003d40d4040207403002c03240001015500d4903002c0b41d0b2070741c50f401488001100c21101180c620702c04d0b02d803240c1001c848480030a10b0a05590a80c40d40d4000c0b10054429883c144140414000650110000040804221450311105c0c4500c100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 281186357 1250 281185107 281185109
    0x5190303030b060405060d06090506010c020306150604030b0c04090f0501080606010f090f080f1005220606051c061a030703031101020d0510030501290f0a150f0201050903070c 77
    0x30500d9140c502c2d024665855000316000f4100c000c14041e150004104028010043c80c099a40070343c0c43d00b404520103602510201944d60b6004008007501d1355401480710628013103000182c0c00c0302c000e0101000240d1003400861058610044544c0c0b242d140c1240c0000361207102c40c1014210f45448010312000c81c0119005500030f1082c00d0201c4122182d00e4103c80d02d2200c2c0d07001106a0071000d2003c28911408550f40c42c003a00180122265440301b44c400004488041d5a007a806118151407050790000c0c8010b500c850780d0059000040036507940c0c001c82d081103c4103004407000c10810484104000b040d2040d8404080803500c00d40b4040381d01004240d55503038038080503040c000ba00c40803191910302501141c6440c08059070500c0702c1e04050f00700341a40c04490008985950805421a903503800d10013010103581400c40101c48090840da040c841078400ca1244650400f00e170801c08251030b0440e030f22100380e80e5031980c0c0f0314400b60a006002821280301a1100b03020b900b0402c250004560341005941c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 281187607 1250 281186357 281186363
    0xa0510060806180a0b130c02061801020c163305071e0f02010f0203030f0a0f0e0a08090f0915010f0c0b0f0103030e010302030402031005060d140d0306051903 69
    0x100203495110002e01140c051075001c280c0320b20b0b80020407106481c13540140c000a2401c0d22a959841c202a1440c401e50389804000001030f40302100141110100819003c0041310306800103140c142c002d801d45051500150601c2004102c407031f010040000c0ca2010516400744034044021898500200c0c5840750340d120f002441080004104101401100c0b008407c41381c0d000c90342e0641800307107803030301d040b001d80000b400f41d001c41c001c9480700f4540c90010040300d03c40c0d4400e000160803035542021031030040c002c1110300f44d240e907a99801004030150030801040414015800147c5511107802000018508081514003410700d9000f8003520140c40f4840c83c414103001d080024500e40d4810040f40c0200701058068103070384103030003407011004500c00c03a94142c0e4000d64821074140c0c20040158241d120507200290564403165a01908040c1680440d0700030000a21106500c3d10396154004101c00e80500b540b440d03001048030414894141c80f40b407000b0038094500c0700480403280c0402001000f02c0c4009 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 281188857 1250 281187607 281187617
    0x1110307020a1e080a0c0305160e040b040312050f06130b060f030903191e0309120311041502070512012007020301090b09010b010201060f0b0f160c0e040b0a051006 72
    0x30152014445400c500a0980c031310480d003600d0920304108020400e188000e8170359014601e00720398881c407030640b00390a5030b000062008103a240c0795520702c5640f00040c0290b0402c02d030604840c5008020740a007600880440704540041e007001000c00924280035141c41d00e0311894040e011005807070f0041a0b0b10014140b80400307891360740b1001e03900d095103d204508207240d04501c60a01120340c01070140d030300352644895042080d040a20098085401f20030001c2d0002129482e4900c485101e90404c0400517006203c0c181071a03a2189910603c5295011200160f0000c03070041c001070410421800d05d1200c03c0001344080b000c00055846282142c0c0151a09020002403010a42d1000d4001841e0160721508a007058545221894024550f445819005500b01b103c00a42440031071300b01c00550b81003d207520302d0001860013040c19907008001d07080030b02c1c20310003e81021400f030062801c0200843c000c0c1240300e10741407510016010b0010070b000711701c078a01400e1000b1018007010407000e649640c102 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 281190107 1250 281188857 281188889
    0x20a021009080705030c21033c070c05010e060c0306130908130e0708010311040b041e060602101e0507030207150e0111070206030a090212100203010501110307020a 72
    0xc840b4051152140c00f070035034032000a00e003021840004105482c5101c500c0c3da0304110380040704070310680c80107641001c1c940601c00c618107680c441ca44030004141510503014403148000120f00c17074138171504032407030b1020850711056402031241c2070240c8100d511003003001c1c0025140110701c0705058040641041d000b4128244d08100303864481c0e01120308180c008601540701e804c0d24001c4d0011001d1401010162907403403000c50b50141c02108028140c80e8401d070781c441812800342c1803000608107211040e6000c4d0711502c0c0c00e400f119030a001001e41c1148008c01007861805c020002e45004c203a503220518851500c040140c0c803e1810050540c000c060000114003910b840b1000c502900a145001d0300b0b24800504600301841d055026501f6201880d000748078801c2c81d40620782c0c1c103002d0301c24065040001000000c0b40b0b907038540c1c004800144010452400850300820251070042800561005a980080140107a68101c8040c2007514141001146071141c4c036800310382d0102091068450032084282 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 281191357 1250 281190107 281190113
    0x180305070303140f030f01060e010c0201020604030e241801091202010c03120507020106050310060f30080304030e0d02130b0103021e1e040e011205011416090504020a021009 76
    0x4110780702400100c03002e984908051005503507090707080c4035230000704441c3e880b10145035000e9400d00c0700d050740580103060725035681c0c4c84c1901c141d007100d5920b0ba408071400101100c0203008140c403266800d21100744035180d0400d03004103621558807400303260600900303a000300004628003035400c0c120345d820b19010811101030f00d42640c1c10700030109005c0a040c180401c00a0450f41503000f001150003c07001ca5001000c0b4550040846000b4019904000b0b903502c0c05002d1540000720b0a400084c601e0000c480100c04050003010801c000e00c004c44801c000001440240350340411803000042044035000200000c1d43c0c0002c3c40002d00c400c000700e0040e10b60355445601d80c003030340c15901500c400110924620b01c0b004052241c5a2042005482590703102d4401e400c40003900701940c0c00d07500709040500c03541e401c018001203d0350440c08220740940d03c41100c004443c0103801698025100194445440345031580080c0c801010394002900407881842032801140d4000303415110300124900000700381c00c40e42 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 281192607 1250 281191357 281191397
    0x30c05030706180627021e060a05070b060604051804021203030a060e0a0501050117041b03080a022505100e0a032402041406030c0909010312180305070303 68
    0x903010740668a4803400f29a50290168100240351081c8010018030200c2d80d503c40ca034001c910303649240541508400341c01418041103068843c00d1000340008500c103088005000ca5001c049000300190380482ea0300200400350380d1507600640d040301c02e1400d20303003040041500703a80c1f18000c0038103141c1c8a10229081d911100e0420303403400f00c0a800e8036030728900130b40b0490141c4154451080003000b400d0002d81080a9032040038143c0b4016501d0000d00c409160b0b400044207070107401640c488103200f00c40500c100c17400101c480110700c0703801c00545035401d1040280c140005481d114038041e009107029581c607103c5940701800d803802107540710903c10460303034219540b42d030b1115041d4002000e0030020040c00000c000e20711210001019400c001c024070724920083e8002c80c45030201d4002e0ac0303105800740e482d003807010303543c0b003820700a415003403601d0a800121940c00a0740243c500c8400a4031083c000755102c8841c0180a40a5440fa15540c1c0b07190b07955540c0721540d00c006000c10000c410000707000d17a045 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 281193857 1250 281192607 281192617
    0x30703020d020c011d0c0102011a04020322111216170a0b09060108010501051f21140405101802060306031501080c01091703031305070b0408071a070f030c0503 70
    0x1c3e802040041c00d8011020799820040004c1552441416132003802c5620500414a070350303912501ca00401030241c028080650805002031f50031181d8030003249130340380382070281082c40c900410104001d56410000e0100300803d01850030000d1b0085440151520341000204089910550500d45044d02c28400507090258081c001800d1500034007c3c020039000c0040c1c2c0324141c441c0c0c02c000b0891039a81c0c808001c206ca10103400000f14101e441d120190345409940c0491000c061385004465410a40c0503050488000b40a00c070000588201400306000c1d08000d21441041140030400140d004d03070051300d60318030300d4580091148100000155164030305111150701d552181440c00600d5849500c0c41e511611040c660034001641940009520f0f10302c260140d80c2584940e016518603150060116030101d10642e06840724401d0020005170015410000c0005101c414007800c2e03030a040c20a203c020121030444c4100c11700782485924045856070203405d04540d0715040c4410041000d1400760f041d4058 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 281195107 1250 281193857 281193877
    0x20a1a2a0d06030b04021002010b030a03030203061c052401270f05090f0d08060a150908030a050a030608010b100f0c06050703050601020c0102070807120f0b01121b0b030703020d02 79
    0x2d08000104015509464900643c400c4400e21449001c15a0403400c070b804501c561079142e0311060060001c81c1c0240c1c000d5400050182c1540d1844842b8800c00881c103408a804690903800f060110700c801907241c1400d4418415070190147c1549004980a160204040107482518125140c100c01c101c0c0b56000c0c0400d0085000c007440700e4a4800d003603540741c8c0e41c84290807400340954100c4007000c5105217804d0b0320030840102004051400c00d24114400c0c0144008542840085d440200740b941c0104003800001d050740d52040d6a0b1602d89400400f92249a80444050b80c10484810856070b1089482c581c41241403405000c52600101c080301c541031400009850030b4500014000e40c0c0742c1c1904058828502a021a030ba144c400400499650f981842500040c1d00220418462850b00200e2449018010717040120030364042e40301c0e0044403e082e0300c070900c20407003481c0f041c04120540b0103480c2d00414a4048000e1107240510450080c80010700010801d940000e44081480107032381600c2110368 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 281196357 1250 281195107 281195111
    0x8190f02120a0207050a0f060f0e0603011a1c022a0d03020a0207090608010c030b0d0b040201050a0212031f0b130504021317060402090a0216060b030c090403020a1a2a0d 74
    0x103560380070b0914031f414a009000c0022502941c101c2050301840b00d42c110b404000e06a14030316032030158508101c6030b0070340d6520300190341041034001180c810310b808540041d031403000603503481003c060401c7c0700c803009880340140716420399071121141c008108104142d0050402503030f86c200602c0c04a05220850b0007050625113014400700744a501507110782c00d54038540c0c4040041000703000c200701c0b0540d1682c00040040d84800c00280040d4418000b50400140c50b0044440301c030100305a010003500f01300c03401d100410f8a03911800c0c40300d51503043e550081c01d000c18010303d84a001d85001e503401009020303460085800040e80070f6060421501c5e40f00500e4402c1d40d182c001d010344d400c440d48484003924264030501c01040403c1002d01148203c0701004a240c03046481708250381e4403203002d01000120365505015101029602c1e4980310301c0e851080744658040c102c0d00d4194900b0790b5402410000da00e000140b03110401207440e03a401c110b034090b56182c2c102d82c5018101c0d07201044084c800d801c04545254 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 281197607 1250 281196357 281196359
    0xa09060905070e0415090819022e0c14030a1e1a1f050d0902061b0604140a11010c02040e010c0302131208030417070209010308190f02120a0207050a 65
    0x80341c0c0f46100340500c1c424001c088012072035100c0b440507602d810402804a030420080c281003d1600407854001004030b0045c1c400504004e1043c0301540064402c4e080301c40ba00f48075160380602180301c0c409050740942081c001507140704201c41c000e408001d112408103039490400a140107491880d807007100310400e1040c0480070980c081c012903c1000804540261340281d91444c842c0c01e0407a030064901d1032070ba903041c180781086a102c0050105800d090383c0241c0c0c100305010410315164080e00b003a4005100038aa581440e04e0840d6541d00d203520704c2c600c140c210100d00c50028403581d4980c0307103e541c246400c1044900d0750001038001c1000200c903600d69032901c0024200c094141d005407104d04a031000302004543d941007004200c00c580e44008100b2807007040058000383c882c8141e0703800c0c0350200144a090400e26030118507030780d01c00e82060b1341140c1c010031030344102103003210081951b82192400b4465140e0011000e980e0300301c1c40c1d040340d4000d02c000c034001344028401c024403070013801c1c0200490011 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 281198857 1250 281197607 281197619
    0x5040e1305011104030615030818040609020705030304031b11090702010e0a1101090801090b010501081b070c0e0a0209031005090a021806090f07050306060a0e041a040e0c090a0906090507 82
    0xd61251000720f61382428802d4921303c4043c2c01f003401c0d08807600719032000d160000401c0d80c0383d8165698551039500c6595440042102e001d030340301401905104500956490a040c100501040500c8081d007015007100310000000441100c1108001e40003601c07050481e44820000345d0140440750030107142c07032191802c580103102d01c0300c3c1248081402030720f460448030f0300c40d50440e00b40c51014902510294481c40100055407060a41c19441840c2c43c000310398040071030004200c1ca0348400c0b019160440e034150b040c0510710207801e555400a49103101140f800c1c2c1d4101c0071075128101d040c1000320310740d80c4000041d0140000d120117449958020003c10b0160041400040c0c645000e0750070f2805002e40d0300c00517121880c00d0800c1c500513038007602d03064103554031981040075650010700401c0c20030956501d903002a4807107005000040803845030141c1030601440a02c030888000340222074442e0702100b00c1c1c0041d9111110002c0e0040581070000c07804042078140500604403050700180130f840740c040d001400e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 281200107 1250 281198857 281198891
    0x8090607171908090114130f120906031d06070c0206090604090e010c0c02180901060b03010602390f030a0209010b120f2e09020d090c08010c05040e130501 68
    0x4002c040d034550200c1e9449003960700f03080b1483c080c114031400354494041109486466484da41003489107041c0038019100d985c5840ba0703401e0f0003130f805010600a503001e00070750382c060080e213107604000500e4000c010840103526913030b400e01a09030014805107000c0e8109540301e90040310041c3d24040c0905130340341e42e241040700041910b079070ba0701e4181d440c1076070b40701d8a54480c0c001200200c1e00241040038a001c2c422460343e5141d00075200b201c00d59690000041e0208648000d075000b00402d4020309105010540700c3e528003955142c00c02001c2070301502707104580300c611401d815404400c0e0754600358400380b9400f092501028107000382d800492a000040e90200c824024203074006085080030203500d078095140035003801900c1000c0798a203000f0604070515060b052240d2107c42285c02c100c0c45690f42c09025049074040e0b200150020f495a50700b40502002ca2035650017014a0002042542c00906d8002d24034010781c09802c0c00c210b4074a000c00d152101105c080c058031604032008000e802c05803c0d418003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 281201357 1250 281200107 281200147
    0x30f070203123901060e041b24090306111c02040509040303050a14101d0903030402042319140f04021002010e0a06150b070809060717 59
    0x40729100b000501c0c45089032500a541080715400600301e20311511101c1c8041050445120703031685603102110000084090050b84014800c6008603807843c103003401c003c16518040030100000d500c96020810111140f150700d0381401c6004100385504208507101120002c10590001d03010302c1c20016021041c4801c00014100d4001284280c803048548880400c10b0313010741d00c541a84400140c00003030109020740c00a50b4003a10b5080300003200486030f140000b06401c2520503060000c0905024000ba015401c1001040c1640c09586580c916000d60b42607640c3c0b00c014030007405161260649941c0e00341c244c003807044490100b40800100d00d080c1410034001055038400482860605000c1051808004d0342c050050a808603006c0540ea519020310503e001098242e204541da100d0188004810620000107410300c0340d0008268244d054814400030f5000c1e8203d400c91610800801000a240c8011221015420354515494403002c2c20640001d0b00c0800444180b504009185c40d0740c0128418681 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 281202607 1250 281201357 281201359
    0x3010609080a0308040602070809130b0301050a0e190206131205010b01030b010804141006080a0b1605031810020a030e01050a02032211061b01050106020c060301031112030f0702 78
    0x905010750718803456030740d810346000c0640407400c40c20128020461a40050a0050003405420f15046491010441c17803400200304064082d80c81d10003017044c1c6000c0c06007075040106004c007444078800c2009065254003400120030b4620850003412411074880100750707500280d2280050101e696168079040040004140c00c841a500c0e01c50481d80c2036000c0e01c1040c0800e28180d4071488240d8030f03603588007480060542140001e104606600a02807214040e850103000e1903005466006181e242585595001030302054140040c0c0c000b25407015402000d0301c1e40f02003103980415aa240d90343e007845c2421034605062011500000c1c56420b4140c050308501007028408000b04540e90300e9021200480c00103461841e40c0301d4400e42150101c808401c138120455004094040842c0754000c0007400603449415911354507811044000c0c8410428400c01d07004203c81d0000d090402c40c0d800c00920720344414000140600d0b04403c0e115400e407500c5e0707141d03105041b40c00d0440e681d61001c0480b80c080b03508441412 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 281203857 1250 281202607 281202617
    0x15190908030301150804050a020411070605010b040821040e07080115080603100b0301020d060603060e07050c1002220305011a010216060e030a061112010e040c0306151a030106 77
    0x40580c00001202d0480300d0320404400c05640641c0100c80b8041c0161054460b803045016a001596903489034110f400e22441c5465a94049880c3c2603064ad00142e100035250441030008010282021842c8030190000f40030104192215000040c0c0d68001e41e0070107092815070300300b0854840d8004800a061782c140060491383c91a15000c110350048080301c0e010381540125001c003500781300d95000f07084249002800941480008032100b0115100f507480840041d484910401c10314184415454001c145450500c3c9810100c5584e150358441d407071f51710300040e94000703101000113241714480b401031180d43d42c1d01000c1595908241c1d001e4810742c1000c0001c1e25014840305015800001d227503d9107034540503510162860301d1015602d0050726120760350180989025080021314522400441d10b0110508548440301d0845502080d04160000690b80700d2007003e201c042000c00301e01000301d030391001c004511101803c3d140d400c0c02600c1c1e440007140740300c6c01c4d0031014141d80100c00742d416143c8650319 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 281205107 1250 281203857 281203859
    0x25030c0308090414070e1002100f02070311070305030f13030b15011107030b010905091204080d0e04060b07060504080405030a060605040c081902090301090816060b0405190b151909 79
    0x840300504041d00c440d00841c80e6146c0300902400d041c104490381407801d0054641c0a142500d01106036580d9120004156500180030400c00d0b402c4942c104403020721000500080c4d04654910782d07280305030b101c5410351500c04940380c000510204100c00180d0391120306007580d820070b41c4413850144039444500d03010889900b640001102d00048500071650401c490030a41c0c3d1810f0102e04c018500901020080c0c016034001c0c15a0701c1d2814010802810385200901c2190100f480040c40442c51011491190382410300401c080d081c0481036409194006c00005115181c41c9096200d61145a0045805004002004080c8000b60740514121002a81c050240000c121402c41e0741490464040c10040c09401e441807844a0a9001e031200380c07c05000081c01c121591160f4041e42c0081c1d03042c440103100d903260703c030030059240610000c00a0030344080c491410001a400d000c0001e10354815616036580c0350000080d6100c0c060081100041441c60b60740d4a4144002c0407644030060f0300001150304084 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 281206357 1250 281205107 281205131
    0x30507141305121603080403031106012d0509011202040b09040807031d1518030109080f130e0906101a07021005070209010b03090d09030525030c03080904 68
    0x81165080c0701410280150181880c00b0002c8039a150a1814040c0c8504010b5aa42c50250b4602e10090744c00b4002d002d4030303a444d503d0010490700468403510516084500100000e002500100030400c1d03406610304c04010b03080244255014160344000da2190402d400080c100351200d1701419a14001c1e942844100d2a08083c8604864141d60040840d08100520350110b845104c03000e9641404162450300e07110303c00002100158000b80c81c088000c070011b0201a01c02c030700d800c00d20801034160000c2c011101070752182c0e80340d400364000320070702e800001640340c903003030b480440c910040d0250707400c0080141052400155200c200b265040f00ea1200010b010400000f46004207a180d02405801894000141c0c280018554000300712808d02c20300b405400010703551401194041c0c040101000e8403440d00c101c006d8500840441080d007800703841882403001c554007044810720700707002480118450445404c11445859150700140c24000b1203d030200c10003203800d004100317281d8216000d201e0508055 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 281207607 1250 281206357 281206397
    0x90f030408030414060d0516030f0e0c10031404050102040e01050109240c140d1e02030711010e030312061e1c02040f0c020705180f19021603030507 65
    0x1c014200701d50700a1004002030301c440c000110011002400c1d09050020941c1c026040d40c0054800e0170b07502401006e1070200980c14407800b010000d004906024a40680795295180c983c84010a8007500b8030444030750b141c501030f400203a220f00d0708111031400c0f0f280a09103a8000c1d00140189040c426040000065a42c49800e00da01922a030581900004019031110032403084200700c02030030700110315440c0c80820724171804404990002d02c041c2034030386c030354010081c040c03264210b001c0c064001c1c102d000c0400a600100352040e1690110300c1614074440d0030b0040c0c41c00305c9510101a414480001c11002810346080c2c500d01546043d11100b000e0240601c403450f0390410449610b4002c4c03150b00801c1c20509503410104ea9285c0064800107110b44090402025980c0c10b002d0840980c1c010481000f150070720305034400c00d0741c6402600c0c08460811303101404c2c0c2068080d0500e00b01000300c40070120ba1503d1039040754402d154010b405c0b41c0e030b19103510b0060068901180c000c1e001c205903d080f0303600c00c1021 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 281208857 1250 281207607 281207609
    0xd080436020a0f05090a0e18010e01020a170402180c0a0311040308070f060b0a0b0903070b120708192a0c02010e0613090e030927060f04150e090f0304 66
    0x3078440005440c3c0100c0116902c1d00a650b660381d04c140003880000c0c00d2040741103080e003d0648046038480b545210700340030b82034911018248449038410840e036104c00303500022090080c42480307011400ba40701c5000252080461012601c3c00655050030711054100090040020200d161814000c4d00940c960b80d6545004500c0050a0320720f003008028001803d441214460511840780001c1b21592000442c1401c8480d4000d10100d01001820101034a0200820001007040c0c00300580f802c04840d0740d142d4030a001410b00d5082c01100c44c04502003100c0385c4001100088411810442c403d0700741e46814402003410001c500b500380110759410090301c0340340c000c0b40c070b9601078407441e015440031828440c40380e1104130076081030300c803448021801407224001e0b002c40b035842800864460220104101e641c4284c20385203407064074906800762602c0da20601c003d900910803503080080d8000c0700301240103407503000280c2c00150302801d070219800c0d5490102d2030041c0445421a94803000c5021610303640d1213130f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 281210107 1250 281208857 281208877
    0x13092901020d0c14060103050c0a140a12080d0207050330070e060405190e0f09060106120906090f03080a020c0c0405060103060806010608070e09010b03060d08043602 73
    0x50320180c00c42d402201040c1e84584542c4a414504019610940c105036003a08221001d400000d07031f100491906d6030148000d02110b1006104020b803440004103280010302c0382c0b1203001d02c4082050b060000c2c80701138030000c1481800035540c0e0465407a00503200d07400608000b075180301ca018001e10380d0b101032920b03411885010055002c2500c1781001038800500c2c0480d01540200d00f004003003040d4540451040403040c0d503841c100c01c01420002451015080200300c60320025014040085141c070008420381121614101200183c035180120406050700d82000380240d0300380039103d41040304603d01e48580c82e00039540d007101c9454200101080e44185c0007103c020303a000320100f9071546001c0e0320041e0000030505002521541d280d07034441c2811030991001020031000b8041110035600542e14130039581007110b2500741581045500d0080c0d00010300000e0152120750010b17000c00c5514000c640c068407900d4030030703000001818078414050203214040aa1010030f03c55207a40d4010a0090f60405c0f94 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 281211357 1250 281210107 281210113
    0x21150f0c0c0303041b0b0f03040c15090311060706020304051c05030c12100509090d08010501030b06030a0c111903120b090105190b0a050301050117040201090612021309290102 77
    0xb256142d03400c0d41d07400440b600c1008182885c00045643c0e0440c010200d5048002c00c280c0c076841c01c1c2c180000145041e03840011040c40c91660b03544c1c400d44c0101c2240580e0351010a420b60001c02c0d0f00401e0583c0605000144850f10000501050000004420152610f08901c42c2c01007607600504035032502003928044843d06083c0b2490902002500495030f000b4810140e0918030b555500c0040c500c1c2c401a01c00342031a4000b80c11a030811341e440f03040c0301d02400c030a003820f10803084c071500401c5051000801c4034030060b58449500300b5081c411492423080720350380d81c04c444060004107c1c0403c3c2408442d0101c0108039240146d112400480c0200500d81500520b014038581c03910080c014481c000d882d0000c085c420034500860136080320300c00340c01c40401c8d030b654071510717981403000151140300c041650360140d10a0b0010000181e0344446054291b408500e0500c1e100d00320a014100a8010f5880c654683e22183c003012412104591241195a0020560146200c80351f1003441204003145d040070b006070 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 281212607 1250 281211357 281211361
    0x409021305101716051207030b090f1303110316060203190b0906012006070e0f040e0c060f041205060402040b0a0e0123030d1808070506070221150f0c0c0303 69
    0x3020113072015450300c903c1c2856442c4c404020017440f00040100d40380310100790707240031030540790804201580e881005100b1028140c1801504480d40030701c3ca000040805c891161801005203091080c0c845520301405200140a0981b5103034029400c206d070320103c0c800a880c40751500e40b00301d0041d07480060015002c40415101c6000445401090b10201c40b00e0802c0c0148034601c0910030018a40300d2445075846445100d0364000f042a9240c02040e610320803401e0007591079500c1408203481001031002c44000d83c3e2101e0f0741100b140640166445504101250a100004d0040c08100c091041c0d05c2110100038480909082000400b50b50107400800e0f420800184440c004540e0401c0c102e050040482101405800010307281c000741f06480d80010f0340c0114285812054802e0381006012448064041c09081001090b01406003940192181d18100d0072094808204e03c024280003814000f81c3d5a0b10062060103c00c0c0082a0b8116404041c10b90018021004a2095610345005c40b4040c0d07240d9 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 281213857 1250 281212607 281212621
    0x11040609031119080109120e030606040504150e160b070c0b0a0950090c1b0609190c090506130e0c010914011403090304090213051017 59
    0x1d46a036410503040700444618000f01c10308041c103079005002420010400031103506d01810070502d108080d000b84901d110f02c0088580d808900c0903030102c8103a030000745a40da241444407454112481110b5420303d0601d10300000640402d80e10307500403894080b041a81d5076019510054030459030b000d0f0654405c22420f000c1011554024160141310389008094503880d2584a0001a201c020143e5040041d0b0100114000c03004406d0428104400c0091840d8114001100014030481c0409100b1844c5600281034540344c46c041c2c0307070501003961001d9442d13064011880c1c2c0c2d0f55410f45500c40c162140c403000780c0041501c0c415440c44640c0c012040200b1603d88914130025010240c0b0407030344251604207050074600c0c1c070b205038808006c00400410a610003403001400b18004c5401030320800d25403035020550380c0d801c1840c03040d0000020720b17006c0d542d0b90b80d150818154020f0340c01150050740000f0b00f0b140049491a1024182c0e40c0840300e60481c490b100b20243da04030074141d0f0000980520500103800 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 281215107 1250 281213857 281213873
    0x14030306011e02030f04091e110a0c020d081b070f03080426120310090905030702120f010603030e0103060b0c1c020109020639060c07031103070605010305011104060903 74
    0xb40040700e00403a8103140e07030b1201500c01a0003581141400700c2c5d503200100c1120300f444424401c000c5480301c1c104854607501411a40d10303c907040e000c60520040c0d4060303000715121018600c03002601700a4440c0c803003600c03038410320200844613108a00c500c100310012a80c4a1010b014204403a40301e000a85404e160001d403181030340404008007270302007222181d0050103800340031049840301016041992481c0c003080440900f200d68110341445e5260059203400a20300104803403000e030f0125410a01592944226886c2040300b001c3c41c0055401c1c07403c00001c15811003900803ea00090301c050052580328a5964524059141150b074035600c6592003001140020102000302c0941d813001142d141d1183e00800c081d03602100c8074106810607109a8001c60350200c5400c5403921071881c0802000c06a0300d8081d40d5008050100038001c0e00000c6c401e0b04040c004c1241d0b200c00486a801d507611040581000002003009200075a0365509044040180da00030030121001d40b06140c030f488502c682141c4502d05 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 281216357 1250 281215107 281215157
    0x2150106140c060901050106090909050c06070206040302030304080709050609041113060b13180908040303080907090f1505010809100f06050a0f090f05040206090402030a0605040e03071403030601 86
    0x1150100402c1a060108010b200252084007032000100c1c481d450042c000f003c110700e81c0d21600d00070b0724001d40e00703000500208511907094003c492407170319143d039400041c2c401e22030b0b80d01c001e43c184400035000403801004a40601241d03c10742e4100526a90b140601c501c0b898103ca00074940c1e110b0101801c4c2da49044102c811002038941400242252a6400950141d001090003a0308000c0355008200c6600c4002e421250581244410b002d444c00c2555051128051400300800384a080d00c0003800242082007520000c014001040c088140e102d80000c0040440c1940d0942818002c003010405500400c4041d000700c6200300201202c0c0f210804840090030603003401da41c03864507400c00250550340c0d5281d40c0c0c05840e20210110318a480e10300c0c4802114507110074a18840c0c100820000540c0d1030340700341c7e8655201600d0140e030329500c01d42d2620051003640c100c59071141c5401c11a0410a8000001e09011031150546594240c8031545450750790100303c9140340020000d4140034010109551161 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 281217607 1250 281216357 281216387
    0x20f010f18060507110d03090c1208040e0711150114030d08070c050f0106080d081f0612020702030d08060f01080115050c0a0b0901020d050c401d0702150106 69
    0x182134505804111030400401d100781c880000c0c1c5a100c000c0c180040c270303505900240340000d003440c4c000e11b544c0d40b03200f09401a0f100d02850b903680000001d80803401028020320055211040d501d5601090030203000504081c000d01001c5043c45140740082e0400280602e600401900d41030540d945840e011291745d4003040d411151070154034221580002c090150401400c0311002418001140c120b000f03001c8040100040f03c00e0b41c10040007075803001181900001e5822525118810194509407580a84156440290184034010b1880c0359280e200e030017a4040c3c4801c0700d00003040011480116010070080c004c008015807001c8821143c2d80c0180024500c680481c025680f0324180b036114440355150484103450301d6500040d034410720048910520b540400203841c06400c0c0b108002e015020022031a00305001c4100c0040d0b0450b407280c9031110b1840c4503100d031900701201900c03101c4000c4001c080e82e03c0300c1060401c020104074650300118510300710a00e00144803c2030fa1070810b00301c03900301134070305c002c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 281218857 1250 281217607 281217617
    0xb03012003130501050c0910050307080601180b0310050a0602010614130605180a0501050a031a150301020a0c050d0e0d0b060f04020d0920030307030e0406050d03020f010f18060507 79
    0xb80e00001c0c0c0038062140705004007281c0645440c4c1c450244440c031240103580300304100d42002044112071300025040d402900c2071810500c03902808411214001c2150002c040c00c03440401044403620440416506542040d43d00b610035907030705c1d84140c0c262007d0303014511a520005804094506040f02c1090661020a401043d100d40d260701203011900a8000700c1d1409180700c0420604030310900682d401048192030703804040745151603000d071000c1d01c0703640d0600048800c004a101c14448408040c0e1071280100210340d2440381d070138003500740c0303520400451302ca01170440c00740300c01401006944404680500015094215650751554420000f421a0380c030040d0350506490940f114806000e80b032203805000940e1040f681445003415205072030b0941004401d501e031a945450200540e071803a64142080184030007014006400f031b00c3c29810589d0001a511001401c1c15800901140145117103c02006005244109074003500d090001d002e44407890302c400c91000440960006a100e1514506 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 281220107 1250 281218857 281218891
    0xd0504081923070306050121020f0a031209030c092705120301090902040f0e1b030c030d2a0201020c010c0201031e02030a140f13080d1104090b03012003 67
    0x1100b14103040b01c0c5110700c0b0b203912082041c0104402840303000d0160500030310b800c42c030b4144111150786072910840024094404005100440e486032040d9a0203541c1c8014400c8052429a00c01407910307820344002c4c6d4500708007204c001140241881010403040060002200400d8449011040e40b01c8030f4104480c1c07445880ca000700845060006103001c2d0092a60101c2c0d8180a801080306642d03c030003020780d856245c912809903400b00012104c40c01f90754030084900002e110340001c0d04160071b900005806026104240d20f8042d4004081850100741d000c000c00c1c400740c41a1030741410000514000c0c0560310081c899245580a01c94010055105240209000100740143d4109982e80d0703410348925034020080c044001034034058250b007500c0c3c40407030400600d045440365140e00d201805d1028802e603035003210424400343c04119800071084010a201540001900d8651648644105c461061804c00241c0b0710b45010b008290301031100039284550089841d181c4111070740302802c490081d10110813 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 281221357 1250 281220107 281220143
    0x30219050d360302030f12040204060902130501030e071802030618010605070308040606090905010b0a060c020117181209010306210308151018050a0305060103060c0e120109050d05040819 82
    0x1c03c88214030f5407c7c040d0703600b03142c410300c01920000d0304010182801402204e000503034031200681101c00c2460046103400009a041c0d0030b00e40141c21090824180301d40350b05a042c0703260019400740e282907408400360408640f03443c064100038001c04000460030010407001c2031080c1c0300c40e0780007401400c00189650781c5920b540111a440c0104035002c0c0d440c0c140a070018903040381c1283c0100304d1030a01c02e11489141d40000d200c3d1403022031495182208002260642c25090803902c800c64800c41100d0030520755190703403010703a004000484d000034146030300840d00c036408004c21f82e880e5081000c501e05034410b0f0740c3c05a0701079000030f00c41002c01d50f804060488942d80c040710490310301d003207031030701000402a1b5408034601105500400d008003140c07102040020320003e00030b8112a0440d000082c0511000c201f100d641c18100b0407540d020074110340c100c8280c50f040d4021090300d07100308116100d0500204060b0b580f030103180b080ba1041e41001181c10781404800d6640009244505111a12a00082 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 281222607 1250 281221357 281221387
    0x9151e28020f070f1809050f0d05030a06050612060607050a05100c110d0c033204091406030601120201110609061b090d080901030219050d36030203 65
    0xe40c128006038412045040716507018031404024040004800a2290400348002050714904140030606075441003a0418040c0a008124101345444240c41c0322090940000300303035402c103480010382c0900d0560001924545001210340326140c8800008860351010f0401c000d580151078141c800d40107000f020b01c00910103102c500407480166100003415890108002c000d4450300300d8542150340080103070310301c035904070210041750b035454507046000d03401c0d811003040000150340841d000d140c040c0100052225001c00a0000d481409604000e60100700c482c3d0304104c001501c0c2986c040e000103005002c8480c11a80340d04005006060001a2000076a1401d01e072480c1100c00c80b0750341d0005d0003404401407040182103084801c04841504145408001801c10b490100700100000710000350042c0c503034004d40548035114107124140000c0a0381c00d07000fa105130b1089a912620500c1e040c1b603000190341c110b110810002d004440100440c02c1c13003040b045030390201a03043c0c05601c018090141c01003120 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 281223857 1250 281222607 281222677
    0x61f0e1c060617010b030a0507031b12060b0405090a030e0907050c0a060b120f030a051c1d010c090b070204020a140301030309150305091c090b0a02010209151e 70
    0x301c50039400000c40140f030301d08443d501c0001c1c610a4004a071607101150000a01d2015a504220348180300300c445504103003041c0d0107910000302c007200700040c5018025140c0c480d00d501c41c01075506003c140d0383c200009848002c41ca00003404030383c081c00c401c0840d00b041d90510380d215840303050841c603200841c032209280c881044030444420782c407205042260b00f04601c0549003209120000e01d82a104003c80316201e000300e52034141004004070f018101001d240b01e400c1040c0120080800106400202c84c80c5a689600300020f0340d0741c200b00903120028841d0448000322808420520b0400c001b0b0f42c200006036010f00302a10402c03c00c03a41c0c0c1401c000e07628008500852081d00c49180140c034041460450141003c600420700d072030003040003500f02d8045411450008001c031025041c02601505035207029103904084901c0301c000c200b4031500c5030158014400319400b2103214040c0320b034030f854041c0240b00e010907182600944614400044044001602004001901d1007030135040410b08241e400e224 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 281225107 1250 281223857 281223869
    0x1c02070f170c010306120609170a020a030e030c0303041406071e0506010816030b19060b090405010803070c060813050a030e041521050a0c0b03061f0e1c0606 69
    0x81c0c0c9061569081d080001d02c018010a00b4240f1049103045643e0140c41103282d00901000c0d112540c400c00c00c13542100c104880b900c0300d180c20380c6613005407000a5440f4244981207002c1880901440b545150001d518240203000400840c5840d043c00365034680da041c52044207400c40030500c01d00c40050382e411340c408030b6451565210030b0032284505009203030140603400b80c401074020401000711501c8101300142586d42001000519403514902080000c20308482086403915064021485c0d0440d040103140c040c0d000ca070140070030790321586da045d2680700d03900d001000903021101c01c00c41c2e01e006916550f0700000910306103100143c1a11141c3c101404070500f18006511012420594500340c0f14103100b0303610540390202d4007401d1005c0c1410710b401c00c60240000240d815080c0040100400044401a0b88107590980e00faa035050b4010054006075212445185c0d103c0c482110356018561040c400e0505030759004144a00c0c1c4103018103000800c5851030b6a04c05000c49070040b5440380200d0000b00030b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 281226357 1250 281225107 281225129
    0x917030901020d26071707050d0e06090601060809030705011b090b09090402150f07050d0e010f0e0d080c1c14161203060302030a0f03021b031c02070f 66
    0xc594000241003040b2902180c0034064054400d40346103080e40c00510b103001c211010b00740b2548481c40282d03034424030030080c0304031000d1100070840318990250180c032007254540410701c20503c0e00400705132141c004031101c15542d400324004101ca94400c81a00e50001c0341c45003070764a050029103a06081d00c902ea02e01246070101c5000c1301d201d540e0700c0000300004200708612030b0f050140107400100e80a80261000c0d00c5a40243d5007217100d0320400c0d0440b0030070501040b90942c1c03951140740c07454079800424003001c0031820340701207860254001c0d100125000c0240d40c40d5100c8004560810880030200441a680d0010600c26500303050020840044030030001d07094a8108140120000c0441000c03e4070450b4185051003064030189280c3c11050340c8550000400644491194003200244820743c0040d5051003075108200910480e0002503040034041e80c00d40700301da51ba5008100c1c0300b242d450b00464250b44071507441e110690921082d0003c2c2c001c184191103210307550b21130302081d000050300407604200d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 281227607 1250 281226357 281226367
    0x512150d03020616090b39060105040b060901020303040605100509010306051b0f07230105101805011a03060a09020c0102090310140f22080a02060f06060306060703091703 75
    0x24008a0a15800d107560f117084000310781040000e5480b0702551000d0804a0007402c414400791090905180c001207402140100315910600c0303850b0344450a11840c0c0c0900c0c6803610a5905090200407100b985c24180c004601d0f40c0c881d44d45400080c1320013004490071284264012a02e642d0711002940214000c0101007000d0420721315600554260082120541d001003040c0c1c600c14641d2801d489955800290340f111400d1041c900d628802d544d0036160800e5442e1504021303131001c40d0005c0340705488100e0560003256403924001400c8070420b01482c4c3c1c1e00010113041000b071088513002190300040141821031941c1c2e81d1740b075040680e04002244a401d03500840c504000b82000c026103018045c003401c050011185002110340345c83c0e4003503c3c016044000100142c0c1c16181610144021162000408109a03081c01e01525507001080c40c0b82c01070041070041142241c0507a041070185000030811460754644108000c3c5aa00085049041c0181c60a0008900100441685002440a006c4e644e50 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 281228857 1250 281227607 281227621
    0x1503020403080d090b06010206100b1803030403030504030b0c0408060a050402030a0203060f0105010f05180103020a020a080706090c0b07050705010305270c0102011407020a030e011e0309050c040204060512150d030206 95
    0xc2c000c010300e06c504651108007000242e00500620b8805c64400401c001d580b540003604010300340e0310b00900e842d05440002400400c1540c4400100704607405011108241e4440d402c040f0300300c1c0310f144103802d010340c4810003050100031158809a0032034802012128a450070ba40400e0a10720100d4103100c4154465004200c696003004128050364442c2c6045071500074800020f40207a00f10200007410140e012500c0b09005008014038000190446501c0c4e45618661034040c01905001004940a6282c24000584402c69100784d82166178000068081c0c41e00b800c00440040a0050940440c00003240340b0106001c0c120b0680c0c119110a1001717400b6540c615400a400e5a0203541813100249105003000700c030725404111284015814078240d00c200311060700480b130702110380d00517010b0003402c1d0034201c0d046038042e8407009035140301d0015280320314400c1c0d0030001240181c0c415140455400c10551400400b48210242d0001c540c005481c251209170300442e010f645030340402c60140e4048422b01c451 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 281230107 1250 281228857 281228873
    0x9060b03120f0714070e0c0a1202070b1f050d20010206060a1221180801021e030612070b1803011a04020705010b030609010f050a050403091503020403080d09 69
    0x201c4002614092a000404681005500c02c01c03002411407000701882c1070400c0000c1c07020038010260110a03100300c0c100b20f031b4000e8090340a8900000401d1078080651b00c030174494020707224200c0c0c01c00f001b0360155030341d0403104511100c4010a0600603015620124080c2c1d00c8a0304050800d0144591401c519000b003400011500718262507410740d0b0109007045031555030355409506403000304c1a84800c82d01c40b4501901c0d5106502e0010440c0c0c80c041055540075580701a00b83d42e024030341c12607448071981c0c0e003606034201e200d4005041d0031640d501d8811504100414019600240e0107480781468812183d0a20b042416580204507420303c0003402545045000d00101040c600440c002c00010349604034003062201640c02143c0919000f08401087c04800e42c04070490400c040e0585502e4580010914002d100310020840d04a03d05008600c11074100e2240c14401d940c151940022a8102a0107040c242100f02078041016000c01c408400520300401038100010241c0380862070288518103510 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 281231357 1250 281230107 281230123
    0x3041701050a0b060a0c030302070210031b1409040209120a2a080d030513020414100f08061b040902040609030b0618061908031215010503100504051909060b03 70
    0x40e10f401c042079504903039105012603141800e5030500341c6c400310f603034034043d03010307024401010b9131010ba41c3c5810407155130150070940c007035000b14640050700f0004560039a44004001074610030400c00f40f00c0c00d0450b08090f401401000c0b0014480d45080104050301071802c160400c0880d04801c401031100000d117840e040850120308100d4602060500f089482992a0006d8401000701a20b071000701d900700c140d910007244096000790040c04400c065440908848600b5109003500007112070000514003152a8407006480f41d00c000340c13080352a450420810070f0010f0302c03000528502084002103804961005000900c039640381c040500d4614104070b819503200a20242c000c01854644810840312248410b5111000b21103c12080c0b02d541031101040245802c8480c80340300001e071240c81c030215007840c10f11900b0700300718100000d0815401128580019156850800348441007032000d450184c01c52544411050215984000d4140d102429922902d42c1519007030798440403101d442c00c050181c0c075 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 281232607 1250 281231357 281231371
    0x60c030a0f0c080702010e040b03060a0b090c04030b010e04061401090608010b0411160503190e0406090902060304030c11100c030206060405070509060706020d050c12010503071206050601110304170105 88
    0x40b1520340c203440c3c8100b14403810034020f0400a003021485110358583c0e01048400c5c5000d07044454034588800303054010040044c1c441d1080c0c050304005100d0301c09181c1118144c0340c2c400444000d036440d00217081e0200002030821a5070070703180c9003212805000040501e00a0a000402040c410f01d0004503071308489040b103030940180c1c1004000d003a00401c80c0210fa400d01440d41580701d100d00581000390031401480c600b8140e000f1143d080310f10143d400300301403450003411a810420695151280d008403016444025048102440003401081c011307500d010900d8001c2c1c0c4906500001d07440080c0e850600c5030005404106548141c4092542c10080c03990300c03010a46040006080140b2702410034080c400d5a039110b040b0002d01c8108101e2145c0680e1684140c07401c0910007403d00c466160616049405441100e0494000005031440c0001e250f200f25038441c4281b0400801d0f40e2200809801d0042c10030303040c05840070000c04005420002040240420f4400c1c0461044032541ca509540002d0190 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 281233857 1250 281232607 281232617
    0xc12030f1b030c031612020406030605010306210816020301050f0403020114070504140a09050f04050f1f09060e06011e060306150c0312050906010509060409110f030c060c030a0f 78
    0x3c018101c000c200e0b6001200e0f84404145144e625900311010324030150f100c00041e0010900084140d0950060303400d6800c01d882c01d1000039164400d0b58910714007c4074408440864117004000325000e00028a5503d941607003400c8d01c800541c0120b42911010b1b42c00c1c41e0300000c90740802052650a11402800000390101c00845090440c0300805e0b5008a0003000740400640c150304070741e640c80001000040440c0d0304144100c0c40c0140b496100300c1d1044130b0a507403d0040449027000020041400603a88010071505528164511250380007082c401400b03d4089540d45088441e04078208034040c0249100a03003a01c2c40d0030590000c903481500e40e0700050905090000c18409003034a2a0114144200e030700c0c003014090b640e402c0c00c5529162079107041c180c451804c01070040303110000c2080350680e50709440104c519254841440111910000c0103065081c100d02104000d14026582c040c1c00748000b003c980864010a0009440d03622100b140140d0703a000003406400b507604000c05289101041c01c00e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 281235107 1250 281233857 281233861
    0x120e1207030201080901021209060106031b09030b1005060c0105040c060f020c0909151306201602130c050322030903060b131a0901051909020c12030f1b03 68
    0x10103603160440e0000a06000850000514502d403d41c1503400740300101c2200e410504010840c030381ca5042c00c1c000c2000103414002031480c0c02555080803c5403403000c0da61141e101e481c54894a0464002070318958480303003910380005041e66001c0280148840100000483c1c1c20185041c0403500c0290340305600317004c03550904003012500170070540340080041e02d031401181d0300e100e0100d040618000c80061006140c42c280100c5001d804001120306100b24410822068003410300c4410800181c0580c00c13a40302000300542c0a198540305c440d00c24409411409500740d0102c07180151070b00643c8100014401104100e1059a0040420a0000180742408092140c2d841c01403a05a0318000504816101c8550b18060344504c8070210b1040b071400030810280c520801c0c00c000c040400c1e4134051080d00c4c00c43c0041400d00d0003844208407901c5103402c10702d030301c0d107010b000780f029410501451055001e030781e1030540070b440114000c500c11072400100000e02c0c54890000e000d4200f012800822188050003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 281236357 1250 281235107 281235139
    0x8010503070b040b070f0215120705130303110106080d0509180108120a0c020d14010c030c1e050f0c0606090a0506010525020301060303090602010b030c10080709080604120e 76
    0x403c0b18107440200c1d016580c1c1d003070380782001c808241e44444001d401080340005030880c1c1001d0390240c403180d04815100c078510740b03500c40115124080c4041ea82860310000d041000003e000b21400540c0b003030448004030307005a50300b0105050015003424500410b000051716482d41c505003111305c451441d030821014165040000c0307a41e64007604d4180b40e9440c24001444c03107045006140d000603d95008211107080c0e01c061500b0720a2090341000048a582009170302c5400130300038001e07014003c8045e92a52130740c00401d607410f015124800ba040052050401000e110001008010540c0540f03c0c00248000d040c83d00912860b40740040c034110762030785401d00340103c1d680e00008442c0c090b9581044040009050728103c8001c601640d0000c0d815843d02e4000001c0540144009040752196002001a01b400794281034580e402c5400703007130380300803d100180281401005a83e4000200d482d00581050312003038103624020041d2010b84038002010322010341d459008800c00c4080314155014007040d21340c86 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 281237607 1250 281236357 281236379
    0x607171005041d010507020c0414070807030c110a05070806090a0803010506030403031b0e04060b0a0c1e021002070f142103090616021003050405031c0f14070801050307 74
    0x302480344120b49440721018554008802460740c3e0440000800403402c01d40f2010356903810f103000150151b400d000703e4020307240310035000502c2a25a038460948942d01c0c810200c000b07104030450003007404000301c20250301c0001042411509449000104102030a09c0301c8039144c0307400106050100e40c8401c100c1070000761100243c0c0e04507034065580f40e40381d455a1509402402d40002c204040041d00481d004070540d00403031100809209803800c200031038444111071564410030a94034042000c030000d14002a0514001601c081c1c049520303001e2078501640003074000c2501c60040c0005034810130050200c1c08090b54020000c0800300300f400c100450714008240540350010034110014201c80e102100d5100c103104841401100509880d904c0c0e4916556024a0040c03000507070142c9003880c05410f000b0700a00c2110f020301d412000a50804110954101c980201c2c065031a8505440d00c502c10310071001809a44845811109000001d2602c3d102c02421854140d0010340f03c0d5101940401a0800303076 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 281238857 1250 281237607 281237609
    0xe1305061f020106050d290601170915101706070917070302040221180601151101050705040e06010906051e070b040804081002040509181501060206071710 68
    0x311146290307614011016401010703540e10007500b24180a1009081144111150800d00b8544400800d4801d04c101103101c0140b04807491404190312080c0744140302c400848055024050000700c80030210f040301c2c040061403041e02c03651a09129040240301c8040080c0303143c03249140d84c00003400c541c40c0900c4000c00f60030712032088982c00040c803c00404001414003800740515005041950f440d410180c0f0741c14025500d21045105c0c04481c0040760240c208040701c8605e801840005190990074242c1450241050f1484c0307405104e0303050391070352010000703000c2c191164050761070340381e10340c2c5c80d0121140820000402e02030410074049014040784c1d4005041d11000044814180600600c1046040c024880c404000d084a042c600403c42008540300080060305d866005032030b4202c80c4001d42009900490180c2640003414200140c1001001071101d030b034140c01c80d421509280f1b2941c50b600c400007420382140c0c0058009604000340e03140c10240081380709041c035603040d285141c00d2081c0344e000805 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 281240107 1250 281238857 281238889
    0x304030309050309030619060f0b071205120a05011401050c0d0f02070810150b03090706030f09060203070e090603070e0a050a060e100306050f040b06090a020c010c0e130506 76
    0x203914140c005021007002519224000a0120354060a0011f414061403038000903000120b1706068000c282c0403502110b41040310b00c8424800d040810903520015000d014051481c10003905000f1001c00621b404212802100a00710003d45075040c00240601035040a01c0603040c00001c01c03000d284072800049000c080412442d100c04030105007101241044525886250b551141d9120341c00075040b503500071300c3d0880706a0100f10503039540e16101e25443c0030464100c24550003551041250700d010341c00001c040c0880020001f40f801c2c050359248100d801c1a69040c1c001a1136104807915030505103c2180c101c90101c00801c0302510b00301019410190050003284540e882d917010038070001d0b203030f0070034005030400900b501d4841c40c00010b00310b002581c0344810b40d421420031010030015001f0a0101d4000c54218030300e1192540c1d80c00a110b000803000d0310001d0000c0e401c1040d011181401c1c4201c41064003140c1c1d846000d90160000c02961440c0081031400591524062200c01e0391040292115112 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 281241357 1250 281240107 281240111
    0x603031d19080114060406030c0e0a0b0a0e040c0e06061e04050307060f0f0504060f0c020d1e110405130f0f06050709061d0906010c0807020307080303040c06031103040303 75
    0x400c0901140424401c00084003190107030000100300c00b2019040f280c107084446a0030003940d038034141007000343c6030f1911000d8202044c01105012450040c0b02e0254421610100401c00040040112320791507820390095100322f025070240005c114403129003000400e0034201541840c105240010a984510f00e88003a1010f000c1d101824044914030030746005000040030789801c0b5988120103410a500035040c2400207003422020401c07680030b402643c003a241030396110070408002e03042c16524940781100c281d90100e580c035040000165010241d114800c500709036000e0342d154616215444c200700f009040e2140c0e040c5001c0010486d161920008072070f030451f80140303c00d51582400366016005120240029040500304000241c20185841c2216903640c5d030620705944640302403003089003403065550301800d03000106205610504441d04164092881549030022990010f860031030568082001e80c0c001100b00001c0c40481e000c00301c0109003c1c03c0a01c2002d6403201c5d20303401e5200040000381415 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 281242607 1250 281241357 281241407
    0x62404021e12070f0c20060c0d020d0311040302030a060504030c0507140a09020703080705090f0a091a03070305060606251a070212160206090d060e060a060303 70
    0x1e0402046001c1008880c641c0c1580c450014124880d0754100711590004103c207440d8243e4914894407030803809541004542c40402c41120780707503181c5004048902da1003502840110100306051201000a90345a0010020040c200002405581c1d0b20315030440d00700c0041c03100308056140441d210140c1f80c0e00030130001c1d459486203000e40704c401010300d002d41a032003200300208540785040e4041d101c43d0704c02c4580c0d518042c0c2d00c448200c240d20664200500280d020307004121a280034102924094000800a844400c2e1a50105922030305c11743c0102c96171521001303502411100c69001c1142d200d4281c0c0176200550440d20f0b03181d17484001078059409002c0000740f150b45103030064a4540d138550010801815141c20b030070458162034000a0b08030300f4401c5680401c2c011070000603549815106c4c0600ba90529181c080c20384101e20441006982069080240000c0707691840c810341c0129214280000c1e0606c032000c4103d281842c0103102250ba40e10303210061000c01c0d0820342072482041c05c0441c0410300 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 281243857 1250 281242607 281242627
    0x20f0d1205090102040e040503030106080115230f0f0409050c04030503311d10050a21050111031609050d06020705010905010f0e01150e0106050a0912110306240402 72
    0x21711030399010b004d4040383e000a10042140c0440154100c0c1d140e940e5602c196620741143d4540f60780c0180030710011a05e071a99041c1c07880c1100708000101200500103509083c0001e05070744659020405a404a080008080c03008200500c602900302406124250506080d6918603590b03110f140b035540c88440302007060082c0340c503070881d8030040ca002c9401e84100c000e07501c0c0130b040c140d6004c82c403496804851800001e480402c41e07a8600d02110402044070645074503250030900520440b0000c041408004001000481c0c000d001b03000807086541c20711031b40d0346000c40c40c00521301140c0c20818100030882104201c50f68883c24154241a040480103a8840180c075207980104a0120700504550811000503008000c90f4000031f8150100f130024402104103000c07800249001d401000721005e21100180042846907002d030540d090241448901e168980f14410076800c80524201c6204402140d529060708091040a030443c11b2561400c91031425a080c07c1e0001e070100801e24001c0741d002c9016040 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 281245107 1250 281243857 281243861
    0x210f28030f210c03090302010b011d04020c0307080406020601030201020d080106020c0108190903030213242601080c0406080313030201110c150706060503120904020a1e030606020f0d12050901 84
    0x101212008001c8440283c038060050308102c00282c005d0751904d0300c00c3c44254058015000000f504c0316290511420300000c0000a400c02000180075200c2444208006600000200041c1281d074000f401c4961461000925040a1039000d60411240364010003d240d00003443d1000c075202401c18078800daa0394280c80030000413650041f4081030401c0d040c001810340550090085070100c0c480b110445441c0d1041c140c01c03600e442201240080c29000c1c000e441031081c0307004820086895040b5008460021110b168030748281c0004905810003410104103107001e2150310f0003004042c0145003061280c03d400360340c290442c032000c1c2c14040c0c488c181d000780e20405d1103090030080c002804044422101a0701d40d030240c02402c02141c00300e01c0c2801c00724003490002000e104110490b8050340c9401d0203031041c00040e4100c1c02c18001400580008140384056240514102000703990700050024034000300289400020407081001d5081a50320030310a9502000d0300c402040d12a41c080b13065155003c001d40 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 281246357 1250 281245107 281245157
    0xf040821010503120703020709050709030803010603060e150321041502030c1501260c0607050a0204050604110a03090804080a0c0f06090e0402210f28030f 68
    0x2200081540c811039030150998694180d58055007101c0003c501190752500b1803064a00140150f40071413020800e08815800c0540d11004926242021584c0c030b546900c895042038100038080381d101c9000780b0061165041c0a64810030055040c0303202c940d1040829100c0c1030b41c200d0343c80d00c014444c003d003a840d09080d0440d4000c2600803145000c2e18040c600c02501c9421003460981c05020f19040385d61407840c40b2072410706a071044070011000040406c0d03000264080030315100368901510f8041851130741c65034003520a981c080c01c05444200c9082c81084100da00040c884c5200c0c0745420308100700400707030509980c00d9a816050000341e2420344c0c1040c0c845401654002d80c1b03e1b2040d44601020004021f666004442503400d05900c030315280c0d9000e0360394150a003c7c4140809a0b000007034090700c0e0202d4080c8079151580c0c03820b0b007500001216a0b081081002d11120942e010010000c000d000481e102803e50000395a0074040601550f001410440440e007a0003c2104c084408200501e840100b40 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 281247607 1250 281246357 281246377
    0x126071103041403120304030504300f021c20010203090319030809060603060613020702040c0302040f14060d0902011403130b010905060d1203020d050c07110303120f0408 75
    0x2034807142d030350300300b4140e030f401590a00d4001d004400301401c80c03480c4001643c2c05682d00d074131030303504017820310150f41e281590003500ad08a0034a0b010180460a000078516108580200d52111103408580140f0280d501105905450100d800402c900400d80d502d200700d910160071003945240f4041000100e10f140a000803166050062a0002e040045111000c41420b84603843c1c07040d05540300c4d06102c0d10340388111229501a08204009a490300e0076281c00103009510400c01030501c070b21500401d04903680c10740c200c00480e0340080e09100840400b00220001c000c86059100a2040c030408541940078940240c000c068440144c0741c11a80074103040281140301c0f42c4855100d1816500e11b1140000308001980c14020400021901e102540540c40c4540f030098403940000034295550300020107070000c0d440030181d00b480009a41050780c05220f00031106c10303084c03035100c9440f13080c0720800c80035100c1410b1295104100d02c0342e440043d6880150b02189610b0140b0043d9100d040043c0c0318030403c2c03000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 281248857 1250 281247607 281247613
    0x80c070b0115080601110a0b130818030c0607030905040e0120070b13050309120c030d0c0204110702130203070c02090f090106080607020a15090c080a1101260711 71
    0x214400c1140410050b804007103960354005500da40c1c0066515041d808903001454101121000106007883c8801d42c20920282c800c4103001441d40782d290305a040001c60f03906541e620008001946010440b940c2080d40488149140502035580070f04010b007648911740c041c986804414045000c29400003206000308860344d204540d0b400300300c101c00d41c044001140e08000ca540840c02c01c3d50748110039030301c3c1303030344007000b50f04d003010702010001d03456111503031030784984950100d0140980701400181480001600d030310344a45440d10404c020f030340d02c0003101e074101c2ca01440604c000d6600e0400e980402c00d41c28400603603075115440c04035418442100080d4101203071409014000b40210348103449030151100030010180c840e280c40d502c4100035241080181e1005c0e06400c00b1901122015948400441e400291003840399600010090140d10481e0540c05c0400d10106100c02c075200c03400b441c0824680406100f4440d007500141440760081d401100780715a0000d080c5a001d030160106c810045421 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 281250107 1250 281248857 281248859
    0x30020d020f040f090501060503040f0c05030f0c030709020a050403031202190804050f0c011425051c020f10050415050903040501270e06010203161a06011e080c070b01 73
    0x405485035020b80f00714160070740e06200010b2600803030711909040e194203544040c07450b25141c0340d0060110340d024058504032031a00c8002680d5501300501d07042c4440c20700281c86201c0c2e80b90101401c1a860f45d01146c00c40b80104144203040e64841e04403004e483d41418214400143c141d040802030060742d61440c0e0405150151000e481e4005445070312070b42c450780441344075100022500d5202c4500051141c0459105056030922040c0c3c0301c00f0b051048140c0d4030fa240e0020f10405100001c1c012040d0a8407541c000d110700d100c0043c5807440b417141860041c0002d00f806d844d0341e014641d50780c680c071550300c0e03c0307603590b10208080240c000c81c5c0107400500c042061156003801301808da200c0d0f1041c4212804640302c41100c100014045001415080001203040382051601091441014008010504600040000441d40042100300c103104d2401901c070700c1400c2c500303148486d6407000064001e5041c009502c20f00551101e214444005400b080e1412200d5500d800d68551ba103801100700080c40a0b0301440 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 281251357 1250 281250107 281250127
    0x13050907140c010b04290f190306020c0c09090c0112020904091113180209040218040b0f01141e03160611160e1602030708190f30020d02 60
    0x2003070642c20466041102c004246c41c4011044000c00d0752200d1301040d1460040c1e185021900007140080c00f4154040440704501401582c0715103400446d4560380c00308448400d01d5080105204500003500d002c022800c150040d00d80d101d044440c03440c1008000c00e501d004284468054136400748002c0c00500c4561000c0c0307801401c0350520000d050207a200305240391740c0078103e03016441c919040845007804c04c00c1e080d0213001101000420598011501d55503008580901110061042e0302410030340d01c1c0c80c117200401c002080700603404003d503013412000d84810fa6032a050301c3c0c80340e1103060504010032a00701c4046401d10260700005901541e440000044143d0414a0001c0030420720f003d50f854921811581005079000b801481594112000001d040c0c000304000c0b11030807440c17401104d003000807681d15040301c0c1e441101c641840340485514000c3c0503400171112031108042e81000546422000240c07054500c02c0058450010b0740429402b02c000c00a0781203810686800c103095540f000400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 281252607 1250 281251357 281251361
    0x170a09150902031c050a141305010c0206070b0705031608010605030601050d06260105060a0305030f0d02040306060b041809120e0a050901031b060924030b040606021c0513050907140c01 81
    0xa1884001c2a034154026003074040800132a9408e030307003e06410081d14244401140e922900100c05c9070404010400000800c0001000910441c49580c071103030b4071303c0d10358486000032000500c400c05201c001030060143c1604a01541d138000001e1030240d85400302c202e12200641030316484410b61708070540240140909a940d01049025114024000e9031204014840d10010360301c806402c03504180910500780d10b000d002040081c0d1000b80c05030600351240c86034070450b02280d100f1100030400080400410362846440d00c0840398401c0200300302c0040751501c108010402003004104090f40004600301d98911070504042c00000e071a103900c56850f8507001440c107e558010144203240048006540d510440121082c0ca00210f28405090003d8214464195510110384203240d11400140e0715a152441854010070482d40100540b00c16100c47c0341c5007010850a03142007100070400c1040080090b01c15504440d42036901c0c0c1041c1c1e940c5402120034078141c1c602c8003601200001c210f00051015 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 281253857 1250 281252607 281252617
    0x1e04050312160908060606040323030d060e16170604090819031d100b0607020303070b060405060a0815061807181517040204110a170a09150902031c05 66
    0x40c2c1c079808070813500c941c000e55842c1000c50351158046002c1105000141080c06c080c2d1501e44803080302c851201e18040002c1c21500000b10f9942c101f665414200704020b1601c510360b40100f40c4c1080c0920141c1c003014004d1400d00170210000c444900600030415944441d0700001c00319421441c965161142c1c030400c4201c9054001802c00004c0c20b120480e01038980e000495100c2e092400300501c4036001010b090000b03405134400d901d6000c0b00600004000d61024001091464812000c1d241d00303180c03003402c1004445000c1c044600440c0012402c0c801401c000442e00c0d11000c0d00c0744142019940d000010f00b944651711801e000720f0156609000445070404c00959244c8451840c00071010340714501e450010800d661154001540c01c140f5810100040d00e44680050000d4400301e6109003492640711594010b038841c0c0001184408001b20580c1c0fa61207040d04000824406c0c060001e213525041d00e601c521403240142c2c0b50381d40101c1d108541d4104000075921220040303294104100107009440d580103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 281255107 1250 281253857 281253901
    0x31805030709140702240a090f030c050d0e031f0605061606060506030f2805190b03010207050c060d0f060b1b071518030507090501150302031e04050312 67
    0x1603d0100340694004110000040800c0302d84850800020311781c10800720000c0c203941c01c110364804c191008200642e054100003070180c0c413207195460481c03504da45402441d031340800400008404483c401d560101d01c0c11804521101d00310021080100c0c0c0000038409036000c0c55005000040702c1320120ba003940c0540703805000300c01c2002a2541c50702400300c141703c201d1b082c205c0c000c150710020360f4958a4a51200c03007102e10120540091240c14600c50894109640f444a12800c40003a80b601c81083c0c09800c030101420360003036003041010785da90b9a607001003621640c07064801140700441c0710762542c00340c02d501081d0041404400c1e540c0c80b10b22115400a4540310000405121444208600150f82c20485031810110102030074070000c00c13600e01485c203d4012103000d64000010100b8410080e0f0300c05851804400076041d454042d4a8800c2d25140401c201414014820401400c4d2014110604034138120003584141e9214502182103200e4010700491028004052203c4000c140101829081c1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 281256357 1250 281255107 281255141
    0xc030209060a030603021306060806040f020714010615020f060a02030603160b210f0402060d180b0f0112200105160c050f03011509020c0a0f0b0402130c020a031805030709 75
    0x1031300111023942d02c140212408140800c007c101c0a003410341c86604c042115260060801000e6a44c41c2e80d200611450b00545a45a1070240701100101c44954881c92440c001408809084001c190311210b008003221000da9010002071401d8400f4406580b00c44400d008001846071143e6140d0f03001c0e00610780c140c01102c1d41248005001c3d03040300780d6500410514030306180c42e0b5210307420802554030034040144095250807481d030000c0e00031800c00f0040c500c1400c0006c07203031521404c15a0942c805912164824112020f07600204130407241040c1129802068141c071412038400582c2c0a2245c5804034000249143e015010301240d0405142554000c07990138410000b44010142a0341090078030140c0102001c000f000350008540c010f09122610f04152500407026131514625413030030b1081a180e41001000b000218507001e121480d42c409010b908102d64100c40d04000d646501640f401803d0141300d41130700352021035281d43c4000030b00008040b180102c0d00c42c2502c0e03001e040d100d041507400341 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 281257607 1250 281256357 281256379
    0x1506050712030b010c0b0703020904090f0b0a150e060a0b0309030a03051501050406050304020d0515040b0901050f0103030522120201090b0a050f0f13060e090f0405100c030209060a03060302 83
    0x94031a0003120f40c41c1005079a0410040e8540d2036414010401408082c01c2c113500300301030754140d241e41c0a920200d6000e42c0c901884415a030825030700c5541d0003481561500e00e40368415160780e15103541c1c08107544425003020b090743c2d0b400010450704a0a500582c407041c0020081020604002000307000761211303a6414441030301c5511a00c0010342e002c0b44803d010401c24042440001c0c4075a0207180d1041c0000c041905468054480906001e0482c6100e18401e11b28070810003400340900d40300360000c690780c0080201d46008901820710900602000b01041800240380c843c13030035082d405002c0b082d0040d0110040b10341e1401801d44403d0260812808500440400030714000e021007aa208014162a105e25041d5100c1956840b5404a094559080d40c14040d41d210715003082001c07400761125803203502c07000c0e45000030400c00d403a00030b0088440c0a0b403041000f000880c0031901071840004403501290400d500b80c403d0f0064090108026007010700400c0094038150b140d0050320480e4025201e0400c04 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 281258857 1250 281257607 281257643
    0x904081603030e330c0415031d010c170907120f050607020610050108090c06030c0f0403060c110a02010906110c0d080405120d0203030c0912010f05010311030c01120f15060507 77
    0x8000c503407071440080180000c01c82408030b0b01f041e0251080c07078540020407051050009883d41000c081481031030b95a00d101314550f9400a032400015003194070407000500d0045495580da1250740546100707503c6030107401c02040b0321188201610b560080071340b000c4d8909440d00a581e20000c5900007000c2802200005803540500ca4060182c0700b5400541050701c02d04084c010760340d00150010f520078078208480010f41c070f8400d002e0300c081c5205460109103101d00210040c5062100b0700c500c1041d41202581c000142e8200700c07a041160500c0c00d0554969424000c950708240400346400c1e001001001040e04002107480107000391902194400b107100044404940c1c0c0300c6840c0c4114025034410001b01d24441d1069002e08140b01000b460301c7e004420000e405804d43e100c0e1091a05c251352608010303c100714115024042c0310b01e044d0010a4841c2c81580001c020520700c40664003843d584528081c0b17140301c3e0b40c21244040d00214a1008200e5440d10018500c1d4000c107015100441400c50b81805 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 281260107 1250 281258857 281258953
    0x180102010513020d26030901050907050406060807120b06040801020403020306070f021b13060602030306041a0f130603020d03080414070e010b030a061a0c06060904081603030e 77
    0x5190084c00f00c001054013569000c8a0b561290906440c80504449004010268000643c483c800d000008162424182c840c0c501e0501507801142c0708a080c4801403240316440149503501815601e4a92210308008074541c0040034603080d00781c2c100c0400607010070346040c150003c1046034400c2e01150076a58501c24101c5140340c040390204010f811061100e1080310b14a4000700185000801d081ca408071442200421104aa4016000350b0408002c000c503515151182621541c015560485170401c64000154905075051072039104428400d1340100c0388060350b000c400a0369028005440c07120f400c0c200a802e00704111002c4034584d2150104120310400490401c0890307490390841d8140ea42003041001140e000208800d2030140c3e1030350300065511200d482c81400c0c2c030341440343c1c554520609030b071107003010401440c40f0f0150b811401800002040c1200701c5034061440c0c08841c0d521b6280d89012409030414010704441c0d8452502810800e82c00c042140480c0d00e030b07580c4006d511103000d0310b10340d42c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 281261357 1250 281260107 281260141
    0x10f1e0501030804060c05030913052508061302040504053c0103030c0809100e03070b03010f030f020a2309070f02060a18020a03060606080603061504090c0b1801020105 74
    0x10a2409010030883c5e903001c2d000314100c0501ca181542d080540c4080030401c50480c2d09404203103a45c035101400900090400c04074180455001c81c1d4030f9a140b060b0010705038440c09010240903148142010526040340e80c103813005040001c000784002d051521213640013411008640d4070804115200707507007107035000c41200000070b044005028260310799201624a21000b50040d1007d090404c85104684d45180d101c3d1018080b5849090113191a4014140f5041540d00b04065042080005000028620006e407048951090b45008080c1080c80801d5841c0840c0d4442a2034520f000300b0100f0a20341140c1c030b40014901510701e40381564418004450468641c0b402c0000341c0c105c1c00c046240174103243c000400c0e42e081c1000746914042c40f41e0100b100b00e0200e50003519800c3d9613070710138001250300070051a0498801c030014055401c04a080044200e0003100d2644540d035104005e0b410841a00c25030802000340b25106900c03a201025602100000010550b0040d440c0400207864101c0c10005c150b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 281262607 1250 281261357 281261363
    0xc01023a02070303061508090606040903020601120f05071403010c052514070306021210030308010e1b030a020c070503030f16050c0d0305131a190c0203010f1e050103 73
    0x34040d4201044044000c0d070000b5400d5082589450021400304039090105040920f160740b580700c42c0c500425100e05018025003018413450400590501180d1f00042c0c150654001078070302070000b6003500c0c040c80003000c0b030380008141c7d000b0114005146e8184080c56210384030306400a008504120000300c5540c803481800f11111207040c1c4000440d40c8030920f2192009200e004190034a28004017014501191944111440c40e00043c03c900e5000c01c88803169002409038688411141c00c0d0b079006021309005000d00c010102a640008086080d001300110b00d460002180030303924103087d02c0c880c000e0750081a00a0180c4a101c1c0009081d0800100311080301403000482810144418040207801c030301e5203026586440f8520358040e1694a0b40d0182d40400d11984440381c0c0c2e011069034960040c0e469900104c1228808000c0c3c209240d200381c1118425800b0500c080403520074a18213507020080f80320069015843c1061410000e06140d01c0058100240c48609980a007074103031078000c2d100240002 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 281263857 1250 281262607 281262697
    0x902090717060a1503050a060b0309030717160f0602090d140f0d0f0e1210061818020918070b0a030b060c1005091e0a020a0510020705010e0109030501020c0102 70
    0x1e1541300344294020340d00a94400400b244285d545c109042d41074005551075002d9070000a109410010140c810280001607081c1d1103050682e000e4640e20b02c0e450f40a000b41100384000325920030020349a0444601800c000c010340310420050401501c0c4600d4940401c030180f081080e6080c03001d000158449403294070f907440c0d100b03030021008100c486080c6026040d4104014440101d41007005000e0b040c09440301d0600040c10178900141401c1c844141414043c065141c440301030b0a8502c40b10040c03818030740580d03414500d6120041d03140032400319a001605c41d400340342d00104500c0308010060020026a640511110f100941000300354410001000045c6d484800000f002c03501075000a07602000c034a007990350301c441c0c6884000ca03640103c035945c100c6800c08880d0a04601d440c2c0510320181c071003034442d0309062494000c06075031191140600d6050041c00544421540e04c20b004840143d40d208000b9900c50340c1d0079018a0107034204c0841d65141030a003a00500d00c951490010b000300201c1c240007 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 281265107 1250 281263857 281263889
    0xc0201140c0904060314030306012303010311060c06090a0507081b090a0222060906030207020d02090402030f0a0c0f050102120301090f06030807050a0203060f060303120a0902090717060a 82
    0x7888040354092000141c2281c0c80301c40000105041120024954013500041c60740e80c034220b80014020549400300c410003484024030b00341c0b503145400607241540c2d44140c0b5103080422040c0041c00038003c14031816250300c911400c00680d02404500d080520b40b0035021550740c903407216035507034890030411102c0c121124050418141494080010364000c08584c134010300e00b506000340154410090318003120303102c14882c402c1001d560b00014140c014840c6240c21030803c041c1d503000401ca0b003850705000c0c1c1725080f45400300d0195a17050103001230041c3c40e4411200700e400103240c0303004d4900462041c59483c001c0e442300002c442d40080742000c6e44190100c8a0b514607803c0030000300080541c0002810240d503101400720000d241d0f00d0081101500034001011000c1070b51041501e0100010079040300848102c043c46080d4400209440c00200f2041c440312060340da1424a00040403403220195020759000c003030041e450342241a140b440210800405402d568030800e00004507141e10030081c1d08106404 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 281266357 1250 281265107 281265121
    0x30306090b06120c040f06080711010c0815130213080615010206070c030c080d02250203120703020c0d081b0a0c031e050f01020d0c021b06250b040201030c020114 71
    0x43c0b140c0c0301d01c400903824201616691000c01d2402180c0041c0040b83c014028410382d290498035103070718060304070000e10a401088800505112024200d00380c580c10624625807a0b58030b0310103e64103d12088011522010003045909001e002441540c81c41e01035000407411944410030100541141a00202040c0d183c0401c202c40e1f07442c01203000d07010130080d41d058500042c0c40e6001804000102000562140e09100b0544600354201c0d40c0c005000c8252102840162008140c00d508180c041e40e4141e190425410281d05026011a07895807113181042000c0c10400e141000d00750384000c02c100d025000564132001307542c4440a44e4040e001802c03440040000408482c09001005c46450700762000f92140e40d942840c00b261265031040756500420901019050352080703000e24040e9200270400041d00540451605500c841c08074001e150001d0008008000d40e401c190f58203200440340340008410f07062140d03800c882514100c1c0007a08149141c0310140c8140503854907000c03c0d032288810382d03c80c0c070707 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 281267607 1250 281266357 281266387
    0x50705010c0503160605160c121d04091202010c0c0b1311040e010e060603030f1b010603080c01020a022b0807110d02010905250b090d080304030c030306090b06 70
    0x14200c2d0310388400c015803d800d05120141c0a221481100003140c1400d28080b003005045070030101008110114000c0c0d03000c254820880130780e0180c02c0c144070700800c4003070710361140110b00d441100780c0103414058000d0412042000b840d0f19080030794000c000070031209a044582440008000e030a1f1646600820400c030602099079403002d1240744920355818181c3c0c00b00b019601c0c28000704410340d54030200501c688006100b03aa5200008901031480c219444000903041d025590004150004120140244ea0320941c05840603580060b0080d48851003210894040d600c100001c0005002e0f242010b104040c040001260203000000140c41d85080700508840310600103221008022556040007032441c0103010160039000302e46d001017200400c2e418000c0c07501e031181e20900e0319000120300304041075110412400c03d503548000c0266491001d400000c00d40b65945030040c28a00c00001030000f05900000300904e00361087e1000d0007899075445442d0100c5880d40401a00030404201d40400a6811 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 281268857 1250 281267607 281267627
    0x9010c020312071b0b0c2a0a0813171f05070e010c11040f020403030908150103020d03020c100302030105040c02010b060d0207080408030a0207030b150d0f050a0b0a051803030405070501 81
    0x710a803180794130042e46500414003c242c580e82101c40c8002000581500720301642107151045111800d91910400000c40d550289114080c122900c08500415400420140d07180100b03000d00c034840d0351848010303549844a80301c1d003040841c20780c42c62a80c4001d00842c040c079481817560782c94004d510200480199080108401c0840d861150305840c0a2281e565104d131007a9000c022100580313a50862801500301748880d00b01d5007290380141c22480d062302006621505480d4159507a089010041c582a4a00712a8046040e0301007008940040f03413552690186040b900201c806000403424204142d0881d103039540b410350009400c20940c0c444807100d07001000300764464500903140c03ea46140040c19500128461030040c0c0141508109001d2221800c0760052442e80104c4210030303a100004460080c0100300030480b60564403034606101c410310078001c0044d00b04840824600d0014400c034010042160340003030f0841035110610401d1000000d0340d101e55400340080a0050a01006480346000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 281270107 1250 281268857 281268887
    0x20c12010b040603031d010516060b0a0305060f1e040b150f0a030503030604050106080c04180e010c030c02070f0b040b0c010e0a050105040204182012010c0809010c02031207 76
    0x301c048900480d1100d02c01c0b80015030080c3c0e9164181c218034080e00c0c03000c180390300c04e15042080510405111000f43d805507000c40c0e50218000994014030404200955200d5002900c54000c0c0810025400c18070a88075102e0030900c0107a241d1200346a81c020201041514084c2c055a060130000708910141501082c40000040c800821702215400244502800f90422103041e0000710510800e41000c6c0200b42c090b01c55420104c80a141a8054803a14001d9110b02e0440717281e00e00300000401c0803940898108041c0ca8001d1062104628019025011171a6800014440c0034070008101848405010940c1c01c4800c410307140c545415812685500301e01e9480003203541c1d0700007407610600b04000c00070f20746115900100b410f10300b50040000300c403c00d1501e2403a2054420309040043c107180243c09541182c800a04925000200403580034031050401641641c40c2c4841d110201d5042600280b00c0c0002e04020710840c0e4903084200c0e141d008545094864845080126080030f02503074121143c226 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 281271357 1250 281270107 281270111
    0x60901060c111f170609070f08060d060612050c03030903071202031507080711150708070c051902040f0b100819020a0801090e0f0c1e0a03060e1507020c1201 69
    0x1c402e071240d400c48102a00d42c1c0011a050510803100401c100940d6988240200d541c6c0386285000b007800f410600f01ca002030f0080000020004440380d0f60001e00c036a4040d0810020050a0b4a55a0341140a2901e040540f041c0c440c000b40c0160a1900204640742850054050034030203150411040a58080c5c4004a070b03d401450140111035000924161260005a40d04a02420099806804030040100c8036100c1c0c0c128041988001c085d10a019070000d609191060703082e903807042c08a440e100c2c1804000e00f60300038025010300c6482c00d2010759500c2070084408010203085038501030101c0e90401d83c15500080340d031100d2000305014002240c1e0066100c07a1518240e003a24021404aa009542d44404980c881005004030340c9548501518000305000070207408a0001e40c40d40c0c0c9030149661644203c20041050641c00181c0c8103020600c200500311440f11364603403900b14090401c103218080d17548207244100c4401c0445d03104141c091300c02900038007440f104a00074444c0004515200c5000342d9 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 281272607 1250 281271357 281271379
    0x40b1602060309010606140306100f0e0d030801050a1403121605100504030e0303120a020c01060302120706030b09012706150e011112041404060f031505060901060c11 73
    0xc1c80380d100a51151242c14000100c01c0d090400140090200341c41c0884007000a004100a82e114184441c1429031642400395206000e8201100c564040c100e010741c00c481088244410560042d107214140c80d400c9035040f10045e164084041360200002c0e44640c540c1c000e0f00c0d51558100000d0003005500e4801d410001304100310f8440306c0c07400c40800381c0c00300b00507a2041080f0605a01907a13642c84288110017031864013948139038101c441000980801c0d6110360004030410010000d5000f90b0080d0b070f014040b42945007141207150786030f07901c52190b403000c2410604441007624000304d8141c181d40310514000c11050302c006a0b18814403149401d11040d42d607a032008075100310391583c11005401e26640748070440c500b42c800101907486a0407401615408034036840413070200700043e64182c405202c038480c49400c0c281d0004e0040c000c250301016582c144502c020061164000e240c1c440c9164041c4144601d8403114184450600c09224900c0021034000200001400e040c030910f41c000c500038030024100d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 281273857 1250 281272607 281272609
    0x160909020c1618050c09010c03140d0c090f05010309080708130905010311030f0105061804050709020418150b04050603090708060109020901090e06061209070e0c0a02061b040b1602 79
    0x40b09141d0000341c0401454a6410110555030003000d0707103c00804c4040d401c2c2890980040c1182c61016002014442560724803078100c0c9503603099640d5070500d44024443c0030407108010340b0032000d0340909041391652010108055010780591075202e07900c803038120700d410200d4641c0d25094000d034510706200c0080303400000e0701c00d02a00466018500502403265100888002c0529155044800c4483c6905080c1007240c40c0c0d585c0d00000c1c40003908080e0300c0c0d030b09580d18900f9a003000c200d42c004000d458404074001c903055103010080107d0400928081100c40b003005000790345084540b0514500100401052189081c01c41c0a1038105040b2012201401d450340f2840b030070400309820a0b641c056000c508004c07a0760380319412100918903000d05010f40e0612501040c058071684032441a00c050340c2e00840c055400c100104c000501d090034103140326051020284040d17030f001c0200a0014810007000c14803039801c80000165041c154501c1d580b03000c1c82e001744030010340c001d0501d51030100c580c000e40e9009 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 281275107 1250 281273857 281273893
    0x11806031b08150613090503070f0605091e030409020a020a12030f11090a15120e031e0c0a02040b010201180813150c061d0a060e0105160909020c 64
    0x40840d40800301c9001c0e0742054030240c5080c1d1000250901d4015003002d1055985840c804450342d110b488901055486c4a81405461440f171600d00074000c485070310a06080c0320a5500c91801090424190340f0322031200510718009002032040c02030250010031040140142c1035006255550f082d0040d500c1c20f0044d515020841191002c014011944903c0050003c3c8502c4c0304e0707114a1540c0c0c960003810100d212012419444190240d040410406000100c14a004d2103090b00ba210401c082800011241e080160f00d035080b441041c0a5920166520100c24080700d050b990411021030081140038499002c2002034413000c2403044c15956503402c02191802c80306d01d030010240c040e82d0349540e69515880c00b460398058a40c052000010450b1210b0f41c0309502c05207659140d80c02c904c01103822a100e46100c6d54113120304510108130310a8000100802c44250400c9507e5804240200b220740c1d035002d1340b0f14040003c1c0c0782050015081d58000d01142c071700e990240c204184030b0811108100b94000130010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 281276357 1250 281275107 281275133
    0x50303041101090f03031211040b04060c060b012a211d0102060c030c0d060504020c011b0807051e0408010213080709060506071e020613031a04080301180603 69
    0x898094904841d0300c6940c200e03120000602100390b11810062968900801802c500d46072060384d942c840304242ca801e900039050300e000c3c03c2c502038295982d41d40d6200c0600314100140003151a11b08105202103a50f02810405541c1c6800c0340c50090128000c140402080c00040c5080300c5907442d180210480c0002c62040400080c00b076101c1c249a103076544024000410030342282411980700004101d0405400001e9a4002c0c83d00104191201702d110450740162042d50485600140302040368625541d0541001e00034110341c0e5101c1030b039030740c40720011200104120ba100700840c808021407200c501080c14880148807a0400c03007418103407911221403c0e40d016040c3c0741400b4822540078419940e046c41680000d1880e030304d04100d182d203020003145450284200140142d000c1140743c0c426030b07014000d01d84603a075004100769aa5910090f64004800700da0200759840f50f83c1c002c0c560030484641c01950f0056802040d028256880c01c038084d40d00040503140c0500081e02d0f034500000180c0c007446508 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 281277607 1250 281276357 281276363
    0xf070602011401080111090d0c09050a060306050a050708010b0d02041706040203070b090a15050712050310050d0b0a0902210a0b060402070f0312140405100e030309030306011b05030304 81
    0x4580307441d0001c021120444184c2103403d65900d000d10140d5518090742c1202c031128001e03500c0e80b4801c031060074010380300c9001d5400300d01090f08010400645002c03550100054a109810801250301c40c50f0642d0110f0f641111f00502044016006004d9046c120020300440c5000c4c000c09403030140c4403280100c1c000c071048140b520701d0348000300303000031480c0130310031000680040c1c16201d0038241940c0c00180680d00300c0c030078860410302840070104907900ca401100c48031500245038601031462541300078000d920440340207a0f60a804100450315141844c10800d81c2a00002079250310340760301118800421800200f282d00001e0506d209500b01d40800804082c580018040c00c1040b8580c01d003000c7c41c101c01007a9030f00c01d6204111090005a010b00e01461058051908030440703420604081c2c01850b400650351056885801040304200c0d001442850b0004240307410702c0350000300019650b9030f01040d1a8040750381c000703100041495203e41207064459661140020b409603c5842c0c40f401c41d881076030700f0303 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 281278857 1250 281277607 281277611
    0x10918021e120313150c050d09151403041707050a0b04050607030e15101e050406050306010f030b0c0f071118070c080f07120f080a0b0609010f020f07060201 69
    0x840440c03400b54454801e800ca0324018500d040b1010503030419000c01d03406441d042844000355903565034450100b044000341d1000031070300550007203000505803429520400c0f8030030010b107031140c0c0410f00c03c1903254454156000c0403415916a540c404140c400c5041c1d5110843c0000d00030031000c41c00410002c00d996024007500c488504290070a6800c0c160010000401d150801424004950000038403c1161803d24604082c070f807503112101814074155400a009a8a110704076860f20a0403620a400c84008a4040100e580d1b01d4040c1130310741c5024450194010030012081010410301e00354580c0c070805a54080c1d240494072141c035070b40c580000406642d0324100300072190484c1000c40303040c09003801070360505040b482d0249008251007003004005009100100d004403154202500340e8980640c442d49110b015100c0c01030081484c10f802007040005403502001c10f5900388103204990f44a11302030103440c5829014001520401c0c0d40015400440c80352841c2c940c0700d00300078030200300503000320786c00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 281280107 1250 281278857 281278909
    0x60621090b0c03420a05030f030a020601090b06030c0f07060c03060302030c0102280507030206040816090501030305090603061c0c14120303012108030108102301091802 74
    0x240c110514080000030840904020381100f400713800c0c413055800101c40140141d80c4914a0010031048081e07580440e42600c80d000000407001000b00c050142c03040150b003120700b036030703aa0807552041e5205010310380c1d0807074402c00100700c454000703a000b0141f0f0220710b0f00311881d0254994072601114900110100040d41d60001801149818403115460140901c01005071a40d60508620071029603e00c0b03903480c0381045040d104000c810f006c500b000319001414203481ea90303100015502d444000c0b00030703d00c00c50307902d80c00305d5031100a01c103c2d4142c0345c0560b501401c12065005202c250381c8040c00d0190321800c0c001080b5402e07920b00c49051030107031280c13030401503640c1f4101c869111000f0302c10b03003203100e91300d1407020200401002069030304541c220701c03400115100100a000a09041e140041c102c0f11001002044050001454a84075400d03103004010f060702c0c8007020140b0404058007007200358035860040000c000c0a03006555421900c3c500d51400c251181d0004640c0c1e4814280d00301514640d420b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 281281357 1250 281280107 281280121
    0x15010e011115100801020724090501090605150a0602070b030705040509040f2603040f020d1208010503190206070b09010e07031a0112020303030a09031701140a09060621090b0c03 78
    0x10f0310070040c001c01c030095050010035620507041c8542001071040c01030b80b035030000440148a0300405290340c0c1210003040400c0706e5040050160404940c2d08407085400300f15500e0a061604c203101c2295855806044182d0405010507595400a841001040700c00e002c041031a07a62114802c0c0035038442c0400c409203415a14000c1c64845402100b0b103e680c518004800728a0b0307591084960040d03001c2c025404034811440051400082480060220b03020b120440038141c0d040041d180c160394044003110b0b62042c5000c00070f045641c01c02002504684180207105c009050b5414480c0c11007003c90021440c20414a815803070100103500640c0c205800302903003991600c1300103c00c0d014208050310401180300603008240d503031201415612040f42d0701d8110000703151040546030491090009000403650f55003801c06900c103a42c1c49554450250140001000380d007900c200c100302d6250342c655141004240907a02d10b1142c14a81c101d040d1901c0e141f10747c0004181007610f5201d0071681e8101034070790400301 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 281282607 1250 281281357 281281381
    0x1801121b051825050702011103041d09010506030105041106030702011d030414030601050d140a0219050102152205070506030f010f0f0803160204021605010203090c030615010e011115 80
    0x18080310000010b690800340c0d43c0d030301c034049451241d02801c200b1003480054a990740b03140704039404040001d030250034049141d0000303920140a4900b401c020b1009031160f104140c201c0c2d8040e1002800d070003050b0700204a5007800000355a1216060000044828800700e550b102c9414080e01120385810015050005a0030400560035201c41500102642d40c1003070301140c800041840040c107001c0f140d03058103c080c003007002082860783d4090a800001d05803041e034968900610702407540980200031136103040d0405440d400d8803a004003103c0308194003040f41420103150300d2000598045c05140d8002c40da6484401c02980203e9101401c010690301d883e62b00c01170184142c00882000502c1001009038440000c00c1d213a00c200007907880b03460000f081c400a0001d2142000c482108984107107220103014041d805113105110b031005840901c800300c020580c403580111200031505034003408081040d40315216048039450306041064110428a14882c40c0042004403100a800101d003045000030030700c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 281283857 1250 281282607 281282641
    0x1903050a0f05060303070224040602010605270f0604060803160b070f0918020705010f05070e150409020706020f030906010303140403050d0e0310020f0301051801121b0518 75
    0x10040402c254203001e40069224806c43c0350103442503040d001b40d82951000440110090703000c00760081d40d1240d980b41c001c0e004e44a240302d120300c0341c007481d10401803120b04a9910700750b080104501610b141e1b80e4103e1101c001c1c101034844ca8100da03886402059400c0100020800000c44030f40000717140000745441442c800008010008100100d010410215082840c0206860800a010300012841c0804000074092014094500d41c00e022005c4800c0041d40d2000380110480d81e25204ca0036400418132003048449445649594001c120401c1189656405441000d2141030098030b40031090300e001000f80c2058420681a41110004100301604902040102181250307400e041910b9034507125160f2090304000f409001d00100ca024080e5400d014240c1c084203001001c54686030701c250003140301e070400d0141c203019040c01d08005400000107142c0a049070801c0324541e0700800340355911400d0b241d045014030000c1814040200c3c0564651881a04401c0e0b869410249860071104281b19103801d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 281285107 1250 281283857 281283881
    0x7140703021507061b050705060606090109140f04020c15162a050d0504060201051008060105130212010b09040c0f02070501050f040308030a06030311191401021903050a 74
    0x1040141c4910a50b52900c0c40782079101600e644860401c070001d0004030381e5408296000b20640140b00780c001001c0c14103640160120b465699641043c402e0502c038954155000c1950381310308000e480418105040c0950003c1c2255255201040109050341c010240c8441a030304100109000c10900b6151a0b40c0f0007800034003150b0680710b18038042d00d04420b401c3c00d600a041201740ca1031955151a04401243c1e074400101c4c0c88013001000e005045400c24041d500046d4240f01c003040300b4440e40101d6009883c004405001503034a000208800c0e240b000b050948215020b10400c8541030242090b14001e01c44a020306644844110821084406206140c803d00c02d00e43c18051150358001030001c01d032002070074907507551005c0aa124505004540c0024503500713002007008002801e68002d08202ca21940310906261400c0c82511744640580036483d001e043c03c440784074081540080f84c00c00c411075031000107140c100e010882d240242071110b0903201080e100c0083c0100c1c141c01744601030b03e41034 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 281286357 1250 281285107 281285113
    0x31a0a0501140d211d0f0907030b03070815060a0b0304050d0503070e06160c0503062202120d0201090b010504090b160314040c0f090501080c040c020c0607080714 71
    0xb0401140c80b140c01c00e01c441d642d0050a4414011042054070b40c1d4030785440f49414000340012140d603c004160040c940340150080c8542c0420300580d062600254410b8040106075031100d580e8103008400820035000c10036498130400200048150040c0104021061202850354142c90f2072030601000c00b01d15032110403070384000c00070080403c2009c43c54220000c490714102c8e079a6221483c040b40c400440d0241c840e80714100069110614005041004626105581ca851080d41e0b0308100741e260441220010a0001d081100e02c2d540c420b000d55261381207100a1100c000101180c80359442c1c0b039082091000580e65441c000014404070154403401428100e6080c0720311241070307486a541d89405044200b000010704881010f440c000c0d080f58a00210602c9954414039160420000b80c4545100b5881010304480c408909140c2c2409064140c521680080404646000900004011a100c10002c5008484000300950354004c010000d0758081d5240c103460702c4490820b6400c0044200c500341550f8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 281287607 1250 281286357 281286359
    0x606060915020d0f0207050a17010c030b1008070207030605011701050c0405010e061317060f07050a08060931030908030306011407060e120c010b0f0108130615031a0a0501 75
    0x1680c0000c08031800402c3e0324000c1d00d00180b40344142e186c0b1000750003480d030080c13002201280c0b0080180c40d40e03c100003030900034032582400c0c1d003082d0100d441c0552031030b8210044c0e503040c800c802d01611001d608440240f04607051160340c0d840c0c8908540080e0022480c3c170020125040a001c0b0901483e504000140347c4140342c5868040003030300c41000c1421541c040d45c0c021880052102150890744001d00025101000c0340083c815181e44844088580c0c2e04451003800c00710301000d110b5400e0f07070701e00d080d103413a4140b0545500c002c104030f00030000e0130441d110501040454500d90200c0c5c2002c49200c45a125401c00403140ca005401c010858110385925401403003040b0442c1e03408000d20070750011088220b6a18103850422401500c1d0f0b00c0550002c81c462518480c54007220704000740b00340c1039010020021a034145042100c41c2107054246400201e6981c0031696400d0214103c001c040e21a0000051b00410385941c000b4075a07072580140c440d1450b400041d50580c0704a9201a4403221a2504110135 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 281288857 1250 281287607 281287649
    0x180403031406011e0908030406090608070504030506041104090c140a08060f06120f070b070b0a0e0c0103180507030c03020102060708010f090b04020d02120907080a02030c0402130b040306060609 85
    0xc00d12130050386a00c002001812003040c06400d0500141580c141500d9035140c5030b0344090a2502c0f2480780714005408000007852042c07041c025181074a6100d8042c00700d54865403101d50f092094078803800e5006558107950703000030b00740c1c02008005250034520581c201441900304490701748194400c40e100c8e040501007150381403550f4222984804100c4505824800007403020340380c055a11100981841280d401107420302108002d003041c1071044054800b180d541080c14011341c0c044030b880e003035594020303070a202c41c944c02a041050501416070317086030f08503030580ba124941980d40e1300a0741ca10705034050900940d41d060100c964408500d040c05070455140082036400c5c02024414041484c1d5a64110321807030755940c04880a00c11548000e545a00a00c5800500c0c1002540c500c082c82c840c1c0c400000e0440c0000c1a035200041d00203001d08006810340b8180b1020f5888401c035103072003a06140c004510403100e880544080d41c01060006401410124017800d4108181c0080d44203040da401041c4034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 281290107 1250 281288857 281288867
    0x60907050c0a0204050408070203160f09090b131103120417010c1b0204020d020c01050603010605010e060a030b0d140a03080703110409020c0c090a092001080c160218040303140601 79
    0x10883d415500024540d59605040b8698012010025410300401e18011b600c0a02e80020609603010b5510030304083d0b503141e80e00c82c200e0700301c0c0100a005209080000341c010300b818101c1c0e032400340aa083d0201c032048510009043c4100e848141d5035090f0089020310001a201d400028030802c0c07103000308400c0e07840301009400c9980340a00c41104901c0010448219180c1e034068074100d00881c42c055454001e0020424044c3c0422107905001790310300240059550300c10700302043d02c02405000e4500d404200d81040740070303100485540d03400c100081c0d0000005000c85c00341f041306d80310f4507014041d9524240b80092510401500c84002c26041c1000050818901c0381150b00320382c041000142d44100b054a07850a11109000140d0300410180030006080c10760341021a0241c40b40000032440f1031382246524000310140207050001e21400009102c040c5100018084085604003883c03105c0f00345c2e8001210662100407240c0d24a20144c18401015054000c450301e40301c0d81d640c0e004481c80c1c00c0c000240 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 281291357 1250 281290107 281290123
    0x80105060f06040e09031606090b07020703080d0f02120901020721080606072901080f0105090307030e01140307120c030b030606060901090b0403050303010807080303010f0504151d060907050c 84
    0x5040070540885c1d901c0c9420400c64404e0001180605000a458101440203151141c400d1368030101460004010610201c1c2150a403580103028034240b1300f1030706c201b100902400014199041d801c00c80e241c01b1010580140d81f08000720000036a450107203140c40440070b51080300442d0b0101c20707054454000340d003018016510a0041e80e84644442d503a003802016503080d0324000320120341d8004500698641c25003034505942c40300b130850300042d541c640d40600301d0318100d90003601174000740102800a4414810105000c0c01458100c2c9088030340340072131100b40e00c10b07507003003000c2440018070841185060050b64260f05660400700089140b41000c2503ca120060656200d00400074403981c1c9a0300410562010344552450b0303030346075034a902c0c0440c0c0e654004e008800580c40352000c00100401c0000071681640c900c5c8007107000751803825040c80090f044070300c0b070b1031441c804140e40030030303502140742e11101702100707170308400c981810301c84140111500042d00101c108402040668901000012400b17 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 281292607 1250 281291357 281291369
    0x50a051c0206030c0421020f0109031a180d090f0512060a051f0603150806010b0a03050406021c1a0307060c14070e160809150117120a02010204080105060f0604 70
    0x183c3e2552401e500349502c0c41603400a07941c3c407400e6840303440040c62050000a120b4170a03070300c120f031172619400103444003155488010000101e00c2001c0c10b0101070380c40e1f400d0b0400c118404488811a200000c07074203020034590303100f000400100701041026000c81104005002c01d5410401c3d40c8240310f00591a400014035100301681c4a41c00700302c000016007054151800965013107a8a2511480000c5c060001611100e400d4040d003000414816000324410381290f0920302039a06e008801602034014100040c01520310643c240b001032070382604401800c01c00e80340751100066140c030031156554588464000c2c00c0c080c4d07014500501a0a400010b0f0600407504032540072003da00c1c4883d103d2600401da000305900021920901461000724503c40050322415115045280c2d540481c8a688001e10740c45050300a41a02c0100300b40c0d80c80e04003409040e00b100d02919110180c103042c1c0030707540d401403010000503036000404100303401c0700380701d090b0b0451011900c058000d02c3e5400002c0c1c3c0d41c05940101 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 281293857 1250 281292607 281292619
    0xd020a12050d1e03051503030313021503010e1b040f12151415360123040507020f0609031c0e0d050a0203120a020d0e241506070606050a051c02 63
    0x100e50401c0141c02816070070031000b0200ca0f0f27a03251004a900e440007603c54228012600c5906840e070803d0341c1c406590594400324000a031941c1d640d1071075003408440164000400c0c008000c080f810824a090440140055400c440f101e00000d152118075100b2417041070454a1503c807515619020070b245064125800d11178004d82c0341c50040006450080c0c240c1c00340d803429070042e040b402d0f60480d5249c19101c01c0410b13801d007210380c0e80c3d80310001782c80f14412050011042011f1021010307291039031005c4e810110074812208008402150249041030a80d0b456051350b1000c2412500c0002c01d02800704c0c00540c4c4030701442810b1011048a689041146501c5c6c280040410b01014041c400c0040e180c0050355200c618019061a0324403030000c0d40402c0c00c0c0d05110b8140340c45076218550008941e220322411100340c880601c218400c41540000190411821070100f542c542c21690302d80000d4001d0314010fa100048052410b42003028800030360b802540590214011480c0c907454040380f00811036019180 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 281294964 1107 281293857 281293861
    0x3030d1b0f050412031b1406090709140c030a112b0501060c06051902070503030a1b0801170a080f1305010306180b0d020a12050d1e0305 60
    0x7480c81c01d40340760311040d0020703101b40703100038001c1006070000b1004401a81d030040d010318917014410582d0300c401c0c01e10150704018850800104600705d810090b80d040c0d07801c0c442c0d03010801091505011804000075031069100c3d0811b50008541d40300469540003484607403803007036210800410005890b401300011920851103141e05841440e1140342c0d100748590b907500c01030400200150605062021101e0007601980080e106540c814400341d501c2e0b1910f41d2850080b1641c0300321400240f0317075090f00e03d4101604202d9480c1922042c0d03c1001249131003954441c9096400d1070002e14080d00007500c100c6000b104009003081d10b01d40786145040341d0b581d2004600350307030203070084003180c40c902c1c03c85c00300c10781141d4010111908007a04642140905400107950040075a002d501d01101c3c1401c0309082100501c02105507032440e0918406041c11141c00790207008c10040d03204141a50303000 = true := by decide +kernel

theorem cover : BRFrame.Cov 281115107 281294964 := by
  have h0 := BRFrame.cov_init 281115107
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281115107 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 281115107 ≤ n) (h2 : n < 281294964) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
