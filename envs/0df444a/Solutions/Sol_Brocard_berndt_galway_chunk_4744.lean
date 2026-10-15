-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4744
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:35:38.379619+00:00
-- url     : https://prove2.me/submissions/0aa22f12-efcd-4722-be80-b4516a24878c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 853057553 ≤ n < 853237410 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 853058803 1250 853057553 853057571
    0x610050a03110f190e090613030c030c03020a0803010305011b031104051903060516020115030f111f05040602010608070602030f03040606030c03030503150f010f0c060b030a08040f09 80
    0x14040c0002030b51070100d6002000d4030540300890011204103400200349a110300001440c5100342242601540040341070301c0059a0f9000c00d10924410b0360740060020300f0030000000840e120741070444566219105035007804010740c840301800d0b017080c0c00655281c1d42d9841403000c45090465640340d01e110354101446082441200c850f200c4c000c903c60b0314000c603802200da20056102c4644070000d9640803404100340c0c180101c140c01c89542c024a2500598030300480104006008031400044a1f44540711000f480110b56650301d05c1c60b0b4660410b0341240640d02e1040c40d400310740d000000c509400d0380d2040d48840c0b0f00795000b400e4840c59404180c83e5000344000784000d0364044101d407580762046000c0c0756651124500800180441c1e440540580000a408010554020000e5004902180c01d582003040001d040058400c042c6041c1c1303011a04400d0008107280c06140210784407802610300140542228000c00d09101135440120345501c40000c00f403000c418400e094101030f019425080050070701c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 853060053 1250 853058803 853058813
    0x6030f18120d0b010921050d0504180c0201020706090b060a0e010e010b03060604150903030801080105070e040b01020c0409081e0a020303040206180d060501030506060f0906090604090507080610050a03 88
    0x30412031414402074840010f40b41c142d001e02148030003000c0b60584040254048003552020100e5958229524000e00ca800340b0294461010703034081d41c00385182d0b005d00016005180e8020002d165422003555024031012000c600c00b07224510405020704449202868034200700700c0340c1d41094026007a05080c100040c407000c02c0680c4c40a054951040c48680c0e292500b1000518a0295500c00346291805440d0001081c2c1d00000c0c0808682c840d0300d0f01e00003640c84951090036a02c0032500d40d030000e40d110542d4071031481c25410a20503140b06005a405038400103000c80d050300c000c0d52040c1c0f969080000e2030711003203180400031120f0584049025050189490009440342700c0684080d100b0000810540405410000729106041d4000c100390400c2c203907441c0180151109100580355400790300300094050a00904039503489034001c150a0341d641e41c0504104e003801014243d5a0800c0d5500746d407000081d0308001d20301c045d1034443d008103880d2805001800005415402c020301400845404200140c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 853061303 1250 853060053 853060057
    0x9121e140607110c09040503041206060e1302100c0213020406050414060408060f250f0909150b1e030106120b01020c0d06020a0e0307090605031002090d08030405010b06030f1812 78
    0x12621000c46031100d0400070703c1d50040303410501e03004188cac44804081043ca40e110500f00c400700015814213958906c0c1c80f03ca5888404000780d045030900c2016001e06105445815245200400191100702090700350403c9030820b41102d80845c0e40082c0610849404500d4000402011a00f8500d4242440e8070140c0700c80707001d00051004185800480c08003050421003040c00110b0310002d0000c050303138010042c41603800d5410b88001c00d04003100482d0911039400307100102d5450b001c040507014078100081019511804c0d000b102c5c40c0b0740c60030040c02c44810400950007400540d4a182301a640649000100ca15554800d4155404a00c821150341c603980040848207421001c0141c98098044059903e0155003a44903494001c0080100304500194003c00940e14181d00b10741115404000c90b40c124420418403035446828100c403000000c2c5900c0007903034810320880c004140c40301c070710012801070f030401c1d10740c5403194440404100096650402508050509800500d840d078926901c12010b4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 853062553 1250 853061303 853061323
    0x2070524040e0c07120c110306010b180103021603020a02090c0a0e0f0102033f0105030a1b080109030302090414130b1b1903060b040609121e14060711 66
    0x110340501c001a810f901e074009403120b49400080950700003400143c010100c54602d0000c440310611010310720000c0c10001000b030306985115420a00e02500703020015894240c3d41d4000b03040580810191319040c020422501401d4800d400410142d0342e44c0c4100440c0b040000e00b140c211010a01c04000c003154007070302c21291000296945601800b184004038110312403c5400349a107803102d1400f050340290310000148d40d0b000c00700790880c0c4806040c21502820001e12603d40e00d075202c80c0940002ca0200300c201c3d2000c0090741d4464070019503c021103801d44650a03429008658003084281003801c0c1402044504440720320300070228a06129903402220b51148040d00d0404250001808400c541c42c4480c20001020122034440f0300031490002160b0016403450300090512400043d0500c00c0070a40b4152013641d201e910006d4100380c6081600c00c0080e80541e5801d10005021a1020303414050078851b500500c0d83c2010b03442e050130300e2440c00d400500400c0400c030004008140c00100410344c0442 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 853063803 1250 853062553 853062569
    0xe010b061c0213120c0305100605030c0f04150801240501020613060213030503091e0a1e05060d09031710090b1206090a0b1e0f061f0207052404 63
    0x2108194154010f1410464008480c2c1d103800c104960144014020807208881c0300c3c9048805074200304107c581606c0c22441555050780c0401b5001009203050700700b18501840c041c00c009400020b0b02900700b1400c039030782e1040001e42d5480040c10644040d288100302031083c80142e21403113514040000799944d80c024050030444030f05040d00000c04c040d9404541c805040401e030720440c3c03610307400d195032680d04c0a04658802c0402580c8295152811603440d4400400107121407a101c0c5403a0000d01b1280210a01c00d80d4103980100114141c0d039070a019009050502c800054402c41c5403801a01d074484074012482c01d1204041004180c03080003525100f80d403030b03003500451440908004680d00c0c0c0d4110130105400d0140c04100284070707a0020781a1380e01350107541000c0781030b01c4620490000360f8051740a0400c0c131518800082d118561045032640041024000001d241c15070100c043d418404c00301c11400603002030a0030030a51030202412220240032021036469000304007801c00441c46944205e4503 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 853065053 1250 853063803 853063807
    0x70e040308071803330c0f050f07050610030201030e0c090a0e0f102c030909060d0f060e2109010c080706150608012c090a0203100e010b061c02 63
    0x600004036410710320003960300c800340500a4000013004060341582c0c607400c074000e8081015211044a2030301031124100b400781c9407a071b6007d4101ca412146513000c021010b100000070400940059010898184600034090303c0d80c0556055100040c280d81415110500b103500c81c604c0b501c3d032a56900c0986400012049000502190448245003041001c0c03094943e140a03c00701550740400b16080048400d000342100940e0410b06120076800da01e0705c50400b003c0b68001d0100b940d0714148504260b41000c0014034a103c550384954a401d41c940f00350f00200c81c1aa00e40e080314840f5402081b20f06051003c0c0034841e00c1d00b01c03003460401243d0084144241c10000c0e40c140450501064600b182c601c2508040b00707010040313515011600501d4184658030004000700300008900e10300c000c4040700300d9031960282114490708110317501d41a90140c070b031000501450f64040c0060b501006508809c01c24044086940740800c441070b42101d0761250068014102049841c0c8040e0160300c0500c4030500c402c20042e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 853066303 1250 853065053 853065077
    0x714042c0a0605090601030210090f061404090e160626070302041a190504230a05061b160501020601030b0a06120506040b06061608031306020403030908070e04030807 73
    0xc1c50301400000103031541d881c24051186881012a809068038000d44c0c41050780e500f459001c40d4000d10034030460424025900d0300b440440d1140754140310f440d0740842d0807402c09488101d440100c40151003948003e80c0300b800c0543e885540441a03c004105a0400040005109020281a51180d1801180100710000041c01c840c041d81c1514050800300210250000a40465480541c44103c900b11b05a100c4249013215500c00c8040310706503100f0305140c0302202010b001111000500d181d038070f5488584d071070f0082041e4481c40b001d0b0000c0703c074004018480c901401000e5061588218284814150301d00d81404603980015059045036400366808040d507031080142002849990005000403018101a100380880028500c0c012409100b9514150312804100300340c9110f03020010008400560a010203d0301c3c10002c3d40e8050702070304002c10340481a0350342d00120b80c8160012004261501c50500c101442004000c01800d015600c03011141010b4401510003040100391a0800c01012004 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 853067553 1250 853066303 853066391
    0xf111f02090a080601080f01050a0b0604050d0f05030a03022127070503030d0203091b0f040209131401180515091f23010201090f0219080d02071404 65
    0x5001804920160744c541e58484014a44a14070a2890403040d801e002c04254400311500c2520301c0c014008041514140c50710040c00803500c400301094800d02c071003010760301c0841c3e020b00041070384c0c1c0c025030740045c0d9501504200502c02c19001452981d506d45410803c0301818010107280040804400c0c400111004040390ba445c0480b50b410a503018000450720244481d07181d00510300640445098902e80941c103441c0c0081154440c41c8140c3c4010f40000c016001d003400d900428201d100501480c40300e20b1040103000c16600c961180c1100840014010041150020105030341d0340c02902c0705001c1c40c10440082c21a0a1801c1800c2d0f104603124404100c26940e845681d20960400c203103800700715940c13581035a09200c0d42541d1140c1c00011202d0760051503106100342007140d540310b0342c50004075456400f0b000035803003442c401a18403494000c000c214441c081080e0020408179600030b100d59401c0446d840ca0440040c400a0701640c00c0c06e0814003070326000072052440620300640a0300d501c20320060 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 853068803 1250 853067553 853067569
    0xb040c08010c0f1b03080c2d0714060403080f10080105040b010501030c050406020307080d0605060f0d1505060d09020105090d0f112205040807120f111f0209 69
    0x1003085600e448010440d09412580e4600c50340c3c444c0d150ba13488030340e640054603601c43c50329a00a00291841c000954041e5030038003d098451180300044d0020b0310182c2c80484c1804c91f400008200e2600410f10b24204030340942c2c01d1640302c482c0c0d000b0f03000c01d0800341d5000e003082c00081c103d410808440c00004921408a0442200a0014000a009905090400610302e000a004070380c0080d080c0080f0074200c074010800ca60441c1c0d02a4021440e28005440760703503141d08640c04665803c0c0d142d0000103803076030302e105c00b0f00b02160105502e075a44a4035281c0c0d02044820719040c50303c1c41e20000d80200042c0e80d9210546e000210000e00220700d6107424401200c00e84141c4070089c0e4044809400036040c00b41550704119003078410126005a603400c0020410300c0342407030b46004880030306140300056030b2840c0d030400c0d50014442c064040c01d2001c0c84e40ca00c400e038a550201c1000183c1c1c0c800c0740b241c6d210b6000020304081380c0a070300602078001030040e00d03103543d00041502d0340301c0b2a00000c0403a600d45500308 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 853070053 1250 853068803 853068809
    0x3102130b0a12110c06060319030e040908030903043002011128030914030c010c170403110306060a290405040f0203070f03021809072102190e060301030b040c 69
    0x1041043c000308106120603500041c1100b00c0c1489158005001410300080c1d54003d0303034086d02c940024403600c1c0d404031442004081486d804c20b0322041e1035000154054061230007041c0040c051500c8508050f00800310020408400b6410040914201002c040160800740002c1c2c081c80c10f481882c0e40f0908003490712a806046080d1064145442280084041c041c4092988030741da0f40d03041140d54441c00d0f140c100000003020350541000418800c03560181c507814007000c1c801c3c80b03603115451200361000c0460b001940251400e8014101400c884d142c20301c01503611140c00c503107568101c0c0c1448000d081c0301880301e00400f0119070301c1030644480106078040d2001410000c0c000c1c4007a80f03035103455502941003505e10b800801d02c01400b2000301402402612030310540d003810240604804010802d6500000d82100c080c00007c1409001c030a507090200482000e60150240e900c1c040c6403217024000380507400d00030030400d2050741948203581c0e04040741c1c11260084d102001e545c41d1400c02e418440a254 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 853071303 1250 853070053 853070087
    0x90f02131d011407111e03090f190b070c0b03070e151207080910060b0d0b01080112170d0c020f061614030402040e06150a0e07050a080c04053102130b0a 67
    0x201b4900d1100c20004014940c00c40d01b500e010541015103014032080340100000304a080611640600c003001c0d029020b800d5142c084c400140c0d25568901034441164016503c503000102e2651081c240b508141003a009009002001d15150400080c1e01034120305020b4100402c009291010501000c020000440352070781c1150200320095984951000340c1d40f020402c0700115041180c03143c06903010b1070010303048a01c40b0b880c030310890b0001c0e514400400d42c3c4d09a401507084c802e000501e02da08891190303c0b98070300d4030780040c1140361400780500d28015005040101a4600f900019219a8806100c00c51408815500d80c2c80e40c5440c8001000382c951401e030030400b482013400b00013482c403180c201d02c00024410b032901c078001500d07801040d1420104550036404690100001d01805d4480c040c400e0f488001071070140e0500b40c4400014080d1802c41030541c0e802c072543e1405224500104860701d0000c41c015101318a02084c041f03890300711400d584200c8102d07202c0071907490b134414028400050102241 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 853072553 1250 853071303 853071343
    0x10f060f1d1309060b010e030307060f1107060b010306080127050a06090507061d0f0d02180901020d140105090105101404090603031e080a090f02131d01140711 70
    0x600e029000418240d0002e407411401c002030105d00e0750090f1560301c49035402030091b41ca440401d442d8180030f4036109840301075a44c0c0c1c46e6a00d01070490414041c04000b8031900e0042800b08407000010300361090f80c0c020042503450300c030324240d540f821404a00ca0415515041c0079020040f420110706001d1416009080f160612000104014010800d0b4050300c5050f200c2600d20690091682e003483c10300d040643d08500134042421852415485060003d8401001407217000320a1150011480c800d403034103041a900860012403404490050701c0c8200342048450031958907010010790085418402c103402400360344081401c03548180c031035601c0840c10801c5980e860340e83c0d01441c0001e020910090380043d000710f07500310b1204201b0140c080c2c4603407940d0302d40c2c200da20b0b5104d80348000d04500100b11150540501c080c801a201c01c0b02c0070200043c1c801c3c000030b02d02c884402d0401c0a151010b1054410b0745455494011400b8003510541c01000f40c0c0380510110101e0358540d0705d0494920020141c0d5664 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 853073803 1250 853072553 853072579
    0x150a0c0507050d080412050301080d0e030f0115090b0111030901050f0d0e150601031a040f0f11090a051207060e010c060513020a0915090b031501030b0f010f060f1d 72
    0x4c0300c890140348179040340e81700200c5100c000c942031301080c05081400d402c000705d8412141d02c150344440508038014155040320060b042c1003800c65042d004485840345031064200550a041d204034483e00c00282040e4500181c18402c99441c2e21401c1c00d0141480400b0416a45a54000e02a9683c1d401200400c21072850315504d8150717921100000e10903030714000000251154464080d40200c041c00c0038503410000d0708181041b014003011007600135200c2d80c3e50300300b03840200d45004002261f600039138240d55450a11091211f07040c1141c1100e400b070340c3c03075424100302c00b08009204011503049243ca024200c1c0744000403580b0511061020b4031160a00d030500c055813540d030651443c0c892084031407442c500c2e618149081a94071fa0300219880000160301006102c84c1a0403100303800700700a00ba40c103a03100b41e0303a020303076080003c3e0416100002d045040003d000040d0b00c2650142c4101840c80c030a00c1e2400c0001400005181c80002c00c11040154010a49020501070b40c4212001372800f4080d0030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 853075053 1250 853073803 853073807
    0x150c0f07060e1e0d0e060c01020d02040e0108070605070f110d06050f160c0b090a082a06011203110f06090d02160302010f08090f06040c030311150a0c0507050d 70
    0xc006a20700405009102680002c41d001d80303600f4a015200101816a80703000341c406403080380074010101d4000d5010028000145000e100500d5000d00c5004016111030908401c1074001a0507044401564400e01c0c0a110540e00401039620459004a80c050543c005190240c103100c024442103400041043d0381204004003a04500d2160100d5542c00740070307560b025035914041c5039030110100032540810103800403859507614540e01c43e0b00c1000700c65110709207654044855009808440c10f500e280003206403410400101d200d0005a40c80081c40c80b54107007014140c05d150351543c02420310110070003150043d00140b0200d224400320301c0c00d40741c0500c2c090090307a44507440c104560006015943d040019107144441503011743c2d07010394950600021000f0140e5201e00042c0060b4600c2c454045184200708003042060701c510300c280d402030310161440c03401030400004443e54450680086040b0074800041030483d607402690f181000c0b80e1545100c00a80c0c00d4401c0341409042401810f8220941c15 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 853076303 1250 853075053 853075061
    0x90312090803070c210c150c210f03020a0207050907170a0c14030f1f08060411181b0d090807062c0613031103030a050f010f030302150c0f0706 63
    0x250040800c0c0c0c0f031409604500c481702e41c00800303008140320301c0b0000c2407041d90300800c0356901e25081c03030401c52012aa243c684c0102128a904840000c5118011000b0b10369032044104105540c036007415400d11681c4840039444d02c00b980034103400348164100040d0003600c1800080c0b450355100d02040a1802c180010300050640007602c0e60224038214101151105454102c03403103102d2101d881803e80d11500081c1c01202c1541d803a0701140d10740a200410b0601060003560b000714410080e00040d41001014440800000c0d105803002c1040c000410281040c0300315010304088400400d01d540e0b40550306800d00521041d180a000710001040500812401d40d20881c0140203000403120412030441154946859481030705001e90069000304070701002d0f00d4030b800f90a034402d08003000a100300743c0c1024610b8004943c0031800307640300d00c140b045038141c1200e4035000d04800905035103860305589010b580c2d1440c110040c201e0900100005022200d80b50546280380c10036100165a00c0850500308050 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 853077553 1250 853076303 853076309
    0xc110601060f14220b1806030429041e030c11031e07081501030c030609020427140c151c02070c06020c1804060c0207150207091b090312090803070c 65
    0x4c820700f10000c2004015107081e03c45001d059188400301064940602c6019040038104990703d07904801901e4031005454420b40c0e0224442c0786041c203a14040c00c2055005041001190b51340364040c2581380840c0d84036001480c0b56410071200500e00440b03e010078135054003020a00364030003108034a07541c40c20002c5490b00803500c1c0395040703400c2031a518040c1407660300300303102c020302804a80000b0000142030f030304190400340c001040000c140e24201c40d107450310803942000d0b059150404420b0020402e219251560792503040700141820035010021880406614284490150001c034000754141085000d00d0312070518040199211840381ca0300390f001c00410b009545c0540a102c06240c902e0401c2c4030f4403090783c000140f03000440e4680d511904020b120309000c400441c0600e440110b10300c244030354080410400c4d03a0003000709034503020081040b9440142542c9405012151170074805510224090560b0340100404650340300313001303003503e813094260701c000d200d408003159030010312401510400807 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 853078803 1250 853077553 853077607
    0x50606390a050f010606200703120e0112060b031306020d0e0f060a0b012001231b0906090613121505010e1303030b060405041e0c110601060f14 63
    0x2c0345614803e15080c5c511030300960300066045c0e82c450350340058401c4502d11244181080d9054551a51501e0f02a20310001043c8003081c2c0e200e901c0e0310507580c48041c1440c5400390210411105040c45a141c00c0d078480904401c00701c0700040088420705c2080d0b4119298400b038010304000c1c0c452441121904c6000900c0c48681034061f210000312504080d0049140c031210507980c0c2030440510440320141c94548420803019590703030308080c44028500d1011045194484920030859180155114544603010048200c1d0342d030051040358100d0303d425050310b1544508654840d251884040b0f4a13428002039440180b0b42e0600c600c5d840140040c5280c5008d9500352000309004680c0c852100b01c040f02010b4583c0c030602c0424800300408244290b0002040c03110041a035803409540c3d00014041d205a100b15981c80ea000c98040c1e45c5610061084c2c64041d00d007410f0840035014460081030310340c1c0f0144900b0f0144041c1c2040301c400f00d403081c42902100080e071002c2c0f94417545811403086605101c401440700c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 853080053 1250 853078803 853078813
    0x2030c010c0b190e06190608010902091927050c0a05010e0d0c0810060f060314181c050a0306080c33040b070c0603050606390a05 57
    0x401948502140318800d9009160040b45440e1800e0b007000303035000a0500f2505550b100741040d081c03c014860940181141e09003400d40300d0102c882c0608481040e807207000d06030700d4034046000607126420010f0b44002d1400007042ea0030407015400014203500019100c00c450301c00c15902c1d140312840d0031000301e5400b40089540e6a016031090209004640c05254007240901c41d0b0714403145003100c00c1402c0e0900c1100c1c400da503160341c1d4082518003403001e03801c40c096580b180c3c814000d0b80c2035011400014041e41c40e0a110040d407441300c7c02e00c1f1420252000701c600b810804601d0002804100000c424015000d20003414070680c00f0083c6950020021080024100800090304480026544420540013080d40c00e540092090041e006140c541760107542401c42503e40000b0f28401014100178003c114070301d50f980d503207407501040380c09098000c00c0a052800381448119110841941d410500083d9622134208400209001c1c40c0c0b00341580c100124044044003d2207000400c0047d8005c0c4036000702c403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 853081303 1250 853080053 853080073
    0xa050d03050c070b040f060b0a080c12010204051c0305040b040f0905070201050103170a0c050a030c030210060b0f1c0f0608012018010c050a080a0f1e050a03060e01090501030203 78
    0x200c031603c281c0707030054042d000c01d0010a0218808152000c119442404001481a0410040780d40d000f5550b000078543d42160b810b0541a0820710700710038180881800840c40e0500704000244003084008001ca004400010220201801078040340c000e06080c400722034403140d4892040c882c0b01014020510840d0070f000c0840d001c0d03401400b9080c107aa03480780c2d50040501c00c60781281800e4020707080b400100f0044801c484003140042c000740607004c0c040d90b98132010a880e800c0281c540700c845c0c1d50101c241850403100300b202c03140d0001941d080e00481d80810b80d5a602e001c44c10192060010410f0300141d1074010074088400640d400b44e4221240b0704002e0200b070f000070b904a14000c0700c4585c0d0314a040004c100f01003020301c40f0312003c2c0c80520141401513050034691101c501d4800010720490f1610030010320015000e81090100061411510300148040e03c1549402115815548181e06101c40450f08110300c038029005440a4050305400d151a907035180d01d03020280a00b844207a00038000c640202c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 853082553 1250 853081303 853081321
    0x80703110303031003020121020c01020706050f01120303050a0e0105070908010e070b0d200c0d14090105190201020f0a020a06061e140d2f010503091203180a050d0305 73
    0x502d10405003144c02c0e086142ca940c00544651603105000c861601900c0e450150b517080500c05020320050704000142c58100030720b000003c880f0080c00040650008a0040099190300d090014510b51305180c0400d1741d884014001014220483c2d07001e000b54240002c2100140c0d2104003401120180c3c4001d0040c0003281040546403074050003070f480070034010030000f820790907075400103080700c0004000000880484002c02d1025000503031070403141d81080e100e50412607402525000403082c02c2c0030031481c0c065000006032142c8100762902c120f55039003403a05280107000398140c83da144009102d0b0303603403070540e00703c003d49401d544503007141c0c007031301d80350303012541d40300c0300100c84040c12400c44501c401a00b44100e0b032099521951400764007075480f1059100080706001844124901816001c1da0700900a82030010009408810782c100a000c0c01040041a40003420b0710601200031303c2c0a82e01e0b1220f010070b001c10384e86502d00f044c05105584120781002000149549010b005030f80030066601c0301c56003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 853083803 1250 853082553 853082557
    0x51f06030b01050f07050a05010216050d14030609090703021003020a110a05030a08090a1523040302061b0714060916080c041a0907020309030c03061e0603070f080703110303 76
    0x40e600007102800300341c1c0904150002000343e940a14215038947c03d0f595296800d90b40035410a6021494a51106041100400c140544c0c0b401f0381c102a04003802800220810b40402041c2038415600b440c049460360720305008141c05903801812040c0c0b2002000c001070040c0d03101c0c0031281d0005034150100011003401052040040750f102d0060751a018003528103c83d40d05002c0e0120a0724084d05411034002044c011543c103081c1092003011400302644080401151050f048800e2004001f400b00000a40d0115200340d00c4820f065034070701c04810800c81c405090080c240020103030014120030550004000032454845c00c1118102c4101000d0311900e26955103c034801c10046611010b26103c861070b207500320024048101c0c880d00200c40d4032030002100108240d46c1500035800000d8186107504082c080044002d0301600206020700706450408050000b6442c08840c191903107003c2a0141d0f000d00402006082c20403504100c261101040c0b03481c1d0a852108448100a544105000b13090103c2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 853085053 1250 853083803 853083821
    0x2101060627050d06020319021c4706030f0402030625030c0e060711010206130c03020d020f0315071803030f0c080906040902030105120f0d050c01020d051f0603 70
    0x30f164003500a542d0030002c0e4001034210742a203540d000040035000b03403e2010b40b0810741205007a03030840c2c0385605e400b02186c020303000180f417038407500d0301d40360041000e040000b2410084086401040c10410a00c0b01a01003c0c03210940c80342000044c400e4024a10455074002c50084041c0c56040d11010700204842001c1d51090602d60031100c1c0d1075402d14043e41c4440038200207418000c641c1d03000702c0001003060b4001c8400b2070b1008d03801d400868544d40e040001c503a204151101ca400c013040701d512501c0141e285444028480c0301092601011900d42c1c14006400c901c01404480f046854030b85840c07000d0000b01d8410340014207034441000d504a61a5110007200c1d0580c0301d141460f249084212900c1104450030b41d01d4050402056a4a8407858000d000a1018120041c2c507035040c8010050051400c0c11400c1540e84003040c800481d80740412030304030745201800c002e0b1391001503200e0a0301a01500981c03041c150729010402090f6802201201560540e11850b440d180751121010303001c40b50604 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 853086303 1250 853085053 853085059
    0x503060f030109030f113a0912021215091c020606090103030804020a0315060812040b160f0503030403030f051f060e0d2003070b03090c210106062705 66
    0x881d003421118042c580318182422032601f030300d1410003050400c0083c003564500700c50200b0047c02280e03008980380f4002c051401285d1808090b030780c0c0382c50b00214a0070b8400c00d02034811080c000301040400010820346030101c089180700207440c500448800c0d1502c04030049034100c03040340300c85412803074408543c040c4101c9009206800b1642151811103407000010422030f004a0040300101c00308840b2040386101a400315008100c03941001c440341e040283d0608141d03a4258103101c28020900c0c0c40e000d5030714a90071030390708943e45c50250801da56103000700c580140c00d0340000000c7c00300b403541c190020005010719400034400d82c0c4404040506007030101c04003070700f800c49800b03050001380e104650302114407100422415850307080340c0f140c584101c1d5850b408042c0c2c2d640000418603a0509110100c02411f002d88103509528000351410b86032580749a19510079016640701c210608450030a0300103510084000704800c0341c030f500014082c0010102c4c446030a407081c1c40d04110a010304444002524006 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 853087553 1250 853086303 853086317
    0xc13020712031e0216140d0905221116030503330112091a06180405190c031a10170309060703030204031e12050408031606021303030503060f03010903 66
    0xca00100029003000701c00076584003010721780301c0200700309500780341101d44018054800a1616070018280d034082c2c1d40540d0051001044090481003400d401303034500c4001c02c5010800100e14400034030a4031410b03031001c5a81c0d8402d0098003d065002004d188500003520244011340d8034110742800b52185020100340404002c0c01049644d48540820b8102100300b41000c02d85441d60fa50308920341d4000b548400c0907100705e0007000413600c0c201c459000502c80150300940c0a003071a448403074a6002802d00c00e1603444401e4000410082120700c6440210f4005189030040000a80c0484508205440700030b141c0c0740280c2c01281d0744a20440c16141c40301c002d00150301e00821802404960741000c101981415801e000010200741040300c10480b444c03103400d0a00106070140307020300d40120300903041001c01c64240410f101c0901c00004a80c0b100704a08846840c0f0012403410801030310510f0b02d101c500103004400003040503002405180144000c0368280c3c0c121f5807a40a25080390600c0300c0150004200d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 853088803 1250 853087553 853087601
    0x114210124030e03210405060c271c0803060405010b09011b060209031c03050c040608040206030901200414060a02030f0310090501032003011505060c0c1302071203 72
    0x982c44611551401c0007542c0c2400b03010174800070003024503480028804503140030841000001e00c803280d80b05171a640c10505026207945c0602c0c001a412540303207441031841d00c030304c2800c1e6140c0001c0301e441c002d000140c2d540e14010b440c1c2400650001d817800c1e80182d0421001107003064030f090542d00d0140c01a95400d40d508405665101a0380a40d1000e45545600300000c03104c0d5242400001000c40d824a00c0626020300c291004003120700090942084040c2400184030095001030607a801540441d001c544a841e400703009401010618030746100b004105180c8a03205e04400c01500031a2085d0b0300c69401a143d510500c102d511840280c2c100580080122005d1001340c0005140c001c0c0d84080060702980d20340c9036000c200c9400303800641d840c05500001c400407020540c0500070652003a80240610340c4801c182060309086800703101d11132180400c9800d40e6410400419079200300041c043c0c09d4030440f0465000c025442480705803040c1100c6400c0c125460302034000c601382c0401200f0f5000d84a14 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 853090053 1250 853088803 853088807
    0xc0e0112020d150605040f1202030c04050403110a050d0e04060f06030c12020309060f061e0f0d1e0501060803030108061f1518050102010b0319020114210124 69
    0x222400c01201c0056071100300000e099000f030310000c00390520342c0701c2c95950781c10251458107983c2c550344009003100c0e40848403001a2000701c1c4641403c1400d440220385c1c0d4403107203410384500c0340204100c5100c1c0f03d0309117088140500007500f408008a10345880450b4100b000c14001542d26500414400c40c449001c10040c1c40e03c80c1d48402011600b610380900280755845000d001d987c003d42c0c250645034002c00c24000003520401105400845c03c40c0c0960501400100b0380c0f05290034404214818040e54010030403548a0528000006502255009651024080308450035034400d100f999a50328144001c200c0b54000011281a50882401480103644205020050486040c0c1c2020880008100060345403032090103500800b540d625148800030403032403c01d10b801c0c000d074072140c11681051820846030310080340716403013010404020362401c046800183c0c2c5030b600f054400c01c090b03000041c4468a080000d81c0c0071780c078080e0f00c1036906070070703641c802200c0b07103454200e0040a503001803500700742ca01d94 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 853091303 1250 853090053 853090057
    0x12030b1c0b0c1603081012050c01030c090b07080c0c0306091209060d020313060f051e0615032d0f19060801020a03020c100917030c0408011a040c0e011202 68
    0x540b14030301c3c07801038030b0101c10030b20f1a610482100400c03000c00130b000020700120701102c0075010041d045841e0035406d4452035a1441c013592018113141c0e680384014420b0b80308440303079005042d0040105940b940c4601d03201542d641700056041d0b0901461294500903e0080341d43c40c05465104010003420440f0161403900368000070019a00c4a001c100c820300c2199280003543c0303e0b82070684d80c0441203840d800c113141529000407800d00c0d02864502044250000c2c02d01c4000c9203600c180d0550714944d155400314400c10115a03100400140202c200640d402c041c0b00d03000c001d02141801c448002c031070601c00031108141590741d0138100c0030010020b89804100310001c1000c4403155004100300f030360740d50f0030b6003241e01080c0050006030b0005811349400c542000060051201102c00f00b200541079145c03812640c0f11070505400c030303d9002001c02c14480da0178054802500c01e6000070800103540c18022020040780000303a42c040c5040c15a505003040c003a80044030002c0c41a12003600b000c0c0710f403004100079 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 853092553 1250 853091303 853091311
    0x1804020f040b0d02120a06030b09010504120e060913451e0516140a0b0702180a050406060503010c140c07030c0806070e060a050409230412030b1c0b 65
    0x51340c2402040c42031550300d060103010b251040d0b00043c043d400c0d0b040120105030b00404040c0d00d40c4c140014000010031080310340d03119192520b001200c0a4029000584a125110400394040000450100304038501c0c2d0000480c110090384150000c0f8070f14140ca101c03c00e814001c1116902c0000442c031440b01602058684203119400c0347c2c91550400f10060752405624074255071580c80300154448944180030b0b000e025241402d0f098881c02c00040c00501e00c010f07940100d04d8201804a1042d0454030741c0f40c44003241450b040d941607010318010740414010f140c1140c00355555400c046d00003a090406108202d0480c0c1143d450580000440d05009525803241c0c405144034402c3c4080040812000e0a00d90041e1541c0d5010f003419007440500204003003108880d0604c203010070071009411b1a02305003110202c4d0b60004d004600341a0301000141d01178081064548054880d01c10070041004248046003a126941c40030452610f104003801032200c0c0d02c00407800308242a00144002c83d50300104103600c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 853093803 1250 853092553 853092577
    0x5010e0d1b02090c0412060b12031315020a050f0307060b04090503031503190803040605060a0506031906050402041e0807060e0d1e0c0303081e041e0503040b1804020f040b 75
    0x203043d0395080d6900c0f24080d46c49081d500155030b42070b65500ca240031800f50a107004c19800030750600310800d10000c0c0101c0c2912433004820303619a100700c140790003841030304560380c0c2240c2650240b1000c01c01320758881c2e0203241c0445516281c401d40188600c0d00d440b0702e40301250080001c60660742c50211704401701b1001850305905200d40000c1a1420f00003a054482c0141310f44121500d07803c0c94a03102080e6240a468188211201e84051200303454442c19654088000007502d408408450402d0009210701d40219400900001e40440c5465400c224a441010301440e0040919074400c0b446445480c01d0044600090b0102075040f454504040b2101c034650088154861158032007410b140c5440850034100c403e051190010024150080011603000309001007119a03404805030a49036007500800041100c1209440d11414984062042920395481790890fa07469483c3c810300400381c0c00c202032060100021480703d54441c01d080c0207540103011082c2c013140c206418640f56041507006800c002030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 853095053 1250 853093803 853093807
    0x3040c0b16050f01020d0e0714010507060204150e01080a11030c0a051903060305060a050c07030f02010b0a090501151103121e1501030e0f0a030e030c03060405010e0d1b02090c 77
    0x7000c03440900c611050451114001030303403045120000000e032000d5007048007007a0000c440400402200c0c03c010740c4403c500f484c19540d81c0d042894540b000b0b014030b07003007036031040d6104450742d207002c2d0454001c4102d21401d889540441d0340702140e10303041d603d20140914404400780302241d2800f0305034001e4490b0b054142130081c24407010490007410003c9114a11000a80b201020018001d050000f2a00006107003400d00480c030f814141d4075054032600c9001001c120600042000700d610030344c03011240600c000c000e031603055511451800a070000780035502202c1280645800c91502591002c01c5900502e400f841c00c2071500001210b1407000200b807102c40300412441e110030302418041d135901c94034205142240000c404400101100c6030350007002c2480c2d0000e8110307203000000149144440ba410315002483d400400080390400ca400c421058041c483d54040c841000010341044084e00318000448034280050b107130480392480040000488010710903541805820012402036001107400c3c900d034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 853096303 1250 853095053 853095097
    0xf080d06240f02030c060c0306040221090d0c170a051303030507031803021e0a050301141501020c0a14030c060c0c0405060a180f0b03031204150203040c0b 68
    0x41200d07040c040d0119044889a140c6441c1c1d0031401d0500401d4080c4029420078012101d80f95a804c0040c007a003041e0f840110029580303951307680440d0014407111459201c901c600b01c41499600c001a60f070711907140076260b180c0c0d1200388a50006480103402c0031103410600040c00c542c1280f40d01208a6500f0040d0420280f5520011218044011880382e44c40d95600c2805083c020030850f1040c082c0d02211080240030005660756404100982c840198403090060350744002840d041420351202d90554200221a03a514018401d4940710304200301081c0b88048030300004907202e00ca076038200303988100c4d08001884a003070500000203504001400b03c4149820328000500350343c102409c030061a500c1502d4405071820580120b039002042038803585d4509040c03200d000e480105140b0034080b03196490035001211041c0b5048800450380140649554171815500700110300011103098401700c0125088a03294000343c401c50784074940205500e1819400c00c52080c41561040d440c040d62112600002 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 853097553 1250 853096303 853096319
    0x27010c1113050c0307020d05090a0b160b07050405030c0607022206050303190e0405010621090206030c0304210516030c0501051f08010905060a1d030a030b09060306040f080d06 77
    0x1e580541c1c001001e40e904d0345000c600007803404d00204604010014144855603c2d81c90b01003002c01a80d113120121a1a281ca8400d40c26010300c140e140030b0010000c04040c005400d81281c010000d645041d030568520000800511101e8403d0400080d001025590803198010008650007132011a824000c920503a488002910b540c000382816020501408201141b968010714241e600c080190360601980d858000301500350b5400d580c8080ea034a03030b110340c0c50640b20fa05034801c24081d5401440d07a902c1342081100c0c81c540340c00449003154040380700510580000b00141d00d15120003117990b2203e2810b00c1030b80c40c20b802400c05080c21001d00c0a4520708400151003030007414852840c100c501401c24140b03100d2078961950303c0e44044004d915041102021a4000c584503500c40d120003004111201900b00b11200d02005561040346400081816001940e02d41c2006040302011214026a07407545020107403184c1080e28001d0681e00140c8a4a00151a040241041c80c4030700030000340442c1e8400403 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 853098803 1250 853097553 853097561
    0x60e18100c050306101b02062101090212071416110904050a02030118050a06020c120a020a0210031103132301060f0b032a13060527010c1113 62
    0x2020100d4004020490325041c0b41c401084040b0451031b050809681210031403d4542c0400c4020780600c3c80010141c2d0410102c000400848c0d6200c1c500d1140c9607540c03c00c0304004c0d0402410368001d078001d0400318001902c00d015001108880c141218503146e0340e9034600195980c0048211406400141184016038400301c1c581d20590095001d80304501d80d0344105421244007584d6a8442411900401f0115400098801c00b0b10760211005a91300100c0d1101481c044151051940300da038006101460180c0c0400c404c0001c0c0d00c00d0300d0203241d4521991007542a22811042d07410300751424070000b0b584903034054004d83d409000d100240e03a41c0344e5162024600e801c0740030400f52241c0d120f500400446004c10b4800e40102213424a241c118100b07440500e000070000c005120021951840d00765030303045401c04032406803203a409485140c0e1394922000c0e00036000200c0c0f90b840e5155a5051180e0324203030411a80d0542030507034981035500d00302d0366041c900a00346c0c14926000070f002150040d5040d800c3c41 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 853100053 1250 853098803 853098821
    0x3060203040605191b0503270318060405130f24050315060603060d0c0503010518010e010b030304050103091b030f17070b010509070c0c0902091201060e1810 69
    0x1020036240303844c8081044d4030a881600440e0185003440a410265160b244001c08440c41c0c41c080e07030b580c1c84010100c100b0140d42603614403695111080591030f02c00000003040e4007041c1c5481380207490381c81000c0080a0055120303007900600382c03c1000d0205031003640170944040c18108005080d5012035410904010300c0c00030310912018201c03044c0071350714041010028460036000c03007030201e123402c00c081800c1e40400b4209501840702d10031a41c0c200403080385160090708000e0700820861510301007842c0800c040001c210301d1541381c142d11001d40d940600400c3d9503040003030021854145428011002411180420f80d203000c0d1042007003482e54054010300d0000e42c000d40c07a02d801c1043c0350611201c1030119107600786590318100615000250200d003140e04595044231504626544d040d41618016018003004042203121030000c1003c21242e409003c8441c010341d9481030400d090b03141c290880700b00d401800c6040110000003500d08400208400000c01c16100b40c0710200f0845004a0694103028 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 853101303 1250 853100053 853100063
    0x4022e0f17090f160b160201110f0309090f061e01110709051e01080d0302300124051c060e090106061d09040303151a031611190303060306020304 64
    0x1c010540049010000c2404c418030840795001d2070361414008103200d01c6a80b83c14100010341100150540e07004a8003041c0590307010003901c1001c00032020950301d0b03510008010f0320801510000c1501114001100d5203e000041e010324240810203083c010000c0e00c0454190400c00010b00800010342c1c04c0c083ca9008000130b00e03021a95080c45c0c2205840304919040742980080080c0041102d004005805240385a0900300140d4071305030000c413010304c410049000c21040e200700314031000c418044510385048070060340d00e02107550084904a40c2c400c0810300384400103607045c0414881010401c2d034071164000c038000700042199071000038642c10f02e41101e6a5004d41d64683c0c0400440e41c0080b0210052200c010990400712507510001d501100080c2003e420540d64a801b00d00b4000c0d4084002c01916015000405402140b22618142da03c2200c104801c250030700f00402045002e03540c1c0b2040ca44070040035003d2130400c81c12a950881929500307804158071400c000020030030f584000e50090b4003c03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 853102553 1250 853101303 853101313
    0x15040306090b0a0504200409020a0e19150501110304150207060f05040f0306050402150408030c0c0d0c0b0c0123040515010819051c0804022e0f1709 65
    0x18244580690307001043d0300811410311042000180e180b40740301401070514205034941c0107901d07020600500003008003d41084101c5c4002c9001f46504001c0d84c490072140d6a1400b62000c1c540b208020303100201d01d03084a1175041d020501c010360040c5c1c41c5220400754072049a0070660381e12043c40e06000d2260341d01000d40c0000c1e5044c440a40d000c40403595208081c1410b0340703801e103404002c8030086050f104c043e181950b124017040071540d840d080100400c500b0b20055840c0c513160321b0003541325441000d4500d114415415040380740d0134101c1030041c200c4d8200e0050440c003884d101000c1c00c16032241da400c852a558640600031107190030b0080ca071550280004810f81480c2c0303440e286251264003502502190062030040003c0780001440f200b00e41050001641c1c911b480c0e01d40145461643c0ca8040100c04c59500c0504906e41c0c45690316124500031124189143c01c1d1001c02103d403d119041d0101c0e507401101200c0e1407a0080784581e00d00c0c03806260888011203a80c0200034580d20607136072062507401c1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 853103803 1250 853102553 853102571
    0x1302240c0d020a021e06090d060b100810050909030705030a0e0112021912020c030d091a0c0f1809100905090127110a0f0e0f070f0e15040306 62
    0x100074481d0240c000380010300f50b0412035000074461444d0102c0166070070f040d0b10307480c0c3d8003500c42c442514880d450242802d05041000d2505502820403816503502900540407460141d901c0707002c0443c061260300503480425030404051040d0f000303009109109034441049500b0024104200420001c9510341c1d40e03910361250600014102c00c6000c082d01c000b140103203e04140302025880c80004801b40f4101100425400c61000c0041d018804005d01103010104401d034003648241c208210351440348402d90712140c01c4901a0b5011102580c011169840911880c0994210342d4014000603045040b038803014121303180090750144049448403012403043ca001c10144c8562300415400101d00c00003808100301c0c2061403041000401c000702c1c040e030b60100b450b4060240508081454030800350030b600e0240c0d00c0e40f85414a0902c80d00c154681022040001380010708100001402a4410366811590000c1c4a800b105c2d49a40c4400075644900398500100c00050701c1c800500056100d02c070b010400390701d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 853105053 1250 853103803 853103827
    0x616060e01050115081519170708070b030412090506161505071d0a080102030c03090f0a0b01090f1b18080d0203070312060b07080403021e010503130224 67
    0x8181e110070380750050040e1200065810150a40c1c1c85000c1c4000103400b2049000040c5100491f05a221094142001c01140342851113500c85100c0f64124116484181d88440e40c1d40d032213180b44280382c81060280046800110391049517100d910052410a070b2103602c4000050740da44c08080401102580340407814104003400c0850f004490399010100560318101034003501e07d00d802420205200603400e01904140c1da00f40004025102410085480f0f02d41480d0001c460741c805c1e01c0010140c03040d100cac83d031081c80c000500052859131182415045910f0181204094551071807400700c2c81d900c610034800749956030a88103a0031aaa90360f42401402420048640340c0425040710003241c0003a4004441260000116484542c0c17515004003120401300b4158014010380e000011050030010b410343c288210a4054010380f8000c440c0f0402c41009442c0c0c2060991490b00e82a001c24000d0002070358203140540507407482070014124003c281d10625403001d40301c0001c0913680c801c0101246034081d0315 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 853106303 1250 853105053 853105061
    0xb0a0f0e07120c0306081e07090b031504060b120a17030601020c0409030203040f050616080a0210090b06130213060518091f2106051024080702010b0a03110616060e01 73
    0x803145842d01c507095541f01641e581c075941c25001da000c407a03803510000a115203007042174100c0401c0c40000307030000382085d250060150a0040100d48a110456039040b024440462100341d4654000d2140704401940b040300069900000c000b00e065000742054444551118010001001d1081e4091552103080101d8105920225080389004900611290541d1a81c084001a010303411a220b2625a10780000403864601207110b4488074034200350b13030101005184c031540c41c0a190101e030007801e54043d207040c1d90100d000380f954662000e410350900b040310900410007072010b05016090755084010341c2001c1003035510103985080c040301d41800c2c08800340724080042c00c06840303075041001c45a844000b210f0596165084d01820701a1340d90b0114034500ca0707401100b001040300000243d00c0031070b14502c4140d01014040d01d0008100710b480041c200324410310400c031510303000a0139001e22a01315100c00c219254000c0a4640000003004020f6401c0601c0f4403210841d40b0401001c108000840b060901303403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 853107553 1250 853106303 853106323
    0x80d060e0a0c020303060d080c16090c0305090607080a020c0138100809030403120e09014a1006260a021324030b0a0f0e07120c030608 59
    0x70a00e081065205a0307804030880e43c00042c1110311010511140c10816128070481101e040b152180b84072881d1490180103003602200e403904020050001d811030b0079400c1c1d42085440704401d8112170000f901490243d28560382004005100504210a80300e1007402c55048658020703421700a10f40100345444c01e9034402081e0900c11011450040014000c00e02043d07070300d400718040c0314507500002c103d4002001507900541d04440c420000004290028040082c808449030049240800214040458120407140341a60701d9540c0154808660100026002c1541d84800b00000380e81840e814461111003d026003541400c49244910f01100079100d044110b040343e1800c80f002c91000c106103c040612584600c5400015a4801d07282c0d03880200f20300c5a400c8150060781d07200305010100d01c20480003809039030580f0704200030483c1c0401c0205505583c805c40c50040310901e402c2c8042d0b90031040c920380000103414005075513907500300d1001c1500c207201e5000000a5641d0303c1040905020411a944 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 853108803 1250 853107553 853107571
    0x1b1503072708160f260601090501032a06050a051612080108010b0108061329040c0507080306040207020a030c0b031012050721020904050606150a0c110607080d060e 72
    0x1810b1801950240d1301d2110320624400a2018224024200c40221000088449202a82c1d110b6849a0108006141c2808141ca07a100011004a00301190324180c6031480c3d4039030041e01c80c0d185407171022105039100d43c4c0c0b29410008248a60262010391199065a80784078455005004011020061411030140d11001c5168149030340c00039030ba41c0041083d074210750240d518005e4001002c4185028028044800011008002c04c00c1031840f00c2031202c3d102820111028019801e12860480710390180300d10150440700200003140d8031b85401e90003861003600c050f00706140690b1ba40c90b80e1000d0900c43d4464408e4100010801110840380e18016011700694508580a40d40740c1e2516030360349a140c0911a0030311544200342181c103084080c4068540e0780240854007a01c0c181c81c08076141c9905071a46c5011782008041d00052425030015289260340b20360321301c4404912034a481c030108919081071070f0005410810030300850142c40081c1007681512101003201e80c507082004184030401440426 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 853110053 1250 853108803 853108843
    0x30a17040b04030c051935031b1e0721050d050702010323061e0301020703090812070b0c03040812070c111504030b0a1b09081b1503072708 61
    0x70100750b100c08030060340e0140e94000fa054041840c0b2004907e603c034603041c2046e11010540c2c16001c5a050784020040381e40740c0c203a82012141ca940100042c80360140e181d000d40041c3d1080c009040c0700c6294880f0070041d803100c100c941c0320680b241c0c6d0400f20b60118440009d8000909a02556018040c000c804000400c0e10f421110a10088412803034024001c0e40c4201c0050024850307031b00c400c82911428507030007402107540d96070030700d0068050150f80c810440c0c240140341c203003000c2c040928140d03560613411545418595035006428807040d40020310440d040301d41444202c04e4074040f030650a116000c50340b43c2c4250f40c0310074246589186c0c50722210503c20351101c01040e450744206010f076011a580804016840d454280d55003020300200b003110a40c0107108407030320605a85c410030313420807118082e044d00c000312141d05c40d480d9440303401e000359a000030800b9a10280040764070001c5d98031814900e0500100c4d25803c1c1c0401d5405130714001e0200b07680410384140101241485041014004010254 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 853111303 1250 853110053 853110059
    0x50d09050a05010e091911090a0803030f041214160b100b1605150f04120c120f0c0b0901020c10330b0c1605030309030a17040b04030c0519 61
    0x13000d414010400d02e0160310344001090040d01c2c4214045c00c080120202804000414403845000d50880079520b442207628050000d04500044200ca0261040c90001340d9503030380c2ca4469803040c403c014247c0040107401090500300800c01e001400407074a0004000500da200e90034806007000000c1c00b17400b40c1c3e1300c5045041060b1744484007110000b01e8101c6541c100b2030440d042c824100038003020040c3c0302911600c10030440d8422001c0003445503104171910410034142c12021100300c20300f000001c3c8242d4114542e0341240d809201080824001850100302440050341e030a25205820780d01039140b41e4001c101080c00800074031007110a440094000c0140c42c01c2050700007511410100410046401e9690480291000601c002d0140018010481d034850004c0307040c0e680c03648501d962104607030356200c0c00710b4a407502004440c48014000c004000c0d0b25901d4843e480503500250300b924802800f04400540d090400c030180000394000c00a51801b02c1c0340c002444115a544009640000705089080c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 853112553 1250 853111303 853111307
    0x1003060c0e010e03031c0b040e010e0a031b0f0b0c0405120f1b0a0506090f060f0d0501060e091609090603051501051c1e0c0e07021c020c04110f07050d09050a0501 71
    0x52041c09101b02c00100d600000c04000c9070040030200c5441380c19500b0040c003482203020001c1d49000d564800d9680e20780c4045900c04a5510002e0210010710341d01401600350003180100c2c4555801580064817940750035592000541d01048040f08190143c00211080d980e8039414450900d40c04401c80403200940018070004419030107900030306118900100328490070351141041d510100c0c90107840a95102c090b214030424030341010134820656070a180000c1022482a03040c2e1044a2010b09214240c6c2c4405140a22900e48070221104104200c00002010301440c0070300c10007503001e50090504c0307207840300c41224103000c16040280511851019041000d0740040130018480d0022001040420717071641d030501700220403038054040800c0d1a408101d0b5149003101300c4c001c821580031100304003003191581d240203c107181c1c0400942c10280da420200d0505030403100c04201c0d0001d010349040c2066440e0390031a040706105803403c1d4000e4613481d89640c2c014850001800701110000d0b6058580400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 853113803 1250 853112553 853112587
    0x90d08061003020d1425030c0f05030403140d1a060405010903020904061823010c0e040e03090409060e100905100b0f100305090114090a0b1003060c0e010e0303 70
    0x1001c400c141d8009410300c0700903080d40c0001d1082c1909039500d02c02d81001d24450020601c0505180f0410140d1040d0303503d2540640329200081209865494050070110001d07100c0c0e400040c401c0d8144041d10880c0d0307020002000003018586580403000450000140c0c10503082001540e5060099100b0401402160380080e00042101e0741142c1c030540580d038a16008010f440c048100c0004600301c00170b480100302403841c100d015801c208507061035050b032001c0e015081e12101045d41004c40c0c101c07841000c007801d1a41020340310895203400ca0f4607107220340d0040340840700790010a4030395a690f03c810707920540d4144058042010145803d0004031a1500c841c1e40b60742c0340c115000d001c8c2c1d5a45522034056191082c1c1480441c80003800035825260004001d03018280455450619520f000350001c92802d01940707140c0560227a000902031801030b80d503411003003140507042c0d0176107050b1240c0003c0003c285005030358500010341d81e80c5414603da10000350040322f51241c1c1c1c81c07007034100f40240702c0d94408a0003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 853115053 1250 853113803 853113829
    0x12d0504020f04020703050c060702070303030b0414041506050628020a03080c090a0314151e0f0c190905030c010306031a07030f020c011d070e040f030905090906090d0806 75
    0x100145d0341c0c542d51a00750754900c1003035050f40890003403100300300c0c4058010881e030048901a880900200380c00034108402c48501c1d80354181b0005140c0041000301d621040700500f4a5021351001400b075445500080040c0c100044a94418040103010340c010510800c010400340520b0009040d107155a5502800d003d000801c21003209602056074074640d80c40a480c2c000440d00300718618440030b80e00940703a0f152400340d220ba40c02840b0030404500d00248594501d030045d80d1000b1802072a850702154003c0c0800040c041d17248100d424400b5510034004200317041d11010306900e07803401d00c52500080c142040000c9800c2c17810300d45401c00030004501d20002c01e00104003043c107040c082e0b5440c800b0650060812021101d140c91000c41c49044001c5c05612103070602281e60307501e40d801041204e10070381d1110180280ec039610f09030710210b000508690455084036129044c4840d030162608040b074809141180d9240307071680400203001d02c031070781800f489121041c1c3d45041030051030b28001096201d07541c40 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 853116303 1250 853115053 853115059
    0x21050307021221070305041704060203090103020309010603170c0c030a0b0105010f0c0b1816060c03050d06090c170a050609060d06110c0a140105130213090203012d0504020f 76
    0xc1c1c03c10515189810030b4214500806041c00d07030342407a110003001420101c9084a42c1c1d000440c40d41034002c2da003c03e5900300c1c0d140307a00944c07501e030040004402a41000d083c03220039641354440800040c10003414280c82c54502407186445020454140f881c04100c0e400d0140640c100c10302210104108040489c1591002e0800034801c030180e410459000a0740c01e0080d00501520082c0b000b03018440c1144181c042c00712003117074000e248a150500d0f40e81c00714426007002c0340c0a0501071001a025174043d0441d07101c600320000f200ca56895104058620361201500090f040300740000021200300c4105030084007080e0704000c1440d00101040c13000e140542400c5c490403440551404201e840c0e00010058030b288603181340c8401d41c10100a5882801c800200d1351a1505440100752508c14030996105860b1040281d1282c0d205030240005012600074003949030380c940d803240c0090f032001d00400180307000c0460308644800c61000c5800401641038201c9900b14182070038800583c3d2501c0394030360b52500031 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 853117553 1250 853116303 853116307
    0x30c090909050a0b09010506040b060c0a141207080a091e181821050c060a02071a040308010311030109020a031202030910050904050a0c05030a11090a03210503070212 73
    0x1608115107002c01003000280305104c0102085900b86041d0001802558141c8080c0100d040746810062b003405002c05400607a409903010401242c0d11103020241483d180e8203a503806080e165042525031f0019000b694850030014182d40304951040d00c400080c50303003044002c180d141815104150303030301c5481100815047d5884842d03008403694800400341008650042a00c3c0480c60241002080310301d50002e840d004071021000603000d201121124050040030b0906a503079500302d00c0003134201e2101a910444036100a088145041d000c0e6030089009803502002c0750b24503d0681481c1f65000030190280e41040107400042c0c42c1c9010400039a5070107a20052580b51008080b4035500414900381c0c0e100d115640700d400d8141c0c0000041c4a85881510240001d41e544010031080d01c6440003110002442080003c00c0c100321a4851185060b0000b00d0314609207150300002c182c0006c54005885004000d030030343c80d8941003a02000306801080c20480d00354030b043c0744040e4995090340640c004080300 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 853118803 1250 853117553 853117571
    0x305071e2019090e01181211030f0f0c010f0608150c070507031a060103060f1509090e0d030b03060603031c02041a0703030b0a2111030f0a12030c0909 66
    0x1901a1040660199000c800001c590b40d82051018000130300184442c0d5103130011254500a20030036444d0f900d500100501c0b441c6022134411900d900c44080900e410340802c3c08020400b800410080c542500e043ca025500d030703008141d80c0f608546a508c0600030440c81c1200070443c181c004140c80340c900c201185042116035401010a0740391240e800000c05c5405550008030401c00e80100c03039101800b25000c100075558400d001035040f41d0340c900440b4001c41e110f0604000b01c0d00030000018036103003240352030b4000507079504950080d61410840b01045801000d0741d018425410700c0740c01142c09088008041078206070003c41c0e128441e2200417406c080d07180300c04c4682c014103a0110b070000e0000c0c901036009440b5201c1e40007819007054004800003401d00010042c54603199641e02d081d1194404a142195100c9403104c84400e91312408458001c0c01e107640d00203a60b024400421444004c1010740300710081880d028401c180c1c03a4140805151901c40301c00074165020701e800040d03170800d050019110507 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 853120053 1250 853118803 853118809
    0xb040303180308012d0305060714091507081306020c0f01090b032d091605030604050c120f12070c0e01080d1d10091e030506060621040305071e20 64
    0x1171906481a0071814101001007080320004480e8413079409655a0303410b07004171303815a2500b4490070921a07400003510103071a00010014006095980c0f003408aa4074203a0044054000030b1202d5011402507003044c1040b04060800104604042c03d007482d0100c182400c2c030000c0e0311f10b03020146c80c0c102d400040c5940d07055a12480b80010020b1503091040720302c00e01e4110810303a6108484a0f96004e1152a50800146805c0c0000e20b103001d0390340500a412186107180078002405404a1880c505100782d142006000c00306010b20100005002c1c00c05550720440d00307082c895110aa480101182002340040080c0d0b81c0214101c10484410320304406224140b0f40452415560288501da1143c0c408880c00f259580060b01a412504005080c4120101d458201d00c00004144005402d9400c910001403ea203401d0008140703a480c02d0003044000c4e484141503415070b1034115811400325400003501010b122501e01e20030300c80b13104103400383c21200f83c95841e04411306501007511903028140e000303118103503 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 853121303 1250 853120053 853120109
    0x1e060f0b13290c0f0d140d090206090a03050c040509030a0906181d060f0a0501050a0305062709060f15130b15120606031b0d0f02070b04030318030801 66
    0xc910800c0c4079162004042c50f80d4650010803218819807007240e44200046000310666441c11022548a904021926001c2e02c0508616a0200d030300c00410010f00c2059500d958040018501450007404646241c070203000032204003400c5030015920502410310083c1d44009800c1c20385080d49800e5900030801c0d00681e03c0c40304135802003400800b14500d2016290305010f500c070310500317045411801010171701d0f003841050b61941c00b800d070010340c0802403c0d40f1280640c200c42d801c40b401821a800306035826100b810007200114a080400c510241407045008041002540003000030124041900700b602d80195400e00404000e40244000c6002003800308460788403606090001d03044c50784030101031103507040d6a4407940d003004c0e080b00c5060206480f405c16009507441404510300d94011054040c141501941210801400d060b40301c62400c1c2001031140081c1c0141c0c0d00c54a20022942442c0c500941a5000600004080c895150b11000070075444030500e0304540c50070401e03551101004c9840340c160 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 853122553 1250 853121303 853121369
    0xa05090c100e0a140108070c030206012706060216091a21010504051c0212090f122d0f0606010f020a050f1b011b060f1e060f0b13 57
    0x42800d6010000303401c1c1041c142c0e803130f030610241e0b0340c03125983e200c2c40c080d00c3e10a15030b10702134016880400140302e02c010807400d91480e1000400c2010720007138210b1800c0140da2064000c200103130413a000b4481a407200c918078130098604520b0603c0044001c91110185000070f03042603200d81c42040f01c0806400700d00c04841d081480d480c0c02404945490306006903646c8030503c03074a0110190000e1600407520108150b0714540c40e41c40c43d40e14000304142040324043d80b5806099015a2440160000a508214038202d00301150340c0070b00c040d00c403100072003020710b0390b084a03004a8102c1800c1150403a4042800d40d4010424200081002e00e1303844128031f055a8074900504521450b4881d07600300388001610080f1518034122210340c0c00070000112854400a00610103004042d086071000070466003098460903c4003c001400c031040b00004a1040120b4000418140c2e90b01c2d801e02580d682016070002402c040d000c414540745400720424102005440b0308524554046030812401420007546045 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 853123803 1250 853122553 853122559
    0x405101a030a0902041d0c01030c0c1101090e01080a12090b070222020f0d15030f0b0901020d020403061a03060c0717070b0c0c010510030804060e150a0201140a05090c100e 75
    0x4410317142d03184d1b41110788010206515600c80d500c0051b032198071a0080c4052540b00c1c1d5500102d80c906a40c0d0589414000840c041c1889a030b1034001c102e504c14ac0080038020300c2110001d001c0407409040c180748175501c5c0b5581c1402c1040380c6006002003408802118012a8151540d13a103e21824100805010b1807461000300c21b400005d521441c2902d102c040c2181d41c201c40810030098800c00e4920400319060712001b014803401d508600081100141083c1d030226284001514010940c2c00040c01c9a00c1078004451072551340d41d00401007900441040a100030640041c0071608116220341940d00542000900408038601c0030001102c0110503280456807241008149081440b007401c0e551308036040d41201503103041b00084030300d9034071400c1d40201e07074011031028a0b0600703001003103803c5000c070300c031494110503800e1070580d180305910014021a0140d900000d009880b41201080b48600a03001160550401d805d201c40040041003640c941041140e0071095021101400e0300e1028000030f0382c9038 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 853125053 1250 853123803 853123811
    0x624060c241d0c0a0e090d120e01060b0a180501080c090a0e0709170604030c230604200102030f09061c05010e01031a1005120c060705010b0405101a030a090204 70
    0x34040e0000802c007501a804646400700303135850305c88881e900c110413210038041d60b200c09800c40f1298010b42d0b000394120841c042c0407904120020800e425a0b919074805e06407040d0005401d03540310740c844005440b03200b90b95609200320b407074200001c000380005443c03540c0328407001544c1e040c143d4410260740018848564400302c5894a841c001c5d02201552240701c10b83c038407900721001c82d400081506880f842e40b688911151011503119082c0e81c142c000c84c0032011400039070300711001c40002c00c0f4941c41944034200c0c5540c1c44081420190f88001d003950114103640c8103000c152800b00320201a0740040d2402e940701a01c03110003900f074500d640c0c2400c0e8100c1d80c2c82e142c0400402c108410016040c1aa80222078a4484034150403001000e450100c601c1410729452000c1800755162880100d60550400002c6948444c3d42c100060807681c82184201d82e169518041d01c86581024003909a0102105480d065081d10380158144c181c0c19220b0213942d4a640080007811a09043c0e001c0075100341c014000300 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 853126303 1250 853125053 853125101
    0xc0e0601121e18030c150b03010f05060103150501020c0d0809120709060b07110904030201200903071502060a051909080a09050a080304050d0503070624060c24 70
    0x101002c5000ea21000000e0401446105840c1c8508140d201c0d20350543c0c413460b10f4040f940710300d8880080c0200c808400d0f0b03120682030005aa01b4024001611036402000500c4c1c01d24000240071980c4541c0c1c842c00c000075075031042009a03004070344900c55090607210010f0001d01490246200d21586c02d08035402400b0b10112600244006584000d60307201d68420030071030b610b51004c054107004501e4002c0081c0010b6001080030b00b800084030b508030380b0900003c80c060300502c0c990043c0304034820b0a468052030100d04035605180400c840e41c0104500070030200b021081400080d20781000401525806440f00d000c5218040380c881e01c6810346030800e04c104240411454407007003540c0141c480b072002605281c03001c01c561902e000c040c400c070784d2144015483c00f850322081c02207404c218401551280014007090002c58624061303920701c5452001e41d02c02c0c0d040c1010b20b01c54480d0f40303500094200000c0310340090008030359910010b4240315800445403a442e03414440c80240200820b28018800052400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 853127553 1250 853126303 853126331
    0x1005010c02120c090108250510030b0d0501020d0902040b0a080a020d031b06020703030510180e03090603010f0e07020313030209090a1505220515040318180b09040c0e060112 76
    0x140024629407504803030100341d10f10f50307ea000c00d46800f0b000d0b4041e640c000d20310b036403900035403003034540190280072111040c4081d1259400c9800801000b58400e4480320242d0451500c1c0c0300d1580c0c6640c0440740c01c00d0003420b0a280c0c5903214992031000340507840e0348800f80c003458041c02018040d50f036032000800d01d00d0410700e403960180d0481107007207001c00c3c240b001040d400808143d108051712a14100c2e400303c0104a44103102522010a174107030130b80410400c0103410b44440c0c00a6019000e6103149503540c615002400c410b5080081143d0110342080c07100044c41c01982c4840340c00c880c0c0480f900d0800c3d403902c0c0c501e43d003031440031b6800610095034000c4004240006805c41e030310030785806443c5034040c503801800e010503031680c00e8001c02c00e80141002188017000300400310b0700300c0d0181ca00110020b035504d00d00441c14107141c0024400d80c40c0904600310319070460003a1090054151140e410710309043c0e40790340312100302e8080c03002c3c04000c080c000750250340314001502c10300c1d80d40401480944a000d0309 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 853128803 1250 853127553 853127563
    0xc0302040e390108060d06110f0d02040e060a0e270303040f0b01080c0102030d050c0405030d0c020a17031b03090406120c060c030210020901050909010b0901081005010c02120c090108 80
    0x12102c030709212507440030140d800f03481451301c242d0000c0c00140d1408910303540d01000300410030310312180c43c80030b0040c445600c841d00007411541d00001d90042c0e85078201840c44120282c020324061044040341d406100408031043d85075001000741100d4400040c01000c246070251411003140160301c804805c0109000640704c00c0e002145c01414102d00590303d0700e001c0e0351a0305009980307902581c401c1050680760103c80c2c1c0100d50045590301301c80d080a44a60010307007400281141040003c003030b20650019890000c11401c010724107629a92100500d8026a80c3c41c0c0c06044c54100c0707240301030f224050f90345400384121444400020001c204940d2078170060003c4510a0000b5104038058800c0410a80c0c0500ea01c1580150540c00810050041401d550003075480180340300e04110007030101501a849600c4000d019049140e01c854807003a804c0001400603500038444850303154504000c0003030766005511074417215019101129210b80c48181c5528005090888541003a29a0000520a42c02140c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 853130053 1250 853128803 853128883
    0xc0a0f0303050412050a050901230f13350106051c05010608011404021c050604060203061c0804150c05060903070201020d021b0918010608010b0414040c0302040e 71
    0x121341007a04074000d4040b5500c0c0202010340001c241d040010303d0044d070240300322090040052007510103102c6034a03204030490700807480301d40080303001003003800e540710090913158050b24900c1c008011102c81110f1500b03401c0c04c2c4c1083c84004007200321103040e001000390001405400d01405e418041c03e40d01c0c03001c9903416214203054655510b00035010810b0a0107016610000401240c00b20082d01c3c0c41d0200124aa01406059000c0050216440010301c040c020548114041c00f40161280703003200500030404408003a0414031401aa8040001030145082c0e409544840300c44418284148078165403144203140040c1081c4520300c00c000d290500007008041d503c5c400c0c1d00741c42c200b0351000710607680d4401124845a0240c0101200c540c20304054581c1c56114601c880300e18124010f8404039401c440c915004500d0694441b002001c0c10304050260041c10302c0404102c41d45031429840369074a051050000038031640d116500300032104010004000b60903c2426030100300c3c003401006207903043d8801 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 853131303 1250 853130053 853130063
    0xe10020a05101e062d050d0210120e06180604021005030c0f0c10110c0604020d03050d14070e01020d0206060d0f080c0c01080109020c0307140709090b01030209090105090706050c0a0f03030504 84
    0x14640c00902003c5039175070401c4910183c01d05107800125030800000d40781204200c0100481010410b42d00c100501038040d04500d50b0002d0101420810641d031041840988034503030b5503026070240001078403000d121845800c01403034803580302d8980300301800e0280300d00340c18048003000c0407503110090310002c038a91200e9080e6902c00c004240c400145d440c01c46c081c2f21807088403900601c00240241c02d0140c8141e08440c030034603000d0318040b114501c520880350781c4048001c0100205040050b07542c0c01c4803c81c1c0f0080000d0000300480100030900940da59001422103014100d0f41080703d04101c0d905a11005140e840407083e80c0315500351118a540c4d42d465640c90b40081d006200000f1190181e100b1603480c4009500034604e000d8032511440e944624001d010941840754080c00a1411442d1044120542c420520011294075500400c507044c1c502038003070707101a4504002d01ca4039400000b4200210762003401c02c2500c9240311802e003400c1443c5081c010340482403004000b010150300d5880f1601c0380d0b12030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 853132553 1250 853131303 853131359
    0x1090501090c12090602042c0a020310061805030604080a03230601030b010e120c2115101508070f030903050d020c0c030d0e10020a05101e06 62
    0x2a0714072034192503003486000301007070030304074209090403040d0408442c65010b00d0002d45419a00e00380782d4410301a100304100b008400041c002d01e80300303c540c82030360001d107402c10039400d50800201c00c04120803580705150520943c890074501e1010910b01505c000d2400500703a078910314082c200140300740d00c9040300314000f03498000907807521110f4803100c40d4015400202078096580b0500150001d1440c104240e051003140c00c050406070752000030583c0c200c048000030700010007124041c00010904004030001600d411050600b01510009801260440c020135001d003980b035400094061041e150050000b128480d42800e00c0701360400c2c0010700070001c60ba10310307090540100c6e00320304480141000400042d002c120041c201d0302c0c1078024141f40b08600c402d0303e02030f0360603000003850a09200e0f0a00b0214a1074501c8540c00d10300800e002c071440c8810f001420b902c0d501035480075211594011b401c141d55079102d12031802900e41c80c810002d012503010f020409291501c10504c0c0141c5ca100c05172880e4081 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 853133803 1250 853132553 853132559
    0x1030903090b090a0803030f07021c090e0a09060f02041401030513020913082b0c020c011101060b04080a0b010b21041e231f020a05070512030103020a060504150e0f0a0e01090501 78
    0x42402f0302c5944440c03940c80740c0101d405c0c2010894030000107000d41e290f05885903180d07404181c40b4825804d00400c054001a5141d1600c203424a20280310f05d0118145417420040091b860750065000f1807503030381184c034820780d5501c40181c030381c09099886000d020448003103110040c1428086e01c00440d5041000c032148440c032055400000da400745186880160401c80c02811194010340c00180e4503900180040390154488819130125040350b0b001c0707075070356111600300403d0082c100115800361035004402071910800d40e44e013807124040281404030b86080900050709000c0030307110810302821561b00c0030f90b0101041c28502010850403a10460b00f807100c1e00401820f28001401602184074400d83c1c0b0400300d5640030901c001d400c0000b5000174800200314000010308244101c45e404c0d4200001c203a10fa50445c01805140b84990701b042d42807020070082406113603404000780340c0940300f625140205003088008035402c0ca803020021600700d03008641c041442050302604078107980c0b00c40010003042ea6 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 853135053 1250 853133803 853133833
    0x70606180209060d0c0e0d0803010f120f030c02010c02220b0a2709061803030f0c361d0901050411060f040b0415080601030903090b090a0803030f0702 66
    0x12803441003a034810300030001c911343c0c01c5090f08104081c24483c184100340000650204554041c816803c40f07030264000018011800b0050400c40600f545220307041c2e07903810075601e055000381001030150920600010842c1160f104803404490940c1c090201014180b0303040310540110f51041e0080046810b00c405074006040c400c0e4a1800c49200540c076880c200200840061000000c10082d60038035140c010240c04151240100c1044140c0a038000312000351600b4010104d92030b0910506046060084c04580e19030b100691440000541c3d13010003020140c103c05a601088a1000402d00480820300040702d181007110030004450510401c4c246540780100c05089440444000301415441c03d2040614248000035010110070b200d901454540c41d0592040f481c0c000d58450018114005400100c16910000303198200000303080621644141d85d40c050509040741c01076810a400110b440b06042c2e840a81400040c41290b060340e6490520080c40c0b8802c480c02c40742c000140c4540c40104480203 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 853136303 1250 853135053 853135057
    0x7170c04290f10030c0e030307050a02011b0c14033f1213020d0f0f0204111804180602030411030708030c060408030a0905160305060c0a0512040f080706061802 70
    0x40001041031410f2030480905400412070401001c0c100700d038955000d041034504000078018030b80168001c0481107101d200050400e9014182050500304485003500007030000b450780030694514440d25801e101609011928050101203949114411007091110311100305000d8040700003070000d07a4034858101d46692000b44902060012040005000101900030201e00150341031300c020403113000080700da00c1e0056803054a04c02990840002808001141382500c200300d251001800124100301400c9007181c51844402c8015004039241c5143c40d0300e24a00f90300d1000c14542c040821922420141005070042104070080b50091042d00760103e8251000816507840c6032800d8020b107074640c0c80b03554082c05500301405500200b512142c0120002d03200b40079040303a102040b074244c2d004928508103945060000707440b8441000003049001c0c1c40c035070f01c0400c80700c0c0e83e0701e88000c460a40e03c40b4584406808950080a000072101103400002c020540d008802228502011250b00c5020315400204078 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 853137553 1250 853136303 853136329
    0xc22050111191118040602030933060103060b120a0b091306020c03090d03030b0108010e010f0e1005090c07030f03022502120f01290307170c0429 64
    0x4a212181c1590004030041003007450030300b01801800301e940c5803804c80320a5410a503001c5508a40100403c83c0d0038804000691841054181d42c9c540c4c50041054003180b010440c10445500201c1000140680d0080c0c0000c070082202c00c6815644252400026001200503580041c0b81410b16020040320319040407014050b03003c2242c081024074859031064001e60100b8407100b401e00040c820303031005503215014000060700944001c03404040f080001000c0d414140c004644024040c0c0c014032000c0c1402c1c03141c10640702c1d80d0003111443d0f1035400b501c80da410300b1544401d0f44074486104100200c039410002c0e0409510030348031140b214800e2601036080c0d01174004021001c034062040100848259100c084055001515242c0100307890503840b03090180b41e21034000107039155104220f4040140e013461041412003000622141031038000030b51250381c0c620074200c6452000d40b100100c00024801000810b030001c000700a8500c180d101c0200c548902c408150074201c0004400c0702900b0111140b80134 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 853138803 1250 853137553 853137583
    0x1171002030c040b0706060803120601030b032a01020709110a020d02070e07050901110a030305060a2702030603120a091502060720160b030109230601080c22050111 72
    0x90508020311a013150f00b00842c155005500c03040005009201400107041500d0030382e05a07011403401400140559451041d1107009034010942500c0509581d481c43c2c13071540d0a0070034417844042c48030040349820312582103d0045442c00e90a41c000c03a02d504003c1c00b00c0790680d0240c6019a10070704c41030341c40b98100d2280c1d00a400a40340011462445035000304500141410000e04440141c8403c1c0e19041080030110003182da614107102051400c0d030040b100500b1040070f800303c45610b10140c502c802c280003404908841c0c0100100c0c074655000d202540030444049035250b254244070750001d01c098128820a80009800072000008610100707031544998543d480300801e001c142102188c081c05540c10011140c002c20003004960916104000c0080519a1546450b541040740840c204c1b000414144001580f820340c3e545540c5d058107802e54090002d08000070a0b680d0b07000d11014034428107a0f140426035541543c0c00c0308000c000300c000e003580c100b070740d8958a85111302900d41c2ea94440c8424051 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 853140053 1250 853138803 853138807
    0x2120a02150a0e101205090d0318052508060a0f051005060318160603150f0302090a0f0605150a030e240604020c0a050a030e2b1a01171002030c 63
    0x10b03d4100003c204143c09800d1400482040306000a04215402519100b000303801040c0e0504405600d070144524100c17900d10f200c400050990395aa40d181c5200e0301701c0ca41003c1c05080d40500056868107280144603c0054486602d411000c0d440140450302c11005007134900301c007240d15054007140c040180c8030041e00c02e80c5140c070340c0710720b01c10b4285400354540c000748a4014005034071889504610000c04036a1000b040c0b00744880c4c03002c08a4002600141c1c00480c40040400260fa5904e152503001050160b0020ba400786a406440c09080d00390001600a514800e101403903e0402004003074224455404102403111745069030744585072034144400e42c400e0f074461500301d030880308941c0f904541c00401c014030b4080b06542c60350820b07802e00810b94440e0800741e03299080c150814803001d20b94508585c80d64a5160310041c25a149580b484080018180482c603603003007009520300e0020703c2030502c0c115900346d0380d100000e840048901c42075544502500c080c401c01e2094900075240618559080ca034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 853141303 1250 853140053 853140077
    0xd14150f101518170309011e020309120f010911120c03060a021b060403050322080f070f171309150501230a0f0e0d02091603060302120a02150a 63
    0x44651545440b0700f100244030440008003080d224942d2880100c0041c040c60310303541104005014032802041c040740c080e4000c007024074071941c08811140d644608403a811803142020280d603207049000800159990b2a001301c2d081400620381c1c0c01c1104034012101d100e00d803040300f10015258008017501310b801d94041c2001c550910902e8024003070b8000310f1124594202c541110380ca2038000c0540301034020030400024072162440c010030202d5120302c0440e1900382c00045682c2d5100c10321035442c11200098001ca101000c010300c560010040030f400450030400403030740d131079150415485080080480c411308640040c0c420500e004400e0125481d00c07081103001c1c80c080c0103503840b0741e0114001109070038140d212400641c110018050080856a64104c0d000c110300f405401c152060b040c01d8422075180364031000503030781c0d8489581e000760b03c0c2c10014511b8805c1d403400c4e000b406180d00001d51000c0840b901695108000030110380040c0200e5000c25982c00e40054030f41c035403040a00c8040014003444070f0b1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 853142553 1250 853141303 853141307
    0x3010e15060301140a0c0327030f120c090e0a15030204050601031b0e030c06090d03110309060406180e010308030c090310060e040c0803040b04050d14150f1015 70
    0x199034403000180001c40c6400c0340305125081070313408503034007503800e5550300e20706480e141c0c1071144014990817044000c0105000d81044005104104402000c105a1100d80e07178070144210301c1851410b088003400e012040b081c01004c0c1181100303000c4e40c4042d03200c44002a44158190040c0030410301ca00c858604810b003140c00780805404014095418161034001d000d041540c20141441800030540d169844a04514101400d05400f00c44d0144159002c3c0041e0315075903a06400310742d03907a62601f8404820188070710743d9801c46c01895902c031780c0014041400210503170800c03c0103120030150344800040303980305da550441c40d02e07080c0805402043c007880014101e8004c0001401d401c000102110800e0307008104c6041a11601d400101ca003420b284203000810148c034890101404408015505042c10618000d0303250040d40309030b502c10003845c1040c005202d000030082c6034050280042c0c85111601c02c52540c0700030b90540300540441d8510300007400c40039045200b14180c07a2368440c8040d00ca88002c0007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 853143803 1250 853142553 853142593
    0x405010c020d0e3313050f090703052e03050c091b0d02070f12080615180d0c1e150905010c06141008010f050f01060809030d05010602071403010e 64
    0xc14010030b1344034003e0803514a41194200c001c0c0c2c16640c14a646540140c08000250030b184d22803809807400d8000c40e840ea640304003500c2c0d0f00142d00d103000201650b0f440140c42c1000b4007c031500402c44641d0240c406448070100c00c05d0242c0f400380381100c00030004c0d0828001f264108a61031244410000c4400d000300c41d0080c000d1000100ca6a009410315403141c0720080741800340103044426a82c40c1841408540c0c003c000d40740e02610072111800b90050301c00000030248910501c1100d41d050100a1180c0b507603540c01707071208580c1c00c40d05105d401902c0f0420504035402044400c1d41254450200203031030019409071071840c1800c0e54480315414680801502c0d4070340070120444445480d9600c85900e41d03002071481703201c0e440f14080011038a103030002090844040d80015840c450038003040040c0003900602d5581180c4c1c080c0703810040f07903845050450a41c09078403940f0344d00f039007846d000142c855030005201060342c041650008100c201c8404050807200200c0d03ca40c2c1c942c00c02440107c03406c085c145 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 853145053 1250 853143803 853143829
    0x2402160b0a020f070828020a0306020c0330060a0807060f050c011514040605150a11030406080405061311150c070801230106050f070f02090c030405010c020d0e 70
    0x44400044000f00500c0c1010200e0700120076550010303c1142520211124a0000e844500d454121012003034000c0742d05050715000150040d6000119248062020800c49140c4840084981141102c0d560310fa080d0700030210801e0500c152000210310300340307172401b4140111340c114001003154928019007541e001c03400c000c00100f445024420003000c1c8600b80601ca0100c2c900680101511b0b04083c0790b040080c0090004501440c90900184259203c84440c0d54024400689a507252682079030b044030b810740b4460080b01107001c0428002941500041c0050041c1c0c414000d80e1180c2d56a406000c1e0342e103a202102a00303480280d21000d50a0804402c207101c00810400741a10340914146c01620304031490b031101c00503a5450307409020903100600717007900446041c01070440c1545003410080450055600c041c0b000070700010403030304005914046000d029400341907900280b0b040c0c03c43c01c09540085900b59202e50800700d034a00c040744003060400324010161202c424440518040c0175211020303078 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 853146303 1250 853145053 853145057
    0x3070815130c170f0d0207050a0e09070f0f180203130b060102070f0627060212031503060c0703030e0c03120c010906141909080304060509030d062402160b0a 69
    0x6901040040003d036101d020310107000002d001c079980300800c01e0301d8016100150703402c540041000340419541c403c9404115551020010b02544404484509000c00390340460890400d0000000320f43c0d02043d00c1e0400c0b078440700c00c406032070301c0300c403030004141d1200f20340c42049121302d070b4140c0d00080e004031449500182d040c411281510745800181c80e020b0444c0d040300011407403e00c2d51a28440300a40d4109100100d0101210850b2810501954403c8150303ca50800b40c0b0100014140c2d6a01c0300981c1c0c1c0c2d42200404907141030610508060345a4400c2100743c00103800c041007200c00720700014a0100480d0050300512540c8159441d0040caa0031440300318881e9500c4030103c20109184d4021011301000d910f49008480c2003608029450010070b00c0e600001c1ca0404250501090280c804c4d02d51094214a012800e0342d6040452070445c410920410300304da107804800300e40d0078043c21202e05419044040383c410084c0c0048107903034501e1a00d401e1650311003000028070140300c071030340a88a141c1541c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 853147553 1250 853146303 853146323
    0x70e031207030c020d0f0f0501021806040b310b0915130905070201150305060105090112080a120603080d060611070324091a09100e06070309210302090307081513 71
    0x1c1e0b47c80d101c8000e040d4200356426900800c420701c904401042100640c04121b405600e0540340400403c3c0501680c903041d83e0100b5407458003086600d11403800d10201843c02040c082c815112a0100c00e00c2c0c100a813000c0c005c8038809040c2c164081c0c41d0040300d20701c2c00050b2540d54100d250025010181100424003c03c554a4413000ca03000400300740d21001075480707100580410740c1010141314000a050b031080961418002c1e403900031560707000440d050303625540352818080c040c44688801800103a070000781015400140300c00c49400952000b0265280d9948a101482a82d103402da940c12581c04090075849195000e54140014000c0c0c800c00101d083c003001c10005c8035600c0340c06072681d136a142d04140036441d000b0000800380c103019250401c0000e51040044210910003543d5844c40244600c0070f2555070300500302070101f05021084030360404a02d81280b050300302802406508103001d0b4034024450300d00d0106074074001144c440c0c0c01382c210f030488101c41d030b075400c0d40e0300c00c48800c00c081566503400d1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 853148803 1250 853147553 853147583
    0x30509061209010e030703090303180302120d11120a270b0c06070201090c0501050306121e1006050306040803040c05060f032e0504091109070e031207030c020d 70
    0x403030000c0c00c81d08034008101a46468455a541e094034036031144014650030400540d000243c202e01c9200559406146c441d2103546500c0c026030155842c0d42001e5070084003454018090900010128400246e075940d407461003800800081d51191020a4240383d032105101660009100300b1004407a0741c020b40d04040400321003100903803106115040082c41d41c40c00a010100c01b0410009150004050700c000c002c02d580c01c0d143c1401100b15800b6481c100040080402d28036a91502d521113941008800d032490115000b00c0b0604803403034100402d04c980600d00c0c020049080610400d011180050043d1aa582d207a0750b540b031155000030411074103407e5440010440e61215006032106c0d1514540c690342d03c2c10705d083c11603e2110403801c0c10711300ca480e400c05a40017003003451061044850555001c82c01ea230035454000585442c007101203400519003010094540d0784140c1142404509400340d649501074130382c10303102c1d62061100203004941029420001800c09a40c0c41540c1c900401c0340c2c0003e809 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 853150053 1250 853148803 853148809
    0xf03090213050402090f0402090402060f071506062d0e220c030617122d0901180f1e0806100504060602030717030402040912050c1b0d0f030509 63
    0x14a8007039191815a560b020081103003410001c04c1d401c0000c031015604649881d6001401f0300320300a000074007601c008541c810100070107805881003154490543c041e0380c400301100300c008000ca40701ea04009401c411400140c0d184480410075200221000d01240b8007480c0c5041d620183c6020689420980c00c0078010b80e1004860300c442092000c481010030842d800d500c009041c1c41158001d0745440c030400c8281d000c10b082c0019400d1029103038849068540d82c0040c0006400c0360145081c000440f000303070440404003185401071202200c26210040c1e500403d0220071000300150003109580014200148814440301212800d100581540c0d2030610340c1b5401107074144034040e10313410201d6294000c14807652030207003d0003004d00303517078401103080105075200e03202c05007450551140000700000104066443d1781d0003480250750800c0084095180300d400041c0103602c06010710780103005000003e0010350203054030850b22200100141d40c62196503c0720400c41020b40822001d21404010140b8a52 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 853151303 1250 853150053 853150069
    0x120c0c050d1a010b0c060a180f02010e040f020d0f0510030f1704060302031603110405060304140d0507030306090902010c080c01060e0a09060605060a140f04030503030f04110111030a0f030902 84
    0xc4103101586444403100345c86149404c4015003881080c508000c281002030190459014440750030400845000c0700314001602c0c02d0a0360824940c21504003414521150800c1d0018076820b1400f0108002144401d0004812030740300355030001c010100048200041540a0345981c04180902c4d141c20302e124025084950aa015510110100f0740110800c02c0124a480c02110300d81002d060030300c0889038002940496200c1c9000c0d4070f02c82c40020002c01c0a009156140b913004030400812201e080c0300ca864081d085400c036007000c400081c04e0100100d50030380b25000c1e140a0680c1030f10751036072a0006a80b00700b4141c00191060155660721000050401d001c4644540039506400d000102000c0a041c4141540d145401c081e005100401502680c01da0011190740e40e07208101419843d201c0c1004140802d11a61340081c082d4403000c41406004094840803501980c8140604050f0081c1c2e800155034091413021305110b80e400c00e110001555004000b080c54440312441c0000d2400d046600040480c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 853152553 1250 853151303 853151309
    0x90f0303040308150907140a05040b0c03040e0a150b0306120d0e190f060e03150f01330305180a0602070b0f040f1709120604120c0c050d1a01 62
    0x240d4880c083c40054131800e41140c0380300b0382c2a41e52444514140201522010b82d09500030700140b80000e072441081d1203001980c01030326510202698911910f540c080c1d50750071502403505a892a003000c510813181034802c4404070806150000c071400e203003425181940d0030003022103800c81e54560603440900b005020144c80000345490309802c4080d00c070140b14890409104000300500007210034040341d03112440d0b050443d00e1500c2d00600e00e05445003ca030525003140d80d03c07030419050b402404640289011041d0680304040424541601c1080a940008500c0741d03079032080c112105418190b562007608103940c00b03d8540c100c4040c454000701d11501c0d1130f482c071505498070b5030302040c01c0003000600e6400c5500051155202c0c01d450801d62101104100004002801024415448003440d0341c46030554400b104020b20040b110301c544918a41c44280840c3c08840412200b200c61000703901445254000a402c0700c40c0f403c0c0c10b400c0000f400490015800d05036500d00801ca0388440c030ba000503d550b80a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 853153803 1250 853152553 853152557
    0x40c0908100507030e070806060d061409010605190b0904050603010e03072001030b03100f18050c040b03120403021c080712080108060115050d1509091127090f03030403 74
    0x85441e103e80c0c004d04a818820218190b034000b41002c000d40c2d4000034071990171000403240421504400c1c41c000e00240903554012a24085500070480d90000c19400441103070402e40d098040c0c1820480301c1c000d0450107005a040495041c001080c82d4285903010540c0440094000154090b40380151840c40c0c00002d0215811420484040c101d031044a43c0d41200719003e003014420521380c00002900d910f085040c45440c5540e564006122000d0394200e41c001807201c81c60344045d0081c5041140c1ca6540401c080c5014500b40351421130f041c100010380b06a02e00504016a0805080d03600b000f0741e100b03c2c442035103411800c0080b8003010035142030040c07900034450f10320381c40740722192072002d03004110590120030769401080c0100a80030040d04c80c020686041c1c54141d0303640c08540c10030f034002c1c0000600c3d004802000e4002040d01200d0754080c0c10103d008080c0014903e8101d4100101050000034010305502400c8510450340e6003884107982100e5240140c401c16050f52140c1032940c0c1040b101940 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 853155053 1250 853153803 853153811
    0x1119020f0f0a062f220e070f02060c1b01060b030c0909071409090403031b20010509031e070f0b0a0e0c031c0c0203060108010c08070504080a02040c090810 68
    0xb0410940d0302c01d1000240e981045030400f405110346180e855184000d001100d90b0340054054a15906050b070300c00458a071810420340340c1c1e00c3d00032102603600100c4091000c00e1f180d40039104a00c0c000110180b1034030300c80c0c604074034007080c41c03204045041e02c0764840c5802d5034031280301041d854202030107184180d00d20040d1a454841c4d81042200600c03026000b0000c1c410f0b081c00160122103260100d5421000c01d4034804402d40350342ca000c03001460308846968200450380c800f020199030021200341c1c25186401058002000c6548031822154256100b0100354000c120015a007004880c00c40d1101c003d0b40b1909044c55030544580340121903900c0c0441300c0644200403ca0520389038403441c40007a414100401d8000442000b01e5074801d2000d6940c13449066515070030750810b22541d40341c0440c1d079018080d50750035607507900752174042d1004444180101c1c0018000907421803084090714106c5a51714003c0209071740c0c0781c09200003071604040c14420040c0480340440c200d2020400c1c400500c07540c0030001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 853156303 1250 853155053 853155073
    0xa02060f041703131715190c030507080915011205120c070602010c0302120609040c18140c030c25060908070320031b010207050a0c080f011119020f0f 66
    0x101501380d260440e60902004100081c441100002c0181d420034250000c5c419079140c14000000d0388550510018405081050481c5d66903459000107004001c0b580341c442c80d40d103a080391240c81c0c0c45185a0642044241001002002014841444240c1c02003003a51101c0000842d215003a0348140141078242d4407810040200d2a424860300c0002011881d0450800419210815034144050b201e24070a1860f01c003c0303014403d1066a80300241215001c4003000361824150700064140311411141c600b1215000601e25504070040341d01c40c95201e0351103881d0101d44520f58002e6082d0302e040d194850040284200061000e201d079046650180302c01a445034400c2ca80101107102c441303007280546044c072000e22240319000064554003080c8043c1260702d4007202043c980203004050b00641540701d19000c034400e0103141034040c03054640b00b905640024480007000340c241c510000240291102c200500180700e9000a5202d0000f07080d407041e00d4090010450440c580300c0007804240050708000400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 853157553 1250 853156303 853156327
    0x50301060b190e1f020f0607031a1e0d030c05120c0615150f16061e02030601020a11010216030c0501121104090b0a031203020307030b0607050a02060f041703 69
    0x2c042d141c600c1e407510108107083c0001155240918000f464091440b2000201c2814024004890781b0201c080807601d9a142060004019000c80007184807055070000e260703d00d604203258001e11103010004130b20f400400030300a000140c00e60751000c4e001c0040031228400010b8082c0280d9204031810100b40b070721030113403240483c10290301038010140031000d0103248850307803a6102400301844d2206013071f030303110a408458031111b4070501140d1000c01807101da001e170400c401a40f01d03245181907110f0780303541444070802d03180c01c9100658059015170b10504101c000164120032654501d4010701c1558a155660318207130035144407375002200c514282001c2400300356030105818a00200b0024244007035210f03100e031110244143d000d8038107a107407180d4002c401d03911029034030070003154002241d0f0b0300b914082070020001e400076584940001d0510941103602e103002c1c0c040d920129000406000001425800c000e441d900101c076131021800300703202c0020f05d4440840414021312448018565070882c24600c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 853158803 1250 853157553 853157587
    0x3020a09051f0807050405040204170106050d0b0a0b0105070602030f0702061339030f0507050a080c2206090e0d170106050c0307062f030603030a030b0a050301060b 72
    0x1400341c0142c404440802000a09400040751039050180d25a201d035a02100c182c071030303500020382203400003400213003121280300000040c9541c54020000b2035103c00800c4502c1c9940391000e001c90031110701107400c180b4907038451050b075041414460302d0320700300f40d8400c1c0070390b00700300c03000000d0284210800c5116501030010550044192941c050219030503503502000c4079a003601c0c011902c02c510041403c503400a040781405001e01d00300c80e05c0359992440e003049000c011400c100c03180c0c001c4610021756428480c003400e0588a94002420713500190b10288201c111041400090f10070090f1840c98820310a44200c0014080310711010031044545d0300054504042c005c180340800c084400c1d2004514509503e0301e0555500d403800380da0310030800d4000303407550040d41005000180750010014901c0100100e460302e9a110040c03903c0103140c000d00c1c6122901048030b050341c00d9001042100c2c0305602c60750002c01d40b04002000f6100b017944400c082030071503e1f150405e900140300051410000000c5202c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 853160053 1250 853158803 853158809
    0x617150c0c1b1c0b1e010b0d0222030b090111040f1203020a1e03030e031201030f1b060504150f052217010905061005010c022e09150203040f030305160f0303020a09 72
    0x21720341c59654500500155180b1030390020300d0005034049410740000300c0b2001183c1d401c40500b0b060b42001d5840c0d050143d15801e0a898400300b66107465250740034900340b001030710202c0c0d00e0580031001071440c10441c50b02a503070402d0200c003107000f5612800000360303408940540c03c4609002c1c40700c41258918018040b540c26504400035179206000c05054080291013442c1500d901070883c2d461a01c8070300d08a10200d1122401341d80c0712900720b80c00714070641c0c407a01030030455502510316001c561001c0c400f0740d00160850054000201d00300404410404140c0c1c4655021035140381d0b01d6601c40c1e4a04804041c3c591101038084d150b5158511401400802c00040d03400048203004488003924100000e0055600220002c2c05003182030a400c00080550400d6080312009003000501e102214000170044000350240d102010303648034164113014800415503080e82e2000301d41c03154680c11510240e9050f0098846201d5081c004811000095002c0c0300c04a44140b180d2400761300e41515400180c000c1c1b2481e0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 853161303 1250 853160053 853160101
    0x180e06040507090b15340807330b010507051c0f170103020d021f0c14012007051c02010c030f0506030a11040617150c0c1b1c0b 56
    0x445901e660719051001c4031000c0415072280c10300d4407506d4058440803801841c0d0080c6602c82c5501e840d09000350313807005100552050b21803182d040c1401240c2c8a060503860140366503100d610500f5186c2d9a02c0d03034055038601e14141000d0b400d29007296031f82440c10107488109441d82e200d6603000c800e8640c108d200c1000b00d107202d0a00c90090f40d902e03400e10300300c051b0512010748182c012004020640d2280400c41d948918500e001003000580710b1006007116000700411199a071171030752a009420f2061003003180212000748644084001139045050640044200f661140224a800464070260002204100c42d464001141c01e400015000c1d04855008907003010150815080003d281e40104244145542c44a050310b5441b80c840042070040c071042e00b10b081d001e91802000685c5050014001a4806516134151a59556041014050b00803003400003100d60103000c003640000181b2045080c6001c024098100d403030401024412a200300c04001d40300c0c40403060910618119130500300d86c0c1030b0a45 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 853162553 1250 853161303 853161319
    0x8010501080a20150d02130608090a02150d0c020622080f0d1d0c04180209010e1801060603020a0f0e03030301090f0207020901060e01110c0604180e06040507090b 71
    0xe84522401c800103a402091410041c201103c8640d105582201100c201c000c14507165400d80f0080c000961014110345031404622000107185c07449050003d1080d11580041c0c08075015644c244040c803d400046d40c070303150009000c60448501a0b20480c0b0010305142e000f481030341006002e812100d0103402d2031080301007418080b400881e42080446003a808600a041da442c2a0391035141d00900d0b10b6480c00b02c00e042c4d49d0703600c02d030b000343c0008847c0c0c03640108450800440480200c420598000b0210081d00b09171103500421006145002e5103500c0001c03c1c0020207102d8002221a0031500f5941140000ca5800300b52401240d51000103050444c00c5410803001500c844400240c0e070340414420f14043c2512440056071091080e016078a42039409464442c1e42c0d6150303103000c0d1400c0c41d0702c01c0050000d10029009495420006103172010350002400091925003800d83d50101c002c82c2c60220700d10141c583c0340c6040c1c40d00081180a01c114000c00c040d0404508090034001501c06141e4403d11034015 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 853163803 1250 853162553 853162573
    0x9060403020310140c1e0c160b0c01060603060f030f020312030a06031202150a05190203270d0804020f010e030f0703060e1b280b030108100504080304060525090801050108 75
    0x20001e0707001454505c01c1b084035201c0d01d5540c8400e152511a2440407002d8090600025a0014410107003001e2105a0000e2003615140c210440c01c41ea514440e8030382c002010b40d020008516a101c052480500280a031005600034081c607401c01d40c0b00341c0f11517a0f110740d500c008000740002c00403903a40c81070b010b04c094208031041c116485541a4050003211010355107002180103400307600402143c0c0ac1c6e22990a548a03d02400b1707000350090701002007010610300c2c0c4555500f003c004150a41181016111041c40380c03501c1c0c0900c80c1d44040051414184880d05c0700848c41c5070760030020043c1c6504000c000301011030862510070152490790422921940c40300300d011401c1108002c07440c042007001d03240b64105c07a80f511203042c085850820f41001503451800046560480640154103946040c4221500c041d000121042150012540604220018004a40018010b4015a80041240c01c506450803420300409600c8515800c4d801c02060040f43c04208040d400c0c002c40b80180b81e40310113080c140355 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 853165053 1250 853163803 853163827
    0xd0606050309030d1505190e0604060e0c0f250317091b030703120206010305010b0904020f01030b151c0b0f0a0501180b0a03090302062a09060403020310140c 69
    0x2c2c2e80d0480710001c1e1281c171038000b0100c1c0000c008004110081444956101c0e45448503030304400781c00f440f82d01403150400103403181440d0246004440880060b02020350340d8900548468106850030416100200840d10111240a1540445001e4242d0034964010ba03440c01502200c00150200035007100748040142c401808a00311914801106d2030078001601c0744000f030b04000c01500020035140340701c3d22010400d6400a034150503644588004c0044014040401c00c0c604d004803002035200007842262102c952090b0040c960012010b413a600e114071050138514090f8002c003100601c50040403100e25011481801496103900742542c120900c00d0000001c00c100000c0360007154184140100018410710000b0764020081c5a442151a1200240400240070301850181540184207043c0825000b80c035120060709115000740b189000b41044103903200c020303008500c640d075211360180000005a141804411002a40c3c1200003c068025200c81f205582c0090700c58050a0403d00144542c55 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 853166303 1250 853165053 853165057
    0x30d03151205011506020f0607020a1709012105060f090103020f0405040c0801060f0e0f15040b010504030203060c0408010e0616120b12013608071b0305030d060605030903 75
    0x425000ea00320601c1024103019000d000070b0325545103070410b0401c4c00103586501144004184092a050701c0300c0d919511000ca03035030390038040e0240c200303800200086d1000e45000001d03c120003060602c40b402c0c43c1c000d10b240359074807100480c0c8101035490700d041203282e01d001c880d50b2114880072a947e682950540c1c000c00c0f5544158a4814040c5950f038003ca800d014011004000801200c00240010341e292898925014003070b20400c880385c40203001040c00b0042d0840d100d48121468501000e0a00e00c4a0800025044da084800e0602c1410031000c03016232800e00c9102d00c03d850b0506450355552a1001160848a020329030040756000b9100307001c3c0e508000c40a02c2e00e001d089140c0050f0080c540ea002500600029481e0b503403243d00c445000c11003442c103400248585010f01f08a60203c2000881d0701071400a1161100600340100b170044c2c0054122030291079450300030000350200c04120002e04003c10807603041564550b001042900110700e80b4019140542000e103002815820b0207000250fa038 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 853167553 1250 853166303 853166309
    0x1d03030424090b0c0f0c01050702091f090218031510060804051609051f0501020d080a02090607050f070b0f07021012020f1b0d14160c03060b030d0315 66
    0x21612407280e000103944214030707900c05051480f0f64690b031107012852456036103501c16910b100b1405005040b40d40c43d8002d10540d40c070260090600c3c0c2c02c503900e100f4200c80f0b05600c081d00c0000007020010100302000d15201614982003403000304200d00c0c840b1000c151400f802c0c1382034400c2407000300c0c00b081103850001c3e02c91000c07508907051503452615a454500c1c00c0094401e02d07850b200f4610207002079043e000780c10550191389071100ca481e00342100c3d00300c03622084a6005150140c1e1045000c0d42610748280d02c13451303102007065001030a10700108006072580e4801d00f01664140e1140f03010082d143c030140880320080201401040c0303031180d000000221402080f00180c806c09130401202c110500981d484010500294811035451180c90178100300c03034010b4044e034649071030070710b40007080310320000365500440c81c890303c400161800c07000080840d1b034003940d005a600d4810624030000240c4001001d07001e5841504049a010540d030306161408000c280003c04140c2000c80d05c2c10180c0002d0002025 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 853168803 1250 853167553 853167599
    0x140711060304150515040e060c03011a12010e040b10060c12020c0315100e040512310306050c070c090b01170a020a02010c0c0809011b0605071d030304 66
    0x740d950740e00b00b1940c80c0d4203a1292a060b54141000c104042440302000c000085013141c007002105183e9103002da0b01d00084030035580c2940104014001088414201c480606040064910301095000041f0416600303a10032500651504140f0007004101b44000380d02401e061030f1038039058904103005064880c8400080c000c1c03070140b1401c002141c03003031001c4041c0040107000c90b410512a4210b007035407041c0031110b04002001c01140810011010f011036805a50032000520b89440b0f241b480b400694012100007040c040000e201208440c4815450190b80400c500105401032440c2420001c0d50030080c04406211401c0011034000703801241c030030b001d61360000400900d41e100c1d4001039440b0702d0103480b60740b60301542c0810000464400e03002000582159030003404800d14030201580e100d00e00040080588605011390300241d440745000d81d1005810006040c610354154440714201e4400703079000b00005001001c0d0010203881100300340078800050f0000c5203411702d0080341030400901e51441c40790f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 853170053 1250 853168803 853168807
    0x30129012c010921060f02070206030613180614061c03080a0e01020c0a020a1a04120f0228060f02030a0509030708030a08091006050a0311040e011b14071106 69
    0x240310b9118181400241c0000c54119107122180740f01c182c84090361500c110740c501d05010380020288818020b464065502419260450701ea400412030301541480d40702c40300d141e44015441c000d91044031850034650045400280c6442080315505105100500306401074024120b0304000e1070001980301c0103260540b40200b01a29041d003110003030031a2030009000c640c00450424081440030505c141c10078402c56182590950740c2c2c002d1080d0380491170040d010b00c0d02c1884100400350440780304002051144e00145000e14a5a00048694400140e220141d2204907007d801070069249560043c011a0424000400010300001d54a2107400c0c080c0080100200d21581c0c191401c11501000d021100107580d00c400308100c004164040440c0e419415100b8071204203400120341c0304040903540f000e060a000d00e030543d10b440403102c03003121500ea00150355000b2940ba0000a1156404e5202d509001c00c65580d1311101c0240204011030f44001200810024040010041801c59045c40310a881e155 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 853171303 1250 853170053 853170137
    0x30801121707050a0c0f23300a031706090405100f0905060c030702060703050c0702281509050108160f18080304180c080c1803012901 59
    0x39040c40c03c40040100440110580400e0606c041075610b8240c4010814580380c0014904070020800700e44800540c00a104140d4070803941090303034514035659140c0c1307030b80e4920040885038685800c511410039800206c00710304c0132201c0142908600d4000d501211003a0645c206a00c03803d4440450500c1690031a0f660110400002c4d51500f081200301e4010094400034500b018041c01e042d4003c4480380e005005810001c0c2031719020344201c1d800b80701e0154206080c0320311682400b034505004c400341182d20902c0c90491408155071020540580380d2041e00034103101d20505c01416003c91500050f050150510030418440102e2a10103544103462820700613401040c01d058030550b01e4407010988161400030049036024000000f0b104a1710a250707880110451550030b802160509a10180080c02c17807000314142c241400c01500001c414100112040c4001c1c01c006821900705c4e059080c001e1901e541080040d4041c0105e45c099980e00f802d14440440b1692032501c1c1845250828800c505945640c1d5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 853172553 1250 853171303 853171313
    0x608090703060908090307051903080f09060c1606030c080610050403020904031e05090d060e011118090a021c0e01021b0615041b030902060c0d0c030801121707 70
    0x1900c02550400b40412039143d550403d9916a48001da071940039100d007120004050034088002416203042c0001c031981d050030b40d620046142d018030b091034500d180900000c101c5503100402407110340e0800004003070300301c0c0740e04001c0c0841c8016441482030500c0c00106d500c3c22038100141a50101c81181c00c80c0302000e000e0001e48060149800180d0040804c02c1000704043e080008040c0c2c41944810a01002c040d031300c0120344900c9092806074020041581040c00076600da080008510281d00c0041003000403d950415103400a0341b140ca1500708840031a0558180810441d410981014056280114003081c080c3c500c103101c00214041030b582d44500784007500c07e5041e103c2810032107840950800c081940720f07544010940ba540306910b440d40340703094649894425044400b020402803181d03000c01e0b0000790014241c884069800143c20014188a074400744228031000095480b00c01005035503007002020040f058100c0d000d0801071405800100e00341e030300020004040c005040d640d0703100328540 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 853173803 1250 853172553 853172563
    0xe04020706150905060616081b3036190302010f0e030705040b01181e0828030c060c031a0103050609010b0a05040308120118021201060809 61
    0x30280116140001d0382484090340a181d000301c5040300b605004945509081080f140315154601c8004a0048450070001c0d291001a0664080e205c08502c03102591301c01e01030601c54503013807403121061011259954a1401c1407140d40c010150b018060810324410f03080e038048000402c210a000380b88228501c03800020b042041c0d80e03c180030300700002e00141c4040d480082d010300c1c0401c070301081510701c2a489a0784618060480380e0030050013492000d02d880300b400000e00810703881604100d039140e040500070104000140081440c1c90301024209100e030514802101e040c1c2010101d5048403083c4100559841ea000c00b030f81d0705a0082402102e012314060f40c02030040000140594104400d08a4954065100200740482101810300550300100114211030301100d83c80c0d40005402c00500c810200c90015004000150030403525013900c0b51151001c0745c00156541400442ca10018070a1030301044402c2c482141400042d4200442e03040c90201c0110140104800c00400d100020707400c48003005 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 853175053 1250 853173803 853173817
    0x3011a0d0216020f010c020a170f060c07050708060906160324150c08070b070e130902031516080402040f0903050702120a02130b010513080d02120313030e0402 70
    0xe0119a609200c0c205200305400001d03050b84160290720300140a540124806002c085d03004140c082a14241a468200c9a08900c0440300314410080c0840e0341c0c41042003141c2c0180d80c0e444800d519841540391041c0f0b0301010307030014406038010401b40100f41d080000d01c0d94100d0304281c6001051001500b00301c0003031010100008508000d40e00c07024003074203d1b40710141640e0008800000c040c461580a4075042900c0301e004056010400001000c14107207090f40c0c2c0c01010519003049428407040002d0048400745041172401e590710b03003d490441c60100048843c440401211200ba460300075039803035280740320300b8086e418001b040c4001000c541e01c90303000440078008200200007680140c180104580c00011b0128040d0b11a044401e24802c00002da400d50190b0050014000e0440303001c040780034000c016810381c107001040c040e0b2412210b410b00e0700005000c20000804035103060100092900c0d4014000d6810341e01c0c10000d02c07105540028911542c41d03058200220642410300100e0000c1c0710f04c0c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 853176303 1250 853175053 853175077
    0x30b060403060f0c02030306030c3607020105241c080d0e10020c0705100c0b01120b0f01050108061c0506101d0106020a021216080f010e0106030803011a 67
    0x50003108014907548441ca00c3c000800082001400d021020381e902e1009840c03017941940040c004905920f0100d41e1a600200c042c10301407182d0720003040396075105088a00c29418442c0c08010051039990901c1002d50200c9480b0b5449102889000300c0d502d90510f40d24180e010351031f00400c2a400340400c90a488136964800b8801d5030300d1000c0000710b401080c1c40100101e040c001e07007090444019050094424680003100540742d03241c6004100f0081c1c0c440404d03507509201e8090750007004110790f0b40c00c0d0b03402442420341c40c01030039142c2e14040c1c04170300700206866500c00807080140a240d0380012629484141680ca202d51080c9200d071b0368440f8909558010403a1080c441000100c24120360454102c4201a103e0104031441d170510408081090140c0001648020103e001520f0150804225100500305032061008003c0a0020054903500441c840740e0000c03003190710031102440b03800086c000c082c000b003040c1411a030302d444c000d02c0117120340400704908209051480541c80c080342d032074000c4a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 853177553 1250 853176303 853176307
    0x20f09040204020c0d02010e15010e011e0b0a0e010905060c060f090f0609150615030a0b0a05270a0207150e19121e02100c050408070b040306060f0b0f0901030b06 71
    0x345c00a01a00700481c84000500614402013100f00191880342d05a669020a50312580e013009400303002e01031018a1808843d03a00345d80040c603a0040001000343e0071199490141c03075000040094000c0445038042401101c003080305404205000ca510b5411074425215540542c03162615a4548009202d0040c1d860050009000140c84001020008014800c50745000c03541e82c5020000000c2c41250903000f0900f0400001d0361510407907004020480f0010090000c19440d80045100070210b0205180070340384404048000046640380d103940142042030039407600e500756841b91540e4045401c0c40303030344a864403021801d8400622640c0302d604200306c000d820314280303070500e012030311413003078052011813007001c140c4c24084081c030303054208101039400404500d01c40d03c000c00c0c0102588207079a010003006100c00b056210040c84500f005025140100d0f0715a421030400c241112103a50101c058568081c00c100118022403043e920b2910186003201e4540c111400140d0203403031440c034900c0d485140 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 853178803 1250 853177553 853177573
    0x50c07020d0f080426010608010b0303030106140f0c0c03060108010b0d0305030411090903042d0b030402031c200d0905222a110c040c02010b0a0609170703020f09040204020c 76
    0x19802c020030040740103c001c3c03145655920340d041c200c940e2b0007881c03078054204000521035107000305405008203010301100341c0342c500d210381481601e4200d41c2c0c02200642000854078150315003001018050400305000300410344141c000940701054600c401002c1c01400b1000409004800d01e8841c2444c0000d0704500142c0345c801a00d5440b94001d01440715080340c0740010002030004141c48141c402c28180071454041d0a1141286580d00014401ca0745482154035212500e00710210181c05c0e14000d4840b210b034144400351075032000d0b1134441007094a6000110b8542c0c240d41c0b0808000480b9000c1d80c981c1c44130381480740c8008000d80900c0c1d1030b60b811801c0c0102841000780c14549500e4001c0b12481015100000701001c440c0704900c50054422940241908041032034154000c000e042e0300c2d03000010704801642d0115010220b5503001d400850380b058410001602e0100c00350215072003282c0501a414116800140e4400107525440e004104010008046489940c119081100040700b00d80e90141 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 853180053 1250 853178803 853178849
    0x12060f031b060c24100f09051503070f06230318150708180d0c02150408061302030d080708190e0a11102d020a02090118050c07020d0f0804 61
    0x795030010104c21010700010350351105100c00d50702554030701106c40b900240752000e034201800d00901020701010342030443c9602580c01700f148000820245808200d0300b86000c1c406040c2c426164103181e420640540303004c0413a40c2a100300c03980302075961000f00c50a60820006458018201c41160780303150101c042c807044079003003d10300e4481c906c40780da9100300e00d404c00d85441d19140104500382c081184860032000519182c00e50032035041b84403420508203691058240e14044050b124540c840480703000c2c50066081c280640c0d0107452941c00d08045600341002c000b00050001090450700d1018086201c1801003250004401500400221212841c99090a0070340703044000301d8a21071074620428032130f83c60007455464512402c840e00700c1649080502c41d010740011899110045004244070030780181d17140d0800c68080c00300078482d040f0440254a146040f1030b400745c0105611801440385a0040c0d9560121410b00769204501000d075410a1815040c14012508401d202d99038200c003400c4824 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 853181303 1250 853180053 853180093
    0x20f1002030a0c09060206060103090204020f040f03060506030c1806150406031b021c0c050a05120d2a030207150e030702030105061806210604030512060f031b060c 72
    0x107107004110280c0c220a007507038406224485c0001680148001071120360184e4400f140c0140050b002520780501c12011280c3c41d803003508003100c48405e10506006100304c620802d40e1080040e00100314151458000841604800c210326120342a004005881c0d600c0700d240c196812020703118210349881d101c80014024000c040c9030200502a43c0045040341480001c4860340c80d02c3c000301d524203001c0070581c104c2c0e44451082098038284075082c22400000c004105201d501c49880060384d44610803065a0340c240e68000b5001c2803080480400c040010500540c0c0c01c5102d2024100140c0d20409850003c07284442c00c501400a9890010701d0310a03201c0c04001003003a203208a0082016540380000c018464009032115910f07040b01c000000d89a041542c20b100e8000d12049205e2000ba8502c1156481c00104540c1200080d401017000c02c400100c284007250000d40480d0508103108000d001700b955008002000c0650045965807140c5030384440302280c3c002d011100558a8403540589000103403 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 853182553 1250 853181303 853181311
    0x120c041a0f0d0305090d0f02120307030809010e032b11130902030108120f040e070903110303090d0312060b03100312051602041505041505010212090303040e0403020f100203 76
    0x406580098080034580b140122402e16807507114a410240220b0038001003204005045030310303580b21200c000260347d905601d0b074034016040d00290303910707116843c004090b500054010380090b81040980211000007000307680a00c84803041400b071070300241101e007610007401a0503250082c0b40c003c444140340c20600080c07511407555031480042681d01c4007444100d2000340b00340e101c2034105102038030080f042540108102e00355404c400e4141034413907100c04070300301c2c0c10b55600e00401c400010400400c81040e04000c4002c6044014500304800040442d0001c080148010308108044101c0d0071500002d0781300001400c0e9854420303842c3e251130310040c00d083c84940019100107104542c010021441002150001d040020b074011150741e1590a20020b1b00c109014072085514602001c11661500d200c0c4403800310340ca0700300102551600340060304009070441c100300102c204102d0f2060a48001045038115190740101c44020b03595410120308098401e0391502d0381e4000c0c01580c42034030905801039401 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 853183803 1250 853182553 853182559
    0x60402011e020c13140112050d030902010507330203061206010303171509070201020901080108060c09221803030e0c2107050a1701060504050f0402120c041a 69
    0x800142100c1d06604060300031100141d000c00c500e081c10b8240351201241c400c01201d408600394188021508000d8400d0b00301c1030540f052516048188001000440c03018911070034100204111600000c01d03600c203d002c058003448059802c9825003c003540c440704510680000d8105150700000103601950041d11914400c0c1526030703010380350050204125040b00c0d0b054841010552000c044d812510308010314440d0501459078100b90151111030070380703114444603800140d4405401c400540b4400068020400c40e51180c0200070754048074008440740350000300c4000a104410020064052841180402c14103003014900d40c400d039081c5001c100e80c14420384081c0196803941111943d2000b01c1c3d491150b01907001c1c218182c010301d00440d5074514404890075030b2102134071500420302c01e410550080c0000c0426200d0078030300c00b034280f264602910b400c132401c1c08541810107400100d0341c809080607120b540121182010071400700103549032950094820f101c0381200d05c0140007a00701541c07400e40 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 853185053 1250 853183803 853183817
    0xc120912030112170c07030210030b0307031a0709050a09242909010807050a02160f0f090603111203280f0c020307030b06280812040b04050108060103140906040201 72
    0x6610001c4c030261125900c80702d0081590301e00e160200000c0282c0c89024800341503039645506095142400810007542c00351801c41e0343d001c04030311041000c4200074040800c000c1e044009001c40d50300c140000b07003100c078114000b28504080b4000b483e902206141c6000016400c0701000801c4941c0401d11520300b40d4181021420002801c900561480340c03e844c0790019410000044040b80660003610f09200359104a5050840c4100104400607140e00840d11000680c1010401c503200da100da0000741024000074041503107196513440340300b0300ca507440703901ca41c11052451102e54001c00641d03a9840d441d840b5004a500300045203c41c078000700807034200103950035004458160280070000c0f00e0560150040c46080d1440d11032220002002d0941640601c4060940c80300084290030b041c0061554000c0c114440c4c60000c0651a22407510b8170120801c03400c1c00200052118203080d60121a002c4c2004000c5550f0240100c0003400c0000700001c06845031424406c034000c00180880c071891003a01c0e140 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 853186303 1250 853185053 853185083
    0x6161404290304080f16021201050a0b030a030212181012050604050106080f040303110c03040e1e040b09070302040207080901030f0203010b0f0c12071412030c120912030112 76
    0x220709440b0440f005031081008111040c40c024610000340890056103210001309040b95000400703018140300d130260b1503910394041c49141c4c00d0034421440021000c400405a15070300c4e0745c000c0c0d19900c0103481c804082d40c0100b001c030501111450404925a801085060f050703000b2107020b881080311032032003410a4504000180340c0d007003e108650507104540c80350501340d59001c118020b0710130010411000c1540b1a0f5450524411080107001d94480c06c102654030f03903040110401c00301d07500910880c04410307940321640c0c0c09080d032210b8581141c0c1000c00140b159880507113061030403403d070b840290001c0c800643e59041c00071500c081e24504000366424041c0e01c0200b010103007a13010a00443c10348040400000041800e40e0005200d0310050605880d603102c8080002c40c0107410009007910000440700f000002c4a030140400641c0d491044031b41070030f50600c459110514043c2c1985103010007281800300751121020441d601180e03600b6204a642c940c0c40e142440e84074040003c04503143d80c01d000440b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 853187553 1250 853186303 853186379
    0x90d140d02010c0507020f1203040b0903060f0c03040f051f0e0105182e0501031b06020a0f121803061b030207150b011101050903030115030e06161404 66
    0x3e03000c0e26269448a0170500980c080110942d05040c03196440510340040d050b0044040c07000d8002002c0c030000f90303515406400e05041c03e100c401000b403050fa0b0282e0b0100500321020000360707030700715130072020b9080d06000600e031282c1340c248030680d029500310308021541c41501c600c2d0000d003110170444009100549528041c00e141a100803040a01c981203404048000d401940c7c24a50740ea80c81c807039604503d00c501d500601201c03070a820a4910300ca5610303014540c0100001c082000b01158801400700b1042030300c03104514000c840c0010207068000f0303031180c0d40324841d03100d210150300440ca03001005036481c64001c00404400403c2007403061550921411a40284260341d440743d085520500348101c1c2c001400d00400320059443d062200300f02d41998282000d102c0c0e80d00c40d06030b04000390364a50602c54105100c45545420904140c2040d940c244c41d0b880100d0240e810400802000980b0044031406440c003001e041c0101c0034500c404140002d50310444c0a8500b05011421041258159540c0701 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 853188803 1250 853187553 853187561
    0x3120403230118140c09010f1401050301030807081b011407020715140c0f07030309090605041a0906041107030e0a0603050705030f1009230604020901140c0102090d140d0201 76
    0x40f0000703d003002100b8045601c4003140b040038842074040c0c07103070914032030002016040300380c03c20641d182c0518400c2c8120002032140007103d42c0c0908064ac2158510b986070713501ea2061700030003824040042420103d0040500c184a070100d0f80000a004814420f050175001840860b48000140f046c40c00024062001c0641254107040310f640e40034094002c2c40301103403076901580b0583d190344100040400c45910502501020354401d650b07241d9001d1a100490040d1106070b086944550b15280c0100d045240c58290400c080e0425101e00d51195aa00009402868004114003905034000f50440070164000c11640c201c0d00e00301d604219854444208604851003260b464011540400216051030f1080d07446c0c641c08030340f00014407452502c0d101c240054544401406000c0086c03d4100e00c40d511402110075840700c01a10210b06013141400000c0c03521151001c9001150000a26128035040039011529080f0000c1c0c8000c0c40d40400e840d20600c0e1900d24a96110030380a100e60000d081481802 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 853190053 1250 853188803 853188821
    0x20a0504050108100515061c0c0201110909041a010f090501170d0c05070f0f061e050a0e041b09051008010e0f060102010e120c0c06120a0902031204032301 68
    0x384030759444204010020b02006d442d43e00000341c0300b200d4035016510b62004040d00e0310071104003014480b070711202d00305032500d101002c0c2c29641050480000c100042d01a942d40d140e0440d103014403034890742040c441006241c0056010a04000c00105d90103110b80301d0003084445001d0108100e81e80d4031118212540711240d1004c1c0758000c0d0001341d21841c03180c0e540000b4107000340c00b5500e4056464074000c06c2d0021990000c00e118204200801545403c91000e40c0e00e100401d401980450003407400504510403038890b8002d01010021203643d0341ca41e41e02c546044540a14004010728a145d000f5120468601c5842d210b541400c0c03041114501c07400d41c15040f00d920b00d040c4092915018840014420010305141c11596203d61404031000100105104030428041c819071f10140b2801e00b504000241d40000c0c02107404000c030303001c00d00001c0c1800358003001c0c520300054ae4019074400130381072907154181480c1c242c0002c40c002c0280f000ca810482682015103800c400380802060000703080ea08a40 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 853191303 1250 853190053 853190069
    0xd0e0a0302060c0709020313141501091107051027080409020d02250b0105010507210302040812131d13021f12051b07120c060203010b07020a05040501 66
    0x4003000141482d4000e400100791007000d43d4a001d841d51000000c0f6001100c3c0f04103a400c05e070085100740700121b0200c0091040a801a1403940711808001d840d110040c418801019505c01c2c20348080752080e815105205e900005860034900708042030000f90003001448600206800001c1041d4002880e10f07080b07155108604a08040c5401c994030300a42110b610a0070030f80d02000380651100c0c95040844002d1404085140384401c641403081120005030000380c1131100c10000100421f1241d0412802d41a10b20004c00025940e40030460181c01a540001000d1040281c80341c940c079025030160804186442d290802070766120000e8007000003080075200030185860109502c900c40040c802e21030f80c005004c1e0504034a0100d484003806246480010010740c6114426188180364028680c005005849410119240d10031500241c030035076400520320340c8548200700c03105018517041880e1a070042e41c2152a903a558000842d6070313111120482c03080c60a0b1002043c1490320f4070130b40381600d045c4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 853192553 1250 853191303 853191319
    0x190e0c0412110f0a081e0613020409110a03080415020a170d0b0303030901020912030301050108011502120d020d0e010c0e01030b0a080d020f0d020d0e010815040f0b030d0e 75
    0x503140d4030450020600c102d03400c4901d02c40b0103029038036440645030041206038010104403905501d080314009506c904498960005414441c4e4040100513102125804440020300b41e50903280841c24030f5074056500360441c044020000a020008028104581003031a0392a1445488001240c503a132998000600c07100400284050400c040f802a1038800188000094100c016600003840d41d00101c60000f0b00da9000610b0b1b40c9181495500c400d803940c5400c000394110350429001030617058050080c101c41c3d240c4070841c01c00e428403c000e0742d80c82404a880690f5240d21800c0d80401075481280d40054180c100361050b0003280d014402e00d0a061881c0e52610400100d000044020b0902441c400d07510130f40040c00030800040a000c115085040317a0018409000301903143c0d41000a02115402075400c0b5407500b4800a41140c03100b9a014001d2074280c5c00e40d6241c0c0449000c11000410280c0c000d442c100b4483ca41048541c030a608001d011411618100401380e421030f8803103040810b00b038010940d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 853193803 1250 853192553 853192589
    0x90304050a0b03191d010c050c03040603110d0c18060827010902040e0102031b041203030f27200a031202190b0105040c08090a021002010b190e0c04 65
    0x102c840555000b100b4003004100d1042e950034010240e5060600c084050a80d081c0f01e04200c1e00d0921905101e81418204281400c0000515907241e0240d40328180038140c0703c11820501031104422180c0350035440c1c200b0001c114a00303200401d01c3c1c0b265004441032410900c808222a4090424180300c1c40c000c42d82d01401c050f40d9480340700710f0380e44000316661641d01e031002c1c917006944500a081440000070b0006880c1e00e0100213440d03a02000c0759540e141c2c2c11007000288110910000300701c1100e9054200481ca02c484180980010590860300707140e03051584401c4600110444d0144d44664010010b007401440c0c00d501030146d0760f0107414115400440c8140400004c0c0700c441030800d019a00b030058403140d00c1d0104800e03d240c0c00042040705c248010f140140181d2400c1d2003100c52414803464100c0c02490480515a0303910300c0400081d10890558070103014252007500907514040e0f000e0600c01c148500c500c0120494003003400b513030010500040000e41c00004010580e401c41e03154502ea0402803407 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 853195053 1250 853193803 853193819
    0xc01030905030c0d120b010c02010207060c0c0b0a050304062a080c07080f040612060e0601050c0109150b03071203020613050102040504050c04050907020627010e010c02010b09090304050a 82
    0x20403201115640030a201000400e8803d04c100841006152101451903c4c10040038046402591403d4148203074400d802001d40d0f07001806a040d250b19041038650200c1d1400c001d241000a0f41c0001c004043c0050f0184c400755005020b2740c01f6603c41d001c00d00c642e01c80040c2c01005803060075014079865502c5c1080c61441d5100700781c400d4100c82c2c0710850910340203da03110f610566110350503603415400001010001c0c1607221000c04150641603404000007400e08412090040000c5d060038100038000c2610b0f400500c0c203610280060f0303400602045411200719a06019003043d410480c803038041e4403000034851845041e850755540d0315034041c107180e82c2d0b445400d410000d284a0161515076092101240f1904c0d00e00c60f66014070900c1c2c603401d45440c606002c101e08004000c00d80030444d0409410700c01c40c80742109a0401c112100411254600e203420740c1c0a00506140d4240c658a6003800035480481d501903100060740042951107400c140d40b40f0000555910682c400c0350341240d402070040000d01 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 853196303 1250 853195053 853195061
    0xb011b02130b011803050706081608070302091f08011a0319050c130f030c09150506090103180602070605060907080408071e030201240b1602040612200d050c0103 71
    0x1c1418003000c2101c4e40c400d5500501000d41007205c042c0c5c8849000d00c04684c10066950f1f12840740c5105070110080c5c040000e154400c0079103c1e505247d004280c0c014680d5171406003068000490030700310404140c022004081907400c0c49480f1103400400707002c4181c003808004983c4550300000c80e0320400145051071380020900100000304004040c00b0324000c646503a80501e0080520441d1407410b80d055003040355004e249540208110742c80c0c404800c050496103446541183d4040766002d407202040b00050f0044d0050320545601003e00c894103200b009640e9029200160040340104829510b4609002d00810152106000300d20b10100141c00030b00c03040c0042c584a4415658420800c103c0d80704010300c520242c1d41100940d4480c00900d2090514101d400b5007400c1000008044d00e160203000e420901c107144180c41000500c941d07201c2035460b2504800000d02c0114079501c07800b0307200d01b410501209000322150b1207061003401e0440a262184100001a410501824400c040140150014 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 853197553 1250 853196303 853196321
    0x3110f12100b0c0a060f0b030a0b0a1b090f0b070b130f0b0906070e01091248120c0512120a030603031412011502100f0b011b0213 57
    0x80804200101d01c90702000080c012103c80d80c0000c140000e0300d80b4144060b28000341c0041c0f8800d2603c6100031582c3d90019442142940142800ca02c0c4d840d174550107000303815101c4800e124000031080540d24582c2c0600000100c070300f0080c0000b9426112010302c072140c42084000f5250350b890701c0205e0070782480b804540070000e12139442c405001c000ca40c1e99101d40c5a04907851400c175000700d0308100c08290040182031150009103010340d485070070300304c9900e41003203002800b40c25504000344501c00010340149003c0c01c1e2100b50101103141c4009885102e101d008603240c81d1030400303541d50020b404100b0304112071140e50b00140003000319007813105221210b542c514000309a48a1003046040040303400c0002c040c0300c60a5640400c45a0560501900d0842c249401949000d030800c00d0203120420f008015056441a159042c07161016800c00c034580b005480c030103c0c0c07107441d0482c401c81914865110017000c1c0000c1e02c030f40742c0102040c030001900c11554800a50050b001000130380ca13400003544040700b9 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 853198803 1250 853197553 853197571
    0x203161d010801051e130510050a15030507120206130b0c0d020f0a0f0501090c0b031023240f0304151e1e0501030b06030105130c0e0c07050102071203110f12 69
    0x81e046e15510b4640c54143c12805a600155407a8240500701e000741c010781900107120380c4201d80452550360345a03540c5545100e140303000c548020203c0110b42d50442240c0c0e001040b42c100255a03605d0f0459501a0350007202e08109a00c210b203500c121083c008641032502e80c0e401405030001641d15103c80310402c0c40c8000071591550703034205480004107151142c802400520b4000d54880c80d012920400f1a0f40c0da400859400e8001a1200401198000c035000c00711015201d09400e5404c005078034a42001040d0b10802c0220045401d00564034460040c511031400303112807031103038000d04141c070040314110169009000c84440b42000801c0380c0d5000861514415160032001a11620500f411501c013a041150710508450074081c20f0728007406102d4001e1004861031540c45107560318002038009078440c0b0664502e1180025241c044074009440d0303000c3e0000001d6603240d11030b10344401c071202d0032046540443d00d40450f103030080e041039042d070b28284000e0200b549028500c100a2a40c16001004484 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 853200053 1250 853198803 853198831
    0x2060405191a0708041b05130f021c020c010c090501020316110a06110601080606090f090a0f1118010b0715060b0403210c0b0406090203161d010801051e 67
    0x1c0364414194099110310354030303500c071a805c3c2050b01c0c05048003006400e0300c0443e040d46090500032070751009212030380207040c0040060400ca42200400182c0140058502d10900d000d202401d0028030780c0080030802000c6d0000c01402592100683c2e08542600400b401a4014403035501c0500041034007000840c01101111103050840c00024110070040d0800800601c2001648008660810606002d081f200001c0d29041c6041c1c0b010a018120042610780c98400b904081220749809114a802c581e07004035024858a40904210030400707400040035008074140c042c5800e5401690400c54142c5d03c0b00d07003142d880c02006480b40007949040d0030000101c10369910b400141e16044e2001007004500c1040d82c00c0c15040c41080001c050315040180b1424006410030590000d03c641422a41c0319500290004521301c060011910f89080700c3c0a03902040c045450118240740080b60000c603107030402c030400c54142c0e2642021402d0340e03819a8070402c442d070900c441c66403002c409511142d1020a40442103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 853201303 1250 853200053 853200083
    0x80a051503061807150e060721110c01030c0e0d06181214030105150322080c070506070f060e1615120b01022d010e010212070206040519 60
    0xc2d05004080d55000201c085102e041d40244105020080040440d8115554200401c0340082c04103c9070202d942e200e08400101002040038440884004000c281180440c4001902000e0542d010810b40c0740130a118820f00a0465032080c0600002161290340d0030440c1300021007070082d42c40030102d048a600c0e848181e07070000340400e90b00c070f0703803c9a0191a02007120107072108003504140036004000c1c0415002c20041c0119210041d07c1420440c1c0042101e0382c1e44d0b51500038010700d028660740001c440424514500c00c0c4002c440141032030102c010b0a65000c1a40c1d00300b006054403038024000d04407411161100041350300c4d40c3c0b001a001401c40c1c03c1e1441c00c80b11161140126176290001c003680d07840225110394071980030302180400c40d50302c01b0420070b030600c000020790b45040c040710240c06014054104c02010002d000c1e80e080044d038100080c00340c0800c242985004c0c0d001205200d24078490300c40011a12840011400e000c2e41c2c0000150ac0f1080342c82c1404000588561030079121403400341142 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 853202553 1250 853201303 853201309
    0x100e1002030a050601031808070f08040b1305010207090213050d02010504080604030525020310110405060d0b0f01180603021e0304030315051f0c0203010f090503031506030106080a0515 81
    0x440c41a50ba400c00092940360010014080350000e0011160016400d251403000031002d2040b40c005035007008030043c0c01111450004064032854106210600e00070a80100040011140c9001e0b60026026120125102c2c0c201078101c0c00f41500040004041a80802040c28003aa032402103e006240003860b150b11800e44a292600a44040340016000102c82c2840340c1c514a20040501302d403455580c02e06003030b80000750758800009880300b1460796981d80304e400e08803180c1144d00420000d1308031520b80301030315602030040a18040781c81c020100c40c100d0304201e40c81500d00b00400200d001403140e020b41840700440c001d4004c2840342298060188a00020715030301406144103070720a50f40850a041e03581004260b440395a0b0142d03000306200c144500c408544940a40d001411501d002030505001e030000a01519075035480b200460319000d001824810080000e6101b00448800c405140c5403d10901003940301c24450b5600151494011484207070319600000d80201c41041020340c622484800 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 853203803 1250 853202553 853202557
    0x627020d02071a10150f1b0b0916050a03020a030f050a020a091e051021020a08010605030f0d02030307120f0501261c050c070803040b0306180603100e1002 68
    0x14000418028408101c0340d640c1c04244c0c00050321018114400b90301450324081d0503c0ca90584940910115102000850300c0d00612125200e03003001c070030381207030802030302454894a07802d012170000c2030201004152410080c030000d00310f960290016501526684030440d83c8684d02c4c004031914050201d001380540d841c80800c0b8042c010350100001d12250300c00d00030a604c006510805944c0b81030108002c04050020105000c56403100c0000c01101a420704440030302c41c050308000e41c000e03492040428121815071083c0242e403411740454041944201403241d0340e00c0d007060408016842080040c5a003480380412050707402c0c20850110305074048520708025160300740c11510349540882100540350030959480f0700e5904215003c5c166400c4503070360018080001580040a000001411104a12041051a009003400b20036640c482e510740e0002d145940c0151007552043c4100184154450f03410843c0d103002c1d142c000c0003810f80e0310451003a80040c00c640402401c2e00e01500024404003542400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 853205053 1250 853203803 853203833
    0x8130308090a090c0e1e041e1104030b0c25030c0201020106060513030b0c090d0f15020c0c37090e0c06031506091807030627020d0207 59
    0x1165944074105881480481903996201240550524100b51111500603030040c5881c01e00381d0f800980c09910398601b0354605200480290094a0b0001c00c4281c0800c00b4440d00100040b282c050000d04901c00f0244d1890155001c05050b0042500102c0d016503010741c000c040540c1c08554800a5210404080c68099402c406c190041036607085034104669080c031820000d80f200d41046c40c00c11805001c00400743c0c407280002003140c007000000c110001c1c14034056030b64030720005041300c400e04e800b894a480c181204100403a500c0000c43e00d050800005c2e8029a080c004403c8010541076400b00104184c0350088519412114030060000c00380325024000c40c50080a1203100c07422081c94a0f280d141120356002c11544244c02001c1e007008690760305c404803900010b0034600c0280d05607982c80080c0c40c9211301c815240e40301060718580c2c0041040c89070682e00c104000d4600300603a40e91508103c8485030101d41402849000380400c0680100c964040c10050921050044c2080225500c40c9621000d0031 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 853206303 1250 853205053 853205063
    0x509040c03090201050d0b01200f0f030c0717100e032d2b02130503061602070302190e04030f1106040203070b1615050415060e010303050d0f09060e0c09010b030f04081303 75
    0x269501c0b610749001c001050140c0400741c00cc0d4540203040308600c1c0c492007140140e9092440f90404c134800582c0c20828214040c640e42c07410403c1c1b12401081d9a0b8907405501100380301690490344503100e13818075001010540c00d105035145800d5000c90442c4c000500e2581800300c0c0311884640e000411311910180100c40c405015200c2d00a0a00c0c040510301394004260043c11005032101c00003459002c241078046943c19995107500301c881845451810009421a00201c00e0307101c00c1006040d8051100110075520ba00d4462400c04000b10301502d0341c2013201c019425070b01040d0308000d4020004014034140541d1800c060903070596954481848008046e44541151100d05000501c1212851001d006440200412196107051080b00b0440014130015040c05000306804c114491680c00407c01c00c440141c081004581c145882001004d40030304140715442854a901d03000c2c00c00c08500ea040c0c0d04410003503810359607000b0100c00781080c000c0044400300b1043c4001b401542d8814520000355200e2 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 853207553 1250 853206303 853206313
    0xe04050423010203150d171c020f0415030e0c150f0720010c05060621010c02100b100c12200708101118010315060509040c03090201050d0b0120 63
    0xc031001c001174815035003c4600ca001003135851070005409280b107400810300000041d4840035005440c000341418680082c49070381c00001c141071800080c80090003600e0802c052200381600b5030302c044013100e50303c044c05074440c0d2180360340400d545450800c1d290186425582d003440c1c02c2d207500180b0116000004101d40403880880c900c2c41891100201141d040800e00c0d1510682c03045c2e865056882901400f40d601038038400c00b1000300d401c1462485802d291108009000418688000035641e020000c465101c0f58a44582204549440e01c1d4000c02e00c007a655618103503141944510f549100f282c0c1c50310341848140f440d00304202c1c0301c440c00e204030002c1510180450703078034003440c860034880035405c01c83c205860482c50411040101041e034000000340700103105d08141190041c0c0003000c2601100501065020000840310307031100090030001000d44040c040c91030305100c05d80c2681d2040000078041102400483c030505038a070b20940304500d0504d40001c0c02c44002d5170410005503003882240141c0c1003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 853208803 1250 853207553 853207561
    0x4051009141603050f040f020604050a060e04050105040b0d061104090908041a04120f0311010501180b0405091207060209060304030809210a1409120c011107060e04050423010203 78
    0x818000e1511001c0301d41801d20461408070511031001170010401401d0700b07201c03d080c1d0f0079919044262006044080e18040c00302c2d442d800040e0910300704d80107480c03040e400d0500100303540c2820f001e01550444041e02200c050049580e80c000600700000400d0703034100c0d0600c0700142e030200501421301e825000340107480e07603141001200b103050000c8012804406404100c01c0120000d0610380c4041c403a08240010100350080c0b400301c960310351040d4403a4680d800d2200214041c103d07241c0b11345101c6c1119001300504440801400150f6004072400901c6420400104800030328000003040d14921070b1a006140c0030104001421540043d82c0581c00684404208051514100490a48031712891884052a00e444141c40c40911176040c5d040100001e43d19402c0590f100c844c140c4001c3d500017800c0c4401e0f03034039001034103607030721280425503001030f1013032488c0341d5403000104010084c0c0f44156601d0b1000130307401041c0720142602400031908030380c68100740f0004840f003c0c1c01c030701100e500000241c0c1c1d07410 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 853210053 1250 853208803 853208821
    0x1103070f03031509020f070201260438010605070201020f010e0d0306120b1603090c08030306010221071b030b040606050f010e0904060b0312030c07032a020405100914 73
    0x3d01c540114a40350701c100700303440e02e004001c0c084d51035495091034176004000c40c200414803a002245440801081d10f001440100940407280c1c4034002500d1282942a0401c1c0c3c000742c1d00c04814011b100300c400510001801010303c02c600400c2a280180101d4803840d118500b0a400c48140400340086600300585030200c06606001c0d140041c601160f0110305050700c6d44a44016040103083d54400615044800b410140250000c0d014240c200300b10000055507000f8681d00c03a44112841070040c000c401e003e4a20b0b07040240320465941c110060320303003800e83c0d0741c1e6001c448880c4074103900d40ca0800d9500000010315200c00c400d2059200d02400b14501e40343c01e080c01602e00780404024184661074070741415940710f0306181070f8450380150012400c200507070301017420111800c8a400005100008200030129030b2401030082e28030035681c40b92804c0038a16a00c4141d029602c010210103003c481c01400742c607040d0027140c5c01c81d40d102c0c0c2d08464141c0d120755800840c0e80980822202e00501010130590079 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 853211303 1250 853210053 853210091
    0x6040b03011e05030c090a0b030a060f0f020703091202030a0b07030207061b050d1d0d020318010216050607050f010c090303182909090406050402030f1501061103070f0303 75
    0x81c8982c000a8121030618000030f03182d0307101c4a0240d0248a8210004030004a02d4121031b100b080e005d0245e400720381541c14100080d040c40110301d16042d0520040c20f01c2d019851080b0b442181d00741d40c0310071041d802e01000d203000303100580702642e062044042000214080f0315000d409110a80c800590314201703480c0260a4030b22074000d031040380f0b4484400c580e04942280c00c8074020041e2400c00a08070f4025070f04500d00b0010301c0c880c5076062040c4244038004940020080030400e445042d40348404a00c8001266616806844404044a0960308101905040000d0714495120b14155a03903280c0c046103850848600034903080c0058450031080040c1900104180c500079884412010183e041400c204403040d650b80164140b540d0848505445c034490b44180c640859004001140b02c0c2498203000d03015000640d4280e110b8000c81c000d9030084200010301c0850b00c1c0345017948d004a0380c6814025a0007030322121a40520780000c04c80c2400044d103140018031080c0c4a038500050b21218240402010 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 853212553 1250 853211303 853211339
    0x515010c080d15030f061d0609100c0e030114061518010f0c050307060b150c0a0201052203050a030f090308090609061b0d110102070804090c0c0206040b0301 69
    0x8008001858030100d4888822100304000620b400310707600311050400a11954554005080079944c4400002048040e80000b12844403840315044038249005085440d284161580c3c81d096104010b003c4002410f50000c07120303403a507070400301145461380c0082425200800121450140c062040010924144c210305031100d55201b18141001c1c0d5040b0301a0b40c101d4030700445410310900d113941c082c0c1c00e8031450300107219035404425a07480f031000d850548094248200000e01c12598010002600d68032036064501c005101001131220720080d030019a12540030444080100115000c10003103c4840406c00700290711400c000c0c020301c0154240180b190012048023001c2006100040001c2024602a107440e540211409075440d1140000141d29214004040747c5880d016000c400c44c80303001240d035120006c015210f10000c852002c000c0c5080f40b0562070000c03e52700d0240030a00c1220025840071004a0315070070005807450641d00010415045039100041c000790010050103510200d098610003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 853213803 1250 853212553 853212557
    0x807090305150703270f060e030409090302010b0d110906040b030703030206060307060806010c080a03180602070b2a030402040609021309060515032e06030204080c0f1030051501 78
    0x1e0741140d808480c5c920310580082c1840d049211079906010140d44480c18100e12102220303034407560b803079000000e0459080d055015518000c01d10025007031403c5000c1c44160f102e50105001003402c1c040107105400075001582103036aa40340014207031005c0000d0409103001e50020f040629101e03080504e04611504008200007041080c048641d8000c150704c0b044991009480f515645041d500724001e0280d80c0300c42044501b0b0307074000028450b49500600845004404102d401c1e0340740d00c800c417000149582050403d15030440c000205c100140f02442d005840200003250f0903507121070300d0040e60081c2e60504501c403002e500802c042c42c200d00c5140c3c0141801c3c0c48201c0503034843c810a00580c00000d003610801c8010341550000b092500851410300b11650203501300c1d2070740380c05004000317420500414009118240c0004c42c02c1c07502d0000d20f054550000c01c402c40d8940309500c11110700a5050380c050f101d65440d070120b103050440d180904d0b80e003105800c0001e00342c50400d1082e001800a0100c80741 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 853215053 1250 853213803 853213841
    0x3070602101b08130609020901030b010323030a1808030d1d0705030a0204020c0f0607090821070f08160503070b07050313020f0307030b011806150f0807090305150703 73
    0x141d04403c0e4940c0c0404c9125020701c0a80c1603081c41c0001d0259900000d500c032030800004410030005c0c0e442c880c10b990081542410804401d5900c0725051010360306404150700520820001d14444e41d020580c6280c00f03000584040c0d50b9101c5940384d41c11100c82a84140d855980c0a2124101c0310404e002c200402e00003002c02e14603220200b9143c400c5075030041c0c0900c0c1c0018441184460400640c0150300103001200c1d40b030711700f00c3d000409840b000c0c0107559840c0210350018540e00f04104440d09031540505409240040300d59079000c9445d4119400c0f144800301780031b526402d04450000116850080b406144d880c1128074044030301035802060081404800e0040c40300040034400c5d410510780d8150f8688180c187c0100c0064074081295000408040704000042030803159001e0448003000540801d200344c40e00d0b00045008040d50804001c000348451003c940564816542113400400783e082541e009520b9803602410105e4207056241050300190520121603450320590f05181880b9170964 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 853216303 1250 853215053 853215101
    0xe0603070507080d0204050907020d020105163509010902010906082401020f030c0a06180503030c0f04150206060a090b0f01110c0303070f030f03020301060801120f020307060210 78
    0x703807140c01403040c003411003800400e505064101a604031400361500401c62a020301c0c1520000390760b0740a602c5200015400c2c40049407070008070f400b03200c60b1a29581c40350080ba12015030f14a400021040035810f203031540400d00106803644c9800d0783d0017084448004102460140005032804144e68083c40c02c01080e101000403c00c16501e20a9002c00c01521030b42c005205080100d15140700403801d60340c14000002e80d00124400000d4481c0568441c500c18003040c85d040038481c3e4070140740301b006031040c0c004000150310412078500600307807003415000007414542c03284840642d1960b80060300c00940d101d038050213500d107845811b800007800924000d0014200c0b0b1808280c7e200680004241440110084c6454a480030301c01c61403005009401c03280c84a49038140300c1580c4c00da84c07100754089840240015403841c0300f0700841e4140c607460b0701d421070640d1a01242001e0000c030b03881e0642e0004401c040600050781c09000346001080719900401d44091a40711003021950b03248903401c40c0d4003101c403880c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 853217553 1250 853216303 853216307
    0x303090806130602090d0519020307080f030a0f031b050d0f0c09090b0414160906080f0f041511130b040e0c03130c1d07020d02120a0c050f0604030e060307 68
    0x20b4100366500c1032001d600c8110070404102c0b4803802c0c0c50018041d0080800c0c4170b07500c0c8501180c003403409008604807902c55682e00c8903030f901c920085c001800182c008003d400741d4903000340c52001ca80c024a02c0d0016081071400d80c0320401d2042c000303417280095000580d030b1010b195075004007489514400c5040209581110300600089071900c11120090717211107510b191555150f0000c040341c2d0b150341c1020058070380b01c5e9015030011201481304010034010040881c04912440341030744034110580e03d020040c4c5900a20340218007000b481183d03581c501900c1c00f805c0d0070181c05403000c107009801c0259119007080840103210501d42e040082d01b01c00c10301c0200041c288440070300f9041030032031302c0b50b5507261520340304452002c84544010b0240c104491001406440103000b40c01480205400c0d0303146901d40c00c004030384480c01c1c4080c4d60010f0f070024142244a4100340001c00065800d8100340005201c1c1da540d060428502c0c9806603115044a002c01c1706050308050f00c0301168204803611451071411442c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 853218803 1250 853217553 853217581
    0x3052b09090f0212010902040501090f0b1218030c0703030305070c084003031b21050c0f0609120a020319031e1a090c040308090d1b0303090806 63
    0x340e08442a12203440c0101401c403941101d56007240d040e0a501150707110341b60003001e50702512429002030041c2500140e003003505000325007502e0600c0042450724011069845507200c000d48604101c500e100440d0308000c4080004028540c820005441114a1420043c0c11260003d0803481803010380c2c0d821400050500c803c0381e00840e0b41c1c3e09550000c2c40101c400c0d5802481c0c3ca00c4c981c1c0348801c140f02000b03030414440c0c0a042241d01c00e40d200e400c40700000e001030341d0922200c00010074024440c5078288164a8a070401120741d68249000e9044c00901c01407140752100c0707110600c40a8001005101140c0300074403440c1b1112490032601e82c540f0030a0300d0300a40d0303481aa5040c141151a03805108031403071198001580c10301204400c801020588100e030302c010000400d090300001e1402c0c180e801d403400c225407564454110350460500b0645552103014042d440021610b03031040c1081381c0ba50004101c25103550365001c29554400b945401d42c84c02030142444c9821042c110f074890304c20445850b0070802c0e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 853220053 1250 853218803 853218809
    0x20607020c0127030819050a0906051c11040e0a02070b011a04082406011404050d0c081005010e070c021005090d06110d11040b0322060603052b09 64
    0x6003800d07680c90200c884450407080c0c3c0e5011030f8682581c52001050144e174501074440d0003c140c0c5031600c01405076106440764451800c2e08008541440b000b00301c150701a0000c0c024219941c250b0101d8005407808490071200c54641002e0030240c0803409100c1400c0040c15a944050544001c500d41907023a11442d10a15051241d041c2411444401c140c02d01010003c0d40d00410700c000440300c10038152802500c00c0600e030a51041d0880d80ca20006540d58462200e4114038140c4041c0b945c0740c035080c0014480307010140d600a40d441034440c1d50008101d042001041ca0807000c14400050950603c00c3c2001c001102804180030441d09a0001b000360740d8071040d0b24803050040c146580d0705c070300d100b0128022031010400a05224a88100400c9141c6c81c10010306101d880740108200d54170701c2400c001c1c81801079001e580d080c440c3c01d0001984d111b40c4511226003504a10b80070b1030b0405100c2e5609004d0702d041c1e4104039410b402c000784241d4001444507042ea032a4400500203450340d21003003c0200320600d548 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 853221303 1250 853220053 853220057
    0x170a020306010c080307020c01030b1903030e04180b0609070809030405210d0e131e021b06130b0606032a0c0a080403140105010b0a0c0204060b04060c020f01020607020c01 75
    0x7040d596802404040085603210801a460349007041d40a1f4413804840c00903400f09081002040b180e103031190005001d503102c81d50039009030b0b065840480700808400000b5070803956030494240d9051000d0100090144030741d00e5184035140110501c5a0900b003d010f2000380301c0000c050056040303000c8144d03800d0302d5081ea0941845c40142400c83e612128000e5016807074001d07003415607941c40d0300171581c1d501d0180c10340b0310000c5850f0035a4010210b810110041001c50f44502422003000310507002081401000c003401241060307288401403c000302500c500811403c8002030100b00208814500d6000000302c0d2110b0841ca0080e0802c1500c90700d20f50380b450071001603540000c24203460350a0394802400401190344040795882c2c00100e07a070040c0801d4801c91404e0150901040050140d14181c4010b2112503040c81780003403040d1a90000d50078200d03402901c44501013081c1c08040b02502c010304039a5500805a83c007030045c805034060500d0160b0440d0445c030200102da40d00017400324403401082c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 853222553 1250 853221303 853221307
    0x180e070909050a050402030c09070c06111201080d09050d1106030a0e0f07090b0f011e122c010608070b07050a060531020d030f0e091006020706170a02 66
    0x2080088404000507000324820514040610a103180c69070701c807a00c15882135080700d1642040404000052104452202c00203112038456400075030240c00c900b5050040c0c0c1401400d1868001400035040000d800941071a80403603d00080d2646c0a680c0800500d0140c0301000d41199949586c80804115000c4074055003000000c00e503a100e0b59800100d440700e921f002c3c2e41000096005040d2035000320300c0341089681c00c00f4004040c900d020342c220b0031414030503158030116411842003a00c5241a880308403040c064041544005100b050003510340c542c0b540a4018960044609031440741d546407801008243e14000041c441d0b48000a8044103840541042546400007868414508049800000c20b001d04141c1405101003003440388a403031003100d1020041ca00c07150b0010403909000c43d50080e40c4000d2020001d804a0f020308420740c00307000c0c0d82c502007800d0b1010102081451801b03650001c400d00b2905001c10801c0d03418030240c1c0140900d03113400a4038111340303076151070840f2005d402240507a41c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 853223803 1250 853222553 853222561
    0x1b010e12070210030e03070f05010e2112072d14030f070e040920090c0a081f091a01180b09100c020a060c060c03022503260a0c180e 58
    0x400076a0621f903403146040c06090090b2074900e020300f840044601c3d15100703541c200b100a01d206220010011000301480303041c1044d080741e804d62a64050300100520036040742e400c061907450003003440340304d00149030110140030703418006240d0010000c0c44000b1400030301c184405000141c0303172940c01ca0141e01e44052074802c1a40000c005100742440188032a07124001c107031700040c0403070020700c00000407200c1d491507503903004d220045032180404010004051000040300008807140119517a44c240512a651589482641c0101c0b100b0800036a6441c3c00211612815030384041c10340070801001c0c00d5a05518a07046a0300e030240951410a032240c44001d40c2094018030400001c0c08054000340181c2c049a0340c0c0d20f0141111602030b2060701d155040c00c3c07840c200389001e4002c50340055802100e141d400c440c2d04d4030b1140d24065114003241040043d042c0c0e031840c0880004c00b00c140728004450310480d4140f1715103940449041c400c3c22001d00c2080e2800f02500521614654111039049441c8061a56 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 853225053 1250 853223803 853223831
    0x3050702030c030a020609010501060903150f200d0b03010e0a0803090a050304060819022a07090f020a02160b041208090a0f030605130b1306021b010e1207021003 71
    0xa5020044070b94400410400300c416800114940260300b12402000241d8a48074212440042800080d21440361400746810703620480d4020181200640b40024040348129500c8034040c0da40b100c0c0300900380e00825a00070107003592141c50840b14045000300002908103010310744170701e02004041e1181c0ca0101c0018200300b01400520a0903900006581d40ea40d00c40ca4050170021040e9150720000981301100384900c242c91003262088001c800361505000040c01411404060810b82c8002078000c208000a03981c1541c0101111107000642c056240c00f21900000c0c600080c6120740d00010081c14401c114422401d41280c0c00c1c0c2e90039003503030043c06285052480c500d20075200f00580150495030001115088800c900c01a24460300d0248015107980c1c0c100d82c0400700303081015221031340360400310745007015a605204005114400c05420401101024140b6000794116442507944580b00015202014040048420007064209040c58002e0700400c8110b264150500c0516644003441c9210303070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 853226303 1250 853225053 853225057
    0xf020c180939150307170f0708010e06041508030d15050f04110c0d020606130e1e01180f0b010501020303070509040f0e0f0d1d011b02210304060f0305040f030305070203 74
    0xc00969042e13942d0070440741c01007480351540c0c10400800c0542d80030940c0c2002864000c1e000d40400ea5640d1456400c01c501d100d8200c0019001d29402981c584070014601c8545060350014a100c102131501c451104a82e602a60400c00c4040c7e41480500424005580c500001c8103450380305076000101c204170b01080b00c51a126202e04040248a00440d6004032540002d02610811042d40c041036511003003284403040c1c40c440c3d40c40701507640001391454810481072845c09030f12032140340007140c0e80700c0ca0300013024000d41c80c0703000742e071403400c030348088814808201c07216801032a081c030085155142c1030500412901600207498440c40d2240142c2054500b00d8021003c403d048109030340e001620880c44907a21060150720502044420700140981225191482c400310010784650046401c1e80a440e003441e0451801281d112428100c0c607641a40c60707000c4180003907100030003503507501d08002d4050003104d05c412911040604040030400000c10020000703808a40c50308000c00c1d15240c2000c280d0442c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 853227553 1250 853226303 853226329
    0x906080a150f2009130b090f0c0409060618050d05060106050306060d0606020a030314070203041217040b07110d111002010917070201080114030a030f020c180939 71
    0x30303c0444440420314041c00414485508903074615038422840000415500c44083e00341d4400c0c5400000b4000d03000e03024a040d4071514202c0030a06c0c240c2c4810701c1000700d607066004100001c45040c42d500006181c001d00070003a0404403a048003001a030340c3d13000d40d1380005004a9042040100c04030fa9261100b4058800024a801c414800c10b512200b000b0b40d0f910103080705400007400e185180b1001c0c908002624007681030381d070145107020f0410441120030f40c0c0300c0c0700850300100b04850003501c13018110b002e4409001904076841d42d600080c00c0c10017101740310181041c0b040c008180d1040006000c8212181c1d40ca40a40d5500303c44441280e090380180025540a0b10b5101c015506001c04000140102803091003605e40907480e90300c0382e910f414145c1140d228035030141d00451b02071000c01d016156100c0c20401920444540820010100b10442107034043da031160014441806850042030154412011403100c81800c04243c00441181d0311080e1300c03190300124031200c440f811988a01040200d4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 853228803 1250 853227553 853227581
    0x17010f0e1f1505071226060f010e011106070e0a0905010b1602012304080106090b100c02031c0206010f05030109020321070204140108280210091e0906080a150f 70
    0x605c00a801c00074100706804401c000369801c89020701840c0741070131810280140c0c0050084100710541000544010308443d000302c1c14440840e200d072014590801c00140700e810710343c0d11080c409005105102042c0702c0c0303030400f0350b40c142004010b004162151095801c44443c503031540707648800a000507190852a0704100e6a003e22109140c80d0340381c0c0c244c00a20440307031400006c01000c0d54914a40d81241c00d070490080d80411480c03000d40005114121080c11a80001d09440704840c44444807000b00c0412000d52000d030b00072400400a8440311039911000f030005500903c4020529400642c881c1e807044440301c0c0703103001c487d942ca89501e40c0d00c007581d0900f54080c000700404600f030440b80701141000d10030180c41c1e203d010000c40708011201d56001d401a12580405d09465159007005101c001052075003003040180c038000900351014a0b0b0480c9000c040d0003100c0c0241c0c2c00d0031004019100d03242c10045051748a5442000040e040f91800348001d1604000000c04000103210a40030300000c403080c1c07003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 853230053 1250 853228803 853228823
    0xd0507170a03050103053306120a2a060c0b15040c050d0605011803060f090f030513050603070f031d01020c0601090501090501030209070c0317010f0e1f150507 70
    0x101c040d4040d48018140c0f0b0041044865248608560700c24070070000320b50031103c08111401d84441080612240d40004005010320410329205203628588149482d0a0f03070782d54242c0c003806004c13240201c80b413030205047e101e00120b40c5046c040b014009240451300240180369090000e40400041084510720300c00c000e106002100003001b0007030240c2c0105501052851400d1000038156004810480050310075940325050b441c6142c480d03000800740c0c118901c100710748801c524000142d00c1095800c0262217a00c505454060340d03101c6e290805807130b1b084140030360b804106010000b9001450f40070090b8552801140d8003810301c251130031010800140340300560000ca0f598056110101d801811b03038151090801aa07a80d4000407419102c0c20701c40a900815034001080c6203921540b900c5070114042c2c1410403418450700304111004a09900000284441d44800d100f030404c07500341d00307402003002203403102403480604a03914004400d12405c803100a210142c155413030702610943d81c00c81e0304400c4a00c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 853231303 1250 853230053 853230067
    0x61005090112060f0303080c04080703150b030105042a050f311b0c030c0605040f0b0c0307120b0306060d170309071503200a030207060203010305010209100906020d050717 75
    0x5001c1380240000c80c0401c1045001445e031110442c1070390704950005004010692442e12152040b03010000802d009a8940c3c0b89210341362403d000f86405188690b8103030907184084510944110103421079204001c004503804c01c0030303550b080a0700300e207060200c549050501d0a40554001c03001d0010b07060b01c2c0781d0000f80942840c043c00c0d501c1094140c4a443d055100002c4081c004c4030a4100840005c0110384036a411801160070360340701c9030348070f8442c2c60200a04056516890811038048890041c00031000040186140e8003544110142915880601030036011400080d01d8140040546d4003441e03000326408288200300146040312050fa44059969003001c84d42d190300c0b0b504c01c3c0501c0200c14400c075020050280300f40b080402c05030180100041d49040c8180c1d8128507030241898508254080c004080030440b1440118021842000010783e40c082441c103015602c0d17007946100c01070100d15074041220940100f4002241c220340c0c90a01e948401302e2815545103429044403000ba28008540340c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 853232553 1250 853231303 853231319
    0x60c050d2f1b06040b16020a151d0f0109150b06182205070f140319060515090a0b030f0c0d140901140a15091806090b04060b03030306100509011206 65
    0x540500d000303030006e506900068006a80e6085801700003421460100406810070800c1e1744110004071880c48005500c10902d00e5091911280d400d01d030507565074400500c020400b2000b041e0030103244031032040c01042d564400140031409001e0f041c17602d0462030410703182260744845120082014400f100200880141c3c82c1c0e02c01040308842d01c00111f42070245400044d4014640d0100700c0081c00c1182c0d20b0360307403030880c2da15101d90031030412080c13070342c86010120300781c2d0301c504040c1d98030b4400b00c020072b803900d05505c10031200000641c000720385030b5000c005001c0320294445407980c1c003090310720780c03030345c0c0ea413404118074008103417030800c5c5c0304082954010f0042c12201900400c12030611007818511035210701110310102d99a055100c04041e03616a42003000070b40d19005000d2400e210341c0303150710190603502c42c1429100c3d28041102e00704109000c1108000151207152010b2900303800450651030414040f8081000b038172007110030300c807021481c0b520313030380c810080c4000c40200b40c1401d2003211b07920561 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 853233803 1250 853232553 853232573
    0x50106091701090b070309050708030d0f0b090c040501050a0e090115020f0c032503080304052a031011070f080c0c0405040b0c0f0403060c050d2f1b0604 67
    0x286495a414000d103032400004140650010260082e013890010b45403460207078010240b00500304c2c0c0e140503180e40019001c1c0c2c1800905000d11104501040d02c80201d9007040844003021034043c420075030181480002c000c0c01007602c040e04c03800e082c80c0d941c1d00700c82801a03a02e42d180010302d941c00500c520001c21800007004141c410762503190201ea00b00308140d10003603100e60b110984280c061344000c14000d440f80c000da801c00c24010000c04d04094560312500d610415074411182a6035a074882c201140d000140d003000c03102c8a20030503580091041078100000e4039100d40502d04030001e1b441c0c0c0d0544000039110400c070f40f56954440c3e80020049894500a001504488040007070380c0101c500715819030515004107403140da40565260159070300d00d15000760310740180c0d00016842c04e00b80302c040300041c2d60b442051044501c5032a03603910b4a800000000580f18454220000c5580940152010b842281c103070b420840300c10103045440340e5241030005071a1484e09181e1580e03205a4060009100c0c000c14 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 853235053 1250 853233803 853233809
    0xc030a050a0e0d0f061a0909010203060a050108072102090607030e04050c160b070e121b0a0e060907120c051b1501180f0905060609090111071103030d05010609 70
    0x1c07120000b07007a0400b040081e444120000e002e2030030311001c040008010b5800381b406450308483c00604294610041410350708101c0d102840b503036002042c40301c0c901d02144041f006000c01d281c0314040b890b00aa009000c1d10980100c0040121404a400180400f54054400d400800390155856900a0400520074004903000e940502d260202080044012400f140c251801803041550340594503540c85020b00b0004100c48100950b1225840c1070b543d402840a4503188001c0c02002480306815001c0301007a2100700c0103109d05420a01044040321303024010f58014401c4601885a039182002034a04c15002140c4081407460061111440e03a00000641108580040c0c94140c1110b440900d031303521050740d8000700c12203e0400c010008044800d20590700c42031501c0c408a0120f403100c1c02403098415603041150140c1042040000740e040034a0f00c5a0b2110a040080c8051416006104203030710400b44041c09180442d8114030660300c080040341d0b250705130010200305039a59036000500380c2c00300b40 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 853236303 1250 853235053 853235057
    0x90509190501080325080d15060f05090f220609020c0106090b01020a12030b03031602092a0a0203190e030f060c03070305041b080f190506010e0c0c030a050a 69
    0x1070010801c80d0000040d100c0350741c04403108108032500c6450403104c25400000440350a01e0400c6507200166040c0202512220080100849030b41003150143c036514005031120100f050a0181e00c090b96501540c00d003040718180e032444001c151801e142494a0300340c80754100150f00340840061403541c00c0c2c0c010b05807050807000800201c0e07250540882510003515183c0e0040e072103010714501180c2504040074440045007000034104510300301080c1036811251003c4440c1010108040c25824011503060f031008040c40c495080c0e01c8882450301e1820700c0400f5810588001255091861b13000704203d64107880c203d0341c80303c1d80e003a90b100001e101811020b007140c001d018458590100708800600c181c02166030b10b20250841d500c05000700d0013040000d01c00e071003140180c0001030510200c5202d0001604401001e00240140154500c3c07a0070322400002601a03820044040030510225a00381512901908940f07251503141c4c0b100d0b21030241004160300d07404001000f030320864000c0300424241c8011303 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 853237410 1107 853236303 853236311
    0x110c0109030c0306110d1107200307140103111201031110022e021c1a150d061a0306011404050108060d030315060c0c0509010b0a080709050919 63
    0x3087c003491102c0d2030025680c03040c0310038065516800c107029803030030200d8200070700465a136145900c81c020307150801207011003240e88030307401450f131080d0003c5c02180c80f416202440352104034203110407140d04081c0190102301d03040c48602c40d0b15040c943d4018040951040540c07040c05125100e001881d404401400719003c40313544090584081c03107152042c12000071004200c101d13095078010500c3d041040130402c3e010340c0c8801c10100c03450300211150743c03100e00c2403602c0006408143c00045110982824050340f03210700070080e61280c18260384040445440c10b4094038184100c2c09800c0c0001c0c0446c00203401400c00400c0124a1840b91400003400784240c5a20200300c816500404005a1141000c0062144000051000d0001112013481a51428000d03008a1203034440b030b00c09102003803000854043c004d05811004210140045080f4a80603e41554240c2d150800707a80c1f0034a4 = true := by decide +kernel

theorem cover : BRFrame.Cov 853057553 853237410 := by
  have h0 := BRFrame.cov_init 853057553
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853057553 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 853057553 ≤ n) (h2 : n < 853237410) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
