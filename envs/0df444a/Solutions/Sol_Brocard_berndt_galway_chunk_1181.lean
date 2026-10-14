-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1181
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:38:28.520567+00:00
-- url     : https://prove2.me/submissions/658d1797-a0c1-42c2-8472-7254324824fa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 212230215 ≤ n < 212410071 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 212231465 1250 212230215 212230237
    0xd120905061008011401030c0b1309020f190306061403070509100306051206041a04020102070e0a050a05060609150f0c030408030403110612070c06020f0703080603191a040809030f03 80
    0x7003c985176624080364150403070b41c000c907191400500780880ca1070158820807a094115108032004200c0c00403030320040c00962607a140b450341e214a010414002141c4c442c416405051400004200e840c0d00b00724100101250017000760780d240e03030300e0600351070600a8051180c0c0191454020898454065215105070b8100300c43c9070f0f034842c40144400342d854030100c03030017004027100100c0302440c540c1e90740010360064030500581708029244e0f11201030140049800f0030010b92500203110010f82c40f48600c0747c000c0c05c160f42c503030f20b00000f07140410340ca400e4070296408102000110500001c500c0070540d12007090f070400783c82e90b6a0f41c07a13181d9540c9030441d020a4501100401c079046051400c0310844010744c402200ca10503550743c03008107542c0c690034484151410750b000c00c5000b54400c09070f0010b000541c4291140700d5141025002d15250140c003910f00d004410756207030a80f001c07030310907258959402045905000c0b1983c9900d4001800e00910145075003600c21410340038003510012010313000c40510 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 212232715 1250 212231465 212231471
    0x41104110c07030f0c0312030b0a091a1e030f010501090c0915081f03080c0105070203092404050a08031804020f030106030b150d02070b1302030d12090506100801 71
    0x19089816107200350748101099038400e0004200044014010060a07406031142009043e9207403030f0003810080702c000460009503100c00000c120b00e040e040510180a18000c104082030106400042600020b400c02d885034401d4011201c400021424100c50001b01805690f1184541d281e0240a171a0a00171a109141003115149420384a900d418085540207640002407520900003a20a500040e01101c1c0a05a140c41d900c0f4a0040c0101d00700290f1082c1109955640f4881115084540c050003d108640040020f400150386400390110718082c400e00e0050180c07481c070441d5440d4403c9600080d0050030440002030704d480c2c0840500344042c002014201440801c070108800ca1145a0b07803c40300100a1006102441c4650300c41440b050740548900d0007840c1c01c0d00228036641220182d4801180c0010700700040100300e070700e0507400c40c04099007a04142c1c05a40001c2d1114040100340c03003040080403400c070f0100303156000030413829000b1080d00c0e40c0d8180100c0d524015041c0e4007079242150f003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 212233965 1250 212232715 212232731
    0xf030a061b020c0915011413060512070804030909150504050a020a1b020a092d020a030f0b060403080c03160b010501081311040b0301090501060b04030c0f12030810030b041104 77
    0x41130f102140c4201c0c201e80300380c140084480c00640c0d000d810f069100449290610114a03402012182c580191600741c45880d04c5040420000010600c0100f526080020309000d200000750807014034401d0380e80c84480072030a8411100c02818004035940015031190a0005014070500b00ea8014200c4031956681d41c2000c1c400d49060881c06181284000c4d04180c91020400880c07265078402d464440e44040100a01d0004c485c0749040030341030007040d40003e075001400322107854061280841c21840d1207001d1101006075400202140190701c005044403000040c0e41c80030f030b20148129404264000b40c4a10461040d040025240728240500b601044080000c14110501c041000810507448070125038040c804100340303c0034000441900340c01d5901c03013004600040083c001c1c0000391000c0c8170003980722032031400c2c5041d0785071040e488001e82c001d164009101072495524060091500f5041c04903d54030342d280400c0614213203a1001e405400c00380144020031101d898904800b420840d000d0164034 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 212235215 1250 212233965 212233969
    0x1602030301030f03180803030708010905132a0b0705010b042007030c030e030718050106031b030510030803070c061103070c0f0203010f0509071502070e01050f030a061b020c 76
    0x40300a01000e420f0002c22082240082c0c0b180ba04000200d54114140701d6659030b41286910310341056980d031021440100051010016910625600c880072440b100070404a80c2c4a00c0e40c45d44d89050080000e820390082c01d54105100a281d40c01860149501641c81405081560092510307101ca035201e2410010010f0608060303908014541e204011005d01e02203840cad4054a41c814600340c100c0038404400a05800f9580611a0000500c40200c88c01d0b900b00e2f0a6121008403070f0144c1120041c14513000c010721012581d003841140320443c9040006030780d05c401c0000c0c64000744a6000a0040000004001b046944441381114041c0300c0c04003448118200c290302c841c6030008036214400548805041c002180b00c60b840a22034600140c00000c1e800383e80b50310701040c0e8808542da60704e1584030303910800600c00003201038201b4006900c040c04200e8245032220910740010302c90f107841003820035050500390350141b04120001d13610134410080544d00301104449001b91102c52005405000c5002541d4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 212236465 1250 212235215 212235217
    0x405120c1510060e04020307030e0607110f0706020d0813060617010b15030a09020114030906010f08030f1204032c040b090103020303070305130e010e040210020d020c040b040b03070e160203 83
    0x1071074181d144c1c105440c000c401400000d4200510610403d904d91200c28100081404040d014001d540d03900f01a801078801074520b00801e00c01c0191066005400401403144e010620142d200c156180c800b40d252510b528403800301c2001100544028600400015624615070308402c25009640080c48043c00d02030402c4900d420000404594080401c0040e00c180c040f603004104176481410718030840b600b00740c0303000a0303608102e0303c890841c1e2102005100c0410150021001004103400a52600c400004000003500402814000590107003011904040c020040e0842104046414030a1944104490201c0503040c0403218022803078031103210940e0070030011240c180c0e50090010b525180d0b46a404980903484400300c0240c6500f4440d000c1401042c6082c00d40c002e284080c01300407141002d0040005640e80100b0441c2550300240d042602d140e0081803408240d00200c4000902007072920101e40504502442107605000388880030078860410300350306000d410748003051000d4904252080c1d0b0b903 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 212237715 1250 212236465 212236469
    0x11030c0703060b030109061506030e0303070e0d020f031c18030305070b04030509030a060606030f02120417040b040b0c010b0301180602030a020d090f05060f07050405090405120c1510 80
    0x62a08000800d0000c1012900203603c6038902400000d20440c09864020868801010012010b26203180130007141d641802031101c011903540144d491814410005800c0d11845070b000c81c014912640c400c0c05654803124400122440542520318070f044000482240c41d401d01c540a0108201c2a041e440c070071401c80c04801540e1345922803a00e0034405071200601c10320001e001b1401c128082207110b6958800b4050714201610900c0301150f001e00b0310601030240c4010294044005105004000c0060701240d0403a0b041030704072070705020400c0c00d010602e55030322481e08903641c82c500008002800703100e807034014004110480000c00400e403103c1d08241c282c1d0700051030f403e201031955098601140c80d542c0215084001a80014a041c04003080c240940b811703803801b550480011303c421002d00505000e400d40c4511020740482c458948010042c0c11390046000d00d9005031018000241000070820800c0281060403101c1903c80380b80060140d60b80490406408001804c0d41c04035a003c2403084080e01 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 212238965 1250 212237715 212237737
    0x204050c030c0f1c060602150c07080306040f14100e010509161d04060f030b0f060307090b030316210e011d190e09161203030b0111030c010c1103 64
    0x807414078008103c500b560004820b030b00c0191540c01d900c8524400502c512401440940c001d400c00180e00345e41c00244880003440f910000c1c03002c02483c40029900400c50341d1241c422280051047d0b52481100300030300c559034000324142442010f100780b40c0018030101c0112a6010701410b550781c0c90f10240001c4890642e1100f4525403100c1030010014064141101400c1a031201502010412800a01501c545034403580054403032a1088c401d100c01040394075845a84e2401401c914100040480c4d600d088bd8402d502400d5078944c1c40040541c0d00340102d40c040c1807820040142140b0a090184042212481c0304d1000384821182d440924010140c080300c6580c161110010443c0d1950b01c0380c3ca000e41428010b40c014800321840340304461030005480030703000055101e119803402d44402c82c6081008082420500300c4101c040045000c3c401e540703440c259040c40c3c007241c202c1002d401130b00c0c048104418051a4080841c418000007070540c0604002c0c7c19564034202000700402c1c0c00d54a030f10924a03a02 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 212240215 1250 212238965 212238967
    0xa050a0201180606150309023114010e0121020f0a0b070602030105040c0f0c020f13020c06040c0b040b0d09080c19150b03030306100905030a0507080c0301022503030f02070602070204050c030c 84
    0x6120b103000c803100c0341c40d074603a0380712742540c0142e01d204c403088883c0780d24021520a26200180510301c0c02c400764034050441040e8008081c0034482d000144881052402481051440400c031802c2d128030340d040c0000c0c4205c009007900c0b2200c80c0b500c5000782d002401020302031842c0002003410a0300c1500c80706e990614a40f103110403142d007602880014140050896003104070324103510007030f0300d0700c1c801420b01048030030140040d030401d4503201210003200c0d0303c10000340340280b00c240140100c84040b28600c3c10000c2c1c00041c103030750070324051966000f002c2a020050040303d6410b8080c580300d007644c070f4445118250301c040041d2001c1c410800c440940c004650550701c20710009a250400d03a580f00390045440c24080009075480c0002072819500c0c440480c0e007608915000c0003220070030021048141c0c4203e000398181600c07806a40d20501d000e204564170205907040e8071091600a90085031060203440c3c0940d0785005a08118010758000e6800301c2c012071038100010941400b403001d403801074401f100c00c5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 212241465 1250 212240215 212240239
    0x4051e06070b04020102030f0304050115050618041a0a0b0d050105040908030a020306030109120e01110d080606130306050a06080f01050108190515040c0f090b060a050a020118060615030902 83
    0x10401d010b0010400c0f41544402c01000030441140e42c0034520440c41113001040388a50701640605000b029400140100c038140b10b04030203234211098500741600240c0d800104c4010903034080c1240d045410180780c10014801000c00d845143d60010f20078100400000d0056990b40d409000481c0e404a101500101c428004204400070580043d0380102004001088080c2c03242c9500000340055800d4001244142c100500c04d96040403a03144200040070203001500da000e00050145580148039901c6260300060071008011849103100195400820070032141c6060201c0b44010040ca0044500c81d1042c070400d4204a5814014203050700c00c000090034500049107090380301c45001c490704481b01e010b0900848000d51100d400240304a004404440700d640c030b07080103401c00b011240c1201d01207605161005503191600c0341155880c40441c501540e445c000c1000c02c034010b003200601d980010000c10100020321405402c0082aa6407015503824912560001034007211503040009412501111030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 212242715 1250 212241465 212241473
    0x303020a06020a1701180c020102120c070201090906121a04050703110604030803040602030709050d110d060e060a09020102010c0315090b0607050312040308060105071a090111040b04051e0607 84
    0x43d10b0240380c6400c0c107404510084040c0000440300340c00c060700505950880c403802114900903060032840c50f00003146040999403000e0040100207050018031840002da0800b1a48100e01400091400f042c08008960329903010a07181015081c043c2d504050314400800c0d03071140301010602855120300201000e6165599040c41140e005004c180c3c8550180000130204001d1402103103d1071151a00680e01c2c0b420100c054444115500100c2c02801443c40980001d0810354000c0c0b1040801c440e082c100e5511464204040c0c6021760380543d1501a59003849492007070380d080795079954400d800901078420030a40440071035a02c403400321122000c0c104100940724950780039640200d07000d080c0300d2420b1120349925207151301c116814000e0310500001c000605902003c030542280c2c0c2480e10038075080fa20b44030115a04004080c1c064014245004144105000d501c0081803503a4008216100d5a440c120b45050b600548612402848520b03012072002c005440f0581c2c050f100141f0301824100c1a0315 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 212243965 1250 212242715 212242717
    0x6020d030c050f0703080117191518050c040c030209100e0402041208041703030402090412030605030f0114010509010807031704030818040b0102010509101e02030708060102070b040303020a0602 85
    0x18070700c4140300c0100b0503000b85040710402018854004e803144c02aa5140103240c140c000040c01140d0303035941201191060b100300d446d040f500700b5900f141c4184050401100f0b2038008101c8021180000d0f001204107030708211002c119046008400c6a081160440405058050303210701c400e90795118040d007000707862860051502d08905400900010704140d01d0311204c60403a601040c0030f40d0000c0000c00d04001252560507045403140c5504040e43c110304141e8041085280080c000600b0b8488084200c0c0d0424841d030312110042c0002411290901f0103246102d0003011110080d4210308401400441c171403c20b4070105040b20b9013207004106461842e01c81c6100c04800400c441c0381c0c11010400040401d0034000a045054101011900002c40040c200b000700c9410700401810f5904001c04c211075120040740c00404180700c042e0110b515030040442000c203044c0352180d424014804024040184e07448404944034010a0302212180c0b510b0b0340c4030400600584c80028016031208001100181e4550 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 212245215 1250 212243965 212243981
    0x12060115140a0e03071205070302040b040e120a0306060809060a0e1c05180306100b030711031605010e07150e130c0f02060a090803010504020c030912010501140a06020d03 75
    0x441c000e440c0700c4880c1c801c62050751180c00c40c440082c00c900000000c2d89400c3c440369004055540343d500903804103a440742d071503580c140b0020744074a0342e81106082503120350304504c80c1c2c2500e11055074543c10108850102a800421800c1c0019140c1140401d215000d0000305016003504170040006646002105c000f829182c45c1d01c00850103001100700d4a03c0d000207a01d848298103858258680341050000c03c80710003c1c0300007e05c030b44e008a0602c411000700c4840345054a41c006031072544d943c1c032001e007501c0904c90140198101d110001c0c2c050070280d01200d980c400f01e03104000074004800036110a542d916100c0c0103d00c1c4040001c9031040c41540a0159000610409031004048041050403103007100c564000e81008584503411105003141e05016041d800301101c03a080004030815103170341e43c09000500806000300d60000e880620002c040068079000c00d0010802490b001d214906680a44428401c010341285031840030303035440c41c00500c4581910b203154014141100c40f00011000781c0518 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 212246465 1250 212245215 212245217
    0x2130b0d090210170a020901080414030c030d0203040c08011b0513031a1906060512040f0f0c0f0b030411091005090a06080f0319140f12041112060115 66
    0x944251005841d90781441d140f62101303881c1c0000304411030100d1514a500204140c81e424070401010516a07081303910700b5041604880201400c041d961001031961041d10003450b054030010409016200c05500114490780c4508900d00b982030741c0d0919503090b91061131078103941012801c51030045034454070140c03a507480c4c10103901504540c0d0751a03229165858046440050880c1010014074564040400d010102c10b0201004000e2605200510601540c141e8007180e56043c2c01040a009061624109807500304452a00d64215450288040c6825100f0480c070007116450000c1c0c9078140354141c0b48200d810000310b05800d0010410490100c40c003d007842d42c0e1544201e030114240e200c0e01c0c202c500c6441c00302d400089132810003454500d8040240080e80003035200300722450200700e0384011810b442049080000700d020445425800a020340d041c5048168004030700103414035841c0081a0240d4000c90703082003008100310a102d012003020034041c0980d44074100401025080b201005054841 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 212247715 1250 212246465 212246471
    0x1f060f0308031e070f0806010914040e16080a020a08150a0207020d120503060f0f150a02120d0606080c070b0114150414120714040f060b1204031202130b0d 68
    0x395540c43c0064006640c5440000d4010008a8030590001907540d00f100090074200fa003585801403071040352944504807401340e0744482c0b600c03034500c50401005010a0010032084a06a101e013030f0740c1d40c0c80845000982c499440710100154010020480c4105514000d1103001c0d169240e0741440065407000384103d0300035034070071030b010003050303244d0030320b03400c1c0e143c50356078140c0d81e08145041103d0080640300780c501c507001c840040300b1240c0d50099200562001540101e4540000003000e0703013021804241c2d01806807000070740c1900042c1e5907000105460160b00c400400f5201c0c1d102c00b50b6980142c400042c0100c07046c41c018040b55103240580718543e40000c00501200d43e0f041e0503840d8070f40040e032044060028501840a651500c1100e2501d0140800020260503181009048107520303c00000c0e1f001d5a40d0750840110f88042d40c010307030050724402c0c0503980d5030301004000e03002000080790250001500f6041001e00c586a50003102d540402e0640d040780002e0900302e140f1030960100c0380340010b9540d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 212248965 1250 212247715 212247751
    0x20f0403080a030504150b03030904090c120308091903020c22090c0515070c03140a0807030f0806040204062a060617010e190f020307030b01081f060f030803 69
    0x20054000d121801040d50045918107040c902211085c45806c00c0b88051410315080d442151400003c1d03d001100454022410800605203030b80900615006840c81c3e09c240e4180720306040d00301c02007078000c0900b4812951411030720b442120907120742a4006006820600325043c0300d00d0800580d208030010f0001c0050140c952806001c2100e00c10340c41114009885501000305103060000080c0c07081825030101d10780100e942da991085000f500004201c0c2a0344040c02c001c3c01001c00503415066030107100b5a540710b0361030402514045c0d803903030704d4000120300070000b4245041c24001e4074116212a01d0701d894078044070039000c2c01402085c0441158011041807200410041e010703800081c210709a0701c003501c4a9a08406094540e01801c045096101d00022019184110361a940058010450800b00c40b20340c400641801d419600c05401e10202c50004990080c012444851503000d2018842d90b4410029044058604c0782c4551440d0402c1d000d01040400e0156006540c007050980c00c1281d418 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 212250215 1250 212248965 212248973
    0x8040506030403091806090b0301060e1906030f15051513020c03071506180207020d020609030f0f1c02071404200304060b0f03010213060f020106031e06050c1903020f0403 75
    0x4061803810b510021b0b11200104486845840741c00310b600c030103400a210550070402054818034026002c1d05036595240b20101c1c004589038030000c051984020070079404465800e01707401c0c409a40c01240c00c1286000046005102c3e01221034004c060301905020b13550b01d0400041001350082d5100c1c84803400300700890300004120458031181945400b0340024281e003040c4c9035903903420504445003c100d104000450150b51009180e50000740c2c104c5800365034680325804207052407503044d8202081d200b074031540700c1c0d40344c03000c102004a110220005042004241d0089a40b844648240030003001d1000c8400090f0809030040f03100d44000314801e11042d5241c102501d40d0354011941074400d00e40da11448603e070f20303180c24810390301c0004800a504004800001e0907411180740700704d00a0041115810040c14000c2d04694015032700481f0341c5926401c440c9800c041c40c0c00c0da1200f01d504070710701000104047c9215040d2401c40c7c1c2c0c24034809600e100000b42c294001d50080d04042d0021109110010010b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 212251465 1250 212250215 212250239
    0x60118030510110a090302041524020c030c130506010c0b01061d150d1a060406020303041703010f0311031006060f090902030601050a0c060f05131a01030804050603040309 75
    0x1940301d41d00801c030b50007001100504503500a202e603420390b41c08000200d0116804845001607030b404480006420350341c3d140d42c0d42200350952162140504081030241d49130501902006806055000d45120b282010205038079424004c580703d922030240030195003007100030790205074417101c18100601403012980f100c80c030b5802c0c243c0c080c1000504030700d48c0e541ea008510387c40d5402900c05a9112440b0340da00c004021440c00342074120b6041668030301041c06d00c0c10390100820103482c000360031240c2c0d6071703141c080094503170303108841c140d944d5502103109141c5003c0000c2141e048900003050705403000c8c1103556044080081d0341e4002c2c0d040c41049281000480c052141400510b1a034484280d8200000000f400350708443d403102814a2061040060302d0760030030700311201a5030740d00c2c08081c0414240340c0348000300000c1c031000400a103400204204510304032902c1e203200c2d02507100420b084c08034044055800b0000d000c0100080000d01080140e41042405107070400c0c8a814030350303002c603110f2441c1c13008 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 212252715 1250 212251465 212251469
    0x1d0606090405100f06140a1101110d0e151513021903050601080f011a0a050d11071406090703060b060c060403050901090e010f0302060c07030503070c0302040501062303060118 77
    0x85843c0d81c403c00c21900300107421040042c585401c1c00c003e208141c82c1c04070315a0044058440a1200c0e566803d0b813111000e40c40707820362a004c2d0f01c0c5903403207400e0400044010204005000082c2c419840c2c03007040408600c0c1c0d02c17442818100011038003105003405000140110003840070766182c00740461101028490882040c0b0802c65a0000d890319203140010030020f400380c541d1070402c0702c00f001401401c0a100e280b061140500d2101075036851004021280351003082c0c560b0000510f0811040d007900c10f030310000c100e4a4012101403007086900c00d00580c8425007560f100d082030b4041e0800308006030154010400c03508004102e64200b0b00e4030304100e400d1800803a400c03000581c002810790199a00060110042c10200f5628802c541c117010400859070014003010f1307c100710204140005510801120001e1648042580e446046604d0300913184d5515000880c841c03801e20002040d064032070084460340c5403a503c0c900c0d840400c10000780703a090780080d10b45410041c2048a00400c2134820748a400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 212253965 1250 212252715 212252731
    0xc020127050723011205130209060f060309030c1e0c010c080c0a11130b031506030102131203090909021018150215090616111c020a030e0a1d0606090405 67
    0x100083d000d20004001d00d00068040608501d0082400100310300d071442548183ea05031807406451f00e4020006031031040440f121603014800204003d0b030200c001c0060007c8941c46001c544240309007045003004402d4581020f81681c1c0701e886117031183c1d80708141b42800d1500510620385004500d0b1480c81c02c04e001d0000549072030035515000c64072420300c1140114403a628440030001081100002034481400c03044607a49080500041111554203604442c0205401c0e041010581c0e0f071018070390241500d115040d4041820007100003640181c50191100c02039004001c03915240c01c0c0345003642c0b000380c0c450302c640d1000413110010503071003002c0c400581041c1c030a1f0000d10581400991400e21010010081c01043e0010410720034140c0340441602d6802c10181080601e01d204410f02d9490310003110030700c00c0040c0364560000c04450300400c904900324000e627070741101c2c580c036201800389e1412584945540000c8031200c0410f181c020300741c00d076003101780102a40d10340004000050161101518205 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 212255215 1250 212253965 212254019
    0x160504050a090b03070b04121403191d010206010b0a0318020915120304030b01060f0314010e010305060702010b15070f0f060509060703090213021605060c0c010c0201270507 76
    0x200413880c00704103000040c100105030130714160074401d40915511120f10000c14221500c03100f01c001500520a44040303000103155011202c40c0c1030801046050340160749501028020034513122544045448e5040c4c0c1c900018040c070f845c590030000c4000308005103000d14040d031408a100010380d01d442c140350003580c2c4940f5244903030707401e1030401100880c2c1c01d102e8000ca0344208003c0000582500d90ac0d4111072036030070031080400c203000302500504801594000404a9017001151340c0f80301410590503640a41c0403120702d540d03070481c04c1e4200d494071600258002e284141d4141c8200030300c8000e00003e8403441030b0789514900d503900c5080c4800245c0040301c14a0b110401c00c508003204008503039002d010780c070b02808015040d0300419410401617040400654001034492244030140ca104a0030359440800ca80003840c00560400c000d422000c4200825404d06030840d1400d0302c14068a0083c8c044501c1c10200380501c90b541051481459000b1a224000e07280b0000301248050450400c0240b549104 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 212256465 1250 212255215 212255231
    0xb04080d0c02010204050307051504080a06060303030c02160b031018060303170f040305090f180613060b04260a031206060c1a180a05071d010e160504050a09 69
    0x36005032540d051114045a105102c10445681c0001e20182200c20a891054240540003a035000c544600d821a0009104505106003048401e501020440c1e002e5079040001c6599868100d8448a0480800d4040d003403800041c04248140700085402c003900e815698000e580d80e1038820510b10031000a08402d0340d0715081042030540000442d02d60b5180044540c100c0e20301f900c14003048403005000501000307000b00c0c40c4035040d00c0760110035a004a005182d045001280d81e104041494121001c0303025951200c0c800b20400103500a4005a0321810110b6040c5410002e82c0c1e05072881c1c2228840e01e410340c40c400300982c1c40e000d11182c0e1540340642e41d001082e4082403000c105a0f4243d91014003000f0004020101090b0300c940324104070303c00341c940440a61a2448420307450070a0148124031406881010401c00100041c440b003201d007035212064441e803140e050b0301d0001d5030911841c40d00d80862000502d400c00b403200c65016085242c2009401c3c10380719000300f191206c0603040260303580e66070194 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 212257715 1250 212256465 212256487
    0x306050f211e0708060705040b0c151915230d06090305130b0f03010519030b100e06060f031306090816151a0d050304030204110334110a0b0408 63
    0x282d4001d85044e0006200e40e00341600007c0043c8624810144401d201042440424805204080d040030175403418800d682048561203000212242400d5030803490440000c80140a01c0314910448024a004c80c2211038064a00d00c1c065500701607503035203c00b4400d03045000600c60701c507480449002c2d40c0da05446d0140c0f084803c449980582100e03840c0002031042101000f030040490741507400907968094141c010901c2e00c1403010060f00000d000074920003c111000e028101e00000710350704004510100e803038100510195108050b0a40c04881d420000a00c20711a1803080b090f4140c8038103000510042c044e211040303240c201c00c10b9003c2800f008000b0030284503c1510a0805540410b810450907110344406d0152504603041d050041c14030750401410b000c2c0500c2a01d000b550007030000e120a01000540c40956442107030040c03003402d070b88040421a500d80c03880c071903080199801030340150042e5000686080c0480d030000c04651296050704d000003580004213500072407041c0c0307a043c0c86009400b1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 212258965 1250 212257715 212257723
    0x91f09140105101a03040209072f0309040f050919050f0706030c0305060405060d060f060504060f0501030606020d08041b0801020d0506090114010815010504030f0516060306050f211e 80
    0x8101c0038014401d00c409a40d9288405800000074101102e0700a411f0391000c000f681190f426038802c001900c3c0440038512b01000811240c40115400c025103500c10724620211441950910400d81c00020780207207010804030320304070f540c0c010021280804400c203011031801a00740c0103200029101d04440103c140c00d1700896411a000321018005458154007144000701c540308081e0003242c40f0306174a1a110f00591115000e090058000c1c070000e511040c100100c0085889001d000038907191000030704a08c0420140e1000e130503a5100881c80e1121307200c55164404295081008130f0b003010b070000312301c10240b0040011070300149020580345400c4007042051001680407420000031111550390302ea0740204d9036076000d038080b0b80d000c0c01c0c0d840741d5004881d10701a9400c02005c2b08050301005040c82000501540d0440502d98548100b0b030f209d0400301c00b55281403103480d4000800f170342e10100500e007044c200c80d106020210b11310038543c4104895803400e4020310020b11012001c4003403024280c4184 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 212260215 1250 212258965 212258999
    0x109060b060901020a170d11030f10080d0c03140403030309050d02060106020d030e010605220606031a0f150f0a08010b180d1704060801060206091f0914010510 70
    0x49a042c10b1a00450000c0d4448078006402800785034512456200c00c19104103640008400480401048807100500745076603005960742c0c80c1d83c51010000038000d0040c1c11801c0c00341ca280002070f00c03405c9003d802c265050042900704038140450014603106500100f07016200446c02a079000c0f40c00c4c9041c0c1042420501041e5100086401544c0103124640d0001041d02c1041c0080ca40060361111255060380140415041164468185121a0003a003070143d0101c08a005143c0c0030020203503155000e90489140b100701161240120880781454500352050700b1668102409045604406110002c0968407459a00e81008000314600f82c00d070342c0c0704d20041e0141803201900744c03600d015036100c2003410420680541c810700c86201e691040200e40e01c034002d01c01c81804101c544035611094041c0c01080d09010300c0005114250016016000c0001c2d00f0200b00c00a442052031031380b000e070703001011300f112400c00e07556904d02c0c000600c10181d00348503941c441d8220310205400c4500b4145e030142d035081d00e9 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 212261465 1250 212260215 212260219
    0xa0219034703190308190b0901050907030b12010e1006030c0b070201110102180f03340314060403030510080613030c0f0606241409060712020109060b 66
    0x400340902042040540d4080220740180341e0000e40c0300888000780c50f000300603154500115403074040070101900061580e0089201014280c070918116044e0411100c0c0101907640c0065003100400080c18651030580d00894a46400304400041c0c1d1701294070394505a0b2a508280c2d5a4006410110b01c20300c54403401098005090011030b28548540c20414010b0050b401e138480001221400c682c0202d5030351036520341c0100295200d04071044050000070f41c58007117501921806100041d94500030981e82300169000e46a28200c106001c0001001980b10981e00b190b900388980200202d000078804c0c066000c444030041000d45460f00c0d006040e1400542004a010151803050101800205086601c004451145560300b5418101160241c4119a0203003440081c105020240200341d0803050544248080158160703410078a00d180715000c9480ca040001c80d61070300d00842e44043e0009190b104030040045d81010f42c1511a50302030301000080c1c1c80907079910f030581000c0040a000740c00c0c0303d08003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 212262715 1250 212261465 212261531
    0x17070512070e0103020609060c06180c101b06150305030c0115080307030f050403140a03020f0c03030d05090c09090607030e0c06030105011209060f020912070515030a021903 76
    0x180c0b002001c2d0720801800028403078500440d43d02030a07100c400c01d50300c406061b5400c0780c1041c14135901c015010324680c2c0550445000d00030108190b0704010f9020b40c12400d40b55203c0242e00304030000c900700001d4041c0d0403101e01d6192106111600044d464070000f46000307102440e0755480780790f1036900b12103101d40c200a081c0c9080008100c0c004001c400d460860341c03d403c144809442c0030380103c6180c465038000070314040000e210108241c10004415103014465001c0320216034130200e90a581e0418035550030b900d60300411040440c40c0a507002190044400d07030440d100000070000044485c04200d548202a5028004000c41d0552600886c110401e803c0b000c4c143c072070042404103140d0712050284906204010001c525546030b41d40c86882c02c0e680000e410005070703008003003600296201d00030b803501c10b240003401c100b20030401046584c21070304014000c544071001a0b5001d00c994100030030500070309609018031070440d01c40c0e000721410703200255000640c4201d40f19140b902c0c0f2042e80182c1d544000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 212263965 1250 212262715 212262719
    0x10c09050f210708060115170f06120f0a030309120908060a1116030e101704120c0f030206010e091507080c0d060b03010509010b03040c1e1707051207 66
    0x81d1621000c2c00c1009103500c19030840069500d0915064440c0c3c00161380703202e92030002405401c1d8807035068550309130307540b8803c0401c4900d680203141001a070f070304858462070501150207031606907031044424030082c0683d91001741259840d420600070407001d4010075100d10612040140a0380b20102406c0c81c1e041801240b030400d0501c5540d15801042c0500b1a43d0300c19070103000c9030300170301590078200348011011045812840c00400071760504030030034003500c1c2060813822043d0151540029110350446403002c83d94480d25561200341d04107244609100c010980240840d044900c0014840e00a800034105540740c107484845ca44030090044000740c1000d05504d240040c48904030b90001e000d403621107000d031a0f03030b4440801c034400c40480150451501000081252125000e58102c40d822203444241e681c0e1414180784c1d91200302c0c1e0003090710310304100900c0030400c148a14442d2000b2009014100358452001040c50b040d503004111599024107001c101500c1c00090313403c03c1c0002c45016040287c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 212265215 1250 212263965 212263969
    0xa060c05060a0906060302090703150501050c0c0f04200901080f0708040b041b030302160803040e01031b030606080307050f071d0c0f030f0106020c0105030103020609040e0c060c010c09050f 83
    0x6207000e807002c94450b44605040c001d001c6903400c80ca01a5030000c10b1107443d070410306030190081020351051548006e000c2d0000603070b58022419a050800000080e044540d074030020041240c0f06c125540358402d5072420300656560703200c450301c3d002d00310410841e07945843c428005800c98a00510741003002c1d00b00010856650b51010200da04942c3c003c04001c0c0c1601c561030206941800d00c01841110002d01e100001415400070300c1f6a5103a0304a8480958140c0b1200724503280d210344e00603134a07080001801080040c0c40004560b1001014a400e0b00072140c403a0341e04400d86140c1e038411140d50348041007180c00c2c050140168120900a0001058418600b01c5244149400c0104c00c0700300b840c90300d0000700c440101004481030640c07810030413035803450310710108040c41100b8042d11005105000300584103500610440341a41d4000f0070145c1040070f6a410800079003180360071120940295444500551240360240c02c407011280008501404442c1e801070800c126903000510900710384032054510313 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 212266465 1250 212265215 212265223
    0x8150a0302040f0f020307021e0d0c080c0a0606030f0525050105091309030c0515010303140a020c030a03030b1302031006080621100507030b010e011b061107020a060c05 74
    0xa9074192808901004002c5903907000704540125482d0700e0f4000810400c81e80c0d404110f00c5039001c2c2c0b64200038910036240e17500c103a8824250403104080b42d540c0e0105804641c200000e0020040380b68119451455280d46a005030780140d80f00300e558591101c90601085010f000c41d440403d1140ea8440d400c000e01d038113070030000c0c1c0070b8400d80d414010001001c03041900e460390545078880c170441d01400400b403a0b20b801440340c00194020365441c01800204841441008041c0b41220342603900c44450049a039640c1c025580110a80410741c465024886030645040c00107210590290300c0015003031f8141e40c14400445600544404030a02c10001c1110b10000c801a041c192a020b02d090440f998449000c81c41c00c2e514480c41c0300390201202c442104c002030002c3e404d4042810407a05110396258140281c1c00c0e61440407125000c00e100344000340300307548905030350040c46000f096001d00b504400c0d1112011074118181c0c4d10602200020310205508003860030388010f0009107800c0001040320380380c036038076 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 212267715 1250 212266465 212266469
    0x30901020a03030b0315090715080907031b030b0717060604031e030c080c100c1706090703150b07020a080d0c1e02060d0c0e04150303140c0d0f08150a 66
    0xd03d5a02d01010313a40780c5042140120302c0b0440a908074907400e02440d81651041280308a429520911001940480c820748c0c22502032000342008040712411641e4891f0801c460881d81900301d041d04d44000702091048e4540750280420752140b41445540c038031104c01ea04002024140a0001000200700040282d400b00c181c411522441c01c0d80b0050324a001c0310880c3c10884003605c1d0510115a0500b400408500803c803103260f07110820004a00e040241d4603590764a4140f00862803141c0007944a0406680c0396901000c286070000d003a101c5210b80399881200b03600700d09010038010864504604161040b14064400c0d039009000d0fa034440c4000405611020300e005008003082ca2400c000c004c0c0141d40701d080035600509407030300e038030100755404018003060b84600c002078482100c202c11400e0030f106004511400400c9940c465081da201914040748204020300051400c000d0444011300500c81c611021007a44d440c01414040410000d01d4088054001e292074103110840144541c2c0e00920078003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 212268965 1250 212267715 212267717
    0x9010f0f1e0308041d01050406030803040816080a020f06061203090d0f0506010303170f01080d0e0a050307290408100b0609030d080a060b030f060d0c0b07080a0908030901020a03 78
    0xe07a0a80c0d10104180c40c10303107900003040d2003000306010446004031102085184055801e00c000c40c0c2e6070b001008191102480b0250840310304002080208a2000080c40704c45400100c44140350075982c0c441c9507a43c040d0280c1c0300140c00c00150b89550010901280d6001034084a0a14007440030130551500d82c400c040065115015a501c22410020200042c50b18681c100c81600c0381ca41e582d040140940d920425038000781000302c00050060101001410306840e111001062403200401c41920303003401c00c00c0c42507841503180d5400506a40c00b080700e18094650030101d90b800c511417100040c511a00b158030071103041d0050006001ca07141c0002c42503540c11082030042a13040c3c00342c01080151258a22441e01409540b00d60503090f500501c6403030141c0d0b100142000782c1541d0f0004001103020035680b0b51504605030f008902c41749410320442003118000c807421044250703134070102c001c6036000c02e078101c414038130110b00a041107800294141c0144101d0b0051841e110990340001e46404090000030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 212270215 1250 212268965 212268989
    0xb01030b2e1d1c0807110109050301090c05040f1503050a060507024902061803071a04060605060409140105090f040605041506080a02090903040605031305030715020909010f0f 77
    0x3503000e054091009040c3c035009181d00c0e513140954107020301c1000c480307150305012030401c0340001001d003014800c0c1c42c522074104075240c3e01681800c1c00c10002e80220a40c6491954035200c4040507100c07202c0944009601c01d10041c104182d05190003016a68020070010a540213408900040c0356018404007088c1c2d40c003040c8a000940540140301c201480d6010179108990450355001c440d900003810034012040085200100184098a035590f442010700080105a02c06042882190a461259013180c4034400c0842d0700d64807440441ca40340c02942c094002070351a6041c5545002581c42d0207400340000b07941e0440c0c2841c0070554411003090181c0000c2100341d079500010203005003c0409104142450401c0c8581f07075035026459078a061940e030584c403510000020500c0c0e000004201c504403a0b81e61903003421a611880c2800c862403602109481c2c1e80410010600060399900300030042180620006895002904c01e04c07080110581042c542c0b220503a00a000755400b282520084800300c00c218 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 212271465 1250 212270215 212270239
    0x70b0319050a09060606020a05120c0c0f0d1b090e011b0e010c02030111040f090c021c0e03030d02031e04241803051c020a0c060b01030b2e1d 62
    0x50801450702c40f0003e0710203882d0070300103e20795a0208900c510103000e40110b40c094192070070003400d28811130007204081e90100880300c0007030a141400d60500000180700c404280466124441d140c170710940b041e586011968020b0210041c6032203900b90701000070000b0041428a1602071103d0010050340405105040c148001e2aa109441680341c099003d4024032000d200941009141d8200b40155032200c45060380116038401c072441404ca07100340c59801444500866042c0b040c412aa01d01a682089114040300701591010070081406030320480700141d9034039040b849006861480b0202c052450030241c1488041503d00c1e01e0411001468074001c071081596000c047d0040405c0c180c1c0d81d8100ca8120015814140c000020301030030fa01201d10009194280361746441244603030103c10010030b5074100703048041040b9900202228506050001c0c11004050005030f0344030070700c14158403a20060301208074902c00402c103502c001c00142064050480b400003082c8403895501e801c80d008000d41448 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 212272715 1250 212271465 212271481
    0x5031e031615140a0c020f061501050d020315210a0201030b03010b03070e04050606120a0605040c091529040e060a0b0307030209010e010801050303070b060a0510020a0203070b031905 80
    0xc81003002c106202007041142c04500c0c5041d00c0f404442d80f04c0c1407440c00707518000a07800804d200c54241552805800d06e40e4510b0317031a9054480540119041000c2404860789111591006501801c54000030200600c50082000301c510785a003414078021864030b0200920a80000e140c14074a542420045a1a0540350100e801041015038450740343c03085240000710140420001406540500d00740c60159407407206000c05445000304000e000e51000180b04081003030303640002d402c10301c54003240c00010303552a04031050340d60110f01899401e40c0a81e0800440e680e0700542e038440e0000c15030400d024007880b508031b51350740564413403420b4150350b400029000d41c2d0303400014005403102c0d4003401d8aa080a1038020000c1d000404c01c1c602085000c07030103801c290302503215607048400040056142070482c2e52980704425026003110340010052401242c1c81c4d9402000311401c1100d9402804006d040d80109131804174030b0762108600f02010028070803410707040c0e1101e40c200c4218240102d21602c0da444 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 212273965 1250 212272715 212272733
    0x9060e070f0509031b0a091808090d0c0e090f0606100509060d0c0c0606060801030b04030f0c0b1e0c03070903031d0d0b15120304060309030509180105031e0316 70
    0x2202e1907240c0a200c00190003855024aa01035181742524050155034840c0d0102c0308407044a205400f0001c001c00041c1d0005407048018210b5403406800c43d5507101d107964919a01e603245d40c021182c0110040f0403c00440c0003080320b500305941403002850305007041c0d0042400360134034a1341e0b1010010002100740080d1544c0c411214011220780c020410b041403004018880e04401d88102c40c1e42d070801a001940701d10404590381640e821500000890f00d40365000d880c8640071003000c000340010480c406004c144c0c5014902d00c00c0c41c04800803026401b1000202c841d00000400301d680c0c0c2e4000b481806030060307008440a060b84e50604019500e42d14070307080191603041440c01c0e654090080100c01c0f04000d0025141809413001d0a15050220154030400003200b0400b4210310041d40b0901007004064402d0304082c500501034146140b91241d0403000c541c10391092303402c91418050300d50040055007010040340800e0a20400c01d800e0030301c910034105450b881104858140c001c800c070200d9040c084000c0c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 212275215 1250 212273965 212273977
    0x60109060e0f06070503040b0918160c1a0711010b0a1d18100b04060b0711040f0617060f0906091515030d030c0305011202031005041406011d0109060e070f05 69
    0x5000c1b242c4a603902c03014901503510441556000e18600b000c420141e002e040c1445009015400c1000050880d0700c004072240c2d42d0703010068580d40a0440e0400100b168180d15038054076441c0d8070300e0f882040c40b802d00e900395040d407080c0501a40401800308a844042c3d0040d0488100881c0040d03502d844120380c1d81c03000f9a81031240c49150185982144041c00907a024000d007500542c0c007072154554030f00101d030080c0290304010b0840d00044441440d28501a407040300c14010390304000850544808035079100b4000061086000d074000800e11a0040743d08000e43d900044c40300007480940f428211075610368002d07000c40401c144441c030204003220000703402d07406000b2020b03013180d06800726080000e0182803200e0680d80480d01d0f0600204100503c1c4501c00c158940103001005448823000056005140050068540045003a100c59030341406008050003003826014100c0c2e0080a001c3d10301034954107034071030707020f04d031510404201d0176049200e0ba80d031081c01803c011008200201b0705444ca842a0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 212276465 1250 212275215 212275223
    0xf080a021608070513050106020a062403030305010e060f1005030714120708070926070b030408040305010c080f0402040c0c05030d15090c0206040b040f060c1205060109060e0f0607 79
    0x41c4802203031042c80050200304403070086a0001121070400d912808aa00030300805006800c034420300c0c408110150000000200b4500e01003034003269034525100700701c40b00c0c0c00860010740c40c0c20041050380701c405426608003030100c0e03807030740c0858121340040d0024603101c441c03405100c0c1c08000110380301d00800801d10844080101c40da0f88000c4040490847e000803a484404038002c04046508603104000c850140c0d522854040c6102c0141c05902c006010040c4204005114880c0040b1302c0600c8040514020342c4540304981e222425890100e095500030403101007000807100c10894008401035030507070416015103000442890355101216182c0c918500a0f01071300c40050500300c08445503003ea4064040c00d5400c40c48a6200d80280c1305486020094a00603032114022602040c598480759811522413040c0702880b048a07a00c00056031403c0c00d400c00490321b16079100400c03014134003c89a03c06824a052800c040c1810405010380c0940241d0a014043e101c4203125952500404c6841c904e0f00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 212277715 1250 212276465 212276503
    0x130e0a0609060603021902120a030218060a020f07060305060a18090203060403050405010e0105071a0c1306022a031f020d06090603052e05060402040b07050109020405010807030f080a02 81
    0x60380c0c00580658080248040f50100c6141015189480403603503e80307108d030486070140b806581c1d0b0000c501070b403c00c242088030071104484054290f034030140200111104c9401030104086a0b02826040c060b490b070081050604000401c6500c0d519911843c09581c00c803507069103480c0d03c0c420f031a8018220034100a425100703220a00040c160018064400c0756401d907281c005601903a801100c0318060444011b02c00000c540d120865840f101002c142d000e00c980c00078508004400e0301648640d0700c19071085015070058144004c0c0300000200c0c07140b040c2624a940d2490807000c01c0881d6481680041046258941a0700f006c0c103403031a1340441e440b5050b1482f0a0010540742c400c01b00091081f48412070fa5072103080749603112000c10400300300c1003041000340307070301d00b044201044409001c5c0105040e912070b60030840400d403d00d403040a00100c1c0c0c0900000280d0b03501d03600c14802140c0068014002661046030f0800000356070805417402e0b50390080d006034640c0381d941401e17490240c64007106048035034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 212278965 1250 212277715 212277719
    0x3020d0c0b0d05040507080a0803241003020d060e09190c0b070c080601140303180105070b0a02030601030c0302040819020406030506090d08160801060c2f1302130e0a060906 76
    0x58003e540203602a0065a54260f40c070042580c0d50b2074a0b0000030f040c2d130780520000f48501080e2050b6521134003001e070450010312036a0001000b04414aa402011a40c00302c0e0301580c4642d035101360409040c0c034000040d11420000c8a40340d40c1c600c2442e000741900c1002d21414200004260403000034808100d0780ea03280e4401d8a0500031884d000e003c0e50300d4030f02c20600005105540210091002e51018000e146440004140c80610300000c0b50340c42d0500008100d10f0002441c4c2c948924800d040070000141c03641803104c00141510040c02e601e13801c00d80140420301c145c0d400803c0f85035202c0c44503c000002e8030101e1000c200a0000d9074400307042d80c098201084030248000c18140101901e6a035090446d5941e60711444502c001d02a40b940007807a00b00041c441d540c05090600783d214010f00b50f88500c464000107160701c100800c164510401c4001c40e04000347d007080140450b03900001c500541c00c007000407a0310100c1300003512800d45030040c0300010034816410b550010000e85065201480115 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 212280215 1250 212278965 212278987
    0xe0c030d030b0306091902060307210f0b0d081c090606030501051906140603130f03090513090503030f0705040b12010f090902010e0906040b1816020d0903020d0c0b 72
    0x4030b00200c02e14000e025604c0040c40c5950081411002240e4040240301401c0c030396002c3c8813040c0c00c01062001400100044d14254035070300005c04021504498010030030713000da4240030042c1c95007541c006001344080c1000000060717034a81901e2820b111162400c207000000103070840503011000019145600c0d1540120900806401c694803c40404018910008840c0c02040c100c1c0c1e010311a1400d134035001d2040e8502ea103082d1000b59000a80d0614943d0b441280e903d5140d400025101d081340868002c034020003543c2098541022402d41c003540c1044175540d0798440c0b540b284001070a03a00000074640c0014a40360080050b035014100e9601500c0d1141001111419101c1080c000d0405190031041e001070900100d01030b9a0005606a59400c642e4a0020074081079000242000d80d00585400f6090844d8642c1402e06d6000c1480103a0a00303c1d040c6007408910a00d08952140c00b1900f2050f0b4404006030000d00c01422243d06403507012002075241003185001100c0d40100450a400141e0074080e6 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 212281465 1250 212280215 212280221
    0xb1003050a2a0305090318040b13290315040605040305070c0806060307090e0309010c08271e010c1101020313140a080303100e04110907121a0607060e0c030d03 70
    0x607884540b0100080d44817170004503903e011782160340b802035844d001d0606882c2481d420510074440064030ba01c07809112444a04244c903000109039401c06c440c19880e600c0e00d020407004881d07180054000c0c0150859880c2503031500360000304080c9c034854079100800c0c00c0510a008886405801207201c800071034403080300e203803943d04c182da481c0d01ca4031032140c0108001501d0b00c170b42d0b4079481c1c5002c01503280c440c1680c01500c500340894010b84540005005407201b0041070f0001545200c500038980d1b031403d40e038108018800c01c015070b114558020904468840e6604003400d49100341c1c00424280c9600b03103d4004034a10310401c00e2800208120140002e81006689013805103c4e2007121010300580c1c0b02d514847d6070780411103800c1c4c00d0301c0c440038003002140700c1510055002030048400c007003880c5a00010179101c0200f03407404000140704003590741042030380d0f07c1401018145406c0980001e2507070380005229008206002e003a0390380d50240e600c06541c0410950b201c4040103415903950002d01d407800307001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 212282715 1250 212281465 212281541
    0x305030912030c0a1d0a1409010918150902030102072108100603090503070804080309010809030a021507181511030f0f070201020709060f0311040b1003050a 69
    0x15071007624920740c003035425a41600e1044440c10503490601c480000308451803035403105042e00c010950503c0442944a042c81d050107841e0b0300c00b54000141c2d1000c280071403080140d000300785103454881401c50705c001140b9944401030f01b200a1940030802da4610320018039114500a515600c00600e41e001c00c6000ca100800c54082c0c4200c040700f460b4114002d4844420449260302d107021002400e20819001c0e50201c7c0c001c50290003142d080c84000c0c2c0c0c51600343e60154000041c6a4404104105250b0340000c060b40e101c20b0400156041250f040000795580c0c0303030006840305080340380380041d0885216920402c2c0c2d60202c0e019250000c2d03920340015090030704d5904941c00040700066008000c0c5400011a0040301201e4000352919a90b40700c10fa01c41d4004441c100d0460140660014150603076014010160514403080000c451661420050100d590308642c1d00031400d0098001e415940d081e5044001101c03400c01044036554501240e004142030041030555000c9034030020480356200d248062 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 212283965 1250 212282715 212282731
    0x30b18040f03030501080d09031407030c08012a1403040f02040c0c020f0d0f15020403170a18060e120f1510050f090403051c0603061a0411180d020d030503 68
    0x44146d80f521005a181d012190900780400c80805080000070301a009261810441c1d0041e11425a2682c0d00c4941562181d80414101c0e03455540e40008201aa2111300d04040c0500b141c001380004507201802c4d480c102d09500c0410310010000405200e00d00d084500031380d0f4006d008100301c180310000500040c3c0a40e00c16400394402444035501411f01c0071070011001e410103040c90441007940e640140c203d600501c0740703402d40d409010000014014880641c0c1e80c1d41a211856100c0200d18401845110040481c02d19100714040c2040280e0300450039480055060301c200109a090321100f40c68450005040080c40c070541044481002c0c0100501c0c1c0102c0f4100002d04078555100d00300590300191086c6135038060185404034001a010303d0003055146100c002c14001c141c42581d1000c11110558000d50f0066164001c00c1500d000c0450030802007141160304000c0c1140900c1c0051160140c421100d504800100307101485540c0e11409428260b4020800c254284a43c5002003042c0c00642d1072403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 212285215 1250 212283965 212283971
    0x1b0112020c060f06011107030b04050c09090715030204030b060d050a15020417011116050a2111062202010c17040e09010507020d08061c0605150306100501030b18040f0303 75
    0x1004d035031207071580448400500c1c000b81501400e58441c2c1002003405801264644141e5002c40440d40742c003040f45104200842c040c0c08030342c3ca003160344000880d5460580081610400041c030000e64078481c020f8200d10b041c1c43c6128075815510301903181805c0741d10007800c003a085031480102e20f6001d800400584218000076001080c03072600d002e0903603480e40d40013064400180031040c02c4060549501000b80d010b1030031200a90f4458881c0115035449080c500c0d1a4040305035506c0440c0e801c48e010a440c00032890050039281781550ba045803840440c0030021106882580c48030941e07100b104d80d00345054200412481005540a40c4e04a030f5115114005402a2020018400700320601c182c9200f1400703500a002c0f140c1b800b80d011101c4030f8000b00a280c1c024480e0449034500c005140051080b6481b82800017008c6c2000d1160b544104c081118951003540500e08001c030f1503ca09200c4801c0b83c500782404104d41e82020001100e140c823030a9680042000312040009101d51081103500d80c41c020b880c10 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 212286465 1250 212285215 212285221
    0xc01110309280b04080f0d050601030c08060a0303051e0d05100b0703020303061302190e010e031b0621040f03080a06030b060d1509080414060702031b0112020c060f 72
    0x40041c2031041184580c0640058011408103910b9075629500901c40e2a0b01c41c0b404a000c002d413882600440d5452000c2548e4104100c0702d0358042c0300c0d8555014060a100086240120004200c04880e010044c200603010a8815549000c800c00c210032850b003400c00ca440780c144a04580007060222604041d00303000010008a41410000300c1c0d00c1c5a4151340035618503600c5c0b60900c0b04100b64092112403882d0b0800008026489001d00301c2c540700724954643c41c3c0d5110301d0000400400004003003e00c00e4001042c0b507000400ca421400b07a9510003906c041341c540da00d0b040c2002500000030100c041c421040750401c4100801d041c02903001174800d0b2544d19460f2181c074034a070f00b2269240070080444600c42d011504a20740381c045561458450000100d1a000710001c02c019580014012644444041418802400302208880c0302c550250b40060420340c80e500025607640280d140c074072512000b0203044400d644a1180b0041c2902c0c420400c4d503403206001d0302180d07100b004440c0540380d02060004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 212287715 1250 212286465 212286493
    0x4020a0804171c0504051e010b0109050a050a120f0c08100c080c070206090307050a060e04140702060c071a010b070303150f090e10110304050f15011401050c01110309 73
    0x341c0703542041d10310908407507445010300f5000504000d001510340380f003080d41185021007611800740d10014003500105600030010000362565400e90400344c0b2403d81410280415115035600c402281d003100d00c501e060705003178100107800c94401c0c1000b034000e841031840410031580000b5200c84007814100304100c0c90043d100202ea0070031040d141000710040030450403001d8074201c0040d0054090040983d14840e96440000b1164181c1c2c0d400040070078090144992031b46494071502a40c0200f40d100b9070020b2520003c029242c0310f00801c0c07141c00c3c0d07034080391403000e2040e80c28906c40c8003449448020455611001040880c2d000b04908078002230800c20150f80102c24441c8540031580202840c00072241054140e4019101360343c0c0614a900c00d002490001d0101741c080d41c4500d15141003000e41d02e04250400354185041800c1482d090343c0b01c1c0e0142120155038600c407a0450703803002d5900c5204101c0300d004856a1042415a070465030801d04a51981d50884000b9402640e00c40c0c00c4480c0b200c0c4d6516 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 212288965 1250 212287715 212287717
    0x30c1c0201060503120f0d06090510081b040e031903020d0b040e150a0b0316050307050a0f0e0a020405090f06031c09140a050303040f030308070503060607020f0f04020a080417 77
    0x903c1d90990441490b103a4807004070705c080d040c1155072241c03d9040820861015044500c41d900c8201c00d50f4455040c003241d0f07040c030b100c01c03c054101c00003d05601d400d04c0c4c2c84070303020300e02c2c4408090040383d46158400504e84248251244c12140341c00e503207081e400804004020350890900c8011151500d440400f06203494441c5050500700000548142485005101c070500402810286050341700c540c00c0565640c18070040d158070300d5200803107000d2800c1809040c508042d43d0881401000f00103070031b00c62101860750050446110441c05d0344e580d80c9152044d00030740150780c0455002400c1c44180030703043c10045081071048074251b08072400c032104101001e4141142101690208403945d40a01480c07000d100f0407400c090028041c680401e035240046403640e030185e4008481150041414410550f0100384550040c40306c2c50514114103044002650700d202d4400028400d41d950711200c41a500c030280e0711510150001d0045445d130380d502e03001400030a81200c1c103d801c6096407150140c8054404 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 212290215 1250 212288965 212288969
    0x30c031e070e09040204020903070e010e0a0e0304090b1c03030203061905010e0d0609020303030f1005031609021305190513020c0d0f050706060b09010f140d020f0903030c1c020106 79
    0x6510500e08540c42c00510040700d4001d4016600f05030204050965510200250801440040e80207041c40d890030000c50109a00648540400d6042004580d020704000058400b5034998540000e2501c02c03c00005e8040018a408121030550407520f139020301d5059406544074402c142c1d0b044c0c80d591244c0350000c6507041e16020b0309010840c2e209010400d41040780c0a4100a841604000341161160300001e2454000f21150b01701c0e0307181241004440b000540000c1d006040a80080000500d4420520201c0340700e1300138840900c2e130109949004540c1441d800f0010100a0030700c41070445040d48880c80707450389004a0f0300480c0d0014a44d188171005200b100c80303402e6030724080c14042400e018202e03640c40d101043c4100f004000c0c803003200031503824032803034004020315901981c5e03405002c0300150140714400350b828144550081d030b80f036079880803500b220307041e11000c0700041e48d0b0407810802c000b41e806180380040d014800890450765040c80001c00c80c5070300d2403500d0495400c1c1c5c5032980072801d1f107603a8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 212291465 1250 212290215 212290217
    0x80d080402190302060f0d11040b0712020703020f040e160602010b03010e0c0a09020c03041d1816031e050a08040801110301080706030207170a0e100315140103020f030c031e07 77
    0x20080c40710a496107074081c007d01e8540200115a80180741009161600107411880c840400040d0000401001616244070200d0701c0c00a001c0c01451900081c042c00026154140216103d50040210f00c40038000000142007101d44c81c2039440c3c90b0907000340201503865545009602c0c011103048a8580003070914044400241502402414031600c91302940007940c002503107100038040868141c201d44500702004003100c1c200300d0b1030f140000b507aa0700340c803d0840441c03241d04003030002d00b921020b400d8010280c0b84c225002e03040c900181031424510795900301010740785020f540300040030492008001d208031a4640c0090003032030703030143c042d490074402031140030301640c07100c441001814040d07005030040c80d02a886800c444884014108419401038045400069960714154001e140454292055083c189400c01103024400030a4031b081c6803500400740e000c1c4e408002100280e2094040380c11480384441e5117512800c02014034070141c1c005680d41e4150f01c4540203640764420340010320a10a03401c07 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 212292715 1250 212291465 212291467
    0x90c09011406030406090f08030a09021f0503150a05060c1b090105100315030206030a0b15030c09010c05030d0207030216150c0308040c1512110c060c0c07080d08040219030206 77
    0x180e80d841200030f20303503001b045850309001100c03203021a1104c0051440341602c3c54012403405500d2040120165045c401c0d551807007040c031142040c490b44601925440000300c1410f03644150f4000c00503000c014254046540618002114068200081005074402100d0308421056200301d100f000000b4009014240d00101501070304500e2500c2038000040d4814031011140103da10b0303801264060f0300858880c100203032a000d04107428200308000c200080e07800401c2d80d055080c07110066119101e2803601c0e604003c62001d0714428018103100b16501c10400001c111758231709980c0360103501c8200807142d0898492280000181e05445040c0e04480c18400c0d42d1160b4001d40203030380560307441c40b014000b590000105000492180f4000c62003044044c0c19840e840d00e40d120400c401411380d1502c04000e94881c1c400e1140006092000a0301030700031440500191f04c03642030405440c509002c40d030042d1506c0c401d400038481c500d9004203903140518002e40e03420b03251045882c02c000055000b44002504008 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 212293965 1250 212292715 212292721
    0x5130b0c030703020408071202030d09030209060f030c04020307030501030210050403020d14030903120904150b04030b13050601090504030807030905120a180f0609080714130e0105090c0901140603 86
    0x4000d80c015079000c00b2a05006040c07a84602c000e9180c01296000302d07824920703402e0301500b50301e010404618030311032915041042905507408036404510191410f4040e10324080e0541c41ca5505000c2800d01da007010304219140c2c6020180140940b0003840186d00803a2445c0b00c2c10801441481203406a80e00903003c1c1c15000669620060710410000b05020305000900100d4541d0754188030948459000280c000d8448484404020484100c00084400300290300c00c10004480700c0415541200c0d000b071007102c4969501800c00800c413518200003400ca0140d9000419042c1c2158051400365000703a44501c4181d031480004d40440d0207100c4040d00503445040f149020300d04200007424240d900f460305148801e6543e1405002c00c0403034110281000300107030b082c080c80b03174486140707002003a11a000313000162401584d05a01000581e000c0c0c0100ca51040807000341307110741c100c0441314440e20000c000b285801a44a0707210222151181d106510300000011203800040195820305801081e46285031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 212295215 1250 212293965 212293981
    0xe0f0609040606031a09010f090c050f03070e010b0a02011b080f0601050903030406030605032103130c1502031b2103040f1e03031b080406020c010609050a0b0405130b 73
    0x8001d0003101c0842d2101c8000c00003841003641c99204130388800c1000d1140c18a02c00d070501f502c0300d0401c0342d4541e07031510054101207050070120b50100c800c1601d428019074480c4000c00e09180c8070350003040c403130100840000344840d42c2c80c2c000c3c4054142c56000700212100780d100ea00480b1000144000014000c00202e51400f5010555a030031650506200d85001120004682980c005501050200b6a0f64800b0800c0382814401018186450074a512a1112002c81842c5500002e0003462111008080c03040410240e00c0f4100c02034000794400310b4490400c0c801c001d59070341c004070040b071020b0500c01c07100d0450200022000e01d80e0350481c045981c0d001000210b09a00e80000f00f040e20403818602d80328001c00d12000d10344a40d044440c0b05c05003451480c0c01d000e01500d42c20500400d18a00d942d110f07a200381e5001264641103503001c1c1c0007503030750441d2008207405001f080d040784800914100c10311034000801d1b4091486180107031824001503407101110251404062009840001032500040041c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 212296465 1250 212295215 212295229
    0x5180303071110031409070503191a07030e070e01031209050a21080d05040507150504060c06020d0f06061211030610091710110319020a03020c0303130c0e0f06 70
    0x400d955103000035240340030181c0040c20401c1503130030300100c7c1c10090060107641024024003c540304040d01101b040d40840d6100f04001410200c241c4c0314400704400702c1c0b40726100750004001d910b0000112125182c031a1640780c4494421b00c411111983c0824140b50410302031000d0104407500140403019003858205419800b601d00380224404501a6001034001340b0b818000d40f481244125001a0b45e103082c2c5010361415405070010210a10300e140104003131a07010003250203a48481c03038100d200180714901078010b40036560138100110b08021200581031003a602c00c2d022522142da0f0450050001000a003c58035201c0c0c464a00103420000680c10703080034103407011a00424a80101c00540d101c040e0008141d42101041c8250021040030401403210f0007030121240325041c109145041402e40ea07040120065070305100c0300e40208004080030b0085c0d0548111100c5081660364078600007a1009100700120400c5400d90714485c80850400c6444440600c10004003c0e881031940b2000108410 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 212297715 1250 212296465 212296489
    0x1c0902220906050907030308010503030c0c012105090d02160303020c09060607080703050d0b1f08040305040b041403010c02010603051b040609020a050c010f18080706020d0606051803030711 83
    0x512070300c0d1203840d0001182480341e28452034802015000840c11468002c00004040e07000c20301ca07500602203e0389845000c6240a00b00009003403800b021054401c29440d800d401030741d03400c5511301c1c2104210a00102080c5184124082d0b403d41c0e601e4050700c02c95100d4030280d40000ba005030f105800020160400c500f003280c005200070a21801c02d0115601e41c07030b013548007640840c0003820100700c00303000c500240290a64944121420701c00c01c005016010711100440c00e258040207800700119060500400440f00984a0026840d40c0d40b600d680460b10195858811103000390b10304002d0a030228410b1050304141c0343d0090190106801038a045003007a105c25520035801176480703d00040a00f000c0c8002c00e01c101507910f4917511040307a031814900311841004030f4802d407402d00f10200044664610030300c0001d80d014480b991900800c0c28100c3c0240200840e070011a844c0400c04508150004082c20800c0e100500207102410240706160f2a03008a107001020703040790f0891fa4156140640890702 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 212298965 1250 212297715 212297779
    0x2071406130314060a0b060a032301060c1a010803190516061d060402090c250b0105150f0a0509060c2b0903120503041b08031c0902 58
    0x10400854005460714402594802c42d01540d4002c0e00800c402800d100d441c0d8484000b81042281100c0c110216107280b041c12901002c26a0b661009101d003203030480710703000b0700b0404101e000035983c41d04d80240c60103100358002c1c3c0312031050709400d1040400d5200c086040c1c54603c400396081c0071103089e5018040c04040214001d100d001c1c014465201106503816101a0003203101003904111110710901c511820001183e81d6003109081002507200e03601001c0e04501c495000381e0303644440c4040700c000c20380d1818440240030107000031081807050900245060361004c8640300d03085400050034a0441c0300380003c1030a4480103001c441209030044000d0240404080c200038540041581400e05040c04440081c3d14080b101114100111206500c400c61100c2030814020719400d64a54801440394840d14204102c0d0000024040000c019868220841e44200d040e04103512484880c1d12500b2400c158240d1010074076408055103a1401190a0a84c02405525802001801e801514000881d810b1303 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 212300215 1250 212298965 212298967
    0x30a1112030d0c030b0f01020d120f060b0406080903070b0705070f08031f0501020705010516050c06030702061501090e0403080901020408030f070c0501080615070510110d1b02071406 80
    0x251241001d01c000c14200c10003a41c0083c020100480c00760446075401c0c10103000301c030802071451107a40c001a020000d80c810742005220b04111390f054038040c10103020104005814000d00051b50408400504240ea999456400c1140e548503890307035a0707005602002d090785901d8400714010b203005100a000d40e038000c26502840042c5a103402c0541c3d80700b0768500c16004d880b180b14000e40452050f0031805080f0134806810358628140008065001e20202c0281c3c08250051201c1045420030241d4220740b00982069140d2402c0400a500d90000312030b088448031288566641079031048a50f0002c0e43c0720300003030380d04540361510b0807241d0280082242c1880d42d4204130200380701c0820005002035600c40407060f56140900e28052006052503070020b0b05000c3d00f48140100c0d0303600c2c0c0703801c0e803180485592169222030b01820030914000c055200001c402e850440300b4200320180d60014403480801c25010f1041042d80082034258100c0500e40d04010380161209112054806541c2d0312040002400f403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 212301465 1250 212300215 212300239
    0x80f070e060706051302090601050a050406030e0a210801050a05210a050f0304080f01111c06091103091504230106050a06030c0f0201110403020d05150a0209130b030a11 74
    0x4030101d644c240e90304c0d41008500304408045203455410164001c42c20320308103007030803107138480540745005034050a0b0a040c2c4030160000f0901080201400c52600030180c8070070703030050142400c50900c0c1d001492001807030a40001c9a14100701035500300310f50000d40f451911442801100b2055540d4056110180c040e16880101103130301000f10000e601c1a00001e9a922454207a100d817500c1c0f048500690140d0600703202405c440310401c1982d200781d0f0807030b02241011004800c80002031039650031000b105031400711220f600400990256120349404070880c0c8140014445612002c0300448000303144c80d000c50000b00c00c1c0c0c3d49042410441c2c8000000204005440c4c03000908022040c0c1c00500000740c1c1c0c1c03070101e01c0c050f500a48100c1c80655500003040540d6542850260070301c110301010307008581c0c0340a07003410081c0c10000340c410f008451140e07688038200040d00710003035480300c0c0c10365202d10781401e083c1c0c00904140c1300c1d002c0d80c0b42c4020000c004043c000d40e5180c90085000640e582d000c070f203580c00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 212302715 1250 212301465 212301473
    0x90d0204090302030a2a12020f030a020d030b0102150703020f13150314010f12080405040213060207050303041d072102030601020105010b030720010e0a0602090a06080f070e0607 78
    0x106151030740b20340c000e96155194200000c040c45d078081c418034a00c140e602202c60900c44a007080e940740c9900320412100d10034200f8070603841c141106040b5115423000266815220364007023003a5100d542c107950107201c1080c149004903500c0038151541005c4031503a03008a6400c60103980100b4500c20709420320343c180620080c40d00000d03d1103512170710080c080c0c3e08280d0280c5034588110b540c6103900b40c840a0541d410b0541c840d01106460244c1d99000011250389400c3c40700352400e840050900800566035886041250640b0000714401c5001500c05c00c034000c1002d2a0100560381540c100c07940003120360010028651407000007a02a2003030049050580ca0801e49005000e4240600c2c28005079503400d101d0002030031140b0580c4103051800d404e2050140d429440142174000d42003004d40041001060282c040c010003a02c0c51040c41c52103940b2040f02000825000b402c00f02d01c0444442641e0746da150800c0e034200c41c00325040c40000e01c9600004911038042c12070701f1003240d4094845418038031180d407 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 212303965 1250 212302715 212302721
    0x60103060512010207110604030f08030a060e010b09040e0607050a1206121b05010e06030f0402012a110d02010905060a020309040221060d02090a0b06220e07030e060408090d0204 78
    0x2c4480c00b140d40005064043c0821900300c000c41240940307403a403500389140c80c0c0c10a40c0e4140340c401001144000040307910023500e034010714003410b80c00141e40c006582d2949658099400302c07107a60b010b41d0038641512107880780410740d10302c1031340b00c0d85a0501e0301e41c80300300480d11241624131001405645000106843c01030024000c00140304040115181d107103070b00702d20b00c0004941c0c840c4c0e0410010418424443d2680001d6942044048a0030099a1624801070b9500c00c1c6101c0302000d1040c0d00c183e6401c0800103442450900d074040e0480c1c0c2503440b500014002d20f07075204207001c0e0104000e818100b0031810320f20010080d000701841924205041e0340002000c2e83c0c05070a03d18940038040711161040c0f00c014810b260805801c0f121041402c84990100300001c10042c60b105806541e10071544035038a1b00340c1103c48101c09050500c0d125015840c840541481600604110040c490300007113a8502a124000c58004208005c1c0155902c1d030342c0d1030000d58003805056800c440e1144250005891b540 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 212305215 1250 212303965 212303989
    0xe030a0308070c060f020f1c11040306110714060604140c0301030308041703090c0103061d0c03091014090c09011d0a0609021c0b010c080403020f0f03060a0b01020d03020c150601030605 81
    0x12540d40c1c2c3d2301403a02060070065803e04003140d94629020010407100d00280071070302281d90000b00400d407102c400201d84003d006065024003401030500d16061698008034400b0300c50002141d003003120b00d0b06005c00942c03a034411210859140d50420052003c640a501c103158010711071600d10608001c940703200e14285c5c03c00d40340c60046078004c8100807080d40c1c140c016079001e4105400f991003c03000004c41440d00b40d00107410000440c1d000404a84191030910569002e4560b000d0140410500d40d0002c0702442801c6449a17480e00a130112581203261100031141229107082c0084036080101d10501030700360000e0801ca0b038066580000089801c4e442c0080c1900140d000c0018140b0007402d4581c10580302a421001d04100c8880e45100005000c81d0030750307081d00d805440b114042e0340d18030702040c0d10f4034010019950600c240000c10003071100c25008624031480030b83c01c3d9001716451150603026401491120500c3c0c0e04882d51454070003080c400c0c080e80c000014900400e10f140d40704041a6001214 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 212306465 1250 212305215 212305237
    0xe0a0809030615060304032a08090901090c020a080c07050a0e19110f0c150408070c05010e0a06080603070f060332040b04111e010e030a0308070c060f02 67
    0x4560000d180c41c0500070640d000e81c81d00c1040c012000d2031000209584401030008081c000c0305001000c041d1315201ca0b0030050f1144810203184150f071401c014419410170700b130481c1700c0d80210002003061080c6000e055009200e940082c0580a070fa40d0391000a5003049880244510405000050f680d6a2a0a05001340030311900d614490030800124030706451445a10640182081a051640e02559040359811920446450f494268880b1031038180944e11060b01c03050701c4100f0501c07041c026101c1c001c0500622071044181000d07583c10055410032010822240d22505406041100380d02880c8021b510500007029644001c4c2c0300e80890303405d00f0494214a0000390b8a0f40a860009400395000841100740f0000071400381f210016001c5000c0c005000405681c1c1c040d02080411034420300d501e0743c407070008120218591882e40c0d0750106040c5c04d444240020100c243c40050342c100441c658007601c0d050368440e880c590b200704094401842010040303039a1b40e614140e042d113000c42840a45202c01023 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 212307715 1250 212306465 212306467
    0x250b0601030e0106060212130e2811030105090612011401090b06040503030409020a09080a03020c01090e0f040204021e070f1202072102150307020105010e01090c120b040e0a08 77
    0x28000181241c028100707040c0300da071601105001554002030150000c030316050046a8804079410100d0401100d17500040c0d80e504500240550603421001203555080c0d025514207498506400000030350b040c03000d071098002c0d000c00040c8000c2c10320824a40c1d00c980043c0c03000d03440e10301648802d400c5038581294403844200c1d00005002000c03441c040c02d80c070326608590313070303402e150030040000e40300d1207544200c503d09940003508440c818098071a550040440c7c4c41a64410169030401035141c400c0c0c14201070000d00d1290010882c001050340c1c1d01e01402c1001a0022a0b03607071030742400001d51008d494146184901c11114a41c040300000600250748901c01100303448001d0300d42049042d0440c0310003400c0d50030074031082c00502c601208907104c00602459905444c5018000308000d030b040c61a0300324021100004000d00150150070460485100b100424030683e070752240002116854038000e40000d02250010458221070b400c480d14465005000091210209070210703c2d007101c003001103450f000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 212308965 1250 212307715 212307721
    0xf1718151c06031407050f1207050a0b0a200c010309020319060605030d0c120c1a0a02090910060c0b0a11131d010303080601051c290f0105070206250b 66
    0x4c04c40c1d000c003095840c000061a90506000c000b81c1241d100300003071400380d140c00340f2990602e40104203410023008098400c00d4000c2d250400c0d01d540d0b500261a001c0400c591502c0f10404140c40d522400c00104440c0140036581401c0340110041c106083c4140c1c5d041c42100108112822104129480d55104580000e0700520b41010b250410510b00303848014040045180d10205150a034481414a4a45810f042e5000c1038038220100c2c8118200c11410202d407401000804040c55009080000c001c0f10150340f140d4a0307900e1010080c21a02843d000900c491303401000107640d0003081500148c0794803010030540c03000e13031410009401c81015104e50b840f002208106040b204011002c880641141020742c9604540300a4000e040180a040c1006800104551040c45008028001d80d60542051240e19038001c0c01401c15070302118800e40040031164500710b245001004007a400301d068565500f00905602000303002d4002044d00e40c0c0441c154001ea107010701c201b60462061074401c85107a98682 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 212310215 1250 212308965 212308973
    0x30c0f12040303050313060906020708030403230a0f0509150a18050a030b04061e050601020c01020a11040203060a030b040807060f0c090509070e09040f1718151c0603 73
    0x200304200e035442038030400003403022070b5200003120b0f0f01801080d07012502100701d19100e4024403412034043e003003500c0811309400704080f1000850042e4082e0340c1d80f410312103000e00307500100d0301d40c1c610038010b07030004203c09a145030260004214445940c14214102001d000118035419000410842e10040001c0d40d07401c03864008030000d03058484140e1200c02641850081038050b01207000181000d40c04000042c1045150b400801c0e50303503650940342d0341c80c40790100a10082c01050f1045070150040046a10043d4070010f00f8005072a00048402085840c00c0305000007036201070902c0c1d8000c035555001001051a5886950203280b113402003595494040c14000110340048400c04030017030406203405d81040d8011240703810754404442821207921070041c2511641c0074001d005811900c484108401e2150000c80c540580d4001c41d2041400e800d0601113144603c40c0c60115081616414440c690508003c2d4042001007951441c407880c01c0c038030850000e02800304102c03d958164407100e041c4200 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 212311465 1250 212310215 212310223
    0x110a2306010b0f070303051909140106060c050601140307050d051005060a08060f06010e130204031104050906130f0602030c0d0b0f030a02010c0c1a0315090f0720030c0f 74
    0x6142039803a0382c3c00c00440d0300c0c003240c0901c00e9980103410507481c1d0000ca49610740c5203005148144a40380100545601464100c103206000d0159540a52070048002403c0b800341c403101114540c040e000c1c0c8220303170804412075000c00c51883c3d4640c0512a110303000c40c0e80d0301c0f07078114820031900900051084590302c811003030640e88000c2c115401801e85130f81c1048680c000007242d0341c10081c1c0890f0303541540d841c04012100c2035001c8041c190300c01903000c4121414910f95004109481c0103803080c00c46c2a940d003040c030040d6941503e901006501c4800090f05010300c0117020910a41b0a15241e02605120745a84c0240d80083e03802512102c000141c004040307d052241c03803148402590755109140f2800c00080e150103819002a06000440100804000c8000d501a02804144840094810034130711810307019041141e010300001d0a8500028080c50990001c5101d07840106618110f5515500100da0030006004100001040d07041c0d62141c19400340050075011110100800d1007024885c10342d4a0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 212312715 1250 212311465 212311469
    0xd050c1002070f15120c121b26060108070201150303081504051501031d0f010605090f0c03010504020705101b0f050c0705120a0b0f01050a0509090607110a230601 71
    0x40030410324000d10030540143c400607454106405c009000083c040081d40e94034038010881490b1440e10300031107001e11181100d0340c07800a9650b18042040000e81e549002c00c0c40e64405d0628030041100050b111390722594140e42d101c03400c0c0c4008182511001c154900d40500c038bc0040300071130200010002c0050101d45910400c500488040c4184c1c00c1c03000e046125600d000c1c4403a0b0416071646030518500704414040781944000900704d50250a5040445000305218014180700d50b4010000c90420280705c0d50807070141c2c5840381401e14503442c00042000170743c0050800ca8850041c40c44c4812039002a00c2128110f914a520160700c240761848001d08100760724003010705200043c82695003154001801074161001964410900e002c003c0d007413440c0010b200002026040f44404000000807030102441c100c520907903070f26071580d40b100100006020101c0b0042031940c01a00002e043c10310501c115130302415844181d0347d24032856100d10030345040f20b2005007180c041d50030f0600142c0b4010480702c0c0c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 212313965 1250 212312715 212312729
    0xa090f081f021201140f0306180d0504060e1309020d0c030201021917030603010e1903030b01050306030303070e041b02011b020d0c0b090304150c060b010203180d050c1002070f 77
    0x450f0400e9900c10341007140042c000c0700c40300e8854030502400d6441e0b0b042241040103006088500f0391a10041d0380010986000400c40c41c1d004811304401054094029901511180c0c0c0322000c030b0b040c8400600130307a80031120410b01e10a07184d9500e0005a2248200105024081c91a04000034150300019280211540240e01c101d88514400c0008c075010b40c100e80c509440c0a4184d07a5039071110340000e409001c0031401c4046a00501a100c0d034a02054194030a070148692024010b080c0040010b44141c001120410781540007000000c00c0c07148036145194000c180100700140c3c6001c042600801c0c28000303100100940c0d9101c040c04000301ca100c01b0450390141c5c0b4801400004494400100051895080100007149a0021600041041c400eaa0141810a40c0300c008405c00000040c004011850f040e00d54500d00ad94680540d4404022202003580d400300c9155151035039818401420740307a000941c0d00d4000c0221000c0107030303980d001041d25414164001d041d043c1c144510200c2c80ca4003640040 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 212315215 1250 212313965 212313967
    0x209100f0b0904020d0c090806010e070f030c091a0a1803030f0f0c023105060906060904020c06100314030a020d032703110706080405030f0a090f081f02 67
    0x1021162401000007580c2603a032403940c845106101042c040d000b8512034400aa040808404000d51b0007285c1c030003161040e104440e40e59a881b024201ca03100d00781c81c4200020218140021298001e42064030048424504254125a42e0b1000d10000c20b40341441040a42d00094145039a85e1107000800c6009138410b02e0003030540365980c00360442d04903c1d0742c00e0512501039501140240a217406041b5250003604140040c151034428810072044901aa6440c6840c41d540c09007aa0451245610404000e0580f4040e91030701c07800c20910f50031600c5c12a5003e5002c00101c20f0460080c0200d07070040040c074040c0c1c0c0089045141c410202201e05088040603071090000d6034031564001800c01007480c1c40d08002403030003804400c4c5504040c8078103c0c5803500a0101191040582c0b00140303a03c03100c0540d041c0ea1010380c603001d00701c03081740d81a0340290640e0300a1040e1a039041064000745100c014604051800b0f682d034030b286103d0f600c451ba021103929041008518a504403600900f0a81c0e48100021 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 212316465 1250 212315215 212315219
    0x12090b070f092d0815010905070507030207061211160201020c0607080322140f0607020703050c040c1b030530040f020f0402160c0501050906040303050a0c06090f020910 74
    0x3240950041e40030560424903070403ca00200000e801103c0040d10701d5034142d070b44003039070000d51301c00c40b1000b845141c500d076151000180301e03e803280c0700780c6442c030b503160b8050446140b901204079102c2240e4098040c007680e070340b0866500c2c07044100003007040c9100b5112000e1400010f0001904120a4484603401120100710303110020340c40004882c0c0c00b4902c48880da40c19134140701500001150008014800e4400324001490103400141e840030394075845003100e015580d586400c0303843e885039101c010040d071b01800c40072032a86004d4010902d191076626000c1288190a1942c00182c40b000c201070313020403400525071044200719078003c003403500b150344404410384000f603d0583c10390300103202400c0e050075005c04104540c0c034174070803020307c5500920035511050440c480014034409600120341c2200340e00c0001403154061002d40b050004018200b504251460302d050700d055124070442c00421000c40310400015046201e01a459070054226400c002598814803032181e40192940030451600d40b41 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 212317715 1250 212316465 212316479
    0x403050a030504080418090b01090605010c031d030601060903050706030203070f0c020f130b09010503060f0c070f02151206150a0e010513081c030c020a030c0312090b070f09 76
    0xc64884046500d00001d45665a082c00c1c07030700780a6074000d103065501d50400c1c03088140d0035030840d01c0c00345c0c02011041c0d42d590340c0310a0340003114410b1090314007048900c40d40b4001710b4041e10a1083c80395605022184000302d0900180c10402e00341c0010340440ca01c80c400f0300034403504000304806440303a070804500d942403821001d0400c440e603456810800c01c2400315a021502e031070b42a61710320000684401c1c94900304600d0b5202811513400c03540e000701004800003400b80f900240300b034010a07400b020022141c45040b401ca1103a441504141c40e10010300301d0000058840140d515507040540d0041d6440c0c20480043d040116405407141d4454210481c17000d800700207040444000601d41c0c149403400c0c02e065401aa02c3d03010f101d580b002e400180083c00a021400413608049100c3e6510307540d1060403401c003090f41281c80110323500006034480c4c020100007901070440d9046160003400e28140c803c4090302c205041c5d59141404a0308024100148150759401403281600741e01c0ca4101040020300f0108 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 212318965 1250 212317715 212317717
    0x60f2402150609130507090c020d0201051308090a080303040503070c0909030906050a140310060206071b0f03030902030319030614010203221206020c07050d0b070818071715040305 79
    0x302d520a0070200c0105405400c1c041d035504640d544002a01d841950b00c18070784004110384454000035008601d1042c10781803062062905c00c16a121380e011056580ea202c510443d00300e00301e0340e904101003a1b4042609403081020754800d034442c034005d50781d8200510b025a8684440e50059414a080504900000f604000036170199819864500c1c0c0324403032140221540980090300a5890f02c001042c4450103181c00721100a58409400320741c60750b1600e000845203100103100c0f8859880c240080d520000e03040c03d0382c03185070038024600444c001d5995000282158046003000088c0246406144042c0d40c043c00f500e401005034000122900d540e000001c0c0d100d12982c03840d4203000e05511826003203125114944070240c4000e0f410300103042c0309807030600002d42c80707610420ba0390710900d07400041500c3d080b902800314a0303000c0003060160312860810b540000000d0f10840b080b00f40b98003c0041d00004020b020020300505e13011081440100140b5800e020f0038003480100039022908000101e90440 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 212320215 1250 212318965 212318971
    0x702030901140405040c1716050406030b030115090e060f011202040e1e0d020c040c0903030503040f02040f0609110703051b0715111b0310020d060f240215 68
    0x2c01c048400c0c203002c003004032141c401e0381c0040d07a20134a8000001d072010303400100402051094082c49043c1d4590a0144405c5080e44d0744035000181c5c100014850140b04c3e0b080621070300000344c000320b0100c2d000e92800d11200c040740c00003010740c0c0d5070b998003241d8034008006503500140034031803224155040401001c08820b529901070302461302c0303075242c8005c407a0420100c45441c1c80303070091140317544182d10025203801c21101e0450051040310200002031404d445142003000c016191100424030350754050b51143c00041003621241c103800362886c05a1158040c08190707a03003c960005c0c405040904204c11110189821051241c00f40181400203400c90b040721071890702c598000c0310102038070b0341e5075150066940110322102e249804002c0300a420142e0402c9100350103007641c0c00306041402100380c00300400c43c0a98503900901582840102a40c0140348901b40d0000c081000345e00c91201020030107440d4030046070a0000343e0495440c03241440c00340d00404040c4051b000141e8000340d815241440a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 212321465 1250 212320215 212320217
    0xf0406050a170f070312110708030d1d07080313080303011818080c03030f0601020307020a030308092a04050615190c0b0403020a0b010f0812070f0807060f11030702030901 75
    0x303019444202c4410802522415041801c90380f030592a854440102d8070000882c10106e070920180540c1c90402048100594030040c0c0254185a0b1140c82c42016104c02c1040e0740720304482c29250323203c2034424080c1e0009840c00c80c0c000c603900d003812a082174031240190b010142c15000fe0006200e10000d0f1003200c3d1151050002c0810600c0b49401346007081c0b5149400100802000140c0100307501c2c02102441c4601130151400d8030701e540300310041e600c0e84500c220003944810301700c0d4140300190203070070030641140000c411180804401d040440101c1400034884444100c0f60440e803030385160501601e81e20071000e84e8402005040c42c2d100000310b00410355046000507903091781414080c4102c01660003190040802022810706050103034585000b1102074840d12604000070681210359070490040743c0019004201c0c80c20180d910380c2a5422a00c4100e40b10040c1114160100704000050b080080c0541d00000703c0f206038111200c21035085003502c80c0f01030424020806901e07004000d84450000c2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 212322715 1250 212321465 212321489
    0x705040f120203030910090f0f08060a0e011107030801080706022a06090a0e0402040507140702040e0a0501090b0106080a0b28030c060203070201030b192601020d0203060f0406050a 79
    0x3440024194040c3c4005ca0341c0110040b4010100d03550b000100c0d40c00c40d01c01001c48032405803282800c2160800c54003d0540075408100407941078000e0f47c1c003611000c45407100002c0e14580503070392980a40d10040b0260300140402006000d01081400301000412981c001030040b142901c000440580100c075007049024070200ca0307031185072a80b904a0f01144001040150b940d45c5620500008800941d07050303004615000006944030301400402040c801110307400c40c182100c0c4c1c2d0030000501514444000da0b40039000070071000410074040c3c0030700e0522440c584c44480d810032400405500c0c0050030100068240141a451603c41007441d10b44892603002d14031860090f0380400a04d9001a400200682910346c40012802d03804409081128400d903414418940100e04025040344582030f003008180b008401000618160701c007202414061103480446d40d45a400a14226007003140710ba03000703d8002041007228a8120403400d00c508044600b000b0769400c180119401422a02803110391000e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 212323965 1250 212322715 212322749
    0x2708071406010303030e060601020a0b13170a0527060a080a0b120f070f03020906010507020315040308010f050409031202090d0501021804140f070305100302090f0f0705040f 76
    0x101092240011a201030440c0c4040d6503c0c03034024000d00302e50816150350b0140001044244d8800308040d03803400c1d000781e400d01168075200e50810703504250402c110342070345000008001d00151003000d4030300713172046407222070315600010124110882030b50011840c000c0c2c5002d03007440540c0c500c810b803041d28403d4508118290348041e1124010414440360079400351403241e1041d0585000245406401111410b844804d0396411071041200c8050000a52000c041c00000b4a1548100040c011560004085404ac8000c02c209564805002c1e00d0540000780030307500500c046080400b91500070325013610200034150750b588000700b40801c06007000c1d001c2034002509018658400710707821071240d0040000c550f10100c0d03810300c0b5072031035840c03050a00641c10003050404d181c002d5a21180b10b00340900d890801a41e4581c021402440020903044180241d0000030001d41c90f81140d6601c140320490b01d0f20580c2c2060501120302240080400b0204002000107203d85c0c0c02100ca050101c03040580d543c120b0070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 212325215 1250 212323965 212323973
    0x3011206050402010e121b0d1505070c0f140c15070b15040e01060906060309050604060209011709011d0106140d05030c0f03030a0e03040b0a0e0406051e010201270807 73
    0x1e14100646500490a4a03001e54031b80d000328003e020100c0b0054942c44401c0044c1c2800541c2031720000107041400090071030140e161340343e04041e6101c0054606261002c4080c1c1e60b0341c050664a17601a075203007147d034410f5003070203004010714000b900301128486600c1c08800e103203005a01c04d8010050141d07a040c1c000c070340b048682c4640d0031400c41d402007080c40140e4191084a0007091913110304001c050400400103580b80c0a40f00b00c0b40d2090300440076000d0307640c0b01d44409001c1c0d88621003150401080c10445582003070400500b82c01044414008120070100362810350182c952a81c80c01001d900d411002c107da00e00040080303074040400d4aa205a0480300d0800e00c0c110301900002c0e41c034038000d20001403030100c000b200642c401c180041e0104070740d8241e00c14040d0789004501506020803020030003107001601036003118840020007400452080d0f00c40022800c5940d800c0f040003803030100c01030b20444c2580c081c0101c200ca0070b03030f1110801c540c0c0801040a03403802300302400a404d461002a05034140 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 212326465 1250 212325215 212325227
    0x1115040308090a081e150705121b0414040f110a0e0102030d05010906060810060801061103070c06020c041a090a090f0c06021e010c020c010516020a030f020f03030301120605040201 79
    0x8110080c01c0d14040c1074030200000c512030404c00841c82c2c174007505e01580c52078240c1c0140c05001f00c1d01d5944282c20107003504a894910440902050302c1c1e001121403016405d80301c000100064060b106182a41c5a102002e010035a4800319200c5010703410039800901c0003c61009803040301001c0d00d041d04500b0701001c01030f070031441003100104007541007000210304c1f4a43e5401040c1290300f1035403022095514501d41061503105405400d0021300c522004000042c4104008601c000d82002034a05e00020b95072408021481e950142c00540c0003000c0030100c5d45828490103118014a13100c01460300701c1d0f41d0004110110050030070140c141e64071164400c2c8145048001c01050f8461104006075407100c40c040c1d80c50102c0500b8420f80f540400700d03098644411302684510510a40050882c40920f60041d40c06030010f45442c250086140c0610000da512014140001c1d0300a8040e081c6140850040c0801c5c2403503018241d00aa204200410800c0b2a803900e031034450b40c110740005500e807510320040b106 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 212327715 1250 212326465 212326469
    0x602031801030f02040308070f03021c091202010e031506040f020a0e06070602040305070605090f01090602190303021c0204091d12071a0c0c0609060105060a0302031519031115040308090a 82
    0x402040030420900b0000f074030a991609c64000d0702101c0360001000b9985d545000c4942d03180c0f0001d202c440c0f04100d0340d004030919000491050400301e22421103503001c42c1c1340c00c21400b210b0700681074200510102c0d0800d449038144410130341c00154940304041002a1414285090450290400050103000e0200d2541664080c40d4080243c840b26542c0b4400249690070049541307100c0c1b0a0b42080b101d1740d6000e407142c1e10032603210790050a956445001124207001301014141c040c540c007004200c04001c1e0000001d0051036044500603104c44c102320b802c5040716101d80740c4c0c0c40649215a004d680406000030503d00140c0c28140c8140d84000c186045018a00c00b42e070b004607030b51290700c1800780001c2c00b08058050a8408012110680d4070b0100b86c603640c0000303220b4107420074010031001d1002c0380f0980040d903000c44105a010049440c56000c602c940c1a03a255110003044c207280240100309c426100000000fa046030124103954004003042164032880c8001010840c0000f844503042d1684105500 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 212328965 1250 212327715 212327723
    0x2070e0907080f03030702060a0204031703041110030c0e03010c0816020312130b0a05010608130f0212060610210c0c02030706080a0c02010608100e07121b0602031801030f020403 78
    0x200f00042e035141a559803c2a0350050160103143c0c0010101141482039408594028041d000801482c50a040d1960300161080d1000c7c941400001e1403516000d0706400301d0507544d600000e00703203031500e001485240402001442039040400c804034181c0d02014458205000106004ae18038441a0aa20710721444003000403048c050002c01c01c690392039517802444940900444111552020b02001c2221000d0041501040103900891f10440d0009031040c4214410440c03060f641485e5000190003000c1000a000c40ba0b101400b04640380c1019002450002050308155540c0503034550300da900804040311050b0015a9a102d10504c181700d00968070700d05401806850030316440d0f980042c5004411503007a10804c3c2040840703d4094814490241100d0840010b400a50164600c1c0c401525980c5260300c003510803102c0100b10143c0f03660791018000c1c8a8011707046420340c00316004050240c5503200d6015500140880c61034181c08a5202c0c0701c0070005d01e030004204000b80701c184024022608050 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 212330215 1250 212328965 212328973
    0x8120a0e1c030315080f06220f060f150f180f0f09020a080c010905040506120d1e210908130602010213050603060d0f06140405151602070e090708 64
    0x1805041d0550302103081d40c0013401031880d030b030740d221640b00b0741d64203800c040d0300c182c3e030f1054001030710408004030b4070f100401da0032408515001c103545450b003d40404070410740d803c0d0381d902c41d024000101c9101d03c0d1107600c42d008080c42c1c0c482c40d14021807080b929603c0340300508400d503900b0008129290703001000f103210600c0204850300505c825840140780c0100128040c002911010508081c0011010b0300014160b41d120300190070002030101500000d029580c0100703088050155078682070140001225141c2d441c11a00d047c03282d5159500084400b9034800e00a1840c3c9a070b1102010035106680d501102d14040b03040c4610749000314440c8924480956100303001e1030085115641900104508411122401c0c0c80300d4030343c420481244801d691866101408120b1800055400650352038218028000060741541d0280355440341101200c08544941022007540e0907003512802c42e54104400e04209022540c0380503000c1d40e0341c00301c0c1c0141134a0003c0c120001e40300725003c000b030001070900d8000361 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 212331465 1250 212330215 212330269
    0xc0c0f030c0512040803090d050a05030708070b16081f2d0803190c051906051e072c0a03080a1704050c01050a03020904060b0306010908120a0e 63
    0x3004101c142004491501844920400c0100300009131810703155843c0241d4078002d40da008108409144c10012202c0c0c1c0140c00306a00881d000303101505005000b010095550101444d0410020000601004010741a040f0302c5080e542d102c001c0070791220700440008400581d401290421941a912090803c0c900c211014800c0e0122031400b03c440d40c43c21a050f6040f600d888005490f4015980c524000c18424100c941c1400c3c401d880d100b0050303004e0f5080d501f00d088100070b2a0103401d50600b081c0c03060398441080c04908071f0004120300710b41034201903443c91820041c00050891502c044440d880d12584800f134101c01c10503031015005158001e141200c80d03952460509408e41014927454080b031501d0031801c04940144018501c202c1d88140a0006100284015105600005884000c03d503080c030021010b80c40381d1041c800680f00700c034109074681c603000d400102220001c0d00100016046620307880002a100300c01d4420134110b60409401030581e50001c83d400d41c40f200680032404100d5060 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 212332715 1250 212331465 212331467
    0x103060b04021b1f060510080415050906040218040323091c020406080f030a1d09090f0c0402040608220b101d0105030a0311010b030106270b0607060c0c0f03 69
    0x52005a0070fa100d035000220f40513081c0c0101207070030300e1094540000c500ca00503119513100e28002540b05220b1041d156034004441c2e001002c4410442e151009980804240025440c0500d490105001e1980c4d004420385050f5074010090b2241e5030f00602190340300490094038000c641c06590710501c01401c0300a2010907280c1560700c8298010060f4000c40c075000c40442c1100380856074059002d004002180b9181880c0e40031943d01301501030407141075841c01d075100340b5a503c1c160070501807003a400080c512580c003030340e14506140304c805071076100303600c1000100300c8290416230306075002180580c00d42504c030345401030310905041d0100041044401004100040c0482c2088109545019032880c0c40e00e840350700744000107202809107581c554800005513000a00c00d40b20445040d44907000403030003c401078017290941e029500041c000e80c0c035071400c410042114600b4948a0380d20083c050040503403901c0452410f1207030000c0507202e15259a5281e0f801e030b0103114003508447c1c1c4a0680210340040b814 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 212333965 1250 212332715 212332723
    0x2070503070b090c010f0503040f02040603080712180504020c0312010b0403050c0406050f06031e0c0703080c130e071812120305060a1502070b04030302010b100c0b0103060b04021b 79
    0x201d0354041c4480100700e2680c400130b00d4260360001030316076908180704c011090f6941e800c0100121140c0020150103c01030303c1d5802094000d40c0700301c92543e02e0301d610749000980c0c0e403801201e2108000052203051282c1e8480c40e00301c811940190b400582d075100300c46241c0c0c20740c890b81074401d45160207500005001c103160701c000c208403402780303080c1c9260003040c40422003968424884d1661002610007031900e54603200c1d000b190801d0000b140b5140c2400188001d00c6240300c1120319080425010504500b40354000c41015481135000d0481c520342441c4102c10701c0c0c1140b0758042c444040c0401c1c070014500d03078010410780419017580e084076501c0954602d241c03008940254400c80d06401d64030080b940d002d0090041e41d008140003400d1450031030410082c0044203c04041d0001144141080010b0001c0201d000380060341c042e6001041c8060250300380203a5454200d981010001c96a12a0011840c107500c113905695001c800491907020007400600a030042e0800280000960030140c500c84000007 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 212335215 1250 212333965 212333977
    0x103020d1817030103030203070b0a0209040f050a1823030c0316110303090a09020915030a0e0f0a0b0403051c02131a090310021e040806040c170c010e01030b030102070503 75
    0x4550444108200100ea40003400f080c40018050382c0305020300000942c100c808540e02600b10800103040c00e004800107400c0d94490610b49040301d0f03507502030102e168071601a4140d100345038003400c0300c0010306175144614541071040305510041201c50040c0440000d10469101c03441402c220782d02d40c188488400303503c241c0c80c001119070340d02e80345245603c0c1c1004000e80d000203c00070503840600d80390000d108080d40c001c0c039903a03034130a80c210810203a9020500c09980201104840010303459508001240342c011422400e100586c00102800d0000d511403440b980c1c05541481d049844e0844001c0c8400301c8005001208902c500204083c0300c0d60f82c0001c0c02200300d44003245822003445030711064520501c580d03240b40360550070414440207903103181c0c1c0060040c5260241240d040d800da040c1c4c0c035410794105800c0f950141e08174105000a01450b50341d040050300305400d9000411445482c5c030380d50f4821160940d030501035540b0098030207a002c0d03800076085400c0600203640e00e500c80e01c1c20750f40300e52040c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 212336465 1250 212335215 212335223
    0x313020303070f2a080307140f070b0316111209010903020d03080915090a02091302040203090a110f010905090403121a1201060b0702010810030510020d0c0305091b0103020d18 77
    0x60704d00b084809040c80301d090226014030000d58600101526205074848040c9074a071480d100b50410f80c3c0c400c400c10010300c0020501d200c070180d282c2c05c0c1078a90b0100402940424400c100042601282010000c18501c2040e25074050704c41d40c6105500041ea010700300e6600184d4050312802c03405047c15088403c0611030308540c0182e40e43c82c1c0031282000900c2c0700a503a59111540b00d06000801404c00d0700405411500011250758140003a6000a00b668001c90b486a5640c02503164841008040c1d0511000c508080b02e4a03c4d840c081140001c052002c10b01c14644038601c480041000e0600070010f400c8140c140c02410300c581459004c1165805407080080ca0240c28507282c0c4401003501842740c0401d4540860045241245e0380d001118000030107044488190445a0004001041084541d107034a15080300580c40d01c136505204000c841c509000c40c1c0c203050400017001403040022620350210030030580381494900e0403000480c000d00a224604640ca0700e05040c44600020356207600c0b116500c1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 212337715 1250 212336465 212336513
    0x50109020a080f151509040e01020a180b181c050d1407050604060e100f3306050d14251815050c030a0e090a110313020303070f 56
    0x81d2420340d251030f082c1100c03401c154101e01e0740e00e41c0151914030350001c4a0f1082c00b40050500c2c3ca01c1c000141101c52071040003d05070360003d00001540d2304100c00c1d1482183c0081c0c0310031114908001f8151511582c014801406002c0e01c2c0924590b842c444c1903c2424090300381c0d494076480324030300940e4400c203c00c071440209201203240d4150203582c8007110405035200024299075140d517035611028051f1010001d5490045030805031100b480c5115a295480c0c148101003192855003000e01d09d00343e00440200d05020340c403031905403c1181003d003003044898500c0c000d5640e4404132140c00c001c00b0580e25000c1202000c8050003240783e69410040c5c040720000c0c40140060b00d00b10700a4640703118910011a9100414504100d01c64400d000840014218101145480d41105009096500c02190740c03021600c001c0b0200c10303d0401c0413800d0b0b8807251030f46c400c2002600e00360043c0751a0200401c51400b42d000c1860240864030144180c5a4031541300094150314182480c0c4081200c2d299071101804100d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 212338965 1250 212337715 212337721
    0x90c05090a06030f06020c0a020303030a05010f0501080103030c030804080f1219020903060a0c05040e0103050319051c02070602281b02011e090b040b0705120c19050709050109020a08 80
    0x140502c1124201d070f601030044062842140c0d070360000303900000c0b00c0d00343d14044c04d4400005a1801e100842c0b0462018034006900d40c10902400800d1400c0e4018a041140d0381c801400001e4108065404440e050b051003200b65581d85482031141c85060300c506d40400c40030a482030701c900301c06419806a2085800c0410314824090014103c0c000c07500c400e5450b134481e00100380e11b0141588070103d2080540780035454541c43d030844000d500780030307441142d05500008110f420701c00100c441003e403200c81d00e492031030000a41845040c1510070100f500080e40d001892908200c0d00ea4102c4071075404440795520400351140580c40b18102c40c05284003c544c05c000214a81d042d2521500540c07035050b160b00d501c0290f40341d00cd0381112980011203090204440c40820314040c0d10015100812070b5600056480810b07150a81c200201c4445d080c090322001d001409900b600483c140030294a0346140240881076410403d20b861070356806100018504000495002d45a400030660404545c1300c49415031 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 212340215 1250 212338965 212338981
    0x60503061b0f13080613060b0111060c0d0204080a03080702060c030c120702161e05030102030f15010917030304020a051009210c0f06030e030301081209060706090c0509 74
    0x2000c01104014507940c104a940c00c0e6000302030280c80f4808aa9249903200ea0b12064031918241c4203071010155807100900784010442240205102c1001c286420700c186503404418960b1020082c0200350310300300c0414041d82200031681039a0040c0070b1034084503402400380c01e0251601c80192481c400502815001031018071080040f2801070400090780740c03529058810754000c04a0280c0b40008501480981001c4c0c0e0041300d8095020301003900c500300c800140304107256180d242030340c0058080d034014010030944600c0b0249003039100806640c013046034400040129240c04040d0002c90800134804a9003140b5040080554402c5109440f41800c05845030100000140c02442890020b01c0781c1505004400c200c4400786001c0800014000c0c52141596440c2100340e026000710f05224000d080400c40c1035414095451094a1240a1482c5504191a05840e80d81c080e80b00580180f0020b14800151102c0b400c43ea41150001800c1000314880c0c607024492010303038840c4030701c20794051001c100e0032 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 212341465 1250 212340215 212340241
    0x20c0603040302030d0b0a120606090b0f011d1c0501020a0813083a0504051005041709010527040b01030b0319060603020901120606060c080306060c1f06050306 70
    0x41ca801d0f030001c0d800c009020001d43c1c09008503681041e000b02500200080c2995000080b0000c94030810010a0a9050600d2601101c0c80c0510681c03054003518129412660402c0c00e5001c46050300803030b074003440e0440020642101e440301691040e40c0310030071807500344a0306501510810a1941ea84902903d4034003034042c0340500350350054000d980810000204443c202c568001c4811454503030710346051102211010b513188540150042516501008100003090042d10030f140c4100c1400c20030390038503403240241404200500102c01c6030000703024206a00400640d0540402c90701c10500101582100c04100703ca00c9680d507000703500700300202c5059802402070a102030b070042c000f040300e50305c0d03a66442c08982104406a9520341c0d508808405600d032054220702030000c01c54a04d06c1c00c0300d6441c04004681309036110501f006242d40c0400c00050818003241d400c0241143c40e651200310000403982003019911242007101d460b81440100b5020503040b07001103030000c5098460f1503075160262a60 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 212342715 1250 212341465 212341471
    0x7110601050d0b0a0b0a030501150e010e040b0103021225261009030e04020a0203070b010905040c0504021804060807051005090303300406201e03090c030a12020c0603 73
    0x84040c02c0000814410301d0398850402584010000003001e561f039201c081c21135410b034808920f02e0380d041c2014004008010840d50060020802441c04c4d0f1409440342c410000060000034410403a920445006a1080044120002c0a8020206807900340c1c5e1402d045002c03640708403ca031407601501250840c641c03202385c1c00001000405448403043c0070031040c008082602e000c800340040745c3c2121020f0784442c03001c1c10545080f0340007165107500b5802d1154080c141644800f008034100030400001940e0000703481700b03d030016500540c966540307900b4014071001441d40c80e500185451000214080c001454a080321029901c001e501d16040c18211a944950071b100c5d50550f00c01c001e481105c0320140e00078074000c142c0c04000100c4036400f0801e030320400f005a07015100e071511800e180c040c40d0307401c0d0500c507020b4013554601440c2603107040000c8051021060716503520351010002502b60b04040c841500d01e100d0007002d03510302104500d010320f8941603001c5000014801e0580300d0540d81007400850b40 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 212343965 1250 212342715 212342723
    0x3280207030e0f1801080607020f070803040603020d0603060509210c0c100903080c01051b030103030f0c05100207081803010504020105040306020706021c0f150501170a110307110601050d 82
    0x4801c102c2e0900c2010050500c0c40d0390004034030b1200c003074072040b1000498060010180a05018105200000d1414104280301c40182d081460104505503000013110211516410003603102c105040c40c1e44010161340e840034082900f4441041440440030501c1c0288202009910740024100000807090340100d050b031103401d500c0b10030440041e2500a400c40d29180e0603250600070f40da100d68030358034681c00901c080c60a50b91584280329800382180600980500b000782c0c0a0309662450700c00401d803040d18540001880080c040d40e0b4140b0209109101d4018500c110545d500d40c29440c00c0c003115403100744050785400c41c24000b03005a16040c016180119016500d0a08050458072048029805039100b219519820405101d40d10040e0b6001c1c1c440e2010780c40f0015102041d0a928025102504404404154018414072050703070090300d10a4030000880c00100540c1d10a002c28004014903405a91088404020001160380c0044c502d1441502441a41d0040c0d0b038503000d004200040700341c024 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 212345215 1250 212343965 212343977
    0x1080a050907140301180f12020604080a0c0c05060a050a1701050f0603130c0b0307031a010f030b1c0b0103020a0801050702030f0c0c0904060f0b0306040c060318080328020703 77
    0x200c000503440d0f1802034140c00900000380b566125103020b1807028040300840e200c05102c01290b090200c000c0c4810b00c1c038003071400540950724007695541203a1040010360703400e202c0744140503006c0c00300844160000c2d20b07000c0c080c01d659614000e4064440d820042c100780c0001c0c07121000c250403050b140c00044c100c0b0009003004441c0c4030702c001003001c1c0d03030002480386c0901d1652071402d80215281482003001040400442c1d50fa81c01c028070010b042d0b506800c441075200003204071499460741c0c40000c1324140103a5107000140b01c1041400914039000d442c441140c1032604076130150502c2400e00c00181203a10071100411850703502c5141e1402d8070000c903100005038005010a0303094141010040c02c070030741031205403120000104002241c0c11400c0e101071b201c095070703200001d190031098411150307400030490040c482c0e0302c2c040e0340d400e00e00306450140904250721030318207070703089104e00d007061904590200350a61a0301e809071040c44021802e02030003212880f04640291491203500c200ca009035010f60349d207 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 212346465 1250 212345215 212345219
    0x6060807080715210213060809150606030601030e011103160f0c060908040e0a0c110703020603060d21180f0b0d0504022409030607050909040314040b040602010b01080a050907 77
    0x10746016035044c42d980c0e807984600104c104031a613980300070b046120300341d40584105400d22100520941d030041c00c0e800c1550001d4031400b0115583c80f00180d004c00c0403070b01507a82c1d5403000b004901420481c00c5030300342e541c00c0890b004e5854040c035000d94491003040c0c6004600425144007140e1120200d142c40005c51000c12060303011484607000001c42500030b11149103003695600b40e003c101c140480e041d0411351340d54076a070000346601c8a000c001009201d4010a100c41c116000a2550300c40030340303224403030600050002d00304070300081421180103aa0034020781c20f80b04883c014103181d40600141d1950140c9a82c04079020052140c01000d40303460050460500e40709408420040101400582e8040003034480c5202c5150b8241c2c0b030750305400072485151380700c16040040c0740c82c1001c0a405d581c20b0040605c0215126103e5100306544540c1605e8070025400403c49040068865900104c541010006000c038501d601500300da01501020307a00c4030b05950b6698070900c01c4030030a880c2e0315825000a07c00b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 212347715 1250 212346465 212346467
    0x70e0603031c050903070f030f110706020304050105030a0609050f09100510180905060c0c1614060d060b0a0f022a0609040b041803021203060603010e2206060807080715 74
    0x4091340c84020601124039101c030584801054410b40b06040300003c402e4108002d000f54001131246018481078010020f41d400c04502a4680c010340c05810304001001c00000c5100e042e07900554024600b140080109042110b6490715014044600c0d400c40d10071819681708241541c490a07208480c01403480f981c0a0400c40a0404101d11004003c00c090315052004040780c0c0070b00080c0e015400b440a41582c410740302650790300701207942c0c1c5409505440c6034070800480e03405240c80c40d40750104071801075481520480e510300809541c0c204a043d9240480c4010f01c142d0015040051850940c080722004106107000d443c19411111451051501070341c2180300c9824414060203111800900c0490148140004902210101d24454096182c000402028142c041c00843c1502e1035071004bc034510719180000c41c0c214070040c45840800d00d000030004051003403050103010b098540b00051035620801d0b0400d5030141046005044003406100030001c0c801ea00019500c00b00c800703881000301040c41d4a10 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 212348965 1250 212347715 212347721
    0x414100e0c0408150c130807080c0301020c0304030212030f120f0105040b01021f06120f020103060b030708040f0201030e06130605090304060903110607080c1b090408030604090311010e070e0603031c 87
    0x11101d0300c680700510084103400c1c01c40c40607002034030940c4000d086051030710070b0440c540341c1c0ac030017030500a0f407040113010750301c5001200312400d980d01030340c070070500c0040c406c0e0b40ca01d584a40220520203040c08035411154521108009000d81080d010800d03503644c0310303000c000c02c840d2100c0071a4050791100d0b2000b035101400c000da0f19140401d041c030000e41c4584d907540d102100d4103000b404546d10582e1401c08800c41da0144121805001144959800c42c540170901030110b060107880502610700700c0e441e04085a11a4004c034600c02c2903107003561980d05002c020000a14a144000c403441c604000004040d00e00010946089811503078800c00c0803440c540f500b04841c1071030314000d82c20001c00c0100b5030100d029440141404194900100245030b8001c0d0128810501913400c148250152000d11022481480650760000703022900003441585514096032201c40b540c0b401d4034031f54241211070724100030100c3e0f07141c22944903100521456580d00308158503486000700b03000342486000603a01100100c0d40c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 212350215 1250 212348965 212348971
    0x60405090a0204111e09040f050105030622021804060b0103020918090f070b0a0807050304230a1b080c09060d0f0c091104050f0109030b13020414100e0c040815 70
    0x59150307440e0640c070f0f100d901700c1c0e842107030503550060303000040e40c40850405109581c0000f04041c8200415418900088c5d116030000d40f8156007000c1d1340d40b031a0842c5030f040b4102c404240d4024180b403014803600b00c04403002202150161240c40c502800e01c280c40d4041d000300e94603034078010b011000003142040a800c4070f00303000d0020391883c41003080070044035404002800141c03480100103521800e81e1500101000c2e00140684c00b000014024000050b100101401a40b21081d0941d214859544486490507900c0c0f60301502c545005801d0150501031095084c0a60320340b8416070750b0004c0310380c051120803402540c10f150410000d00912005c10180c0c1da1a94a4030321940c2d085040c203640b00403050a50740916001280e03240d0001e0304004510303000e56400200fa00a09007000c90728278640b907a100f5a180240324660141782307909403a04541d9685e20918035000300e841d1411040c00c004040260f02000c07805003009070b4680001155442c03584030103031421030714814000c2c50820a441000c010f841005 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 212351465 1250 212350215 212350241
    0x6200f0c0616060e0114070f020a020402030c12010f08010e010b0d080a1b08030601090e06010921021c1b0e0a0c050d0504060b0319030e0607050f030d0b0108060405090a0204 76
    0x7002c0b00000841c0d60180d10204000c240011564220525880841c0324000d0014020700c07104d00280f088054001c1400300080d40c04490044e2a07688030b006039079040c850900d540119040c4400081203c1c5500070142040e110b40c503000300062200c81d05c40e60300b03c0e0241d10f506640b10300b000c00001d00051885006000301805890b000d00c030204600c1c0c4500d04002c15000031541704d180401040900d5074026081d130b00400014407440f01d14104a00040e01d542442d000744c13992420b84c800030211740c1141c0d98040c0e1020794060151342005d51020000d40300618404011200c602030400440380001500f0110340c2919a0803103045065120042c3e084000d0101d490800140306d0117210a01021500c1d11074184168000c1780007080f035000c0074007051305210300c28031a8025400340c007200c0b1002c070b076022481e0744e050780068640d030307035102498140f0b6894a00c81500c28803083c400050f40100c0b25100d608500c001d01003c1c1c984000c962140420032041da04121401c00c140d61007003100502515054200c044d001d022 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 212352715 1250 212351465 212351497
    0x2010507021e030607030b060a0f021609090501051b04060503070201140c030907080d0c290123010f08040b07120203010906060e2407060f0606200f0c06 67
    0x1a56000ca105214481150000c8031850722100c1443c2c1018042c20b6400041e901c1c0811600410740d002640c18000ca1004500300315a140c02415501c2c020405400180e03121001020710a40d03484001c03000e81284002182c15501b408003041c1400158070082c0f8561000d14a01c905140c145101200d0b2900014454411592a00c070030078a0703101034480090280c2a19211642d40c0d103810301e01945007039001d0780b0090b003a50040210840c801c5d400f4106c8515180e00ca0101c001c81000b43c90420a4643e48403004651204003000014503905458001141c00140d6091f41c4008682c00c80103540e0720032000d10a00110304454000307400a000b141040e0303404206410038034456084109204100e0700240c2040302c1c015a145400d00c041c0344c00140030319540d03504031244000440503032055000c1003000e640541001101240300420490710342c00c000e0006000b203804124180d45e414000344030541c004d04000740b000f9003948034108220041040d0b20039200010003407e40904400500840360b101d00d40c0c80c2d8030150 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 212353965 1250 212352715 212352727
    0x1090c03060e07081617010b0c0105060109030b0c070201050702090901020a0914220e01060305160906030215070215072402030421050904110a030b0d0f120e090f07110f03030c07020105 81
    0x10b407446e046806800e101e058140c446040140b0182103d801401582c1400390b0000100700142c40314030300d11f52250000642a446158920040e41c00340260300000b988032014004101606505602030854071480303a496031750442d034a18461540d1a649110290030040d00407c2c030343c140610180d00c60307003a450120005641c1a095101d03a085401c1900103e6003070308515140d0720007401074200c01e4041c00b0010010404a407466001aa81030265031151131015404a50f4a00790b6071001d43c6030102c0d004240f0003990301c100314945254403803500a41c0100100b01d60012214100041c03007070300e11465200d6907009001c044100307803102284840c114a030400c001004084243d031901e00450b0091980c064540b92501d001000c0a410f039002004c4e25070291210300b0f0942d000c0741d040e44082400c00d40080d04010315a031142412129003100707000d040e80080c203d03400e03c110710201118551050074503079201c07804c00103201c10668031480c0000241400381e0051010441d2003607807100030700c11640b0504029141c0f175 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 212355215 1250 212353965 212353997
    0x1507050909042a0603110f073809120a020c040506030309060a08060f0d02100f1e08090c0a0602210408070605030a180b0a02090406090501090c03060e070816 69
    0x814032041d814180b0b481c0d080c00700013094050240001e41070100008509000701809409418020060b0180c240c0c42011145d07507400d40541c100a05800c225900480041c89140c880c2124182c16508a4680e11030003030400011904d10090b6402c02009601800d02d0b8252001000042c00d0701505443e898082003004003495520b101c014040b26203a926805510300d0100d0400c10f402b00030794810390040e100b01c140100140d56050b1035082016507428000030618061034200c03400321200c40001c1c0100a10886002c515401c0003142e44100502c01c111400345030301a09114004150340b0855000d07030b2000d0020480180f01414540d05407120709546814195100c1c5054030382803965006001040740081441901d118a01031003441c1c40da603070403190802d2044c3ea141142040020701c031040003580440c0c0c500d44c0d907945400c00070050028000030301865854041c000021700c100410030000c2440d0081c001101c140d08002d03103104e41080d80f101034490b0344184000076440030b1462601c08101094100600711 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 212356465 1250 212355215 212355263
    0x90f0f0606180b0a080609060f0901290424090b03010b1f1215050609030102121f0e04020609010f110a080d0e0c0a0303030f0b0301050a090203150705090904 69
    0xc641e80b0101007404036140040c8405500107801000c629040760041050070b01d030016400790066485011481e4641c0d80c11200f500501816a5600d420307440d10040441110443e050088950800c031001c003d043d410b02402d40d82204c501d0400c04006c0d80e450410040041164040c075405100a0004107480c495a000100065030407444550300b02000520b02200980c06258211204000841008a0030f61100c2c0800c2c0007041e841080c1c49024001200261074400303406a0764500c5190340406003604103001440c0282074103003400746455903060f03800288210071101803805181c01910240c5400c2c0c40d900111494038046100400340041c0d04102c0002030800c004a0000d54040c80041e03484551018100d010745039403c40410031544000440e2455035074032030b0428112179040c00d0008440000888120186c0214510240c0c154a400204810703820150030494400d4401c0f02603a00f2500403003003d041000045d5074800009400b801080032600301502c005401178010f412607040c4203180103c3d6684 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 212357715 1250 212356465 212356499
    0x130c09030f0515010b03070804020906011b050f100207200a120606050f0405090616030e0d0801090f0203040512070501110c0a03030e1f0f11040807031104090f0f0606 73
    0x3070341c07110300a407040000140d1004c4c058140c01c10124a1400c16200040043c03c028001071b00c42c0c106200814142da0044024070114035090848200d80704550130100c1c0c4900203842e00f00700741e0044a2808a4420b030620807610010b42c07144011510b00320102850408482c001801c1f90408503500d008911000c0f9280e406240c103219040101e021f50910081c0155140700b901014062803c1400380050713041c010610030350040c1c1d80c4111703030904803c240c41200542144c200790240c2d8080e4002d072043c1d040e48050541d06841e034111041c00481c0b003e40101089100440300606280c00003644288070420500c01070032910b020f400041030f035040030320380310f58590301c003200040032540f01401035010181c05000c0d110741580240d000c0c0a00158a03032480b07140d40c003825030f402d69282d035464036482000f405501000c4425040042d1075262512152a5030781d403007260009440c9802507640110003458140140301100b85d01c0390b101503501025030703201c0954501200c1c0446e1104c1d1207540214541003036001d1410 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 212358965 1250 212357715 212357723
    0x509190e030f3004120e01031b0903020307050a080304060c0807050714180c0f07021903080304140f0a060b1c0809100305130f020109030c32130c09030f 67
    0x403d40e5000100144072030358440ca998454035a050402001c07520900040e4800c00c99070800c8401030310700d0f80041780103004049030018620f03154a130101040358080d01c404181c80c400e40071a60803d880302d0401024060a109104050340100801c2c4242d51046012002240c49001c005040051710750f501c80c00c104036900f0810b400011034a420015250048464801c0d158072440c401460801c1080030100340714104011144070340028184c0115107881c2d18801003544c0400f56030602c03580307074039040b040740c0e009860948280c0041d043d030700f042600202d0130292641242e0300034000418981d48010113054103010155000500c5464520003142c01c64103105014418801da07542da800f00c00c104003561501101c8582010700d080d040204150407500c1004540340c000f50341c11003a2078588012582a4400c0c0c00c010a100da2106002481400d4110380c4043c00040340d042d5034400ca40501403040081c1c28030902984241168151400d501e8203034400c0003214403e252007400b00d9201d4031043c0c1c20805a8030100c1d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 212360215 1250 212358965 212358997
    0x203030a0506011e1d06030a0f05100806010317040e09070906140315060f03030c010e070509130b070908030a11060708040804030b0606120c07020103060509190e030f 73
    0x4028606849a150700c40c07801d003000806100d10712000c400044002c84c00d04144001c1c070107005818104200d52520050005040d04c5d0351b8641821000040c100306e8580d0070400d4104030115071202021140002620f040000908a981c650703199094501d404110003801081d0800001c101c0d0b01212007051300c00c41e100740050001514091000e0121545548644000d1102e14030004040e035020030078175150a8114030400c1d00e61601c600040c00740c4c0109004907414400014040701000f419003180d140640c0c41c0d402d03555011b654806000e020041120340c1c002c3e243c06141528002005c06c21129004055450604045500ea030360140c5140e002d07000350004184010441042a4002c0213025403202c4145851a07507030520355211001c900403404000c112501200000d0100c0d110303d0700355007591030f0ba0100701090307003007004102610380d00405007a4002424181e001c1030714206540703518050500002003034242d140c401c111600402c0030082410b007600040007840c0015001e800582607079410140e04c2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 212361465 1250 212360215 212360221
    0x180b040501051603110912010204050d150e01020a0516060b1c020a090216021c0f0b0103060c0806090703020c1203010f080d0c080906030712110913090b0402010c031707020303 77
    0x42c5a03010f075803110100301802d05555400c2c170390704902038a004100c10380b9000b100d20320f107071131641c013a0090f500200d070415117540b00d120912038000b40d4030007800d240303c90421580096451160030303882901d41070404138404006051441c4006040d00c00e980b0300451000a00c039465000241d01e5103100c0850b14a0b810981241c0f0f020b618080101c0002820750240861409001480081200c038445a0191151070306000101c5c0f04001d0521b0385c03225940c08039041d005407156103400c0007403a000380800d45078949003540b80c8000398040c080300d0340103540050210b135186e510700700210046e40c03028002d40818020f180c240410b841301b103005103004e000c2c0310360350340350b9142400103c3d45840c1140c4542c20400c08071007012008600031000311210602c05403000e640d02c1d915004140c41400d40c4811442c0c47c2850001c0c91800350705a100500003444048502000090001c561402620354000c0054034420074000440c0066000b40b480d00102807181c01c00e60620803642c0500c10805004481210141c0c10000030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 212362715 1250 212361465 212361481
    0x409110319050a080a0c060204060201020301090b03010209010e150c0a0b0f1f0501080c0909100806071d090603150907060201050106050c030a030b01023a090b070303180b04050105 79
    0x1608180700e6420644406001d16074541d980d80d40101c00d405818050700240000307440748100b0005440d82c1c1c02c074400303558a0380d41d880000c6c000d40c02403051404041c9802c0001001e03241c103008449a02c41e05039982811015107404100d40807402051480703008004009000304e018090010300403c60090b80912000d14054108240307080c1c1c014410140d50542c84164030b0b9100b1140e107100c0513500d0030300c1c1c003903080d035542c04045c5040e21072040c92552041c2410100030704802a58161010b0b1140c01003030380c50719211200c050769070344040070f2011104c0c001c00420341c84034140700301040c0e48800004c00b12010b40210f001284407113031081e10340c0c1750250070501041c00000d0b024001c00703006085610702180b03001c0d001e200143d16170140522a1041648500402d842d50b0310070807402501c8440340e040d0b01c0c0850504134044a8554660700090400740a1803d4500c07100d005400f050103c5a030102594030349410390740e0440090442019080709012840d0401000c07561842107079200fa44140c000140c1e9091100c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 212363965 1250 212362715 212362723
    0xb04380606040906030f141204090b01090f0b0a02120310061409040207080301090b01020619020d0b03030c0a0c050411040b031f2c06010504120203070305011b1b0c0e1504091103 78
    0x307d004880d4006011006c07160004005c0340d04407a220300001404214840c0101e864a00c260f108010000e4002d1001c41c1c508104801010b00e00c490342c0844042d003002400e0070031203010807110f40100c401e80340010029680900001e0000c00280e03500c143c54960040700040032030700104415544110003000520814101d482443c0d400d40090008150138903148c4041c0080b007901e0919801040d4020410300c1d0220752135007140e0b01e5100300130240d0341c850301c5030f46046a440e0741c0c04200b40d40880284030b00281d50b003411700c5088404003690054a1502d4186080c00c000ca503c007414800d840c8280090000c428002041d040001d00003002400701e01c00e0300b041045540b5114242a1510050b1000900080da81c201084400b00c44040b050101c4800751400003030b08040072580050110b50a00490741441d813214074400000700915110003210108801d1824200f1030070f60030081c4030422559007800b44070b0b501181ca661290419454100031841c3c44041070541da80c4403c115034183d0345c5001200d0030324041c8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 212365215 1250 212363965 212363993
    0x603050f0609030423030d030f060603050606031f1203091508101e0306021204060e07030f0602180d05060714130509070309020a030b04380606040906030f 68
    0x38018a01c5090600c40540c6a10032885400c01018951154860000307010741c90a002000040a54000c8000c0c9480034024002c8101c03170102e16881c0150202e6981c0c06441003c2c01607001400640c11681c440e16415240660908544820700841a0020f03401c82c0390b01c142e42d2614400d41d10740210b076103007901005112092003030b0b00051104140400c400300300344c98150402c88060b00e10640c11a00d4014001940065541015100c180000f4115036419207e29030f09008611070001000241c0c800e035852074984045000c000c0c04070301242c15002c0403507501c1c1c0241c828000c00d90220700700004500c000420700a002d072400c4849800c1503003040840c5411801c903805190b074070140980b40040610014040701039501131584541c441c000403071002c44c440c2d407260754680d901a0400c1c9003184c03039044c184543e90086408a52048407100b13056004400c0301c003a0ba88030030f50740740c2c0708102841d540140c1148900080c200c0741c104800703100010b030303549045c02040300942c041e40d00760351103002c14148103080360b16107 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 212366465 1250 212365215 212365243
    0xf070e0402060412030c21020c190f0902040e06010c150506180103050f3003040501150308030a05090d5c0a1a19020406051206030a030e190315060305 66
    0x70150341f138600b139008107811400740c9003200c14400d400005a610346611410f0b4100a420180910011a50001e1b0b907008100b5a0420f80c00e02c0029620800115041c042180000701544003500c041d1301c42074001d40095411040040032801e0360304070540523444c4044268016074036580a0b0000b01c1d544002400740311240c90303003440c0190401d001c51900302e0401148076464022030368000001001c1c48029804006c1c545d007a904126013041c0d9a0504462581007500c40384181c0f840c2c24085210240009440c14003508c103a195004004021142c444040d4900005c503824150740145000e1b40080341c031180306121005030b045401c10804a07144450010041340110702d076a21506290001c94258103a2420202110040e51401d540c3c9a2490500c903d01c0005200d0341c900104022407020741010161600c1c9120f0340800b0000c2e50b0341d008140e0b0741c01642e207016008c40c2050300000f00034180200754621403640300945178011a56540c62040429044180c081c1d1290365200074000c00c01c060000c1840c001d15 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 212367715 1250 212366465 212366513
    0x6060302042901020a020603070c060b030601031b080102041410030b03101b05040b07110307080307051b04051005040c051303060c140307020d03020a0912030810080f070e0402060412030c 82
    0x2095011401f903202c013400345414041c4840f1508104861504001c06080026050b0b900e00c1d40e503440e280740491034842400302d1501d565540820203c105100b80d40c100c0e4007800003141d200500c14140000c025120a200003019160140d140c120b440030004110041c85000001920043c1c61b0711800342c207620181803e00f0410100000c000c104071641c00c0d108a036400c10721904901d50300400092a150791a8007120881c0030104600080c0400840c20b00c0320410442d4072017442424410401044810489442d440303030135590414040c42c10b180e449041c030030b4414103100380340007500ca0ba6060a5001913100300c40c6140c564420124145d44039080c1c1c400d582032820500c1c21420500c1c5d0181d10781d03801d40011020158040b40b440c034100d101e02c410300c0080203a4510415114401c0c100185010350480704207144807100318000826240014842040f001030901030300c4040c2c00c1800303000b80b6480c094010390f44040140310115620000c035070501ca840b8480e8891520b0380d6906c1c68002040b450040142c654080 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 212368965 1250 212367715 212367733
    0x2070f24060b092803030207031e120c062403050705100c0b060114071506240c0f120507050c0306040f08210a09060f0b01050909040606030204290102 66
    0x103010040c3c9070810002c6074804103600c0801601c2d180d04094854001d0700f581002000414940c02003a45002e0f80d000701c02241490300480c2031045072800d02d03c4001e000701d190031940d42c04107200d4010840c0607072213017074080f804003eaa0000d41c4030030101288040419a100c0c41001040750400a9030700611040d5000c0c200c2c000c203001c0c081c169600c07810b40504030030086400184980c0c440e07a821100e1407810440561030344103604260b01d4420400444240840c41d00c02d0206001a58030f034240000103100e4480049654448811222007045103412105404844a90b400284803901d502c0a001101e075107141d1124090b04183d4075284000c0300d800d00a0f045001800046500480b4031640d240e00b1070400c580d50451078222020794040e00489500e8818880180b01a0540c160030a40d0720a015040c14031184440d2a00c6800b240c402ca501c80d03010407000c10400081d82031000c40710758801d0150b040000e40d5656900030500741c41000c0034000083c9040c0ca0702c14011683c485081004000a00c000c150b070310 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 212370215 1250 212368965 212368979
    0x903080610050d020a0e0301050f06150903011d0f0d1107050108060607050607020606011710060c051006060203130e040b01030b1f080706080702030a0807030f02070f2406 75
    0x820240c003aa02a50010aa05074110b0054080318442c10b1040307011980c0d041d9034480185042028840389110354245004240c001e04481e0903a4090a401040e41580c00c5c0f014130304040340c1d4841c014054055494507034034545e4941180c00c01e4603100c4d000c0042c0c5900306020075880d08120038400b081050004404050403c03d00010b001c0c400d4880030308040b049a26200d00094490040000042032841000200252983c0c00301e40c16021300008e032103510351209450340c0aa51001e049030028004282032000f081541e00c1020350101d102c0c01581a640c01000310b007110010348000340c00840259000007440c02c084039070100355500404496461a0392400c26940350700081d20103110203828884031501190304511b012100c400a01e110032420100b02d9a00c0307800a89451540c4103210200301c1490016101c0b50000c001c031040c580041c1e6401e6995a5004410741c01085003846020341903a0a21007040041d0003890781c1c004060044e21030703440100c42202040034104000120705401c6003040d0b000c101c51 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 212371465 1250 212370215 212370227
    0x608010609121509050a060b040902010206150d0b15130209061903060902040e0a0e190b090a0b070806040e0102091021021b060604060b0412050c09280903 68
    0x10320340d4000c0c02c0050310b00c81e0420a5402c18840d40354007000f850411440c080160001e1065411031089801784495420941048212040200060301607000080004c2e0407054109080880c0000100940020941c0d03444001722320f0705c2250904070342040c00401310f846140896100042e0200780d6419442c11031190301184041c0210700f21903684a0030754110780710180c040e8004030082d2a215a00f107403110307a104440d401100007620b0025906241031241030903100d003c100e003405119100c030340d0b00f0b020b4000c1d0380715984998000c100f410603004002d181d10002d8400b4070314a010300021b59540c1e1312410080100800c03a04150041c201e80da10400031100306850752024986400418184807100740f5105d00e13411440204884160010340c0b0000e80420025a4820051103c440c1d020484603c0d03510310b01404126441c50007442c0c608042484200840a0100304d05004c03203101c1c2041d14410601e44020500c0b4400075103001c140c44098845030004c1c8050855810300007002c201d0140300d0b6002546014080b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 212372715 1250 212371465 212371469
    0x3080c04030c06181502030403110d0503031602032502030d090806010605090d02191a040f050906040f06171501050906060a1e05030a05090309090a0b040605091f0608010609 76
    0x28048401c10720300c3c41c8090f0000c00c4c0020040031004004000000000949a500030b0000b00c1c0c60401d12003401c00582011090842d610ba8404001c516688601072200c0d075502035101d020045100801121100c0403886d81140268003c0e5841c200d0035011500c105420300640700000c504205006000f00410900001d08504645841c00c0240e614031541d40450044040f001c0003035008442000c401260205015981d001c444cc012054900c4050144000455120300e104052500c1d0720003034203000a1411000c0350307410400040000501400c0002ca079016200381ea8410b03490000c425620f003010900c2445251a0f000d180c881c49112076040c0000548141c0d0007602c12401800c01284802c4d17102d024022114101541c003040c1c0481c00d08095004120b81d004540b01c09411b0b08040c04201c00b41c600000760741c2c011100910a00d1141c0d0340180100c000d01040300c005600640750320300043c881c1c03102404140207102141340030200c1e01858001c810340c0d040079842042081032900041200c55417018920003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 212373965 1250 212372715 212372717
    0x90f0507170703150b070c051c11040b01170f06010e030102070c0b030a15080102090a0f05090406091707030c050f0c101413060c060e01110f160f0503030403080c04030c06 75
    0x2821041060000c0d0301d00b960707401800108070009140420b01c512010707d03600701c503030403240b0300004014015608811420800700804000b01c21640b00c3c07a501d0290020b01e01c0b5201032520a0300d046100741030b041542801e8542800700d0900c80c0a01589503400002d40c0a03589050700290300d466010782e10f440b40074005220340300f81508048045440c0200e41d41048040d107503866035517600503841d021f03054001e40c002c81c011403045c190700200083c00c0240801150840b400200b159195070303590b80328076001d0844018103c42c102c03200354581021081e0300014064050096031403c0c2c0050852a00700c0c64070300c00c02c3c15001c40394040a6500480e940358401806256090315000c400500f8000304241d00c0c0c007844000d84800702c002c400200e14560f000c00232040d403501412060112504080845003200e15031100151810700400502c12070034030710802030038240081d0320ba040347c40f070a5880311a980d100c183c50855468100005010501d9031003110360340c01400c8881d1032407801c0c0c42e560f41c84441c0300e664840d00c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 212375215 1250 212373965 212373971
    0xd05060f030c1309140d020c0d0305090405070e03010c0509120c030a030f0329091503120901110d08010f0f05030606210a031214090c04050c13090f0507170703 70
    0x103009103c0d80c114085095204006000e00350b014a4a281c503002d10480e868018070031000c0e5086545480d00719221010740580f00e461514030440b06010141100074410014065040003020080d00c09200e0904c409907603588083d20303001c10743c04001100c480c5101e24000307507000f94507201c142d0345c0c08110070f80307141d506080266114186410950103032812803095002402d65000e101104ea500500511501038111000308135945d91b101e041c030a600c0d1055415806a00407412148945403000c011320300104141442c0c2203040544e00814540312469440d900040c4901004100001801c043d0802400c03208040050003821b1a010a0344e40e0320050010f440703128500078070f0041d258610400845144a501030f1850140380b403c0c0030340f0400e00300c020740d1503041c68450541c203401030390f034442c0f030050350302501030f041c400c60702c1c0100b10241034042e0042448000400c28149501c0b501d0b02c03040014144050b010a900c0f044008200481d0350080032201480103882059201841452103183d200d04241400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 212376465 1250 212375215 212375239
    0x720120919080105060108060306090c010503060a030c2409080c061e160201120b0603040803070215040501140f1302041a100302040807060908030703080703180303020d05060f030c 79
    0x90200900c41d95582035611401c1004641c8070810f401c0207228450a0300c1d0183c1c0ca442d10018180e990004a0f0940800d0300a0002500d696200d017000710340010f001000c40131603036280d881e101741500e2258055075211030410102168016880c07040c0d440d50786641000101c962404200a8039980c40c0f000840c03098800240140c19030169084200b6403c03118500d0f9600c50f080810580c41d0540510b030103902081c980c0b00042e10b04c0c5010b025200d08104c001e00b255080d92155610f00489810141102040d070054903202101e179082c40c18000c0c422401030002091601240c01b40303a1a10710013601c50b079403400e0603004020070f09445078816010035906890000d00040c1129442d44000b44903040b1541c401051b040ca52002e59040c2c000e403040d200c003842600c001c9680c0340c405980c40c4c0040c0c031840065410a025010102e0301850000d540a801070a01280c0c0b80c0a00070040b4903a52640c4003100800c3d808941c2d41c4001446110b07055010300203030b40050f001420800020358034403503c0c600e103219214038808 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 212377715 1250 212376465 212376469
    0x8121902010f0606270b0706050c09030d0c12030b060306060903070e1306060902090d0b070201110d060e0f011a1e0c0303010611031c0c020a120807201209 68
    0x1058680000400800c409910b4481c0103100200c00b00292010a1000e8101a04c964170a03080d0012244915001ba1421903251748100103480c0c000c182521440b024440507100e5202800200300e031000c075944401810354585000000700b4081d5444e04200751814100241c55258081283d400c00011a0f03001d03102d12019000a1600c6070f03230341240721a08480c005000c40240110344045da442d00c5104e0034800c980c0c5640c2c040b0f049000c1d8550481d4040d201041c0400402c0d050784a040e0840d102d4130010503440c41d14035214100d544103114901e1000d60f219410403516a81e1560307140c018900c0c00344100694505030404250b80442500d00400500001d660b42004080c58400a441f044241203251544080300a01c3c0c1c40b50024452140030035840591248501000320803070b4050000c180b0118546469140703104020490441e10005620807001810701090a85028215100607540c64078414034007540b008019066070505030740c9180d0500c5d5403402d04040402c6001c0c0703d078a200c0c0718a84503804100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 212378965 1250 212377715 212377721
    0x105033f0310050603090a0206161707020a150f1d0301050108030d050903030103081912020c010605120a02010203030a0c0513121a0f070e060f180306010812190201 72
    0x200090114125a114010000d148014500c680c8a1000481d85141c0c0c0d441400680e02c011201c94a00c0c1e008100701c07900624088018124182d0103a0289800d800140ea070304503010b11400d02e0160071400810302c5001c500d00445030b04042c00c04c2c29555071040060b01401b400c44000d42c0701c0102400b440d1030002200030300c0d69030312850300f0a000b80217000c20b503564400140c0b60341c0407001895206091a00154203503c1c00000c480c102c0c1e81c8070031038a183c4008002c5a0745140b034010404010006c40780e02c40c01101d155400035101401c074100001800c1071800042002d404903030103c03158590009841500981c1e00407050726403181c110000803071403008203101107500e80b01c3e45003079941f402d415080103e40c5003800515101c8061207102c014810038410100205511411600101554600000990194414141d1000d4144042d0909081441170303948000980c200750508011284030408640c013602c1e080046034010549203010b06100302405070403101e184500d00c01d5054045c0316030801403200e40300358 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 212380215 1250 212378965 212379043
    0x106030b060604030b041101021c0509131e02160609060b090a2310050901032105090a050103021c0608010b03071a09010f0e2101050601030c083402030309060a05010503 74
    0x740292b200c000c40b10f0710143c81ca801c00a01c0c00c0c0200c1400c4540340d488142442003407000003030800300c0c04c501c950400c0c41e0700180d4412100300805821442003000003035040e01825840500c5101c02107049400caa0034010407460040001002c0c80c102004ac00340d00c0c00c01400d6081c10003441400f0200380d0390b81003a68120401903480150407000340c800000500c030b40c8044010004810b00b942030a000d14042d801ca0307560080d4000305500010840c1c0400856019038010301030782c10030040034510501c41c2c02e212804c40cbc00340e500c0060165150300443c446443d041c00041c028220210400c80d00138146e03074100c5180c0c000c40c10304505010300076000382c00c2140520748807440800014a5003041901c08035014010b0015480002c00383c0d803c000c0850310540c0031740200c44118015075505480d03540e5504110300706d5101d0b5413500403100072058800307050007a880201d1540143c0b0360010346e80c038145070400f0340c82c08100521101040340340c10f0041c061540c0214800018000030300128000903000305038510b2614203a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 212381465 1250 212380215 212380243
    0xc0804030506041a0106030b06121e0a0204060f05030c040905070c21030614012f03070c0618350f06040c0f0e061219050106030b060604030b04110102 66
    0x10780b00b000108001c2c0341c64035080201440700b94142e80d03030351101901070b1074141440550110050004851544004800c0d80c2d111580b048038164061120000c500300c14804c2d2511000650002400e2100a0700301c03000d16010300341c5142640c514035012000480c5c0e03010300c1c02007201071601c49000c82e01d0141700f641001500303074102c1c821850340e28460791301c0019906196840e2001c2410315100207110050701a0f1142c280006031165090305002d20b41d00c50307138008058180071002590305244548000c0400241c0f0340584244503000e010350070000044c0102081c078200c001800d40101e414003a80e122207148880020200320720054440b12a0320092503c801d65010f0340d054418070064003414040060300c14029070155054604054403034105c0d0011100900030602d03020003080210300c041c00c4c0000250601000030056800303d8040100040030401d0089090fa80d030f039100d4500b0300a12074108149034200d441100c50302d04d00751555030f5050a02e04000c00103801903140704e04140007a4002d12000503c0310701 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 212382715 1250 212381465 212381473
    0x60402130503150603070b090d110a0b16050f010203040302030403110f040f02071403210c0408010608070801060602010204060c020d0c031b030b0a022d070506010e0915040305030105010c08040305 86
    0x40c0348a484102904130344041c420f11580800080240322401110b05003140580841c00001507504c079400e02480807151180c00085080c800100c00a540000e010405242c9010415550003410b2462900c0148030103000e03141d1040040c000007a40001c00c9800322940003441c1d40c445c1c00d580e80001c1c0c1e9110781031207454005041058031000707501c090707005040302d601c1780200340c5402101c4c4007196601d01501800c42401d0f08024401c4030b102140b4018107500100c101480e52500d501ea000840c20f45019910542c0790b540f011a041c0050f030700138040c420140c1014030085061038541400101080700c1000b0280c012103420b00325400340000d83c0c0742000030b1500040110f21101c2500500e0714488490300c02598428140404aa904a418000c541150681c40e040c0700c8003d503440354060940082001c40c40180000700000c4001a0052000c5030080c0a0103580001924080182500b04484145640ca00c0f0f040c840030000003070f40100039281551300c203181801700305402d03180c840580d1003550005002c07442 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 212383965 1250 212382715 212382733
    0x1d040203130b1b031506090301020a050a08090a0b041101021c0e0f1e06032e0302013c090b030f07090e040503040509101710060b040608060402130503 66
    0x300c100001c1c1680c1d10030709034904035603a000c107140881e09101c0d501c6407101c0c1040020849030560740c40c40c07407070302c4900820b1540360040050009003241c1c4114298400f040e4041100c420080d0000400d40d4404501b8000e440855000d40d252201540300510060010954044192040e4420803007100e02d4080740201100040f41030300d0180c0031118800c0075921805001c180a07a40b4107040f41c514100103068020810301100c00c9007004000d0300b000345801800380d48103005410030700034600150240c55034070015030300303103030650000603d821000781050034055072803181e00202038081102210b5036031080b440c800145200d8101181c0180f201ea0080240017000310130300101803101d890481c02074219482d08072903981d98031803440f0034a404031000f80041d0001d01003003110b4100b05600c01d0703000c50105e18416450303454529070200e500c086503500401e68009142c010308001c4c14410240a000c1d9542150304040c80c06400074082c5400810181c052a0046800c0e262401c22a0464010305002415030714256 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 212385215 1250 212383965 212383981
    0x60c0c0d0606181505040c020715031112040201080f090c040504050c06040603060905070318030e0a05060d0b03010e2a030a0605130c0609060509060c07050405010639031d040203 78
    0x9030382080d04c00d0304030420008a038509803050030410461500030342143d03803070201d00a40317a92117192007009158507690a074a04020600061440000881070b244050074140001482246c0080210503011040400e101c400d50b800601101ca40b40c007110041880c1d070b298a0002c3c108002c0c410040c0c0c011602042c081104c07500350700420190303a00600100115560400201e05681e10040050301c0321840d0300302d12004c00d108840359501444081e0180c01801d42e580c1c003080b9075501c000e08001001c2e40c0e4811803140d5140a00071010b81e1410a001040a42c9103400818002607101c0c503843c0382c06008080e8009180c406003c0b00b24055080700041115182031101103d0840560704129041400100c001c02d0841c015844c1d017041c1c503042e41d2101e05010201090200c95449881140c44510030030000103440c1d600c07030081c98003a00b516a035641001c05c20700c042800984014001401804961000382e09140c1c61103072048000b90540390612110b00c1005681081e03002204040b60010700010403c00e000d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 212386465 1250 212385215 212385221
    0x1101320f04084806130209072d050301050102011a10051b03030f0402030601080a110f010e09090304170c09060402161a040b1e04080c070e040f020a05060c0c0d060618 73
    0x30070032010a441285d0760348449020010413210000b0740c01040720000c960004e00c1490000d030020705c040060620320b115080c002098000c4515024002400000140000d580c20b0240580c90f103a40c0d0011071014003000005807081616032581f804010300490032162005110441c5400348011809036507482c20000d50803000b0050403601030307000e413146000009110500040c0d0f81070103504580c0c0380514017031203020080c9074001d842c0800c0c10000001d20701030855840c07040ca5401038000134011550b961078800c0101f41c0464180910580b42c118100d01c00e981d8890148941d8446003c6500503030790f00d00901c0310300c0c20181c9504082c1c200400582e0001804e815040001c2c0511300034084a021a5990328103e00c0d800342a401010540c9c0324031010500148401d80601001a440da00b61011a40c82e00a0410b00c041f049030151952415003080c00c0550800240f4078007c3c04003076400c2d41c070f0b0119120300b4a9a5240852485014504845071901446030503172010019211141e092503644040e0210070010b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 212387715 1250 212386465 212386597
    0x180a090c020f1603110d02100f090b041202040f060b0c03030109050604050403020c0d0c2714071b02030a231b010f1101320f0408 57
    0x1500c500100e050341c5030000a1000907070892108011141421503a41800745c17001c0580d666000740e200c034100401683c2e01640e03159884520703a40c4040400c4000300040040d1240d9010b0308000504010905c039800c0311000142d03c5580540d008a00c0f0382624041c9001000c4a40c482a0000408a43c50301880808001941260b503062b4040c0050740340c1d5010001140c10644008015034403143c2400d2950508415000803240100320f0300756103e039110342e909008505100c070450083c0041c000300b03690b59014414000c880052001d010440c0c80c0144c40601139000300705051199a140b180b5407006c540c0c1c20042004050307401038240c0501c87d03488519204842c5000d00a100340d0040c03216440c9c5509011044601600c0705a680c42d40306e13030081e1003c2d1800f81c581d402c41c44240d502c80d1748002031601202c03942920010341d50001410018200306110301c1e050050a011420b0040c6001c1c000800e1103034054070890408401c0c24012400303c4100e01e1600c0c0440765042030b580d03000c0e9001c50a110b03004140111 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 212388965 1250 212387715 212387717
    0x30f07030c0b0315010f0c02030706020109031b08040608092802040b030c0328060617070803030c03012d030b0105040c0302030610030b2701060f050c0d05180a090c 72
    0x10706107448008112550000b02e84043c030010400811850310361046460880c2018a41030001e4440d0050700131a0800905030001c0001d0307910b43c0c1e122410580c1c40051010201c40c02c500740c40805280342d071185540c0c42148030b900300300010b480c0072459440c4213010040c1700e1908060809247d20401c1e041c845081000c50041e1b00c128584403a0780c48905010a02e050608070040c00b03801240041900041060600003048201044292403000044d245200b40344c003600740d000c02d810720048021107192410700181c008070001d40051051180900c4600d0580e410b5403200c51844000c50403c0460342060b6966111224480300d8030031002040c0f12000740e045040e02c40c143d03014498009031750b01c194140d2100b9500f2640009203001000310407446940180c516400040140c00044400810740007001030152041c0300c4840e40100401907aa003203a6680380e81106814140e09228200354a2602c0d6100403c1d1a01030200002c0c941c03900e6000e40c0018641e40c0c500614455520752240d8440005103c2c000c4844 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 212390215 1250 212388965 212388983
    0x120302060f090c010801030206160204020708030405060c1201060e040f1401150c02030303060d05070e04120306050103050c16030e0d0c031a010b1b01060902030403050c01113402030f0703 82
    0x800400002c1802c0300441d0f010f13120001180d2850b0300b4081c1e41e40c05040b500034182c1c480921040113903184d00061054601654440392a0b007401d04259040040c05420101c1010081100b09501000040920704503440c60600d00c1d4021110710102d4013a2485004000c40940f40030411210001090311080c141d950180d0440d40d280c0c0c000c0c5040d5400321080001039410b0b8003d000040e00d900c1e12082c032200c200d204106a40099960381c0c00601d00c0701c000d40b012265403000d58144590540d0602c0b407240200024a81070003e0304203104013000e584030f24050a078280d03c4105c0003106060288008030310a80d009000d940d450180341c201510003103083c2c001110b128044140f0380040344040b040b0705040c0c8156000382481c11325407070352003400001010a440015505e682c0c0001e20f07035840e44080c43c410782c02926416a00c0205a400d0307800c4800c1185180c0c401c200074045120051410380f0301700307044440c0400a041420007103481c0c1107400c60301c040c025031500c1001005c41061202051203030031207114502d03039 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 212391465 1250 212390215 212390221
    0x312020d02010c0905040515180708280e0a1b050109080607080c0a0c060c12050a05070f0f0903050d0504060f020102160605061804120e0613050415120302060f 70
    0x4a090303d050a15207000524181001e01040c0b4080c3d00043c0c03c48044840402182c03003240101e2a6104900007400010300804200039441e60800500e591103070340d881220400003038012800b41c000b0007841c070744410316584100b040d0310b5450400c01424034641180c5407204404980415260941d000d0150500040500100141c020703400540240140ca03ea151a00c4a59904281c2d00b05504005c604c0070800150840b450301052107032086903401c50099032644156404c1d01040020390b8000b81c0365146041c58035042000740c552008008501000c40d2400c1034229030442400c03242100c550300041c0c0b5500400d291300620941140c000c00032aa070301c1d21010705c12040a9026400c0f4010a07410b288a543d800c0f04000000303016138443d980c0440020014100d074282c1a0006a00503001c40b030447e8007000040450b00001c0e041604002004400c5034920310b0000c0c2d04100b800710307044601c11980695101c1d1100d2042c244000144006440d003c45000908080d1f81002035840340190384601c0180c0340380e808 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 212392715 1250 212391465 212391467
    0x2100f0207020d0c05011404030209040b04030512010b03040309060c0b041b030c1e0602062a124b10080607031a1507120201060815090d0804020a090207020f0402040312020d 76
    0x1d48082729001801040b1603a5603494410700813000520032000c002c000c20624001e48800841c56002e88808440070740c682c500380c500586001040c1e08000140320540c02c0740400922a024a075900983c0540424070002c8991a440741079442500001d10741d2140201c041081e2403c000c1310814580e0000c1030a020359a038860998641c14269100d040d0090075009080507510950481901d030030329551079034942100c0e1100d0700705c000c00513155501560b1548601c1124111a44109045000c0d180c1c0760b42c0c030041031240b51803086d42c500e09803204200359410024400e400300c035490070000d02c1e0b4002503940515220b10003c00509001011402260a00301503218505200340203c4203200020500d91a007582c075155000c80030428140c880443d92030b15004200b0103818044004003243c4286105c81a0030558416030a0840c4030401000f0011001c0411015a032101404402c0f1031008a006980361040c0c000702d000c054a20308001c0d000790000070000200301d01001d200079945003075406d0301c4034071070300c00b40c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 212393965 1250 212392715 212392717
    0x2123c220305040902131a031009060503071205010204030c120b07030b06070201030b03070305100c170907051201200a02010c0206060f30010b150a02100f0207020d0c050114 76
    0xd0006441400b040c0200b41450b80180545444501060b260940c2c072840060701c048a0107d680304000c010082c0a502040080000003400c030b071a8040c00b15030706000c0425030b00d4000d441107041581c0c900740307a581405020b60403a4060350300500c101c0403040e120192100320144c00042110869695030000300054480e00c615141034900900c00740c949103007500110094061007501c0ca5043c0a0342100000181e8100301c07009001038451000b1400c8444004090440e1505200f40c400b000c411a00b00100d6150200e03080c4252001242c00d0090444003154490040400185191050201000c0003040d5280034001e0720100110358000d2044c131120640c02ca0300d03141d094078030582044410303100030360301e162508015489a6040b952131084840c00042400e80c4c40400300006003596480401d0051810004180382280702c0a002e84c2d450a200301c24000d644001018107810250741e904040e400313540341501250a86030f00141040000303445414850110762080c89400c1c08036071140401403580850b00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 212395215 1250 212393965 212394031
    0x141f180c091e030b190c0806010306061103040512030f0f13050d2d0501110301050102070b1303030f05041d06040b0d080409020c150403080f070302123c 67
    0x1201030b10070b16103541c0c0d5001c0007080c040d05641c2880c0450306030051085940c40f0340303040c0c116155620842800d202d00094100c80321b503008101001240c0032100582540001100d0032a03200b0340b6941820070741561140d041d0b000f9050071403070710000091018200000071000e0404044881c48500b000d503a070728100301d40307a0b04211004215450703501c100d81c0c0008a6065803010400c284185842030741041d6102802c413040c4c950015892240400148440d50341040558050281c1013581da107000b4060f5109255044103110041c10404001030700380440e849041913070b00818030340d60011440c0034a03d2010705840d0301210900d000714640403040d00c8601d00589400c01840e00810a180340a0408131480b029503c58031100d40c5074859400300c85844140180168823031400f980d601075941c10304000c0112480d9001e400315003094014400b010f400b441522450390021040715411704201140d0b60450542400940a0440e071820386d42410b140000c3c440c115840340b070008407004c1c980c4007901c1010100b40980 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 212396465 1250 212395215 212395259
    0x305160806070c03120903090305010e010c0203030c0a090308070503120609100311151b0c040c0503060d051c030c140c0c01050d0609020304030e030c0301141f180c09 73
    0x180200b25030901070200580c48500901d000703040d902841150b10280c0d4088031086000400c512010020b22000388508180920700c0c20090000c402c0b070060003992800040c02849241c6030011700003003000d0148140704002c5a001911a07203e0207141800c6840350804190f41201c40307003c00028099143c01015036200d4440c03101c080b070480b4190380355040e98000101c4c1054110248003240403800407004003424800324105c03001502d640c0300c001024140a20220780e10b0050703052140e1180825001000d40354851400d49061440c81000e00b012032070070000410250030400301030003400d6026810b42000c1021b400d00c0e168411a0542080116000d1040e040144560381107801100c84561040c1c000300b04003940d01c00d000c64140d446050480c1280d00035034003100072403601e0300010214181441180f802440440003080310350070344c055180d0303000c40041c458245000e094021030b011110321070008001d440f442c50038030580100550100e008003007440102010450500c4006902028242011b0203d000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 212397715 1250 212396465 212396473
    0x9021c0302070b0c0312040609030906030902060906030c16030201060501021605060301140a030c06021c0503091b03030c01020301030c260d050a031103090d030f020c0a02090606070b1003051608 85
    0xa032501001440e0004e000310101400200900940070740a079002c140540e005406c00100030345503250190442015a010f0018141042c245d8005a0344903410f5402450003520000d035aa0f640b20b4021a4610401c480c5458600d980030900b0b060507415030042c01900c4080e0216802001c02c0c81d00700010340001e2147d154001380400051100b031080d51200340c0680409407010388042d840707507603504864502d50850001680950050140a10002100c03c06100c09007807091031820084040c541f03848040700389104002248031000c071162400c000b2501035460b40b100840d165616864107400f0200d051044100303545403030003040d0036100140c0301440030588210003800d514000c0f02c01640c9030b0700061400c10906a96203610040054450300651080b0700040c0601800c940e170b00c00207002c58003602c00c0301080620500c000ca0780c000002650f05545501224152160f0743c680001900390700c00e608008081401c15001e000c04a85184000d4007035a1240c019111f0054449006098811161140c40d04c03030343c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 212398965 1250 212397715 212397719
    0x60501020c031b01020a0807032a02010f030b010e040906050f07020102190f0e04140603120406020a0f02040e010c02060a0509012d0f0c0c03140f0405091003021309021c030207 77
    0xa461405080b09040c0151000001141c487c040190404502580030500c2e0340348100c083d51103104106421103e80f80305a502c03820fa03400013880d900007400c20310181035550041000a078041c01402d500614001d02c20f0015104628106c0082c0c1010b40d051032014142c000070402e1a0700600940340c03191400708204207401301d58201141c91000c40c00f40103040c070400750400b44076a207560045500c2c00c550030190818a013090700a0528000701090b460040c0d00f820300c4180030030341e40800c04900454025046494060b01400045c000b4208400420080d40c648000000400c0c2c022034450b101d400040802c021a98032035403003600b65404c81d0410140807615001480002c81e04052200000c0f06210b00090607400c008100c20481d000e06c0b000b03101141c083c058407801c25501c007604034540c9840d02e240300c8c24060003003520703081c901442c0a004e11911040c00000d0040d460002e012000359002058464043c001800e0100100501c001c16401010070006444031094941980c204540d415401055854 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 212400215 1250 212398965 212398993
    0xa0804020910030816050c01141c0f09120206130209040609110d05010510170d1b0602030109200a0806040507020a050a0b011d190b060f0a12060501020c03 68
    0x100c40103142c1c00c2880740d03800c400700124007804007800300c1748840402c0c17001120701400c1261400341410551170411038001000d9400a24100c15600702d1403880740340d01d000003080032815025000102c40343c2c41c064940402d0000303120851403011400030403502a241c5039150b100241f00e108034661030294006070443d001c41c0c0054000e50010f841c1500848444404140c0000050704810000700180c1c3d1507034407082440411280d007003890780100181e0b20201401d10313000803815212024060900c0c24000512982500101d07032111026080758071000440da00e42e11154800000c01d8506c08854020440c3d041003014900540212821100b05442c0c0441c0d547e1181c0800001d488000c00c140d0442c0a62901d0300001ba070204001c16640c0d21036032a040103581002600c60800c0f00613031070a0000c101200c10321004450902c000c8081d90f82510020030300640b1800852480e2141d1440c42000c01c100148a4031401e43c4080700e070000a062550070301c135007681c1e40012a41c41206104d102d6240d0800c0300c01085503 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 212401465 1250 212400215 212400229
    0x7020a0f1208060307030c0515040e1806060f0a1a1e1e0403030c1104020d0f050411010e21031b010506040b040509070b130e0717070201051302091b0313060e030a080402 74
    0x1051260590391318060721000382000460007610741c03080790030260300e50070085d40041c43710a034440390940742640c03d0403080c0f001a080d04103600c81c14401c40442c8840712449004423003104d80c030f4990b441903001e030a01d1141c0401910303404080b1805c6041c1c5821080410445810215012a901651403c42403002916010a81403a500c596648207a00304961400c0b0300081c001c014101e225144000381c2d034030f420700f020f0303604035080748290f81080901d407409089030752040c00030030580e40f0341c0d458039001442200c00146144500700c59140e81401544540c1248201504a1803044005540c1400105008000d10003652025206003030940c1003480b05002c00c1481801810f000d44461024044003603807514074465102e802d4a4000000389625000d070102602154042d130011454802080300e0314040c000c041c03014215950003803103040e80c0400b2070341c113144410502050210348016183c1d6810200c1804814800c240011200c8a040200320072903280c2c00300940c5d40b5851286ca03001c00c240d03070310b0b403c00600c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 212402715 1250 212401465 212401489
    0x901031103010b150a02060105090c1603110604060c120c09090f02040f0902070327060c21020706090b030f0402040b120303100f0801022107020a0f1208060307030c05 73
    0x590f684441c0301c1d11964444944500003501d450f00141d940c0741c02c2038000d052582c1604040d000708200c0c0309101d10511402c0807184c074841c1c9414507500300b800d185011903403603614035008c410074400d141c2407000340100c40c2d0214072500b440b610340451030b0611074081002e58a01d05c1c520f070302181c00c4207420080410f003038202204100032007100624058880448068081d450f401c08030340c0355404a02c0030b00b0035030440a1199140d6500c180e0a0032070461150b0f0001d4090301c5d0160f18104011008008100704488480c102c140400c08403c0d08003005050000b99155154443d0000045805400050710410ba074200c0f401415a0707007413004281d807503400b80303c054104c0e101041e0300183c002c16580b0800d4018005140601c1e45d40a140d00400c0c60714114108804007034120600c0c0ba4410019001200810045410a0f0307042c1511856a65558031041c0d00346903100701c0141c10165000c400702c0030843c203140318008200480d25145525180c51062595034142c0d800010701d049820001480580f511601c4101 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 212403965 1250 212402715 212402719
    0x1240e0a05040203040b18150c0a030e06160e060403022103071709030c040b10030e0f01020c34030602131a070c060216030b0a061a1206010c0209010311 67
    0x480075640c10205049a104480507107100c1a08000e010031b080e28880e8440a4142110003000c3e580e40559031000c0c080c0c0098139070400c1e02d80005100c0c0016002e0380105c42202030503810b8806501d40481e039081c2a000c00091880055081e25450788680f400e001524107030390700501281d541e501030b940410f6407141c140d0750509040c401031100d540014002c101604480c00036039405030701c440c000030515141c02d03e040c521074807c600b804001070940d10340d0244210703484080e15011174444482038580382000140001070134194000204a030418800181c031410313110040d4907401080b2b1200609200c00000022441c00151039130f00204082100e6402408203000040e00b50240c40c3d5440f4490842c044203c049268002c030007188850500c4401c0302e01c1001404070380054001155003410840b40c6c201d03180002050412220701003600c141c40c80d8041c502900c4104000b200c01e4586801e1050240c01540c2ca1800407008580041c24030751040b84940440c0b5809001001941d086507240d00b40100100c09042d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 212405215 1250 212403965 212403979
    0x1505062b09060603030c0317041e02010c0b0c07110a03050601060503090c0901030309030b0a1a1507050105070e03100b0303091c020901171501080304030f030903060e031201240e 78
    0x40081030b614882c241c0150712070303121621800414580903200c0c1480204d41501402d0340000c0001050114845827080c0d0000800040d02000910040e1191a801c0f1400f034007140148040240010401f8001d081c031501404103442c0c5c042d00c1404001210a0500000745103801032001001841c0c007501c09150001882005c1e54640c0252074045914104260700903000100003460420a2066240640d60400284007082c003943c40b0a114034810088c170182c4060041412102c10400901d03400290744c042c5a0040c000c2c4203d040c50b2038024804040c0e6801c041c401c1c047e512440100c00c029120302204080064003a6080c41003c0c02084003480691454541641140c1216001030f41c1300ca41043c00ba002c042d83da80c03c10a444070f141c81c6000403508194152001040c014008000000150b81c00c503540120070101100c0c01e403508a582c0e083c142d20082c0450705144403520740b000c010000d007659107a500910201a82e030ba003241e04030303d2000007440031100f103002c0c1c00d0720b03606110b600000d01000c005031480c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 212406465 1250 212405215 212405231
    0x1e0408010903020705090a0b0a05100909050901020c010b03030a020706050d02070803040b0f22061109030712020f012604060204050d080705120423031009061505062b 73
    0x150035a50101c2003140181c10010040c80340b0700e48103000c1034001c01400c40c00c01c8901071000106804d45028001d0383d20802c0e182000002261140301da440192000c080301b40710504001030790a000c1d4005405040d015403c0c1050010b2074207000081c1d80709500301c1c0c0d0087c80c48610700702d004d40d20f40c1c3c000c4280c1000c0079000c2251101203600d04005500541c8590340350700d100e24240b44140307440031010340091040e03804020f8019a051109d40926961900f01e1030018520724040d00d41c00c184c3c4280140c52703425014030000011485010007c1c50004c5000351740d40d2444640d20001111a0842d280c130b41c41041c84520540e2a00d030001600d15584148540c000615040e10703500042c18014004070120303032014002034103804010341846156018810003910504107400c1880301c5552010003030307040341d035800c180c480d2480c5c940e000c01c880034614440d075a040001e1403850900001500c044011202034034a880f800103142d0a11501329082c0c030343c41c0400360064030009109801c00c080d0641200b0b8006840d0015 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 212407715 1250 212406465 212406479
    0x60f060303120e0d0f08092803020d230a03090213090512070b07110703080318160506160503130f0e0106020102031504240905071d061e04 61
    0x11080a540651542100b440d010b40740002a40c0d01d02c45001866000030101d01c10060f0403041103076030307a40b49050501041d640d511000349022840728804200d5050b071889042d490b40308014480e6a540240d0940b59010303c8001700340e0705010014104400d54100249980030800aa00500002c410030b144c0070690108a8000840d4070034614403403070080703603900601010044104002d41d40e0108940015041c0001d607150400110310042112090044020507031241c0d0f0700500042c0f0203194014a00da40b83d0030600d0340f00400c130444289410981c851224240b180b903516000520451720000d18051810070704070410130a022a004c0126031903c028403140200d15254007800000d080305401055459180042103426440c0684c4400d003903920400c240b00c5107919906400c40062801d40e030114031070034824034120f42050207079843ca00e103071040c0d040450400200e40026000b01e110b0b55a4821a0030903a5250798842400e244185d809481002004003007640508008411030151356142d06155039484 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 212408965 1250 212407715 212407721
    0x901020c1209040b04090f030804080f04030809040b040504050703021e0a12050607170402060313020909010c080c0a1d01031509062909040e0f03070605041509030203040b0304060f 79
    0x80303001c03004004500021541094418642d06413022281400042031039114500c840c003003944003404101080b0000780070710401b002120045d480010a1990b282d9580c24a100540c01c41a0b10030312990800c080c00c0740ea450180640303401190840064800382e45964200300640c0c50005041e0148414074039108059581c604a0500410b003100440103810500c4c54120f0070407100612183c140640c202c00e8000000c416000c1542c05a4191403c9507640c541a40d8400072042000c4020361000002c4100301140030b064111144480752515005c85982b10501d15a115000b40e0200e080003841a210100840c0c4004860501c401018180000e0000a880105000308120313001442c0464446804010402e5084010720b031421510320400185260a04a04a1403180c501841d00c142e07290842c0307000080741804502110744585044030ba031102c080c5001e1000e000300321001c0c2c40b0b07100a01d5488021003e503004240115500d540a03510703107401c280148090341c001400940c2e00750b50f00c846401280580f84 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 212410071 1106 212408965 212408983
    0x5030406090c23030706051603030203040606081911030c18060103060513140903030f060d03090905040b06030d0f02030d020d0f020310170a030c0b0901020c 69
    0x1040055540c802c0350001c1d0301e041c00b0700d00d003400003081000a402c0128402d40c180c81c042c5a403103c0540c0d107401034042044030351140c0000000002e11a074011a0300901c68103002030055100c2c003159103808107103a400011600344441e01c1081c4014101c60800d0341c0021802006900242d1001c200c2c03029040501e01070716003806002c2881d9a00941000001d0280901885000c00314107070f011000e41300c0090010341041110000c2854100080216481403100f50640c0c086d503114181440100700d52030b0019000c000d03a001d4045482500360094501881c01507221003840d0504208050510200742d4454084c0112110840d40c420f4010040d100308024215006884054510100c0041e02c90542201a45440041009903440342d8092002c280d4a1100314150849075000603da42d80c01e4508000c2c0100e13080101000010f6680d280c4c069000b40f00030000340c1044454501a494a5021 = true := by decide +kernel

theorem cover : BRFrame.Cov 212230215 212410071 := by
  have h0 := BRFrame.cov_init 212230215
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 212230215 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 212230215 ≤ n) (h2 : n < 212410071) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
