-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3925
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:04:16.621114+00:00
-- url     : https://prove2.me/submissions/2f8fa02e-f1b6-4a51-a039-e47ae6d1306a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 705755395 ≤ n < 705935251 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 705756645 1250 705755395 705755423
    0x11706151c082107020304031514040807060b030106050f0d0320010905071a04052202180423180a0b010305031210080a0816050d050c0d020a050c010807050d020a020109 74
    0xa5051140784c041c1d03016a0003541400e003543c031424568030f041c21526200302c1da20500d19802c0b120b01b82106200b28010900a138841444c1d040080980e810300d48181c0c07190f4502081888141d60301507550701d901070140d071210503500d21840c0a440c5564030b80f05845c44441518000c9034114815040b040d21030348a502558445503951149401d0710080100e05080381209210501c100e0501d07591240d5070b0343c01e4048030b03824070004a80d030700201c0c0c4c4258081019800e01507000016800d141c068009003c4003001a12100045545500d014480203032000010b414041c84c0b00084010811503103a4064001d248603c0782e5a491603c140d5a80c44031141d0707840b117510400007078a00074032540c641041b51034030000703001161a02d54030024664030603019103481e810811014804240100308440b641c2405807540c6a844003010350052812001c94404021540302c0e14170240090000708000000940a003081c80f100c0c0c840c84015502801015180a0820310115018070100d40c150410004030b8058040c001d4250 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 705757895 1250 705756645 705756697
    0x30b030a020d02060a02120f070209070c200a1e06030e060702150c0d0906060501020601090204050a1503021c09031b030e0d0804050d0b0f011706151c08 67
    0x1165140000e54400e04014240000d130a101c0c00400001a951065030240d5201000e84480e5800c24000540e400034049003140841c108510304580110003403d00784400c03819990307a60341808500000f5481c01e50301045840c01600d4026a100c043c120030442d0807140215900c4401c43c05409206040009041c40710380b614404001c80c41034000c060070341c00361154140c8109113480540002d000420186003c00c0250f45401e6a4461260305904c65100401d00300c1c50040024034041c41078000e010039601c1008100826920340c11300b40201d4020760541c4079107044106041c0d009010b08012440c0040c001140c3e101d95002a03840300c84602e12a450300c0c4001e00b107540c501f80d540c10b21040b00802052100304040d54900c2d0551001c903146224108651400d03854901141c030440e50401d0132125192540c1c14440031504c40c150103400b43c0742120103103c0c3c01b07070b40b004826a5550083c00e15802400d48200707914580e26201e030003600e001041700103424540150700d4180d09030b80c8640440020005500d180500207 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 705759145 1250 705757895 705757903
    0x1406060301050117100b2b020306060909060d0b13050d0509010f1b050d1701140906060f07020a030b06040b0108040c06051b06010e07020d09030203060106080402030f01060e07030b03 80
    0x3075001070f501d00100c07102c5651404c0c0002809018100c022420350000107482c0407500003808501c044840454003106d94080740412203418903106a007050043c0200721407611070109032511650300f100e0584007a00c685c00814941141c00030040d1030f22405000700881e040c14030364401890351043c0300b200c16901400d00e00321080d000705181c440c00103a034080700e541454402c14810748488000c044d20b43c0034148659401c0e103046003655103c0042102240f100c5034034000700454a00500c0680100c42003003903608005014010f0040c619441018089450445080c0c140252054aa40500103c40c20382d12410074811a0000300d458500c104d0400c0742014695120321031503030103103074800900b81010b400d0400540d8540c000d580b98003080140112101c10041042080798002d10000c00c080c4410b00300300078000d041c07000c507111420612024402c10401a1400a002411201e40f03140c4101c0c0b649075440000e05240008040042c03540c20310030f02059529140008501800e8507850400035256024149503c03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 705760395 1250 705759145 705759149
    0x303060f09060e13060b030a0b160207050a1e03150522050a021003140f07020d050a0e091302030a05070e22080d0e0f06010626041205040801020a031406060301 70
    0x460b220180400c84141c004c020440d5400e110345004510906020b010928004da84042645c100505005203c520b071296074100911644030f1000d446c5141c02d10020175040c038602e1290302e0710111030b140000c4040c02145c500d0780185a20010340b81100b020401000082c090950300384d81407200641c59600001d0280e10b03440500d581c004080c1c18000a00c3d020031446100144152003030607210851610309140e40140a442081e4160006109061403c002403600b90515401414003004010114070755402400c05c200800c01221200c00700c0e6200c80e2220071200c1e120700000d406200f0012b68004108001c99040256140e0081d0901c56989101e800310240c4104501c90b80403a0100718a00701040d501c40043c07060042c00b08012425846000c180fd1502814900c442c0c81d5410200042c4410b40d030001109040c00d82220843e90300050000300e9606050000c0c00091090190401c150252806601690000e001c2d1030000c40d2541034024000d4041e1038144010402c0e90000b400040e81c0f8940103003a281 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 705761645 1250 705760395 705760409
    0x60a050f07020a0b07050f071a01090b1804150e060a05060102030a09510f3f061a0c12030a020c0613110102010b1c0615030303060f0906 60
    0x41c5940030348138402d211034050043c80030403004011205560340200c0080800b030784070314408400c60004980b0403201d4101a00002089400c08400920968404102c20700303d4103140310082594a0b6403500c5c48103110050301c2e41d185c030f0b400c00007410205500450480e125459100b400e00c50365850308012a1a446446504400700d5950503003400017000154294400080c00c1512041180002080e801c8581c103030420340e80c01490302029142c101c1a82c01900340350300110b08001d030003146182c1c0c02410541c00900000c0701744d11015080c20040702c25519602019100c4101c4200508907801c061003d41541d018061182405c901440c00c80401007085400d500c0c0f40002904006600f110000426400a000318011980034031140c50075081c14403095004ac4a685000528441e43d80313090764400043c0c4000c0303070540e407508090f1011b03522020030054180600c88904500b5401078a4010000c291301c04e02c9103030414616070040b04140e010707449001a40d418400b001c00582d52802c03420140d4801d406840 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 705762895 1250 705761645 705761653
    0x31501020706050d15170616030204080706030f021215010906090815190c0302121f090c090e16021e07090207020105090306041506140d020d03090e09060a050f0702 72
    0x408040c517610502d109480c6800e914105a5101c840301c441c0c00c0c6001e5804010740090051124080d001d030a00042000c480c1420f50038140381c501520348403609482110300703064807502c0c9005914510780c110340841d90100c00010340c03030400b2103c1d5044d8070141548513000c640c942c40041036090180d0503c10840d41580000c040c106804e1611180c0c011000d860140402007643e01c03000c01d000140201030340118941e40060311440340110a203209a80989490003a10b0b0001c19000d5840001f0303d44410b4440100703000c690185500b2080b030b9100d40b03d40c880400b403d00d043c1400640e10156120b010042c0d030395030844104444594010a041004046148482d03100940c100700f070b0105600a449518014100701e400c00d2840c802103420300c0012541103850800000c0b5041c01017105116a9010b070080c001405881000300000c140200c801c404080d1164140001440815200c0c400300005007096601180b00b5040c00c544169443d401501c000b6500da0034040042c010281d011900361055419038010 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 705764145 1250 705762895 705762907
    0x100c0b04170702090f10050d0305030402100e220c020303010807060f0c0605072c0d080d021936060309150203090f1b0609060c0c0301050a0203150102070605 69
    0x5000c0220000032800c5241c903042c001c00d40580d0380c800380a4843d640d1048030179210315007034804840e000510341055205400c0b1071030071404a540401500d0384280c0c103440e481800c0080010585e86d58003401e142d00c0c1d100640180032050801c0e890310350701d080003a00c8820320075501c14107026a1640000d00841900d41d0125008002280c8a015110f16076450f50600f0440c5078515107405099403411128440400c48000300160088121480c20380102c040e0403030f440e8805003920000c3e14441140c40b0103000c0d01800709984c00c81141c6a411a0060101c000c400e20890011020180c92540a003041d48031445400200f000b003840100e0300d00300c41840c0003c00003005400d21205070020306141d6429103d00f050400c5a000302803651000b1401000c044d401000c1c075014207505186004850103109901c2da8510348600e03001c1d100c90302039a80c6000103e07001b54688001e0b800ca64504158044110360544c2010180044021980d00850090390013100752808100764400590340d40101c0d10844002600410903 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 705765395 1250 705764145 705764153
    0xc1208070f030318122601060311190e12150103060c030b030d021c090e0711151302130e1b0d02062802161a071401050105100c0b04 58
    0x1c104003440790400040210300d0703001d5200c0010152034202d43d0030442c0e000e59480310350041e40b40003501400c40e900009403110707040c50281038841803151700306044e114201c1e41203c1043c4000d0b5030301f0221a445004902c5020b000c02003041c41c030054072601462000d404201c80c00000309001180300703d890a46801a441c580e0b0340d000600340d00c0101e40c20103070764024040440d682400600003140c100d0b4000c01c00c2e0110508500040c611002011050144075601081845103640c40321364804c035a0f05000292500e40ca0074141080412407038140385e0b184c0b80040002e02e19198150080c518001d81e00c40351517a040b1101e0b40211a8003407802c1c0c6d03040c0d00104100c0c150903200c1440e1311b001c0d01c02401c4801418900d40c040390a41d08444070303c80c900c0c5c240c100c02003105101c0c16840b144541d014030040001400106001c412910300d8000d540305d1140c59007105d1905803050089900b82988610288902e80120076024020f00302805070358402c81d081441c4c0b440d56882026a0400b40341c0003201040d194603141c2d1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 705766645 1250 705765395 705765413
    0x6040b060c03120709171c050403020f0d060e16060e18040215090d0f0b070819022a0c040e07061d120a03020f01050c0703050a050319180c120807 64
    0x8020204203c024000c640340d052004082582c040000042c0300740030603100087c40c031856004001c1c1c1003010070b020800145e503902c2d40d82d0700c0400c01520a1440e48800b4141000138140c22a81c2080b01d12850001c00c0c4a41d61040d5918100c0d5410350b50400721403e550100912090303801c89600710f040354940031a015240c0b501c80d04080c40a06282c544c90b01c08040c02150900441240079205a101d00140703005210003050b41c180d00403580c1c40c2c040401d14010700c19680001c100000900d0072940425811901f46c5210701d85400c000d640d00d850307803040544d51440c03982d60390464982800341d42440032f55010b450000491409072082c544030440100d507440e0454030b00080000b0216030000f0581035200e000b03c0b050149554032070090b400b810602201c0141d060079900080c00741c50741c1d00b01c00c00c03107007001c40d620500b5180141c0369440c00725560745900c00841c103010410101142100d150038a460400310180c0e032000400c900c200001c410303803075031001911160000204050000c4804202c6040007aa442c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 705767895 1250 705766645 705766651
    0x6090e060a03110405090a060c02010903090503012a0201020c061513060821090a03030305061e0306150d1202011a0910050f190905060a090218010809121206040b060c0312 75
    0x1412516207c600b82c50b60703030030b440010320300e903000d83d541c0e0300d000d4181544803c600c0080c103000d41c002d124035130541040348101f07900c40e40c0000d6003600c02c0340e000c0ba5092003074046658041c480422034001341803c0a8100828141e40e807111700c22440c2c078500b07000031100d80c00381d201140e0390308000e0109032000c41030300c820114903c0750f00740c40c1d510104028095030392001040800356000c0c0c1d50018461a0900500100040304050082c41c480c10b81d07801059035800185a59021412042c8000700b8841c031004907002903244032008007a07030300c1031906500580e4154003081070402644158080700e00c00c1c4050014200098505986000444a042c0403c2c20101c40e1508800c0001d4103180d030b5400075400c04008115590042c800480d101c03414060503117000050340300513110940e4114a800c9100d1120705101003080e603914140221100065210714043c0109841402240c0ca000e543d050002c12080054804481d0607205515100d280300690034910141c9120400c41d00c02585081100300c66079a01039001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 705769145 1250 705767895 705767911
    0x120903070f0909032307020d080408060a240e0c030c0f030106050903010b09070e0d030e0d030e041d030406030e1e0307110f030703020d0602120106090e060a03110405 73
    0x101800060845085505078001e0049000c009a14111481c0060442c0303154070b5036501c42c10b0f80140010040340c41c8402c03104066130441d95440054502e1500ca40603001e513901c040401c0c003405003008500e64164000383c0c10013800034612150356040c0110200200c4440c0a0b0b21070041702c86000420904120b40110382110b40101d40500740315003985007008950098000d1000182c0100b44545a42400d00540c4004402103903200ca039403400c410002c080c80d40000000b80701d03450001c42a420b042c020005440c0000010f0150fa40505030703414094090714400020500540c54a441031103086495110b43e41212050b4000e10303d403a2405200b00d0241c20b880480079005c0c000e1802c2a01c40724200355003024407640c00005140c40e80900d003403079104540c8117481d540c021110a0041c900998020400c034060b40d60440d5070b40340c86489414503400a000391311460380040440c3c00041400d035000808001225911404048203a465409201e00c103101440000c00421640125020300d01d0b164114070b40c4201d01c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 705770395 1250 705769145 705769153
    0x9050712050d080c12190f020d200a08131106360109092d0504170705030d0c21020c0d0207050d0f02220605090711120903 54
    0x54409a0446a14485040710180d0008045604064220700c003aa800640e05040c0b40c00c00000c0007211140f408010711150f0704124090840d003000307040e6448086400c1162104540380e900003d1010010056400040102ca11404401c0c00d5005c0200403070720800703466aa0b180281d00e602c1300c40c450010060380d040312202c2450014102c25207405000c0e0000c4014a9144030100003691080c0203c0e0707400c05501c0d1400c6030301130a0344915982080c1110120385c0c986000044400b5001c1e516120304008443c0c108130303010003582c103200440c416040340340200c1c0150001000092484503294203403140500c0285030340c00c04e00480030500e11070390021410f14180d0601c036002c4002c08103520400c03510503900120003540800c0038002c6520410156201c00c0f114001003201500341400109000c0c400b28000b81100c540324058000c548600151041f0525008800b041c403000e20103010700070740b000d0700441f0b00130b040c0d2000081c4203a20a8100049a00004015181403004c2030201d40144d44001906600351013 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 705771645 1250 705770395 705770399
    0x1110412240903031401170703030503190504060b010809070e0114010909020a02010e1903021507021c0207081b0618011e021c11030f0702270402120f10090507 70
    0x310742c0690108a80b00e59000914541c49012030880440f06070460f4200d5a086c80365a0703d0440d00003424419070340c1600b0120380300d0740e0302c07103034a180c0950710761200a00c942010300f8801000829000020359490980f9400f41076550705c00044c1d55000b1501c0b5000300640304000400042c0a100c41c410007518041c50f04601050322003a001c000d903030015a00c0300050703549000d800401102804030b4040c034605103560b40700c1500ca50300d0003507855826140b080c00303140744e40f808214114000c10500612040b1410a48089880d40c14080c1d01d684462040c4c10490240380b00705080d8625000080300a108001c14250401400703039642188032201d1198981070002c08185258009000216400c114840d54000c00340c9035045820703250a00c0102e80080c8c2404686900052901c401206072400c01c0441e080154490f125400020301e00e00881030440207040030f180040341c1d241174190005100307500a9909201301040c554001d0382e038403181c5514400a41004030900e507003130700d80d030024000300e40200100c804040d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 705772895 1250 705771645 705771713
    0x4051501122714062a0c010605030d050a0f020d0c0f020102100501090b040e0d021c0509060304060e0c030718020f0d060b19080412110a06050a0e01110412 68
    0x1418110140c0c0c22060001604082140402585501039901e01d01c14100b1015901c140e5021400d2071701c2001041000709496010602c01d43c0540b000301030080c02c46d401c14540750f80c050842e07801100743e0400210300b00410b0590f00d0000a210361001ca1550f05d00040c100d0310340307a01002c541c56040c103e0440c0140c000101e460500e5000c0c0d00d01a11034820001200c00030720040000f2580440c02011103038000040c4101000d030045204019500398140c41105200e04001c1200c0a2141095003540114040240401e000596200050422110080700d01400c0c0c000105641c8003960311401c0390101e080c0d042c81103900581c1d0043c1907601041c0080a05210328920401c0540390680c00c00c410300a008940e0411078502d40f48180c0c00c40e9214140840075041035140c825507100b048410100b80f0001d45120807502c04100f14445446420480030085401c2c40c1c03500c0c0300945201c40c0c00c80749943c20803101c5400000d03401c0c1150b00315959907482c15100c05071950352203040b035a81d1072543d10190741c0d000b5a00d440 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 705774145 1250 705772895 705772961
    0x2030703020921011505090a0c090b03040b100e06150a02010e070b1e0c030315010e06130e0c27040209060f120c0403020f09060418050c0405150112 65
    0x1450700f40904481d8140d4001c815007110891070418100040310364003002551503040746150042e61041000c14460801e18058840000f113a002e2824054000200070a20408800703030350140992041c4071001c40c0d583c40e0300030350f98201551a03e500c01440d0240d0380f08003c5a0303004000c00700346c900001c91a4040003003058100400d90f48544485640019150a9031038840d1a0f080c030345041d480306c04c0c10001c03441800395407808000c2c0082941c01c070341000309000d80c3c020f160400304440c004040542e2192008020114501140700301d8000e441410040343e40c80034440c09560780c1d901f20404170000b4442e03681030b030a800c0352000d260a40040d4200000e412170303200d800040c50000e00c20207056070340307078402040c2c010303441d600510880511809000900040c0e0790030308003884101044658401c2a140d9000203001008011001c2d03a20704203c039240350400c040840e2555012104960410441e5908504403c241d05044055800a141c034146c04ea03440e90b655002207000380d0f09410f04040c0200c410b20003a94 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 705775395 1250 705774145 705774169
    0xe12070306050103060506090412110307021309060b030c01020c011b08040b181e0607020a090e07050306060a0e0610031407050306130b031e010e0d05090307090c020a06020307030209 80
    0x301e10b071a200140306100fa280101343c1c01800540b004c01b01e914058a41c1c007180f050158010041003c0044030140e081d13420416501c1d0650014404651481d5801e0600002c0116070011150070b0704200310a607180c41d01043d04060600107070043c11950b00440011190501c050700030041e2004080243c1d004500c0c0f50014101400005400b50b43e50026a109802c103281d1a0f907282e440303001c03070a00181d00c1c415041c2244074101c00940f982601c41c801440002c0c41e541854002c5202d0511340981140c203620000b411401300d44040d01594655264002070105800880c001c0140c0c074800c07600441c03000e0402108080f038036031442c600042c1104e40b030f441c021408081074a5480004401005100d1940341036200d07000c0860040c40100903109200300801d450f80a6400303000340c86209080030f0b64042c0402e420500907841c201050715240e44605c500500507410a49515000344a2070340040742c0408144110300240219400514000407913907500400382d8001005681096028420a905500d5038030075585 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 705776645 1250 705775395 705775403
    0x6030605040501020c1e07151e08010f14030607050304050f1b15070c1401020c04050a09060b0901080c060315331e0f0c03040b09090a1b0e120703 64
    0x180c2c44004135007003031415004071001d055a00107038500a00682d400a4441c0032908234282c0c5021604250206840c5000364182c2c88180c808048181030809070b10001036816900703c0c403440060240ca0306603803039119005c080001d030903a1220011413540350191000d9170b8468454011602069019030314642807070708200c1c1155450552440c90506407400c10700c20b01c1342b039a40a5900b07003407007015101c2d407000e103050744912441c04410303640d4540c050744288040e40003503101900c2030200d401c0103020070005219082c0241c030504e2801340d18107818170f0105038160488001381c0040100003c1c0c8810042540e00141c85030b114050314101e80c402645402c216140071900d202c524400c01034480c12101c0b510300407019040580c0000b00802c204c52040003074030050301c0040d180d07829110030180007850000d00c14013103d0344080c400403c00044500c030080041c05c0c2408190f0b0845a15203900303110000780d49400c1c03441480d4080112019401a1140200c1e07201402d004181501c0b6001c1e4032640c50402c00c490300251 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 705777895 1250 705776645 705776647
    0x111b0c150a030b0405091c050417030903070b1306180e01080d030e0c012307060203010f091b050405010e1f0c030e09060105090d110405070c02010f02210c010603060504050102 77
    0x1d8040c0360144107140d00c0440c02c1d5800c3c025490404501a2160340c2101c0c8840031080e07404a20f1126803194081e1005005801c1c19110000c1240c0001a540d40040640521900c2070640200e0722610002c26581104034007007010590781d00300802030f11500c480c59050300d58842c2c44540000c0380c41c4030b107113442e000f000d40102810728910b00c000001e0603548403c0c480c2da6958003100b0706082c640d074001d20081d000b68079003010400d410b03c0c0c4100c2070414452110068850b500200010a1014942c01d00c44101c070180e41003040007800c1c0406101c1201100100080410000c1c001048254042d4070b51017a6050024a07440761890390084d5040340d6036654001100040c02003040d0002c043d00a000c1080c45030b007c442c0c408076440d041c00024890f110754281a4040c5520400c42010011440d0000c1c64400000700b00703004501d400314008140103021344050340014a50300c050500341e0300224014082c01580c1d1a026000d100907130880e4000d41c0004031041031596078041c0000410100e100d4175001c0e03403040d4005 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 705779145 1250 705777895 705777907
    0x31c230c1501030b101a0a02030c0610061206060203040e15042904063c0608160809070302040b13090c08011b080a1505190602010609111b0c15 63
    0xc1503c0c4d0017010841c05020300602803101c61601072422050340080103115a0b1040d542c1e10490850050310181c80c8944038940501c40d101c09110b240800780d5032941d640172207215002d800e0201360703045440f401000da08200700c281b2406200c0510700354021001914000d4507411440440e00b00c0d20000786100c443c00200881070300f09a00e40e52030f0f2005c1c403003c490a010f02c0c1c1c00c0910050840c1b40c01717480d40e019103011890840b8540040099800c05400f0010001111907450744041c05810003100c8a1481c0c007401d008006035030b8000e041c2c2c180215030082c001c0860354115400d204c003c0c50041c0c011640141c000d240c00c0d08800c0c950180c812030303600c1907003284010780c60201c11a003505e841040070902c035984a800d440c105603001c20310350b51003142c40901250781020032000c0480001c41d50040d40e00720616070300425010b829001100200c90f165402002520341c1c594845040320801a00d00d01c1d41f0804110305c00c980201c0f2801400d00001c0e8009641c3c01d441e003540026404031042038100b10100c00440c107 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 705780395 1250 705779145 705779153
    0x515010501110f06060904031106160e0402030f070c02030f070602100f090b0c090a0302151b0712150204171b09060d120e190302031c230c150103 64
    0x1840d440020340100a00c04800b490601c651071340320080c9514080c003990400034060511410786c42018942d214103444242c1054841d00d0391507840aa00480810800300c2059801e0074940f0072648a0103c001140c6a01c0d10740c10001c81d81c0440038002030b070341441200200c0a21850a112110080031290024030190603001401000d035001c83c0c01c0c0780b5a952900080d540410000d028060b44100001d10180d40d9140300e0740080d00c1441603400182d0031010242030344121220203002041d402103108803401c600d403290310740c2d1540c03045180140080445041c00003400a1051102020303128103803640076041589811107000160345002100c1c1d0b5990003900d1a640580c0710005110034007105903821200e6141450100c0c420040030840188952204036030f091301c2500c20211350314440c0c0001c015040442d203900303444000c64800d0006034428011049024600c4810030000d4214108545a074101d408008004103c1d920400203480c901b000100800d5414103014401c0795242104855020419415810 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 705781645 1250 705780395 705780407
    0x60807080f01050c0301060c03111203042a050d06240f0f0509010506070f0b0c220e0a05100b1201210c0b181201020d1803050d180515010501 62
    0x30840756a074585414040c001042c001101c2c15248281065900c1c401c0d245400c5940e050008184007950243d112146050a0a04000d502640c01030f84824a0800c2e0b4070958264080e440b03800d103c1c1814240c0041125042881c0023800b41401440f0003e0b506031010241880445890200b8081d45c46001060054900c02d584030409000e0401c542d031171083c1003d0110f9219034060084600c9554046404c40810903a441030f01d2610350300c00c0d0102c00c1801c21400400d501d42020250460b80c0003041d820041840005280400312422074015410544a900f0303148001c00001e0840e070001c00303411901007801e465010007040354807045081d0207843d43c034213503d100f8007920710390900318840d03050040140031038146448001079070f0400f40da456640c140c4080546840208a200366040320055521940100066016003001c4503004010f000250846040f40c4001800d0100200030800074800d107000d47c8a950301000c903a4504070480c070703060010303a01c43c40e1400b110f00480750701c0361000600502080d41c0c004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 705782895 1250 705781645 705781663
    0xf0315080703021f08192403050706030e0c0411190f0f09060e1302090d08180105130b0306041e05040c140a060e0a0b0f0403060510181d0106080708 65
    0x10b03904080444d000300e00a080d5003026000a00c3d5900f2089180c00c401d126602043c925001e460954454822000ca10030440c1014801561a03005091002a41d203010340918072075080c0d103002821030310000c2d030f082000414070f0f80d03003060704003a042c00030a443d0602c03c052070360b4000560300c5001e506060b002000300500c41e0007034520304024821100300059a0481c500448003001111180c50b40983c4010a1000740218507109601440809091040c4550000104050031303203c2e400c07442c0017011000550743d03446240100680700074a400200070008086018607044a4014400303c3c0c041d001d030490201415400501542c455560401d0208000074010100002c01243c2c6070603c680000e440065001d1050740b251005010418800800c650380d4503036001c0c0a402e4060000c0d4403000049400c080313542103400100c03040740c5040c011034400070500c58141c0c100c502120003107101008078090a4040d2a4040c050b8071407024440c1041d5102000b1b00880c40504900001400802c1c80c0c030002c80d00e007003004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 705784145 1250 705782895 705782929
    0x915030a0b2707020a02040510180b0d030c0c1203030e060615030705070f0b04030305010f0902030405100e010902130507030b090c0405010c031e090609170d0f031508070302 76
    0x82c281c001d603058002d42c42046400a08801c1c0306003907540480a03170500822a00095006160030100105400c81030548001c0d00c4240d10f18858100502030b01e50b0888080840c3d0a45c040ca41510b0311001a1049458607101c911035201890201c1d613500340c0a405146044045000c05d89401d41412104001c00025a10034000c0710031410a00600003070038010711000c2e200c04100f0030000f0713044081c00018900d84501644c40f00c1c2100c2185441d0500500070102809140e4405030284800130f1b00324164000d07280280d4001010300500a002391280c001000e80355031f600030315502c0e10072020160f0703202c0240003500c0c0c4003020701080700d00c0c01c518010f0444030000b104030310582210091103c606c0300c6e48150780503901d00b03003060b000c540981c4c1000e983c02c0054888207145803104c03004040b034940e8002c481c0000c41c1c03407540300c034031414bd11084051031915940c510410140d001d10301c3e80c0342c007a104030811681c0c0980c82c10b00191110800101800100142e000000f49511035030f420401c500700741100343e81c000c4178 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 705785395 1250 705784145 705784159
    0x803090303221502030604140f0f090d050a0f0e0d0321022706040b0d0b0a0501050f4305060c041d04030e0a080a110306070e040e01020915030a0b 64
    0x42541c540048452103407043c401c50740d0101c00910940c0740ca034406041881207510710440b600d84440301040f0454115031030b1100384402400715042c1c40000681c1c101c800c0403074440e070342040d003888070460b035180d181402203041202241400341c040c1c65088880030800d001e6501c141895030744240e00094078024410700e00c14030344100a400b0307213440c00c0707a0381003610090b07851076006026224000a00c10300440e005048800c600261031100c0640c5588801d000a03c01d86140720510b556100650b441d01506265590341c89041120200c00c03446062804440541034440490b400009041320308a0701081040c00c0180403008156800e21104022050303100458000040c5130a04164000010103e940d01886850700240302080030140122445040703800e0151025444d40d0740c4404a03642d89001c0001134803c02d08002c1e2040c6c0b981000301e5803520800d1140c69400100a101b030a01c0014060744c6511500c0b95030a00c2090345e40d58440c12104042d14101c0b070700d56201d0030b10b01d0b104d00403500001011841010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 705786645 1250 705785395 705785461
    0x301230708010b03100501032a120605060403150c0c080a02070911130e0415090c14190611030708191101060311040c11061014030f060112030c0803090303 68
    0x30341e0f041000c00d941b4213190100c2c1051000c4440b2080c2039001c0040480d807440c5224407440301d80c3c070060081c0e45056201d0180209603880c410301905100c2c50002901038000101c0d61108550a5003006001c0080b903d0301d800200f9194448400c40d4200b81b0003280180c02c1707030504011000c0e030390240050700400e01d00f49034940442c4a0400300494403510803c00e41c4050307000000d0500c0120200046d24455001c0203100d0f0091a140c0000c010b900c9028007001c41c44002d803030120608010360100c000c150840089020941004800c0d501a40e1840705000c0c0c1d0f1000700b08520004a0801c003421071a1a4080c0200c64400350080180010181140c8841582c0c5000340400200e001c2481011901d04103860000e070016280d04100e462052420180032a84200d500340050f0b01c0c0d076a04400100c602c41c46e064001104800100f41c1c59000d154102d80850348544014040c4001e40c48405420038030034144443c0720b0300c007591040c0301d079042181c80606541020003040041d110754054605013091349015101d5041c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 705787895 1250 705786645 705786661
    0x915080708060402150f0301061e022e020408030c0604020427030f05040510020705040b1c0b07020c03060405072c150f03030403230f0304140301230708010b03 70
    0xa80020301c01380c4945e4000d484050541c508104440e289134244444c0fa0b50703503071520000341a107649200c0034084086030b2011400307100e1010440609540a0907a91040d41d0401402085442000c030030007d41c10381d00300400510160204000e02e2000c100720003a01c03103864a401000101d80200c00c2e0141c0031070603500408091440303036080014955242c00c010251801000c4101e88500690b0801030704240f05500115100742c00044100880d04c003141c00b840b81000100034800044045034044502510050350000040c0d0140c80b132640c054024812980c1448042c0c0010f4505481034405503459001a002440302c41c0084038058401074030b5074210280d82d80c0e1480404440c1a0050085900c00d0744200018450341e600d041115080500408407a15640c41e420154501c401c0701c0c074170103290f00b00814807006481010490072420700400c009542003915101c000b00001c841400d049606540c0c40103590b44144100800328403c00c540007981c540740ca0480700140c103034501078000901815003030081003028 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 705789145 1250 705787895 705787903
    0x11010924110307030f1805150106031808090f04050f0702070806042d021e1e010507020907050c100c030b0a0510050d020c061302010f030e21090306010915080708 71
    0x1c4a044d00e40010b001c080e075900d100c01407400c0c141a030450401d40c48000280480060000c0c04410142c1003a41641d0f42c4140940072290803e5042c99480e40d23517002c1c0e4020030341c0755019204500015040300750401c0000002011a0f404940c244040c0401034203000d13030f09604100b0b07040500301030401803c10703003000d0700c03038903c121044080340801040c0c104440c2141083e95a640c00c1850303002d45809408941003c008000c5001c0c880703814000d065041c40710300b1503070452000c1020302006031111460070290307400703003d034003d4003c020005110f0100802d00404000300901e81c081003c802d00001c2c111807014000b4155004254640e1240d0542c0c0070900c280e55a007805401110103505005940d8800040003101030f0244032545490340c02030200304904043c000e00743c4000d03140f00b607840a81c070740310541050f070403110110000d0929600001a085201311840411f0990102a961080c2848401c2c40080d280c070409030002e080280d01e440095440003485100f40016101440c050008541055401d50391 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 705790395 1250 705789145 705789151
    0xf2c060a270302100f0501050f180103080306120703080703091202211e011401080706020706030207080d0c030b1e060d0906061d010503160602030304060c110109241103 74
    0x807a07810600400e04060080251441c44c50515200b408039591120a00005020901c180c0c0d000e0015610411014a09844281e040f0100c9a914014903401e585645140c2e4000a28440d0440c090442c0420704280420400f03000f94462003055903652500d2400814414241d17101da200304030805840d100503554500a0181c0140c90391190007040e440f0042c041ca13042030001c0e0001c6407120035010040255040d0061400c0c020040320f6203415983c0c651803107998225034801c2c01c0068120180900070356220707070014410300d030040c00070f1824143c07010181001c440a076014080801d945284c08011810b00e9132454890007050b1040e0110640c02d44041000b41c4502c14140031142e913210220000c00c1429032040300503180924104030030104500d91280c1d850028010075102e071044407003d50f07107a100720082c50140d850380c0c1e000c0c505644580c1e403218080c0070300c0001c00080c400c2070381400110b0b4109218030140e542c0611064003003507180e900b00100840b040f0314200c083c2d030b00f80040408001011001c480e0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 705791645 1250 705790395 705790451
    0xe01080c09041e1b14130b0a030605010e090d0e010905040914060702030a180f0302061e181503010b040303050c0f030313030f1e030f2c060a 62
    0x40541e0b61440c0a000c0c4030010b1210340481c400404101c4244204012001c0300028400541000103403a0180032005620340110140d1003d81c820500c10b40008540103420800d00140041c402e0680301d82d60712003690026003100d0303800c00040041000035001082180341050850524196915280300028060031030390054a000e035882d442068100041011140c00d00c03c0c11000f80c2c0c0c46410401e00094803a13012210180c0003c0f0700c24002d9003680b034010602c108455403007021a1905103164280401604041e24410300c140506400c088941c02100091520380002c01c428441c2c06412000c220700440c02c1ea600144544c000d0005200c413a030344000301c85c01c1e2030b0107062907901c03030701540e42c090b18100c00d100c2c071605140070200910280100024000490318402e454004440c2030208080f42e0b21568a400c3c40b0103c00c2c1865032184640c040e80c004281c01c02d1240010480c030440410300280d542184a04401010f80441d40ca110350409000036074102803074000601c01480840d0040300c0b5186413100e005 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 705792895 1250 705791645 705791659
    0x110306100e1512010204030f0b15030726010e07050a090905210705010e06010513020901080c21040b1e091c03020405100804060f0c05030a050403180314070e01080c 72
    0x8403203a59841101010f10031400000c1d551a0b44078130309121010f405c144112001d13005640400c80c0c0c80e00d0f9503d2102d6191000d0018101c0d44c0c41c000750b600c0140d5040354136440c0510f00314110352103180c1c01c5c003d058110038003000400000d8a030009016501215600040079a40b40080d090005440810382c0c00790305541400c030031019000e03907011042030321500c40024020362800c00300500e070740c00114801d4100c440455101da035004415025006034400c0321100c50001c2c4615001401141c07074803025045801c0303126140e50882400d0b60f0001da000d0410b0714140c84c410345a000f040f1800c82d180e20306600c4104640e918000c24184654896910100c01e070301000c100c10341d02e40402e940c031300c00d6069034014140100400601510a040130700700902c1520180c0b80d09081169642d0b420721140210382407183d565445614655469102500522018004500700801030030702c460000d2003450342d840614000c984a961201f500d00c0b1803032824486900100862030ac00c00100040c0d000851401840c0101755a01 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 705794145 1250 705792895 705792931
    0x7030c09090917041806090e190c180212100f1a0d0204060309030e06090a090f09120203030f010e0411060c15010b0a0810030c30110306100e 62
    0x1080281c0d00728041280c810f180800d0001d0410010003201c40c003002122420000c0c180c4a440724401d684e5880c03d9200c107540004c0c18802040500200c1c00e8003107000d101c00908964a40d2100c50313200d074880c40c820f10b2054000c11441030381d4042c40b402582201211090034142480c150002040c5002c511810001800d01c060320303100707615401d04407408015038443c1150794603240c200150003071203000419000a038002100030080d0400b00106c07404420300900b0040002e06c0c201185e005000400595112151100c19000010b4ac20134900d001c3c1c03206540286031607241041d901c140591050744960f1502c1c0e030340c00902001c034614100c1d240100302c5c143c5242d80c3e1200303400300462410500124200182511034000a43c54401401070401c01409603503440882e04d07a0b81070814141c0d120302018003841001601002081d005844040948900104000c0c145102c0401d40d048406010f03003d5901c10f04910310400d4910341400074507130005190020342c041904144280308100d40080180c03e483c0981050 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 705795395 1250 705794145 705794153
    0x60a0c110a150210141b0a2604110306040503030a02070609060926040f0302130b1203040602010c020f060619081b0901060813060b0d08161209060c0605360607030c090909 75
    0x643d445c034808051641100d9400ca034080c0c8c1c1d0740c101140c0c103889071171150984003c03a250120302140a00d07002001035065440ba581038070029440f824044400c203a96000c51400903415008c0c2d100c045006140c0510380741d0103125445407441c8000c9800c207542c1c2d0304010612480c03840300e0500d81983e03015545400054603c00c0104d000f80340d40860181c1c0414059004504850000024415039003958000e01071a1244641070b84d03103541415450095410000000341d55082101c0071180010a4550180d045580d40c02403c2c01c01580420751345118181c501c1ca030fa0107007445600309004200d0741c5407028203032a20038240c0e44480391001c03004044030344825240c0701e5a614020f2046940d40c120501e143d07503651101d030b078020000703458004444152445a0300d4031070b98044c02200c403c036005511904029101540c1e42402000010007803072450258030507500029282441920340000c0102021032400d140030712007440c01000800c00420941080076000310a0340c403034000022550401800310304640f1910f0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 705796645 1250 705795395 705795407
    0x20a0b060d0206031008190f0210031e02030402100f1205040501020c07080c0f09040503030f1f08010c0206010828020a09020a0804030905060a0c110a150210141b0a 72
    0x19503c42c1e0013109010401008203416001c580101c800c4540c8401100d0340742c4245654010301402c000306000b01e240c094100b05010305a20703855480d0000382ca280d50040094903000f0392424014041c0d02108000440c109090718403180e400f00e0502203600186880020100e1000301090415a51603070045410403500b50191003541c0d100c40c081c0c0340c8103901c90074820750b80c81602c075100c1e100e0750001103121401d080441c1494021a0004041c0d440d55031090321482007000c014160764040e260101c0300501f5240e902c41c019018020300030000c1422880381070000e1070b240c010381210b080380e000500d4042d1500026400306413102c503114030100e6005104e0000814429031644445c0c00da07030001a0206290758000d4546206038401c1c0c90f040110340e192024400039002c1c0c0c4409a01080d801c0742c1c0311000c50801c0d5008007442d18010004480161a00c07002c1d241c2003510480500981e1140185000180240c090041d0914003403600c202c0d60f18008003c200500c5000d16001c2501000180b28184544514 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 705797895 1250 705796645 705796669
    0x4140c0a0908100b0a05090906010302010f17010e090d0311221809120203040e070e040e0715030e0a1a040f06110a11031611030a0204061d090d020a0b06 67
    0x8203503294a00c06101d400013404420307184c10300c108500000403a00e803a0031003c1f603016554450052095a00716401950100c0c41403042d00140b0800f5600c28a04104021080340603201040000da518104002c80038a400d101c05400c03c1451f0400d4561001c040d0610705485086000307100d183c003403110910013480d040320300b41c20000d2142640011102500303591780110010921a50b21014102c040c48012a01c034003c2d40900b60800340c83d103001c40c02103486600c02c15142d4100820000354030301d030803c0d40c0303140c41d0f01640101d44140d2010309800c80290180300306413840a149001c1d210003000c075070b03c14803135000484440340030003003500118007408001e40b09003814591040080040d0b2a1041d43c03012140c0110340c0c2c0070005949114038062400c000300944904000400712598100c1e903590395000c0b0380450200c181d800d4850740300d409002d81da0794020b400040104c0002078600075020400f24420030b00003071044105600c07440c81c40014031b0380000c000c2c902a4000081c1c005a850700300004102c00a41 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 705799145 1250 705797895 705797909
    0x60305010609020310060512010b130803070b04150b0306040f0606180902090601090e0a0c020f0d0c060501050604050105120603010207020d080a09050915061b0a030f020c04140c0a09 80
    0x212001146107141c590013103024041c840502035165503a000700b110b040c0310340700391903d9010008004001c80c51484000c0d04999401007214a070541d110086c892460f000000165207081c8440103010500400c118a04807142c6000020720031000b021002c2581d800300a0401444089036100103030a0110030b40c0324402402c020050800130101a460b00d20150500040c103038071400004020811540c091450b003011200d02890411700c942d50082010300502d0710355600c3d0254011102c04815518041c04002181c0d0300c1c64031020126806810500d0440d038058110a000d01c508000c180080d80e049016119102c2c00402c14150030f03520341021038064080c1800c003d41001c4410322840400c02894090034104003161b85124991342d8441c20400c0e061410b45001202028081c8280300038180700008180c0c0d044902401110890350381c000518201d041d550542c0003404e801d4a900d200380d07051251040608007154140000413641d6050310035820003400071074025400145000d6114003c605503002400a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 705800395 1250 705799145 705799151
    0xc02060c0106240306211b0b070b0c070f02090703060317220612200301030f02182401021006030606090c1b080306011e020a11060a140d06030501 64
    0x42c40703115240b00f00510740210002200003034442c0f40c052192044c442100c049185030b4900e801d45802160207100f41c079400340d030801d0b0000500041c041240c0210f200508090194075541c40760303400c100e01c07200b6000d090710301841c00c20060a00400e143d03002c1a805150104c554825985403480709034000c0186501c0142048141901d10075803444c80e102401c4101d0040c0d803110300c101c4800440c403007000c4032405032002203449043c0600e654103465205030b10800c550070302c1d0481c0c000c049400205980003680708482040080d4290401c50070080c5942c9401d6015044a400e1403c2c1317000d6250158400714494500e0b141118000603090b8401c200d86504d20540b55030401030162a81800d0700500280d00802c003400d400c126030108058424000382e4010f050410f05441061031542c1c801c141c80c0d00183c507a0f41040071503001802c54000804006418685940003803a05483c0c52074032101c122102011184541000d20030031440c683c100c10400403000d850b0034100c2e0b84125000710b1800502c5143c00c040d04545c0707 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 705801645 1250 705800395 705800399
    0x11150405010c120525091e0801060608040807150b090a0906180201172a0307020705010801051c060f091a06030303042402041703130801060803040302010c02060c0106 73
    0x1036102c00e800e085a40d0b20009102d408111100035202c095407804241059010420120404142549000169890400403190347c6003241d92450741703015044041703044900710411076600c00b440381c2c0009206500f081c05181c6010384562810340100a4054070324600402c1d6500d011034642e009003482c680050442c006030070301c920720600400071480201d40f00303071504003030512000301007113802011075050b551451102c20800341c4403610709000e400c0e43c00d00f0707031002e400c207034449086e1102c0c006000801a05540700e1500c084000c0c81c2501d140e01490510180d40c0040c48152030710500c154065080050012018009143c4800203080e0300c03690b18102c51504c02c9a071b08101c03008881d88230710711906011002c142c944404240e140c1c807080e50000c1c804071601c050010100c100350f8160044400e5a01e0060600e9540d848076098071820b140c0c0c0e100d00d5040017624000d40b882400d0950007404500000700001401c103003080f03541c2d105901003e81440811504101103607244c0f8101c1b100580c6200003032090503 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 705802895 1250 705801645 705801653
    0xb0304080d1104141309020d08130909030e0405040507030803010803070309050906010827030d14090708060106031a0301111c0c0915050d112a0d111504 67
    0x40c1112041c81425420a1000c850210503401030750705682400c200109115401e01c02c005446501c020015020741c0c039280b1075000b503500c568108800900403546241c2d54a8900803511a9045d05d410100e07420740350511500c0801e500000403092000c0540300002d281e281d03410240d1500ca41c6034001000c1142c0000080f8070580301102401086d440398a8034100e25440f40100000b080044821134001810080010b1180861000c5800c40507003560760741a1801100274254111303808003031400c3c149078a445095980d500110f142c60360104607503014002c418102480241c80d050306104601c101074655035070110900e455090344000301c0c0020000c201020741d01e00303030507255000780b48095020f07200142500c0d540112402440745081d001e66403220f14604049038441040c403e0305015040040c24450f4024990b460b200325420520074007800e07500c07044107544081c00c041e03a480d01c19000818800390040d001c0400115514001100d0820719101c1040320391041c900100d86200e18071503031556040c00280 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 705804145 1250 705802895 705802897
    0x3060501020111120a02030403053f06010807030509030f040f0f1a0327030705070312021609020a020c09010f030b100302010503061504150801090c021c0f090b030408 73
    0x15542030300280700c20500c034030300d202803809091401910207181200161011046034007c0d64807511038101103003091071420021100c4422054030f516115042d0294240704441050103100f081c042855401c00c82c50000d0000700414000307010002030607241d2010664800041c021340b0103802144031001e480e15079442c0d280302140098814901d26180c0c003400420307205241910898840210020343e403071500e0b40d84001c540905520282520500380380c540b03040c2810140020a0310900650042030003608604124443c03010040002c0155031204506102c030854008560003100d003044401038503130081000a074208204102c03031640c00307640300c0000f184180c2c048413400b003640e01480014035030740d5800503414104c2d0703054000030b804101c09100091085c940461400900e69100109030b090640c0c1d80318088004480e10442c1010800c42c00052107080d203a880b440301170905510080272008205603040400800c40e4a101c020042c800041d10303450781c001c038041801081600101741c1d80740383c1801d0079546 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 705805395 1250 705804145 705804149
    0x150d0503040e070903120e03030715021b1609110705060108061b090603011203031116030806040c270b0f0406020c0a031101030b1206010902070c080a08070209150a03030306 76
    0x49102c9040c0420034003407140908809a0360700440c1d03401c00340e2109609459072441c81c00704c030f60b0510080003407034000b603003c080415100201074405030f103901d18500b40a41d011a00811103c01381d0000c1001e88070340e0f08158180007115401000050302c0c038a080202c02181c821004081c0030f901c140000000d409400140c06c42c0301d08807c00c00d0020120040d01c403481c5d1441109070440c0c0c0540b00b40011700c00c880c42c1e07910315000d4078405d080018034100d403220040442c0c2c00080c561a06110341403901300c141038000d000311f40c3c00501100e0811803000001d4002d80001d00301c03085201c64401c1c440c039171030000c00511105005000058421a2100600015603616500500445005008910f0502820f0500ca180e1209481e84440b82034006600040110700802121691139486100b030300700c40c0006001444400d0280c24119000b41c0da48180d400c00d02185030080c0c1c044203075940400200f5004c1170390a800d848402d0b03412540220305031074a501951000d503041a985a002110150000c20507405074041ca00f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 705806645 1250 705805395 705805409
    0xc06020c0f06070c0b18160b0a021006080a060b060c0102040306050727051302040308120f090f0604030305070c290901020a1b0812100914041208150d050304 69
    0x180541d143c20381107480c1221840018080d80d810700c0401d08524182508070b2141c600c8104880c2c00084900031716004030526409400c22890020b0051036450381840702151140c011201404110701c2c0450407079840c103543d840503201913600c41500749540d46880c201c03a60000c134980250344954480c1044401420305440745030103d00c4203662090380a00c8044d4400380702c441c88018040052034203051210351300c11500d4441c1003607420000800064101000b500c1c414400704050b2029141200c0c06a00361100941641800e500040d2001d1407080d0010710030b0340c0242d141c58041510b032608030044d1160303001c483c0700501e111403d80180710202802120140043c0d0a01c0c070b58080c94480006c807500300e11034406030400084221864034a145030040c0302e241c4261203007004a203400b65040c030703071003000308103440042411741103580403c4450014000c003404106249455400d40c1059943c00d40d03032000901d00d000030b01440d200001c00b500300d1521000c58096003e08900c640308a18501552283d11500842c4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 705807895 1250 705806645 705806653
    0xc0c0e070206060d021305060a05061b0705010c0519020f0d03080a0c082a040e07120c02030405180a110c0d1d0303030403080a02090d0c08010f110d0b010c06020c0f 72
    0x1d803080ca020072600f190320745c016004865461340c080b80c800181200600103908816410000541526090000d0030420031140c6481c2c0310b15021406103003802c1981d4412810841181400d201140700801c0e031034041400340000c00050300c418800318500c4441c1780d24a40d404100d1603160014160042202449000841c078100031705c0040c820140c540700820380383d0f0a689011241500d10210b1080158000d0407840592a07085c19034500030032006c2c010481c5d9000c0021001410b244001e020b60080b8050310100d400507504042c14000860705031068040d98940d541c50000101d5010720207a030142001c030b10900016031b652100c0342a01551200070b904032000081c0072a02100151203404181c0c8810000140a585184c40c1e98800706c0e0880406441006404c2c0c0c00c0240911740c1d91020050043c140c4281088150302e85081036a60071200b00c003400320a41820601e034980500c4540c0121241000405000640e0485d440c00498030020baa640040c0b10074400101da0651a05c0051402400f0341108119 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 705809145 1250 705807895 705807901
    0x9010506040e0309040f1b0e090108031e0307030f0507020304050a09020301150309231e0c090a1e06090603020f0102031804021b100606090605090f0906010c0c0e070206 74
    0x407004549101e03404040682051006003002c0c50a50080481e0790000180403070441002108254400c2c1c980721a040401d42c2c0d0341e800845410504241c0d40108601005503007862010540ca990040307064001c4000000c0010001d400503009034445090310b02106d10801c0f55160044000e0354990040c002c0c00e10440d108030000070004035038002c482c103882035040b6501649400c1c580a0740074107240c50080f00c00041180d10303c0e070a60348084402010001d208018620710070003051500759002d9041800c51a50003c848085007500c9003202c09401c080c1c0072400282e00e00760000b40050186128680d280401e06229001908204035048a4240c0c0d00895843ea501a0b40d0b0f401039036684a0410a806c0d600b80700c858001d601c1c90b15a02601052181c00510701d2420703402d094260420400024644609603140024005554858400e00240c9030904110786042140f00001c3c241005411100d48901d0004000906036441803e504501642c130800c540c410707903144e205c401e401c4c0034101c3e002030042c400c80c400 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 705810395 1250 705809145 705809149
    0x5090f01110703020a0b06040207050318130504120f03150b09030106060203131208071e050f07060905120c03030712020d0206041509032102041e05010917010e031209010506 76
    0x2c80390b4a0760f064004103018966607130754a25034a4001e18407a40a9400d12100b408140d05100400840d900751003410a107440860030041518032400d0901500d6241c00c00708800030380702100310040490b40782081d107003415070994211b01603d20381081c01c00402c15420300246c0c0320f030b084001e890200c03070803002071101d43c0c1c807a5802c030303603c1c012111000c4507001504000c21101802030700c14101c0e00c1c010000075103042c020740c0ba0b11a0008625010384000450001301c1d01c207020301444102c00210206001e01419803500784005d01e1900d082c019140302e02e0850140160024041169824803000501901d448000c02d0034046a04500300b0442c50141c02180440d120705403020850510031a03100c8100a080030100a8182c010043c54030b0407030074031002c0c01c44800a0644400d090100030040100544d5841c2070a846508a950300d001c0c030032424044034814042c9a0300074500c2d00a0365148080000e1812521500340d02504641d00c026400e40000550480d01907042000d0501c40c48880300240603548942c02 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 705811645 1250 705810395 705810397
    0x12041202210705010c03030e030f03040b0907060e01031812020a050609160b071511030a0c02060c030402010507170d0504031d1503130b101401080906060409031205090f0111 76
    0x300d841c929400650703050180e5070241d05c29843d000e01919002543d10400241103241d0380c801d00b20501d06d0b4902108200c00c210340806a958800c400f000a0007143c0c0c42c08101400b815a14092181419110258000314190000041221540269a0f01000c4c080200060344075800d840080d2418028000002c10300c510000390200f41507010341d8014410351808e0342c5110240c00c8040308a5a030b1188000a4480904501401c2d03c0c0c560051715070396803420201a088111344c0c0308801c0e281950884020080640c95000640b0f03885030302803c3c00c43c0e4880c518500b901c2c07501500c0440107201300d4017241010a13001c2d16407105120b00c0c42501da00303107007050001d00711650041110780c1d254020f0064043c0b805041942c07020f107400481c03007000e5100740035041e84c0715001c41c01c04440c05120f98001010820811a20101d81c00d901d15081c2084507203410032041c40e68071801d00501c5503010b07035140c511a804042c070a018507084845002e000300528104680d44545601080c4403480b95503081a882c3c07000440307400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 705812895 1250 705811645 705811699
    0x501110339071719090501030e0709150510020c09130506180c030d120b09070c170f031501081510030e03042105060a06050d0204090512041202 63
    0x28080c800d919032001c10380d4081c0d000c034404481d0110f420210f84885400c0101900851000031007a016401d1110b00c010100303062644000c3c105070400c04038040f41e000100d0b080c13099a030340701404102c060700c400b48920312802c50340c4000d0f00705155035250703803000780d0101e0211001c003012140b40c540c581b2030515080002d44284c1020309950030860106200c00404402d1002c1703126194143c0b2070300300e03e01c0700007410b145d0712000520120311030249983e0b01b4080e80c0300384080b401d4203d4030100a0304020500400194038600700818041512404038024000d40d0300383d5804544000a040d543d00d415040741d4422503c4801c4079001c00e054030042000491080310240100e03802401400105c400c884084000d060310440501c500d00041201040c4801504080900e41100e130503501d178400b071286403403840d024005140200b294a0001c041c03004e540c6414444c40c3c1c0c1c5404643c01305100c403072403c2c41800c2c900c18012504800100107030000d100c1c495401c0031005e450003181c03090851b0300b90090158010100b0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 705814145 1250 705812895 705812971
    0x5222417070806040c0903120903150204080307031107090204061205130512070201170c19030209011d061b0706090603050405030a140708040f090b1f03051305011103 73
    0x4580003c0c11420181e100e21400c61445c9070403a07031555a82c68003202c69920010110000ea80c90f681481401a0008050380903100103104625291510400580780e0003190402010040c00c04660342c18003900704965005048040c07000c55803165a40005040c001a50a0800d1481d00f4038001850a07030000d411044401d0f00310b0080d1029071640703000218203510804d4102d060110316091490344460071041144207400350781200e9a1102c81f2030b12840f9a0000045807401c01d80100314030b00090340e0001340000d4115020b00c821610080078000980a0301030a62072900307280700300c1c2c00d503c1c0e0260001540800c8070740a031507002507161510022815078004545c0500103510421440c5000f5104240001d8004400c12265007007030166516050300b0340c403d500900550040c450180700014103031061a96504040350b02000603060041d101440d0030001c0e00c4002410340d248000f0700d40582803e04082e03556800300003040701c5072140d1142c0300c16400585405d400141e0421850702c900d04420442d20300703c100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 705815395 1250 705814145 705814157
    0x310170a0f030513120b04030e030a030e010c0303110c0d1112070209100b07050304030c270b030717033c071a180d09060522241707 58
    0x1a10203032256071004c00b80e605100c00d00350300000c080ca100c03102210725900c50341e5400784508040c02c00904c10181005614802c1c1c00c0012500e0002c0e4002411340c020783c0d82030a250906108a08055005103103098002031000000100c4848610000c680d000712019143c9442100c40b554070034180e9583d903000c010051031039041110f8000f40c5080140b240d403000940e06202c0000d901e504907007072650072826080b07605520106081c0204140509040003030024030202e50280c501030410b110f680c040d00255149410303940c415041c507030f880a120440c007504424805c40411461058515901d03031254031040f11503064007900e400d181411425205040031a0711111040100303141e00b100c9582d22a00040f108030300d01500d480741c0f41c5051001e0521a140c0d0105080700a00c940641d00d0030940f04001c80310030482504401d00910360030209851201c1400132802d4a0400c0140314100d880c4426046510b0550805481d0070600c00c82031040c91249401c0c1e82e4020a60200f5190100940300c251054408208 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 705816645 1250 705815395 705815423
    0x70b15150705010b04150923040210140412110406030224070b0408070212010e0d030c02070314010606110705150d021b071706040f03230310170a 64
    0x10040c80a40301d0a40200000101d00c0441c40000781100c0000201c5405601d0541b0204800c03a1030f4403030500040c1d80b40451440c150960400c401040c40f00400003840380742d03013200401c02c46108101c2480d03003182450503181d17129204d01342d5210f02c0005900c1116040003440d0300382c420f401e00740200c804880e40a01030b044040400402110010144d15218084031300503c00d2201155805401c6c500843c000e008e00d9544944600501c01647e4020005490982c104400b00b0120000020002200003441c83c002900041040c012810400d03030760b0002e0520041010420100c40c810b41c40700040f2801c3c5c3d11003038520713140d80305e5403602c0e03043c18800c00ea842400e61940309009600c400c0100007502120500510b0302541000100e641040e44405030072030741c00078000b402601c80d0403841c050411051801040700703140581e0380101052158000900b04860403486426019840d40c00c61400c5000403030b55501d84c942a00031500801461090f4041e06150007101c04000350301244010900d43c000b010300f4041e80c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 705817895 1250 705816645 705816679
    0x40602030a1a060f0307110604060605010e0d0309090b1203221a0d0b04020f12100b0f040b0904090c0e07080a020f2a07080105061207150f030209040c05070b15 70
    0x20300300030520811f125030021035100d010380a1101138401d6104000000350503080600043c6a40c10010400d401184209840340220703810030000c40448841c0c20300490b80c0181a000b0841190046801c0760180c1b0020404c4070440007041048140014a40880d003034881e036402007405070046088006405180400c2042114000c1c2d40108940c0400504058940400c103038240b0000e5110000f0f8202545c982024085409203844554000b030a20303041c0d4a050900b6048000694401d81c0f0a2035080c95000803000d4541c0c03110340001207140c0d006618003800b55600c0306a89588181100c084c400525107100203019991030707200399003e4001c8002003500300030200000c0c080c45000c1c81030300b00d22540c2d81030001c040030100300716800140c0781d050000700340381c01c200090140002011001e40f8140e08101c0c0b0510910a04c0c0f603107029200b1091801030710b40d03d0403810950085c818800040e801c5400c0032407004809030480300520001d481002c894880b0743da042a102e051580100c00345034020801e6140003204 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 705819145 1250 705817895 705817897
    0x2010030501090515130e12120a060f180e01110403140c0612070309050c270c1206010f05071e030e04090b1305030c0714011806140c0312040602030a1a060f 68
    0x119412030444003c80d0311410741c5102c64202c150442585405d520812071080000d0141c82c0003086511506251240cd04a0080305d0319038001c40c0f40c540c0d507514070322064000005d4111038040d4024480055459445e0304001903a0028841034025504c280c0b03019070554144101222600380580c0f00f1b207171071034841c00401c50250546460550f801e20405040030030300c3c1d503088000381001405280b1908000c031a030f95000d82c03818000740011180c40c4140b2241c4400340e01110031070750044003464441c1010311312010544d41402450405040b6610401900308604885030b070541909000341c540c9080009100100b0064684510000b05206242404100b5481250801d00c0090340b060381541e050004040c2c85034074048140e4001204030040ca0000e0000b543c0003808069502c00c0c0c1028556a1400c148016126081070200303605120b80c00504420000802e00955110011400c405801401c0ca03090400c041e40050740e05482240ca061520098032200d801d05003241540907240a0414071318411802e41 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 705820395 1250 705819145 705819161
    0x8040816051f0519020318060705030a032408160b0306130b06090301020d050f0601022a04091a010302040f06030b060f010c020a17010f05060d201003050109051513 72
    0x1031003420b00003100c1062151130000054a09907000b5512220085190442c866281010302e005c1c000400c400d40104502100300c030489003080c100401d40101c060702030000c5040107529000c02402c1d0b008007098250021803c586010b00b07500100c0b9040340c42e401e2503d81c82c4801d452031640103d0038030080000e00d41d21380014800d581c00034180303414a43d902c40805d0a90b8071a0540c04119655142040301604804195a030402001c2c40100031000c00801d0014038802c500a103a1a003044815080805940302c2c0c000150141c0d01c1509065103070307000070115500c01e400f80812846641010308224040e48903204017004c490308001550b210340c40d540103000344000286601410491003890725409600c414482c80300603d015400401d80300180a015401c6584a200003007950382800c09006c2d4030350350016074604240e04071701d008480300d501d680349900c050469200150008035200d8098284c80c0c060340b05a04950910342c2c140101c0ea51506003166811800e4036440e480f0303845c0c04c940048012903601c6001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 705821645 1250 705820395 705820397
    0x50109030201150b07061e0e0f0106080d0203121b040801050709090c12020304020a0b0705031206190b031f0b210417030a090203060a1d0a021c060b04050408040816051f 74
    0x80b054560340b441d1400c2d121240d0200231030364090309000d020508244526001483e15402400f1071028030741d0000e440c2e03c101140c03580c0d040111008030f8096407501030b9034088220030a00c00d07591143da5841190207030504683d100003054014900040f0161940181e129a500381d54901608120007400000290400740060340c00c58641c00010443c0c0e02144000d16905010f040115182d54030748101550f002c800401c080d0040c40d40c0d20440500c64460543c0a060351001300e20940c9907a92480300d50605040354540e108900c85035180022141d500c08010981c503008601c1860305802c040000318100c4070300395001085280404007002d40e04052902854222800003800304881ca101d40000c0c2c40c0140643d18803d01039a205100d081b107039210201d148095032120003604940340c00b07400088241c10113918052164200c00c4a05d0304200003948000b400c540c0040c03080005080506108000d50000c0c040c0f4219445405d247c0d45480ea04080d80204440c0020844181041103000c0800c02c4420425a0301c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 705822895 1250 705821645 705821681
    0xf0206090c01230447090f0112090b070f030603200109080105010308270f040e010b0d0b09012711040603022d064003050109030201150b0706 62
    0x1040101310080d0b40010302d410681058420022813007484010840603141145d540c1e20900311004021a00c1e040e070f682d45404a4990320840031090060b1280110b09910300e407440d01d07100d0005e04102017040c01a01829095507041034002c10940b05400f02d403058003001d011248050b401c140d203c2410011401c3c0140306140c844001551070350301d41c0c2913460030f8104031014003001c48d00c500510b0aa40c040050360480300000504001082c021400c7e101d42c08004074010354955120410102003500714680791440a0005642c0380303480d08000c0c800c50015500d81c001075080c000d8a24800d80080c0c20700207280754a0001d42110001544c40080d03240138148042c0d0080d440725000005640d0740300901500c1404002082c07404880302d0024502400300103a03280c03264200344001ea545199a03010103150104c001c8050404041d5000623200c44103c107001008504214800401000010b400060180c1c2c80380d0004d01c15081d0f01c555900507646540078107605040107000c078002084090704510101c0c250790b0100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 705824145 1250 705822895 705822899
    0x60d0f02090103060507141c0f150f0503150103020102150901060e09010207060e1c0c0f06061215050103030e101e020f0615090115020c03030a0f0206090c012304 71
    0x1288424509900503506203517580200080756030495004e544450600100c0c5190044648180304080320175006440555603074030840140103215802051140384091444401956814250107002414090980240a20ba00020920280c548414141c9a0580241c1070400ba400d956441c020750040c203007081992268800a02d00c5041140d40c3d0046020070700140e561102400c1c6401600c1e03101301152410b500441405030412010020408818440d00e80240d5550940c105001043d043d59800340003585000c00010b910306098541000451107452460b51400d10040a003048810901c4050080303400205402c0152524003d403117031400c0301d800c0100340b011440085003040f0800080c5403025a01c0401e0581c00312908000e09030b4402c0030401000703242640e88000c507030414810301c10b040e2000342c030032554031556000384003005040101900f00c90300d41c21b038240c0050040240c68000409400750b203020401103000031400c00040d15040c1c4410000a00c0c0210b0343c50007102103440483c40200034440 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 705825395 1250 705824145 705824149
    0x20603150d0c030506090601181a060c0606092401051c06260118030525061e0c080403180503070f0911043b0f040c050414060d0f02 58
    0x1070700c00c100340900440400d0608600d000c0785003010252800510f980701c0700041108085060001c0303e000010700003c901d1142e201300000c00486485212070b805580420340e00d0b4800000100c4a105001c116481c055903100c1c4440b4a4108400194040d604030280000213105c1d40910024690010100c0c0c800c0c1100d26010760160484416030000c0b01c3e049000190807640d28604444c3c1a0741851501c020042e06e542e00202071006403219100a0901402040384480b8012105e040d117010380740314801a00c00461846c00074000e09040c041096081407103403034040300100da48180600d42c1e002e52143d00d02500c079905c1c10b658a0030000100c540080c0041303c00320302514280030b5030005142044404604605142401c000e4403850007040b560032000340800c20504150990900016201620084008003403070075601c41c4012600000c00321034a075000b84100254800040c1d4807403130103518581c44907a1154200010788000100803507011441d04041440742c0b070800c510a0580f4450550540402200c0e40 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 705826645 1250 705825395 705825409
    0x5030304030906030507051201031407150206040606060c080d050a0e03040605090307090c090b0c07121406160903110d02150a09050d020108010312020f070906030201021e0a02060315 80
    0x900300c0004001c242c0070000039400d4000d00350070401030b051040c03c0000301c5d50840044a4144000381040c91b14190001c0b2042052059401030001080028140380350500003a54406068808541c11443e2440018040340b01d6440e4182d02079204075030728500050300039088040c04000e81421072959549282c400e100d0340420051004103810b80300c0d5501c0e100d03490101800d041041c0d11400c0d006052498075001254403681c11000c0d01c078044801900d4400b06a086407030300409070045801007610f80051014011040c903624003030400754040301d59913500d80302582141280091b1f03010100d9105e480c00d10000740070034100502543c020300a401800100d400003228924501d90401c4400720001d051144a40e1048580011b003105540000c50f200c0180d00003003400c401480090040c0c0107200c101c080301c80c404c1c003c1c0c0c03030b4108040c401c50b141c0d146c807114113400802c81e5120032405880740720114022007404a0139031003000e42140251070141d542d5024051540c3c0000c0c040301515403101440395140d603c2207 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 705827895 1250 705826645 705826651
    0x201020f01050a150e01060c170d391e030f0606080105090a021903020c0c120106090b090624040306050a091a040b150d051b0a051804020103090f050303 67
    0x401d02141c03080c001c40004844e0388080d0421303076010100c070006000090300092a0684a40d000500c02c8107010307a4500c00d0f100d40601c4507805000f40c24a07030b41c06107141441c035400c0103030081e41c03410900d85041211424450402080b809002c900c01c224699103103c410000780c1c010180c9800c0214050003107880030f804a1700c1c1e503040140071424500061049041c2450b5440d48203800d03410031440d1008401440c0030b44903490360001c0c01c0540001b03030b2410300c40041c0310164500304050050311f0a8603030005024080e0a09020381e40030645003500340909840d100c0303c868040c1d20040c025a40441c00d403030940c0f48032210a4040121031004120000002e440c0b8400c840c803500300c18000264100492506041c0300307036220b00c006003946451080c031010403940411280c2000454002c0e80c059018400072818000c51008082c1c1940140c80146540e16010240002441011078000004584035800c0000c0c82c9401d00d840400d00c64060000360065010740d000c004800d0003600c030181021a59034034585564011 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 705829145 1250 705827895 705827911
    0x6131509050f0f0c010203270f030d0c11100801030f060b0a080d0909060612050603120a1106091515030c0a03060b0f01082a12180f03030f06010c0201020f0105 70
    0x810301000c03c00d80030b2154100c8410700340702444c5401ca000d0080280310041d00c9882c0c544580002c1c0e1030080f40e40d0340c480d0400080300031713040e10010401a100038025044422058410400d11060b180162505000558101409460b48030032a4216140d605001c400f07988111401d030b980d40180c818980c0e444006500812044009045c840410307080200340d084161b01c030004046c00c04a05004454100e0800d190044604000281c41c0d50780703000003880c0189500d080d0401c0c61001a030b00b00844e5001030000300c00210041101c903103854025450b07a6502e041c030184004c3c12024404070302030780e2401d075154000e40001030032180c04404003c0010300451700d50780200d803d180d84005851580c20410802d003400002401d28403a070307190000c002d280d5074403510440541da03c000000e075002162148283e0714041d602000d41c0c8006d1811400e540300941030300b00c214009116400c41600000400000c880c818407100b400c8116640fa06801501c40300c00f1030804905502400400442c148400d21450303114040e1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 705830395 1250 705829145 705829153
    0x30108030d09020d17030a0e03030f0a020703090302041508010b060c1e0109210305070201091709010c0c0b070b16021b13090b011406071e0215030703020901080906131509050f 77
    0x403007c08001201c014084001240c0c10600c1000040301c03003260708030fa015001e2403015070780d07500d5440c00700c40308110303500002c2d40280b0303105403030741c1c07200c90b8088050940d8600e10082240303540060170401140106060b440d0164003160030407081d00010201c071580c1c40310000001c911101c140d41c910000701d4000044900359180c40913103c103c103034940192030304031945000070004403034a501c07011044186500b00c044652800204014264841c0c41000341d0107030485511031106885000c0c9003280d522034030069400c00c03042c1002c246550151032070503016520503002800c0d51451a10502c086407a15502030360702100f201041f00400403e4042d000001c0d2207200030340001c1d8107103d4141d000a800e10080c0340504018031404000403401408030742400c0181c1c03415810315001e4400215800403440c242600114044203000410347c143e000361080000981741c00580f542c41d00c601e42c0c1d0b92101119005601c0c001070001d1404600d030000794840300400c0c3c82c0049001d00b9140c4826207008903d001030410b60380 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 705831645 1250 705830395 705830401
    0x522080d060315060909030903120909020313020f0a0b1207050418050702010e0307020102150c0405060c030a0e121f02090d2420130306110a090902030108030d09020d1703 75
    0x1521450014020b942001c003c1001b107a10020302c00802800300a101118501507819124050001348008029042081d035891034403070055108040c4514049000705603043e60350609240c0005001d047e290300034061420540d8030014501074034000b80020042c00340c1004085218000c0360200480031440030313030108040c00c1a02d4000d00312001540706940fa50014442900141e0f804a07441e003c03514800c5042c25113481e441e944010502c43c80e842150300440005a800240b0707804000b803c038440705520342803650750000050201d0981010102d1245810500600540b881c0caa0100d101a0310849001800d0480b43d80100782001e00440c2c0580b580e07105440014103584084c044118114400d41c0107100f0310342c8120620610006203001c42c0074611003c0340701c041c2c0c4a804540c400055800c01c0051204140c0d8204000555000c0c0a481000032030001b00840c0300358240c0212030403a59090020341c54040c010450174010540340740d04030781c072158610f486400310304082c0b174001d80d80c104040f00c9507881c1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 705832895 1250 705831645 705831683
    0x6090b03070e13080c0118030207060f0503040c031b051c0212010c02062a030a020406110a02150a03410f06010806220203190522080d0603 61
    0x1c10703400255842502e0341003104403941020342c040859400b040c00741d02d886000307445030b000d440440c41011803c140e004004050540c0068031804840007615081403540c01d4110468031448126400341401d044108100300003080000c4d00000144d1280072140320316104c0001405140700c5035851510700000300044025440c0140500701441401c0000300072000c25480c000c0d40340c550040044001d10203112a5444000110b01d600400b546030210b4680d40c1d1a10b4580b0314001d4002d40140b600150403070041c8004c103000041c58809498000384800f10b64800d0130182c1400c1e60260422070101030b180c40549072010b041c3d2030060b603e401c041d03d54910340e00c021072031500c42101d07942c03c421498640d401440880c4100e2142e8641040080c40d10a000c1d40e00c09000c80c10500e0f440700f03441d032440c64003c150340e0400001c1e405140a44160381c0c050207016031200c0d070ba4050301c90944034500001110149410880e0201d11200c8c0d409105404190800581340c1100003181c1c160741c030507550315141d020004111 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 705834145 1250 705832895 705832903
    0x10e01060f0902270303040801090f03030c020303040b011403100e030406080c1215011e0207050f10020c04051b1210230f12190606080304060f030f0207020406090b03 73
    0x142042c00021820726400340044040039080e2104048080706600c13030a01c190710305004981c0604001d00081c00f8840c3e41c0d1400703425084200c03030150000f03460007000d17104140c070200449015640058150351181d0030b04070240b805020700004c0d170b9814403a0103440103200d0051f00407100301074010300195032194a00320303001d4040305004281454a00f41003080c1200305007404041a040810761070301024101d8002c006072141414101d20084d104124804000c10a9001502c2130541d1402d490401d0003030660030502a0902c2c0074500500581c012451318001824203910007588281c0495030180d00501c81c1c102140c2e260320042c665082501d00500f00510b1120b4035032014000c060154180c0d21454440e241980d40003282094144680360203051125680c0d9000c6800300f80501e00800e646d0500309104126021078860041102d4507400c0c9840094011804400e450854410307449050358407100450890041490908405820782d0078050034025842d144034803c040c10204200040c1031152004251070 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 705835395 1250 705834145 705834149
    0xb0907090507140a050f03091e0105070c0f050a06110c06060a0e22020604171515060a0c120c05011a01050d0e0114041a1e060d05010e010e01060f 64
    0x2490800c4103010b02254461111400c03042254011610303a03240d103804450754400c490030001c0c001e002000b848500b2501061000c11428095000d2507080b003c010018240c0f00102c0303403c00891841614031f00403644000c040c41025100b40305491100302d181d03513100301312014294450010b14003c2903612050604000365500a40c040701d6607164145405e050305494000101401d2420700708110714049421080d04035602c00d5401002c5c641c40300c1d1180841c02c1807402c071035581c0c90a0b202e08006100c556168045e1940111042c003403203148801c409040c040c10740e11000710f0904201c110351903100441d240c040c80c101c3c1c4506541d1000e1031076002d410301d1803c0d2541c0c00321a4910440d0305a11202680e00003084a40880391070300d010600c0d94441e51591b00500c01001600c040103440ca0801c000c20080c8445618000c0684141d0182d80d226a05404180c1800c1c544000350140e0500105505107800c40d1001c1d86640300300e00110310707182810030041c01d5510516015034680e45500e001d001d40c4100804500c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 705836645 1250 705835395 705835409
    0x1c06090308070e0a0b0906070c080d0e090f070305060d081204031e02100c05122e0f061b02100c030f02010e12130e0c0415090803030f090f0a0b0907 65
    0x2d881c0403c0400075041c45454840c9009020002612a80d1616100151481180c0240c07031600b480f65a4001e9603220300030104400d000400403210400f152030310302c500d10302480c150381c000480b0b5500d40380164020107009d1706407684002410540d0700026140001010142e01d04804c0039118140f500e0090040d82d5009007849000701454440302c0c40ca0f038000341240c0042810700340458505042c180584440c032942d00c0209a414102040101407008449411141280750000080300d03c03140d200716100030002c1c0942441401002001c004a500c10303801c1c11078018480440d20400070741c9a00280d001c5000210039404100c84070880014160421001100941c0307034002840381191402106813035800c4034a100f600c1c4031001c500c0140034514007074a48045c00c0140c95000340b5003010800091160050720030038000c4402c01445066551061441104840e44200103500b5501c1d40a0a800e0740400242074042910401c4c00c4007244040810411800500038002d810311400d010b03c209003000344580005c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 705837895 1250 705836645 705836657
    0x309081912110a1409060d060e1e1504020d020a11100b0307031e06050705070c140907030f09081c0f0908040b0f04080601090f0c021f0b1c0609030807 66
    0x50721042d80212028050366240100c040c02c0503041640c40f0b0b0241c4c40807190070500101c1c00520300310741c56004000380e9075610f49000700d03565819103c1c00400b2161400b0a079200d160408181030800e540b14845101400500241c00c080c03079107400d00100d070000700d1240c0000ba24401001c42011007442003080d001044a030900003101d50340082981d5604601c801000c4801d0b0300030b4079440180ca040408072056101c1018042403c20b908010b0a40d00140400c0d940c0544000700000d2482d681c801031846a6805800410a6a102c6200750014500d0f2407400c07914940721f140b10b030002a0350304000c04640766660f04170052650b079071110f0070840300d40100c00c01c4401d260007408000315500105460481d100030508560310902400b403043c00d40500d501212581c0308440010401012031b0700b20f88800c90b00f2040401411404200c100d035a40c0d075404c000c40040e40e06100d50804040a80c2040344034600203494001e4400c00401c44a204a812000a40c0e0160b034891182c420168010b104581203001e0349809 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 705839145 1250 705837895 705837911
    0x9050f0108010f0510020337050315040207030e03010603052a1e010c0f11041103060a090f0e0703150e07081207140f060f070201020403051c0309081912 67
    0x1242c50070400740101e070705c40e80c040714606410702e10070812100c0c003484000a44a40304090300c038000000c03048844505c0702c005481484400c00b807081c0b00341ca2280a020f89208418005101801300a5000781001d8081051450400745551030034018240103612a1004007500c0341ca075080320b40d10f0748182102401c605e5025503000b00da955110900f42c80c040d08000d04906055400303005070780f40105400000c001e0389900d491142030000604619003416030913034040c080ba41d4440258544d40c4403c6801a81c8410220b000f40300300d060503030044210903410140000c0d229103503000e451034003405600488480c018201040c400e04038034082c80405040090091904500f0100c90301c1e00c0d0103411800301a1088045004401d200d680041d000724400c03040145c03484412540312594444001b11003120b110020303000403511092052013242c0440350490702808082440509004000310000329080800d51107000d41801b081040c40148103e9900038140c82802200c5a00074002e030040c0e2442c040003601c0d20b000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 705840395 1250 705839145 705839159
    0x1704081b010905030a080d0c05090a120b060f011e030e101d060105060f030c04090606020303060f0108070c060218040c020307060b0a060c0f2102070801150305031903020d020a09050f010801 83
    0x35070388030b1200f5080100d120301d01d4403000c0322785014071150907a04c5401c511000070109018030100071914050194400603555040034000b035218900589800203980c0d0500e81d00e203c4105140504250790340c980450080c00c9800790394504401c608600c421142e903004c1c21048010101c40c080b4108c081c02020303128079032608001898038003480c00e045c51008000000554024080030880e006080c4d1003c081101584a5070007e40d00d4000300c408600509600c14040155802220b50601c2141c443e40d41c4080301849580d0180690401480e2000100311418030046568450240300d40310402a402551140d201d42051070a440e500401e0728000c02c490142801601d902180410b1165004101c604840ca014a4280d00e050884500700d231f0b20a00c541080e01e04654007003051000c54100e407000b4825803090700100c1408140703c0c8030007010f03640108111281a0428003038411400000d0800504118100764400240d0340300b50101c1001608881d0140150302d40403a02818034203083c80c126480390304001d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 705841645 1250 705840395 705840397
    0xa0303121a1305130209100f080f120f1c0b092503020d0b04060b0c100c020a030e0627040c05040521070e0103120f0206190509010b0a08010b0f0904030c1704081b010905030a08 77
    0x150a000b2f801000501c031004c849902c04450300188030b05440c4641a910415034001001da10a0141c0301c0c100400205842c14440e9044420f5044482d0014000c8901c8400030740c0250302200c072142c4c0c1d032a2100b504450340c0d952445100000c020b0001c0c0a59520503180d8100d00f0314010b2102415070500d840584c14030241c1c0010030701c8250390326060600035211100001103da0044600c016644ca115448503180c0b8014503d841c40303c50740c180e03814400c08440e07010a460741e005030b01801ea000030b9046503d03039001100844600c0003010a005407101c00d510b07141042001d2100344c000395820000d135019850b201c2e80c41007039980408100d101920302410101d2481211510134100041501e40702c602042c4803140a61010301e448078001c0503045035070381d10b0707903030070b020303004074001d4511850140030420f2141c2400404188180e40c5555241220038070f640c1c5200b6140720b41c00d500c40019600703000101e0f44000800524003021004541e8000028440700014040d0166801580c002d4000c10803420004251074 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 705842895 1250 705841645 705841663
    0xc0807090e0402060a09092d0c14160f030302030f070e0105070201080c0d0e100516141606020a020606030d020d020a06020d0b0a0303121a1305130209100f080f 70
    0x40d04140d99072000c940c1286c4c4070b01103410082c101172030a81c001c0001865415004507000708a102504c0b5940c0d980068012076a51030701c0b04003c99211640c003000d0b0005c4600800401c1c0080c1d03800d27001404103488182c1c205072201401c80100e5400000d1240181c0d4080d4030642c417075030b00e00d03017030540c100c0040001f0400e0244840080c180101c143c0130504284454003515010300860404000c10004d010710503070f54999240361951708502e4500812030320202c0540b10303d001f04035a140c0b040070384100c210f448965409406020382c132011000b05840040c0302c0e400140426001a03004000078103100080505000070780c400308007592302c28200849246d401003402e180039508000300684603258441d80702c02130091034101550002c4030750404810150000c00080c21000c80d0314040010748602d0410103800c40d2030050407075000c0c61040e160101c01101e42c1045600020614440c20b03203640560201e414480c060342c06100e10f80c0c1902d410b12103840b6610000005200450040003640c43e0b85138441d444103441c0e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 705844145 1250 705842895 705842899
    0x905060c1c05040f23060a030e15060906030c010206070f0e370308070803090a060f02032a04090e0a050a111309110f040b0d060c0807090e0402 63
    0x10455145684080c0805940c80c1034200710504401e10702503008259a1240c00780d4583d2402c42e040100b036000c3c0c044910310241c10a1089640d0f860500c40810000350801c83d0300004141e150805104a01410300c014459520b0030242c608050900d03104210b0302e030310300608132802030f84040d100c1c10080e031780003604580007a60f41c14510300c002c03800c5000b100d001929802441e040400b001c543c510004921b80301802443d4284401014500d040902014510091001401c00c0381c0501404002c01c031014001c5401c07000d10002ca8000e071909989030001d03140482d4074035104650100030004000c5580900450030351025000c64869802c1079201c2c40c41d40640e003e000788903a83d650707030085841800c000c080040c1c1d411008440d1001c0b0310b40b420261181380c2c480d803503005100b9400405030845980c02042016544081110016030b02c4005101816800020350341e4007070b889042410017500c1d000c84010103d4050b0102284060741d042001e0820a0003520410410054003c108214424107103002d404c9581 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 705845395 1250 705844145 705844147
    0x20c061b06010803030a050f0403050a0f05040e25052a0a140d021204030308070e0109090f0608070b03061003021e0c1f0e150a1b0207060e030a03090506 67
    0x44000e540d1451603611110054510840c000403c210500201640c400d009a16061041d542d503407a507009513000070744000300030490a0000c401c0d281c0c00703041c1b05c9580d028940307056410a13076219001d0314415800e0380c038240720f0010300d6000700040c014000004822025801c18901e460801e0720b820b1034801e81085440810344e004094200302500601c8652019908609542c503120f001804c45511202c503154600c0c0544290381441984550200681e003c5036017688074030081d07648420054450449503550207040241c0d8141c04904014584100b005004140f0400144541080c41052510046803c40c00f11a401030080080c1a520f0092400c2c0c044190720300580c8444880d80d1500c01c9045000000308034420200d481d403980040040c9000142041e504140c40141451890b1000c4808202021001d5044a000302c0940704602c0c480a40081e070007100003818500e00300500d160105070741c01000040e000b03010100111035008a41c0041244110041d1400e00030b0382d60003070622800c0f44281809100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 705846645 1250 705845395 705845407
    0x3070e060705010908031f0f0302010f030b0d0c2c060a0302150d111c2708040902030a050714040807060e0f04060834142407120807020c06 61
    0x8080d0813420005074403a420b00d80302e0828160940c80200c91100783d012682a04200240070a580c0c0b80c00070071240c06842d0409052246c92044001d82030003042c00c2e070800c000340070030800207031030f0a1140300800d10500711001d55424840034100f00b802c03203000c2848002800c01031054940d2606910011a0f50407101c41c50a480a40c8913554980a140a0020980d2811100410501e01d440003030032a0b01005028501c04c2c42c0b603246210460380ca04203101880150087c2c0f101141042e01a00380d207150103046002c2c142607403806610700f41d07881243ca8090700c5072158180000300b904450110000c02032a0a240c1c20603086c0030b9400da0f100007511034401041758460342038105450310100c1100456001d0b0045c80a06d44444d00c4130380e0fa030080300750380624040c034180c10744541ca072140840c0d0003650081052010f00740351004002c1c080c442d444005511001040719003007640050728170320803a101101011620b85070241031880e00e03c51074103008414444880100400760f0b074042514403600c03030101c403e26202c00e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 705847895 1250 705846645 705846653
    0xa050108061c050f0601080d08130b1f1e0504050f1b130503031204020a0b070c0e09010b0303030403081e22380c0f040b0c0307021e010f0503070e0607 66
    0x310300e0f000d04d2241d00441c0300100781c101e4041030b009503190481e202c1540c561070300e050340251880607003005010440c0c130b04041000422140403041e10000245030a6110a4030342c41840ca4610240e40444020642903070f0810407400c0500a440d0300c00c040400c00030f050724000c88a034089400100301c10103804800030789006820800080c0780d014000240840381c072800300c807900da030303404a0945041e03203d0130701e0650003c0c0103050744048540580d48018400301c640d160140203240d901001d4503000c519501d42074242d8050700c04002070352059010795944486410702c1078100760000340a014020704001154100100e00740e0103010100000c7ca03030440d8017200d40103030901580c810190b01e5502858070045407107010280400c0f405000550361007182500f50380b22444000c0344c0e4400c1444136926001c0500c02045000325400282901900080551740380065503800110f480c81c04100c07000e2001c00c3d41d202c4a142d568000128010202c05003031242c0f65050804001c2e21652013032186a2040c440011100100 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 705849145 1250 705847895 705847903
    0x102070f0f0f0c090213050406051003150e0c030a0513020108041e080409291c0f150603062910021c0c0201111603080c01021303060b0a050108061c05 66
    0x1450f0072031003044800752141000c03000b95000a2022002c85113414002c05e207880c1030311134503040300d4000308090011401030409038040d204500c103400c44940c5803500021000c80300030441e07100b4441e00104595a01d024501030f400c41d140606515100000c00c0790380c20050b42c1260500f6000754120300541140700c100480003e08032071114000b001d4031000f040000c0c0407110303500151004a1000c04180c0c20203800390150005e10007400c40240e000403c2c01c054000080301101580d00907028880103100c40c00c80f034460902070b2062240e105a0b0300e659a0301081408250301ca035910302200a000c014400c07007011070950b6120700355600f00c0d02c9003208110421605008008007411a840054100d0040b8031101010b0855001440180e01080304041e10495000004c5826195021800000a46241180c0345d440d800d0304900c0480035190350801824107040200300b40000210300c195030100d0382c12021020310030b081036590301c864140102c0a052280136038488a407000b24243e01804144c1c00c0710542045850 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 705850395 1250 705849145 705849173
    0x414030d090c1a0c060f1312081605161118010e10051005030114010905091005041104030803131a07050a020106140d020d0201120f0506040e0102070f0f 67
    0x6100c1c40c040d1000c0800c840d01d5401001c03a1200b054101218240c00c49140c0103101d6000d812206401080002d1b41504d1801c0450380c20100074299141c4071a00c5a50303441301301c07100381241800702c2c1d410320421405003160200c1040060301882e142d81041503441c0a8501003c000d000200202e0b105a8000d070191180c40c16070346400d001614072401565900c034203406c0745109071500c00107485109008501e0341000c2080340c0040500b5611145180e20b8400780c440910b1108403c0d6041001e103c2e800101c9642c0c0b44606402000b14210110085107858100011904d0a41c665103a00b00244000c0001c101500c0989034480c1003940600c695036942e10f000502031401910401004212409009504c2d502c0300180441e18112340080040e1500c919000b6a14400d2076040740c2d020341d81012130401420006050314030144181840d49100007031100b140292000709102d4040f41f0343d200c080214a20340f60007000201d250a2000f1490145030b51542401c241c6813840140c4400d64525000042061400803202 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 705851645 1250 705850395 705850417
    0x151203270a0f0302100216060f0219060506030c1e130e070f060f0504241205160e0a03030c03050f070b070c060b0f0a050d030e0330040608041403 64
    0xc901d81c0c030307202c10360000700090100360f010b403c0c014456000d160000803092035407046030f5050f83c1c030f451518208480c8051155540000c501031049090186501002d03102e00a0344122404030301480d000c410b140c03070301a600c400b241c4076194064074a54054980c0d003800301d90150a503005061200e05065400c0075059001c0025101e1045500001c1d0500f0030319488030580e5802c0d52409041d242c02603084800f80210300501d03a014038041107500f450740c4100010750140c01d042c05d040d00c0241381c803040501103400444411031544004500b190550b40d00c9400c40c6039540d0300315401040142980c600415001d81410000c041c004001002104000c00c04160f40c0340301e50040845e61140b5180000604914480c0e4080b5200c0e414090542001c0c50702d2034070303a145000c0140203c02035903d0310f010000140c00129040e41400f0b03040409000c0c0f034a0601010800d408030640c6510448900f103003029440b1600f4298070700b24070381803200b80005a808586683c11580141144003c0d048440c001d506610a04c05645 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 705852895 1250 705851645 705851659
    0xa1812080304120527040b0904051c080103150e0f03030403050414042f210103030801081605010f03020415030608010509010915050a0e1515120327 65
    0x18042050000003948664414034a2a006108121081d511030042ca840080000040c0000d07545a28600601440d40700c0020000300d02d81d11100040b4480325810349040e03409401c0304500c01142c0a01348902110010986807a228075850b5840b0442c1e26440650000d036000e480382018049100c0030000c01e0451902107040e80d81c3e03410035103000b4203154013a11910b0030b10910f20300c102e1080d180500c6003640c000f0300044220f401507400c010008408030f90400185040006014095161005225518402801348465203040d411420054600e400503032000f00031340e003c0911551112140c11040301102c1086c20a032924541905054000c1c0c02030b500182d0390a07064036100a01943e16401000864155000070080c0d07858000c006402e035101c0440180079100c0240400500401c281e1249911202021000030366030101548542424070803141200b1a0391290148841140c5456800342d051404030f4280b070b0321b2035580c0005920f84c020000c0000003c0d98603030b050b1010780661400003004100040100d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 705854145 1250 705852895 705852929
    0x9080717190314040201031e0617060901092d12080a110f0921060903030709050103140703050403090f0f081b06071209080336060a18 59
    0x4840d40da001010203140000c41d100881c08498064072035455801d803100a802250f6850707400640103410040c07410002141c8108041c2403102c4c0e10b100741406404e07039950018203417210b4440c49117000d1001d0038a01c540d900d0314440340c1c0000c580348820a08080342640c02c5020140c5411001c004004100c00540341c440c04e44d51004c18687e00c021900c4c80303407a20b10350400c02010512408259800355070020000740701e0030008440180703002e0b148441641c4440c6442066042030301c0b251800c1540c1a41c911903154000720a1181c42900030324003002a10302840c08002c0c41c0244072405441c2c0783d01070150024150395030089002c0c14400d05041e00074098408000082c0790f52080c00280011042c811046a40588550040c11400c01350a20005420040c00c039801d104090712103152110141c0e8105090250100c0001541402400601100ca20075410800c089002920110040401c402d001c20b1079034040b2156045941d410b02622070003465464100314081c1035113401c246940160f0000e00c9503000708441 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 705855395 1250 705854145 705854183
    0x110c061216020708030901140408070311120102030601050f070f0c0e010f270c02030705100204240c03082e03050c0a120204020d111204060501080c0a09090807 70
    0xc4680151200503921100e000340100403a00c614080c0035030000b039042040503284561182440402c0d0b01d50784d68545142c159662035152130b090240d13104861140c808400f0300030600d03003000c0750400e0086d02c4009620b503182010000b0101d2240c0c44181580010108009051001d081406036125620122069000384c07030f00e4140007100c1007441800410b82d01d580010480e90b1a082031080c40350318400d9084000d15160544402521000703103800c0c01c40c80203014000c0030407000c1091410004a072803005030380d682080501c1a02d801585020744682c0e44180381e0039421030740980800d071001e03094603040081da2604940a503120704418501c100384458066000941007040024400302d91181c7c08440b42041e1420500228840500c910759641d0740701d05201002d0304081c3c0080407a600480c00c00521404000318a1500d42c0141d450000351074050402c0008010541c0b14590142100400401001440000244400035980180d075003654481003440100300105041d58182d9920a081822440d0300c20300e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 705856645 1250 705855395 705855427
    0xc0a0303140d06260f15040f020d2010080403050304060504081605030d0c030603020109060f0203090a06020c0109061418031002030c030406140f16140c01020706111207110c06 77
    0xf070101e2640100001000f00300c01c0046e00c5040c0c0303488105a00c81e1b41d80e0f01e413180c0912038000b034401c0c0e0700009420244030014101003c009070b039504038080990b01c83c400000380302200c04060382c84814070010f6800c4c400400c5d007080941c0d500592146000c246c45d0754910b8403d10310300500315990354003210000501e082103000300280c42134040e000c204001c420300400b0100d00381c44291102034081500d0b0314041c030400d80b1620140b80441c0107801103038540450f0a01154607001e081d8080c90040c2c0210560007402c1d1703804400c05005100354900350a1500c640d940c81501031140b920241071400c0d20a801000d40d031018024040c48540302e1008545a1411140911160b40304a4040b50701034034245021800c18048600340f405030354100c083c1210303551011400e13019160b42c00000d00c28005500c80c11044c02c501c2d0340041c110341d04020009038840d801c924010099651034083e00038004003d1099500021a40400a51280c0a45030003180b80080c04083e03420880403050590304001e00207540405000303401 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 705857895 1250 705856645 705856709
    0xa02061306111507110705100906021606050a270b0712170a02090d170a1805030a080307050d050406140106020c0a050f0307081b030c0a0303140d06 65
    0x14441c10303000305454441036160750b45400400c103d0b05900001c961041d10815aa0f0605180403044644494486002034044a64424584000b610310700c070034001c40350b05011688010074620401c1a1103410075a001d016400360f140b4040422808405080301c0f184408610b1011065204101001c02c1d1100400c41c0c0f1507000d8a02030b0307004110b1050069a4502c03514109100340c001407094021038980c0010704003c2d5003c0349881e50710520000d0310a003c2a5103100c1e03070100103070b0b2f40c1186544888200007d44001651514212000440c1104104580707010030500303c00c0d0341c0403104a540340c0d40c2d42429204c50081150495259241c6030030041005015031042d901c100071040040307031b6a0380e40c203401c9030b55100c030a40403038200039014000c1026051162120003000700c000c064403502070701d4042c0149008440000300e150041d2400e1014000d090074403010390004405d60311001c0d86801d42e2000384c082c1c01a50601c0e8001c02d8002a03014120001d64005c0d4098041c2c00c0c00c1d0351080e41000211050916a0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 705859145 1250 705857895 705857897
    0x120906050f160206010e062e0f020105220b041a090c0a14010518012007150804020916031112040b010b090a0b0309010b0a06020f0d08070e06030601020a02061306 71
    0x2070305602d641240001000c40c100c80003401c01d684140e40d00802d03c4160020902a240088566046c40032162083c00154081643d00d41c0c0303580060099020003401d50398064015030b00700500404040c0c09510640c036034915035802c0803141e18617032620f20307011040300b803240300d40502c80103032400340441e04070082070b0b41001200072a140c600c0280c0740ca5901c0f11001500303500d00d011840400c6401445000300711131481c0041c0504102c02c0002920400007091080301040384925000640c05120130340c454800e00d10100b07443d14000841745490340c04950154000740460a00000d02800101c449101c1d0b080701d15400101c0d82950380f07680c681541030b29a0038040d58200c031180c0d13504d0008150044d5590654241c06001032050361650318003400c03076216901c00340113070703655540307908408510307840b60304d100001400709a00420051490416090400a4030b940100c1000b500340d080c450b0003a84035100c0303641607604860b229920b84480c40181c1c50000e5541000f500401e0115042c591208203024200803141c00d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 705860395 1250 705859145 705859171
    0xd24051906091802010e0301090c0605130b03010302030d05030901110a0c030e030a0203120a0311031003020102070e040213230711071d1611030c0303010302040f1a01120906050f 78
    0xc6250207010b0700c5500d421510320b0b00f0300070381003c05580f00d80c5103000c5030800500002800c0308aa1680321003040181c000c4000700384001100c00717600714003500303002c000c0c10f0505541e400c41d41550b00098544503a00b00601c1001008004164000f02c29446065044140c510300759a440c0343d4400501041c028640c00d43c04180881c0101102d07040c0402d004070391940c01800b8011801d85042602840e4210071011000c0550b1250080f8980324010300840c0504070f40354203503528618620009152403900c0e0016909403420406200c0140c071130040d12044400703004404181071082401c0c2120511420340c030760f58600e64038018402019000490554071085840940c0d881a445400080c0d0b01040b4080d800d1118511000180444c1c8a40d02c0c481d0b4410780c245080c0801c0c09012141034030b5900410a4044103400c000010821840c0602c14018504240c001c103124400e4040076107100c0300b0304408428188001e030300c0312140d41c110540c00402181d038003290400031424441c0a803411031104407480c2c100281 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 705861645 1250 705860395 705860399
    0x60402150f130602101d0a02061b010504050102120115050301050d060f02070f02040501080f07090213030c0308121803181c0605040c1a1b1005040305270d24051906 72
    0x2004002d20200383d901000a1000c0348040e800d009e8603a000e0302d0249400071401828400007002801071074003d1780140005a120300841901000c56076042e440802d050500071300d40c8442d80c0c2c01c081901d04450701281d018660102c00e0600d074000d0454050308923051840010120108191144a0032025000342e804018036070f21000441d94405c210300f00c01c0d01540c1f0035070007009642c1498000306400303407022941c410010382d00c1d42e8105e00c2c0b5000344c008407000d5401050025000081c3c0180c10b60180e000302c02584901707001500c241d180c0c1b0841c908a809801d410325440031644464140c0410320280d808928426001c40c180305c4003c1c00c2c2600c0807215580446800030300d58607041703d102c40100c2c1c000304407481c24102d40c0c060082c0e4504d290601c3c140d40510720482d681420315120305840b0754002d813109a9030b03050005c00c086400310450b01890f10004202089815a02d07032041c042c0d00366900800d00030b203003240149900c403508005900c02d4019070804042001e91140d102081c200400c040e04144005c076 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 705862895 1250 705861645 705861671
    0x204090c0e040c0b0306010c020f0a051504090b040203060d0f020d2420040e13050d050c010c03060605030c1303020d1406070518010813060f05100602060402150f13060210 75
    0x440250313640e87c000b40c4000050030162424801d4080301c60301c02814a075205a032203000c180c070f003c00400d0a41c0b0342d06012900f0400004680650781620700c089800f1491442d08500040c11081c460178054032544a891b240d0b421525030100903005290800900300b000b84000c003201d00164219030205502c1350604c8500042e42219440c000d180c1c4103144200b500340303410a440c0b010180c00c01807110240700e45120803400451001d1101640942c0e00e90b4413641d0310501c07914070b01e003942c40c04012a130416103000b5003001142c0c0e010003a80d4001d048402450f40d240c1c0c81006081d12580b076900060762080400b0382c014100071180031034440381101d26060360040e81e01c010013965107001d800d021000032a079040f48034050707604c984207050303112040d441c541071380724903548503d81111141d40003007044941e54000d006e2140d003845076040041c2a24802005681f62a50100d0b1402c24003004298202d5800324800c81813040b80780540e1001841c0e8428001c07219903e00c0002d58520401e164012800e10340741c40c1300906 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 705864145 1250 705862895 705862897
    0x1e0109020a05092703090a050d0507090b03071a1213051b1309030305040c0b04230409080a0207090f060522021b071502010203010515070204090c0e040c0b 68
    0xd800038000040a450071060101005005000790b215a00e0040c030454102181c05852422410035402962560b1540e07050116100f09030300100d1240d0f4030144d2680000f0303000220001950403c880104034583c01001007843c0003a943c001d0303210100307805000688030001a0241039072136850340342c1d007180341c07030300002e290f00c5280303c0b200038129400524814500201c0a958450307040d1019203401007403038601d0040000c44200f2101280040e0702d5400b400180050a02c411000d002d1880385d151130203240c205029140f000642c031014a04482e050b00700320700d5a69521069003640c01694056a42c41c11000082d141d0415004040300980b81007098001c404440c03041e0301c20f49001810401c00740743c2c034401208205201c1d501100283d42c00b0080c407100c01080346400c1c00c524000c0300c010f203152070420b550a5845134040218038116841840100f0950382c40e1082c9211042e070169100d55182054004113000d040309140c007803c140203030900011402103158025100e10f00078101154061b840d01e03020002 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 705865395 1250 705864145 705864161
    0x151a06040605031b301501030e0a05030f031b180f0d0c080a0614040f170705011506120b090105010516150c11010606090927051e01 58
    0x1900034081403000c40e01410045400c15200e0041c0180781c5090b400d903039025400208401c884009982803490258001c09011418041e5015190038a2400d9101d003014460b10021681c105603c400b14910b0300e5009001d21100c5035080300540765a9040b0035100030856000741e4000c1004000f50000c0075440c0708000c1540d00c21043d002080b464036182d842045924031501a00592040c0304080f0400050911040207006040003405840d03c81c0860030180110b52241d01c41d05c03030711080507042100107148004508440d95020300f40c048010002e0401c40c541e4002c8680003040f661928542040626403600000308a1f120360b40c0302d000300a1003008a4081e1220542ca5a81006040d4014803007076004a0190005185666800322642c00503180e40c6000d40c28103142c5000c85a480304698195135010301d03100039580c4000e00a000c0949002e02c0108a010940300714042c144e600d8042d84800c84056190560303151000c503035010124000e081058444004c1a00c0000314018403c04908041d010300486072 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 705866645 1250 705865395 705865399
    0x21203090d0e0f121f060806130807080307020a140d1d03010b041a0118030507050103020a030603060c0e1251010306060504140403030b010306080703151a 68
    0x480c0d03640c001c0082c1d61042c0410541c640c40801070303201c1c0b181d0742c48010411009140d004000c20090184034000359411180c004400096402c018090004540010f245a04504a96074503103d44003e070424030a58001c020340240300c600004180640240e0000e1041510780c01042e0b11103071181050102c9946d48400340010020400590000c07454800554604e686200082d0004c1550954200090f044070b403100c0110110015102020849580c45038042400c400d02c0240d0740e03065811030f11181c2d51050707140304040c10503400085c19540300d4030a42203c8001c59001c1418805000d040a0140001e89001d103024040d040d0312031190700c0d40c48005460107000300c03408001079004914803865255418110520780c4080f545849030101141d81480800e105a095126074025505500d404000d0b12103a40c0000e1080d41000d903150184240015050b4003e9030500b400144808001c1c0107030090039550b40940c90070b014130100001030014000035000f901ca010541003100207a2201c421a0030840480c04c2a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 705867895 1250 705866645 705866653
    0x270a03030c140c010501230105030a0b0418051b301c0503011a0403030e0f0d081c1b1403040c090510080c031f1a060307090602120309 59
    0x2090295110320441e032014a08498120b81c00c03840041994400c032904241e683d91000104032401d40300300488903c80c104403864080d21100c0000070309600010b08440f80c059034681caa11556616503000d00b05170701039000803241d002c126080140d1070341c000c90078440d4a0030b801001704200349458000400c0c1eaa4a01060b072407881c04407128003104401d0012442114031034900980c1051100c00030000a504042d038131590b0303d604000d60741d01d80503030300000030704100740a00c01440001d41042d040d01c4610b400b0b554420b804903050300000c0d0764145030580540901000070300040c006001c0041c5103c0991324100504c00701d0b940c0e848420003921081450030004044c1541400a0b01c010001585c119020308540d01e045a11140702c2011102c007500c500c00300047c0c0c02d004100040c024400050701140480c050030081c508580700741049805c80300c0b13501e4074595a21001d010041948038200d08240043d0045899150112010340200c107540640c2001d88104a92a69214a1441124407441d041030180c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 705869145 1250 705867895 705867913
    0x506060406120209130504050712050736050601030b030303040f030503070c05010608150a051009111e040f050d11010318050a0b07030c05070809130204170627 70
    0x440d4030900c2a050302c69801e808004880b030030f6580d01503841c450049001e000995003080d1400915150982d8082036000c0304180707401c03000c1800458a5000c0300c45144404001c030b1701000c10031041c112000010035503400084050785040c07006074092840381c04203032000c0080b810140b0030903139240811100100980300c60401c002c0001d104d0b002030354101c0c0c50346c03e100c010408990f03200e03400d40b056500300c02c010794440c4070f03440b00504a00d0150354200500d0081003106051210b904c21080e030300790041504040d25040b18030b40540c021821103285076042c40c2c81c8010398030303280c0540b000e9511506c40d610b06e80781d2440d0301003942d281c20b1040d900103582c007480c0c800d0b41500c010010340143c10300e60b82c840490004903108101264061107000945031250380c80f030041d0700e00203501504452083c07e144041000900280000540b03440840318111012103080001c0103000310002c0107071041e038001c2e802082488551642c1d80b08001280c0c2e0041203400d05a01c001101d120700301a40000c243c1d00070040d03030b001d8448 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 705870395 1250 705869145 705869147
    0x18031e02030a06061a091c1a0f1f03020f09070210140610182106020f030906090c0102030d110d110403060e03030c030c0a09051e0103050f06100f111e010507030506060406 75
    0x891174034403400c2106402c1c80d4140443d55014401c6030540304408908003006100c0b01548c0b0341c45180b40b84c03a40d1a94ac140d0858010070000003080d99210300032101c82d008100040e0007080601407804205800340710b20b90001c2204a21841c0c06da84060091038000445ca05a500500c2400f0790350b41406000460720385041c0c144c450041c804404c0701c4000590340d84a0002c00c2d40c5000404c010308401172201c1d92400d014410307501d4103500034040301c3c00350083d680210035a07030b011044442d1440c1040003c02c000d04610940c44281c4070700c5000c0502c0e1740c5443d181c4100d2a03100b030084d0048a006103010001840c019027610b0b01d038442110214000b480400014100583c1c40001e45000e540d43e00d02009802d480d0b1010900482440c0342d1110b50020700c00c21101070f580c1c18002c1d5503120b850568400401e003800030118120b000c1c0400240c0030b01a08030046d001452081c0b0a81c00c00b407280300300b1144040032203900850a01c02c13940c0d00c1c1c881542070400003040c45009000e8140114000760031189040d2800300 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 705871645 1250 705870395 705870439
    0x60315051e0c0f040b03011e0b180a0e010609030c060201060605073801150c11040b0102160e0a0c1e0f090e040501020307020c0118031e02030a06061a09 67
    0x410300d10000403e206a40680c24204080e10107030058504445e07581d410081500b121503e030000c0d0840080c4440f009205024400307050303481c00f410134290b04248040c940001441a2003540250080f003000c01c00000e20298060010b00842c0e01a00920702a192110300803400c0c0d036100c1c000d441c04150200016400135140c0780d580c0090b00750144044403a2018082c070081c10144080c5d0300803078a1007280040c070000620000e691640744540c100441d120000380d45441061342ca07044154842e41c0c0e038210034009a4000d1000b000c561070310300c4420200a481303500c4511106415142002840c2c0b503d8111000f09000e402401e02641a0a064602c260156841144c2148500f00442c00708881c52100282154900704000e000d18070410015880b46012400203290058960700c05040250102c981042483c1d501e21007802c0d40e8000c3d01c00d4041c0e10380701240d0a0111682c2c407000b905807141c68150014088540c1c481d00070368030340e1241d14a181003c5008495030f402200f0249078003440d52850111403c103044 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 705872895 1250 705871645 705871651
    0x30510060f0507061d0d0210020a0c06020903030f04030308100f050319140a03020102091801030309091112090303040606050a1d100302030d0801030b071b030c020d0209010603060315051e 82
    0x14030f0101e907250310094440c1c0c0c40c907490003800c5c0481d40300714031101d00e0f40d4052107521f1600d14035203402c508241d02908018045089a0b60152040d80d0000c0e003c00740340c500340304964105c0500701003165a02e0b580e1400801c2030344200c03051040c500b40b0007004100c00e0004014482100c400038010082e45c01e1098400d0086101024101c406440c2403224850340c1c103052001c000507500a400041c1c84a80040078402c120212000000c21105008010b000080d04040c448007503c900c1c03400000c080b6680f9800c0750180c4a03a802c0c03594503280030300c20000700101c000000c52065105a0090000395940c400348006000c16000c0e41c1250b1400c02015000c42016828940e44140c1518203008400d1303032a00807a0074801040210350014801000500512610540e125082002032a2150a1498070030b42910315040301c120042c01c002811464206540c1d480b03070441c2c02150010038a566550b520381e0094014010340c8000c4420240d61000c00107030962074801c40b031049400684285c0840e5500c4960b80081e0802 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 705874145 1250 705872895 705872903
    0x3060f0a031b061409090112050c042d090203031801140c03031b0708270a090c03140c0301060c02150a080604050a02090f13060308030a020703030510060f0507 70
    0xc004000007244541e0300e42e0892199811400700401d003411030040100f0102d501c03004418001300700344030007a101c2c0314015044030f00c919403d4604c40100d10b0300030700b0705040c00e01c480d500505240f240d41c01300c10741a803e220005412040b114801071402280300907a144058082c1d8581c000b030125540c2003034042c5500c2c0c085070051400c28a14000500901c001e034002c08061800c0da88084200702011109260760000b0640e2040c50a040c08800d41d5460924800c000c100c00e003003419803080c0c607081e5964254403001c0c040018000c1d900c072034585150b80c00901e00f03200d203040080e0400b02e54440c1ca003a041502801030030800c025915580c00e0017030036603e22084610890704104030488122145040e000608450361070355403486900c4c2441001c10066490107404034650b2481005600c45030364407441c45200c0c21805035051304903800d1119816008102d07990001d4070b110000020000b0409565006102040c4aa1400c100c0e42d04c6031445510006030b14010300000c61002d28000c001c82340280064030205100d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 705875395 1250 705874145 705874159
    0x40504110f212503081e120a0c180b1e0f0309030a1d030d080709090218031509060f15210d03020c031605070905011509090203010b03060f 61
    0x40900e004008034060008141e60b81107072158007183c2c00d002406000b01000541a4a030a50454071074468a226001422030318910039002c69007884e0075501980c0d2042640c4000016034030344445401c02904000c00c0902c0041c1046401c1c0ea01d540c0c02074206001d0311907c038807090602401000d02c07030000c1010040303410300450912800b1400e1003c0c100441c41025a400595105c2c07104103805072841408069045c40b40102c441210407039100000d00d10b110540a00d08109503440300131041e1070801c0c01350048241a130000848803610840070f0103001f246282030303086520040c02494841009002551449119008031002c81d413203550700811242c103c3c01c0002c2050304650395100240e01c244046101c4401c050020094084a9409129041c010311a174102545011f81e40d400300380e00c0344104e8a0a1070215a07d01118050240c2085400054913840c4820451035860f81e680038401000c00407840c0016003940b60104440b00e4900075603040350001103c8608548600c1e0801c10071050f61402c40d50030640d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 705876645 1250 705875395 705875419
    0x150c050a0606170709020a05030705070c050603090a0b061005040e090c0d06050a05070c0203101d0604030e031e0705040507050d050f010810061208070c1d070e040504110f 75
    0x71151188a00400c0100740100600500107901410b00c0403d070300207a4842d01c180321080704990403408a1754042410300e492a6100d51038a8000d10600b1180c0005030814400b100700606043c00203507410000e80649000c04296450608201c0c01d40d542d20888000200b052208008031161031050030b811103140800c1e116100c40450200300c095060100c2070301c00903114002d000121041d40f003034035001030403460300d0444002c1b40c1e0003299075100703000c40d14401150b88003885600d49054564940790208030000390b030071a090a0a0007411648030b00845c510078007640c10781e4050b480c7c55034070b130b0002c00c00f0302c0c009400c50b246440100401040001c0c000b00c10310600b003040c44400086445003d2258000c25001074065050840c0035107003220840b06100350510b0f040b420b0103002e0031039858041c5540d10074031955a810941c504280030358030907404a4410301c0c850b40c81c2d0500901094809108500e00d9881c98260f90044041000fa03d000742ca003d011611540250401c5051110403151440030180055079519 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 705877895 1250 705876645 705876653
    0x11409191e080a0f02061b0f0702090906061503010305071a040503010c080f06011b08090103090c090c18033203120a0506121005040618052401150c050a 67
    0x7201d55a001c0b10704200010349420724a0700100e904c03014004910090856160101e5214541022003000e04099440864103442840b000d00032104101c0d80900300b0001402d00302c0d0502d98992058807080d03c01c80318400815a00d0a10f401964101d079086001001100c2c0b805a00666000b895140110848020000407805440900038281001070580d6524614900780e50100c0351a02c019002a040203031044a5440d0160520003d00010360400c4182d550b0300d90000051b0020b010025004041c00e48403100010b00000e9607004100841e070701d8031a03203075403902d41103142407558040c0002841460007104019418210b2000015500040c41160101c1c1000d0005585141c01600114244044490811004011a025040c0c2100d02a20400b0420f907018a5580d200d980054035140c405990320002000d0001e140c0000380501200300325124a04403504010b5111002c0c0f8803040c030007030782e0300b0880d07180010704120190484142000b00403004030040c0040b04c4040d030314507040ea864411030525401007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 705879145 1250 705877895 705877943
    0x60a140c070312021c02030c03070222060f1401180306180b15041a010503061903080d09110108010614090607060204060503100b0408070b09040f090503090301140919 73
    0x24900d034000b440311713000500c030580180401055603011500180324403011250000f003a41d01031907044802010402d801407012040300d290000d183d82c1c0600380400040c4800066101500ba2000f1134100945070746288015904030401a150b580700000724082040032501a034090341c155a88070601400c003042a0319840000360064540042c03001e8007143c01c14052406204481000d41013081141c903c00e10800080d0041c00000c0086024602c1d400300654801808150f0030051540704582680782e40800c50548010120103c003104c401400b080700000315801041558102c03512580c43d9482540e0082d25404107420038244c2c150808014028000014910b00252010f410740d55502c5032079291095a400034404282d00946080034104410322a07044003180752010380300801d000300d50300c08848011500910408045160341440c0954880c10010040020041c90600314000d022a03c40f008079030f112082d0030b40300001c06030b01c00328250101c1c4040b144001c503a5405a14540d41c0c141e80780000303200b2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 705880395 1250 705879145 705879173
    0x9031b0b09040b0d1b0524032a07060b09070e09190e06011707050d0c0506071a0a090c0f050d020d0228030309170c0114160305090f060a140c0703 64
    0x7081c00c03174150501c51805e103030801c03054070404001d6400d030480410903400b415100103840380c6e40100551800e90b004c0d214092000815001e02d91003260744a80c1030030b041004200e400c1c03265100d40d03801800710b074505101701650507240000408410709074490f190102c61310344604409401e1140c03148030b9119100c2043c841d45000f040010185816410216819801c11982d40c1109216030003404041012821000d2040113540c03055400c965241031600300303450020a11581c0c08462801442044143e01d410340103020710307902c194240381a49448901e6410144c145014041c0c2006800389000007605c0c28049141c056070000d0405000104e610071420048014000803a1485107108420030401d03501c103421301c00078041e1100384080100791302e142e00c1d222000c00501d14100a417680d2181c0b401284074080b1464441c0c00e51012904008600c0c015007281c00c1000514800c2e0a19081d11510381804011601d28039125615503020a04840324204142c0110ba410308440c410b429001c00041c07074214019903 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 705881645 1250 705880395 705880433
    0x9100e100e01021c0504200f0a0b0a020106062109060b041b0f030b09060621090f0f3007060f0212060307141002100c09031b0b09040b0d 60
    0x41e6030b004210560007030250301d66013015400e14101c1080003003104507640700203000b24110148422042e0000080c2d0340c080b00c084c055840f5000ca040001d42030400d0000f0900001107030000c2c0b00b01543c40c00e055a440c00c00f03c6079001c009005d10011a04c0c0195130340f000c1c0d41d0b02d1280400142154120010404a8448410342c0100321a084403011440741c1188140d496050286400c0c00080c50402c0400c0c01c120780500038134040c036400314856a0004120109401f0300c071100742d10701401d117442404c1c1e40e0348603445501c40086000702c610f0b040b20311601003442900e5400c54860181200c0c022580d150000e9940980543d03696414000c80002400714081c454004400480140c1c5900d00202015015139014102ca84030b60301c00e12080000340c80d5602e0801005204a4500c114080700201c2a81070400345010801418900402e60300d031550420050001d583c001c51110311700c690301c00e0700c3c581c1400d0a406030b9604c4041c00c0c4030a4600b45042d402c2440d8081014142d0180e1a0690b03480c240c40c51941c240c000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 705882895 1250 705881645 705881647
    0x309050f03040317030606041401051b1c170105060307020f060406020702010e0d0203070501031e06080d030507050a0e040c03061220010207030209040f0606030b011d0604020309100e100e0102 84
    0x109125072100200011040d85130031620350300740340b4001981841503118202c10784407800e840501580c069030176030b111058541010f641d29130004a00c0e80d02c41641300107451030780c03120b54510564603119400400011100c01030240107a400c0608100321070300002c11a03011841003180b069418181844911300803441200301585400a0f44000b600b4200000380890241d0180070032000036980010b075000c201c84007804d0004800800490401c01030303020382a120500c0b030a00c04001010300c40001c060320381c0d0b4100d1b9000c02a548170a03100700d45500c100d0503c00006400c071701a140d0613140c15170200d07000c641d060500148096840c4403208103031000c40001c1d00c400308403e02813860940030528001203440244080c1048a0940c0d001420742c41c00604058151014045410100b151680c0a00060754100301441125a954140e40a20080c1c8480342030b075142c03d285c0070031290304090003642d0107003101c2e42c040d190a014141815000300103090400d815031080c42c10201045c0151b2140c400c0c985d040c00009 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 705884145 1250 705882895 705882899
    0x1a07050d120b040207080703141b0304081002121801020417031801080717040c030206041211030a0b040305130b030705040f0503031602090a0b030d1d010c030f0f0309050f0304 77
    0x407044409003a600750041d0300410000c000203c107142200c11180c0e2500b030420122060010005848c01110f000b10306c9041d6956030204507410000113407003150040800c80301e000840a21400503800780c0000403004564200201e500c00e03040d181c01c01c40c00c05078500010b04055595078206861030b000c10402c8000e400c0050000070a1142000d2450360b0320080c24080c03018200b15600a0000303421207582d440c1d07040c02e4000701d410800410300442c021a00206042e44807501d4094030810b40d01681c000310344290015051380f1a45c1130201d980001290444500740840e51251025030300c0380e101252165450498102c0410200389244c00f860281e4925601c45072114108000d0010703845980d04103031311a07441400071100c2152041d02c03148011340e0650f1520102d894000e41140944028410b46078035001c2c0040b1a05816401000001280903089882a01350254001500c60340b200300c40c0038000409154801d601c283c0640c1000c00c50038004c0c81c001540c0b070401e8442d9418880c0c100d1608006030400a41 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 705885395 1250 705884145 705884177
    0x120f06030c09150d15051e160c0b04050c12031b07051507030c0b0408180f28030203190311030309191502030916080102070201091a07050d 61
    0x301401d590050361402d00394103100c45011006410440300c40c4c03245440c00e280341c041103004c4040d01a103000040051000f418825609031241403800002c41e50708441c04002000c22052032106500080561219400340d0781a449034003002c50010030503074892180c104101e1107612400540d92884060202940d1100e80340c20300e4003007802007140412219030010b5018072403617690800c9107459034007604045950f00728526080d150036500c07100180c0001552030401c024880304000030302d40440c0d542400002e0004a03410409420200105141c100d51402072400b014501c03012904200d40074888079100943e501e50000e032821001c00000c0e401001140b00820801d508034241122110700c15001d142580341404400750b40e0100034840004030101002a401170015041c1c1d007100034a9071500c15035980c50122205a510701c50407804900300d070710910300040c08010620170745020380c0d81692401000c2d031400c100c510312011a80d07441c0b81000000c201400000300708004203d4410007a8440c004256181c4036 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 705886645 1250 705885395 705885403
    0x40203010b010215011214150105030111030408122a0c0105062b1b0320030106060c020d05030d0203070c0506091603061805160305070f0b0301031205120f0603 70
    0x209180c15903200f0304d009036100751200030300340c1514103032142420502038038281002c071022152002d007a0340c010780e101c0c0079081e501080b4060507075078260000d10bd01d011440c5040d01d6803204440c0a401140301b0b020032524440300c070f21025006045420382508170b00e5031804d4018281074680019014100000d80d050f041c55080c010598000c4003116039428000458001c5c6900d0306c0300001a0107060850440c3c00200b0003410007502c08034000207010903003144c0b41d1401d0380940e80f44011182440d01c6119402c0e1071490140503080640c0c1d8165a400c404840b03039401e018001c1e411031011251070005000004d0f00c4842e83c400303144620030030b541e04c054118460606a0070294041c2c14103107103800c451501e8071850820108001103941c044400500401032403407040700075442c060024001d01030440c0c80d00c1845103170340190303081d0b034007410680c0c8246558100010351032090b441109c200030300500c01040400d55200084003030031800c5c18042d28140e02c083e11107001c00012a07601c189c0241c03200603c001410100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 705887895 1250 705886645 705886661
    0x3050a030203040f050712151407050c251701111b0a38010b0702270109061701021e0a0504030804080a031e121d03040905010608060105070f200303030f04020301 71
    0x5401000b040312740004115100100030b00d044280500001c0303040c00c0c3d0350208600f401221021180d010b05111580380c03c0e0703003a10b082c418042e40f403080d0700c11b22141e01818462810024042c40c0018980204042d10000304000036040306d482d070207002c5994000c40c01c0060403180740305030780c441d000c0903441591246019a00b01034124904e4036054006019510450040f6551036404480c001e18003155400d03003106141c0c212400750302200c0204000108800b0b550441c10548000d03008400f032171502c0100c03480c202d00a588070810400c40c038013405491140d0001c028051103072a4a45241380c15100d80355400942d0040c4d005086a9200c0c2c200f480c1456803100740d04064080c076451507140020592002070003201e0035664072043c030380e480a504000780c6108402541050000c41582d480e5039503000d08400030402441044007142100c000a007066100313204482c45180c1c031200e01c01071110551259905048042c541c440c2400782080181c00d6aa0200045c6100d4403580e4408003144c9030500c14142034503c15 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 705889145 1250 705887895 705887933
    0x3030c0c3715021204020f010e011704050102131404060f05010c0b090c12160b031b030606040f09020c010609151809080c0a03080106090303050a030203040f050712 72
    0x81c0c41103210004038491055030301c101c007001100d07000e4450a00380c5000c810040388030b41c2580700040032501003495a5207284120700803600d036a10500014010b42c1d821440c18041400680211000d04003801d04010150300240601d0005081c06488003190007207014640101148d9948880110403600c1d240c02a00003a0540345241c0344041c3c500300010b41080c1502000034201001e450006020010170049151050002410041d601c442c008a15031241c0a5400e03074100f40f094400302140401814080b40c1c006d9070302d4422903044804c00c541000260704003420a9074403110801c00021240e0f51041440050922480c00603a2915118062400c503409a80b01565182c10f0144045200a651740d40804540c00d15000340310034120031700d111005216000000300104000b1424141b5008009003501c800d511984806250340d0721201d00761505042c6100060006a003004040783c554480d801968001d4403c4006000b440304941d6a43d04011681d041100440341d03e20b40b0000340501c06640c00940d0303103c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 705890395 1250 705889145 705889183
    0x8070501200a051b030307091a0901140703020f070b1210060e040207110a140901060813060b010c120525080307050f04120c03060b0303210601090803030c0c 69
    0x8580c041400c1030240300070a90a2120200741101c419040ca01c07400c0210318a403056950300c7c60005005051032006d0b0054003103103c0e10123a90606c035130000044403540c1c14161130b611064510750f50148880e6101710b600301c04501074100d854044040400000380903007914950309440e80c4400c81d17001003000c0010844854101840c1e000c01907e82c000d0300401c261041500c0250382c92555050044101d6160098a600824030501c00220800e042801044080c4100c514a115990f00c82c41100c901d0002e66840a5205c0215484000500190f106118a401c181010070310520a52582000840044001e02c0858000036251800c80c590300910701007211034071881408114a0f40300c0707100340c0c04004c01040501800194040501214505070390003403450f07621540d0240054540003419251602c03048401d1414030904114034079020065078a000042050503c0000307034943e2440d521600038201c0c43c1400b1005501054080c02480198806c01e05c3d050140d548006888189150000c1c03030760400c039a0340d4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 705891645 1250 705890395 705890441
    0xf07110a02091816030c030b0601020d092702220b390d030f050f04111e0a03051b12190501180b0601091403100f0608010908070501 58
    0x25404030020b800c6000308841c04408400c4400c1245131181105108041000d056400030030440046050010399210707801001e4203441d4980103907929814843d85c040410f2014a00303018505080e140c81c98030b080c4d50004801d0310200c0006070022a400211a146e091a004d8012a0301009020407080104517115402d13242114518288003c0d21103202549414070025410075000c10205c0c00047c0e800b40104147da50001350200013a0040104040120000d42408005100c1901484106104030740095000c400145003000b0000351074078000e02e024541c8031840c0300c140c10703880305165200030b14411030040160088038909449001040040d8600c281d01030f28048003101808120031041c0110124042c0c0758003000e01d042801340119a042600800c07034403d804c401d2100c10b50b5154081c03602030305d03041103264071a030b0740d502d41d007a2581c2d0051301036015500a442944540e40500c1d0b101d0b801c0300300000e8080d00c0e407101a0a42d6503001c0159040000800c541d410701c00284100301c6851240004c624540b5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 705892895 1250 705891645 705891649
    0x1171609020715050c124012020a05070f030c06050309011113140904020612040c0b03100501030c02011a0d061b20030a080c1b0609161e1a0705060f07110a02 69
    0x5030f0102c1c420281d140d042c881e00700c046010820980d280c1ea02581c0d4002523112a00001d68440302290b05483c1da2107000b1001504240e604030342001e4980000c0e074049060700300360301039581da0700141121032207651301d80030401d1040b0311101420261002c0c40d070901d012032802c003901c801142c02a400900c07070f008120920006a50398000c840a01825001c0b40e00b05036110704041e000007416038829501c0c604c000040141078041c0c0030198040e10401d032400c002c0308900d400200d089405030740700c600f00002c2070150600c143c90301e44420310803031784900780204114415111904030b40940c546082c011906220040104c1c40074005442c200060a078000c504251080c04024040900501900b212000001d0600d0105100901c461300f01c50403801200c015042c017040c03440c0e942c500142002040403040c40c01195010308818201020092240362444860505454070828806120542d5102c00100400e90000310140107681c403030303001e082c003421007031610f010064181c015a0459910503004404980016 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 705894145 1250 705892895 705892951
    0x9190c050a0e15040c0507060903051b0f07140a0503071805060d0b011202010c060c2a0803241002070e062e11120301171609020715050c12 61
    0x5000032a40418100105d040c156094400c2210180c2107e04280850b0145074020000f07058054120109046003402c40340d40945a0501c0c0101d040550004001005011036441240c600200002c1c00f055038035603130f44006440d02c42641d20541c16400008050290041c41d807141c154410f000755112600c19286541c2c048203408140200001508040315840640e440f030020596459801102002078120301c1e8005002d00f040b865803800b01c01c2540380140d056001d640c11442d8040e03404844103085444085509001c1100ca24102a20340b00c1c04003d01044c0e41e414402480040a540281440c40d0801e005500282c03001400c845c016602c444068180c800c2861808004c5040f0001e4140c0380d8500c14400c030748185a0317081000041c49110a1300c198080940700450480380180e07004443c81b08190102a101c0b00307802541001103c44480412115210341c008040492240c9107281108488980d6002144ca007943c00c1c054014020804103403212403102c80e1034001c503854002e10000b0001c03e0205081c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 705895395 1250 705894145 705894181
    0xb04120c1e03050915030f01060201180209130203010221060303190507020a0b0c07081506010207060f020715120e0c060a0c02030709021603080a0e0601090509190c050a0e 75
    0x181e0030142905006040c403910a40d42e504800920204c2c1034890180c01c42000c0d0410b84600595450010000400c94014481d080b001c01d101000c3c008260025000c0100b03400008100303010884441ea502001a0380070700c02461411141e103501c04404040b08850039030641d006080703034000d503c10828038035490040c0d00752903143e00092500c103942d8103081c404034910101301d9002c1c800c1140040385089001d40045521410380320000200e498070944602c0c2c0c1041c00105440450150300441d0040c46541d2044440c40141c014600480d101650f80340c03074650300f60304060000c0c3d00088901c810a5000d4066010f9045003004140090030b806d0a104009a114480c800703d420a00001d0703080c0c0021503c0c01e1146c840207060f82c072021903c0f82c0d00721500340c40c280c01e1030780c040b400500e00381300007a0030038100d1251807401d8030510000c00c1c1c0c1e40e0a028016005000180948030141b08034860041d292400d582d2606000f44900c40c9510000e1602050190083c00e035008550349252260070405240b0460b215a01 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 705896645 1250 705895395 705895433
    0xb030a0e03070f050c01020c0402041a09060f0406030902010801060f2c060309060a0b060c1203040c030b040c0501020d0e1e0a0503120c21030a0f06120b04120c 70
    0x91a15051403005145104000c002800400f00d50020000e0002c00703e0340103c030a0b002e80907a0704102d106000c0004034840c0c1d0082e80480c0701c104011041180410b80941402107002e407880e03290604c0600490720581041c0d01c940000380e02c4100038011540e018030b1060050469082245e000d1096030401391001c1000403c44a034070f0034040100c0c91116040411510400c2c014100315520704081d51a1030b15800e0807104044400d0400d030300407034241440c50403900c0d03d0042001400d00c048260071490b01c1584003900039103012107940f0b00800854070b105801e5000d01d103d01d509080840c908000a03050207000c20800040c0300b04262150415290069900322106c038003440c0380075500300c4500184100000b40c10a6805101c2c001c0742c05c680a05590080203d444220f003103c4445894007030703d807049200709411114440f41480411803ca85540114015916544001c1503035a250444100847c0c90b01c1020707203140802d1400d0205102201a18030516009440d040400300f4240e00c032011034a8803040307000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 705897895 1250 705896645 705896651
    0x27011205090c10030f0b0315010312050d02040902031b04050a1e0b1314030d0c0b0a0b03010f0903030f050403050f0a09120804061b0308270a2108010b030a 68
    0x548120041c0040386804100401c1000801000f42c0010020020b03000c18240c454a004903000041c6000550410100b0050803150381c50303800c65803114000d0115903215818040184070100e442c48041c0040c0c0058031914230f006889140100e042501c281401e141c5440e1848100028465515034030044030543e0311104d0200516041001da40b121501d26a004050a020205454007c0031a10144000303c62110a0340340c0b4220000341056124a0818078400c0824064019400003521100006034884a91100040c1d99008000400d00b9a0201724943d000c103030b9078a41000415405100d0b020700700380484001c0102e0f00d4640c0e009440c1c0e100e00d00c0221107005000c210700c4845845048050007070010b034240b94041c3d070740038600200141c00c603014000200b19500340c1c9800f0720000329900841c107605691504019120480c6c1440c00d9070600c1013515a200000c11454817076074082203485011032240b03652841800c81c4a5a109117444041110740420405034010031854207520107882d08085551400 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 705899145 1250 705897895 705897901
    0x2031e010f2303030711011710121515092906030603031b0d11060f070e0325030605100b070201030c090e10030b07030603081603050f0c0327011205 65
    0x4034481e82ea00a500c6a814400040c8101c1048000881e1b000c041400785c0b01c040991f41100d20740c0401180842c0c8192032101100340070414000c103d0b403220710391400b405c00900300d0401c1f00c590b442038502d620f0090a55500d002c10803c0303905260310078180b0f80b80b00091500030400d0124001507007003028100e410b104000c04004100da0381d8050040343e20341e4000340d45140d21000003070075903904e03071203c402c0c80004501410205070f0311380340200b1528810071106540380c240c0d5840500a0729001d4a1144042d010301c60904801264000c084000c01891402552a24034519620f4041c050b9400109000c1d00703903280d50f41c10401115031906035405503a090a01040201c2c14500c21268042d20341d0142000b03018400902007038083e483c40b2181503a01032a10410190340b9141e007602590203c0c84000d12113032041000603401110410380d00f00171842403810501c0c102c4883d4000d01d02e074200c0e589400e800c1d0000900c01c4000d807001ca03048516000101c80b00d5603810024030010706105040925007a00d1a01c50b400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 705900395 1250 705899145 705899189
    0x60601050f09091e01030309061b0f171b06060a080d3203010605070c17120d0e0105090f070f050904060504050c0907050a09080f0706051602031002031e010f 69
    0x3d01c0661200d8134100e8600d07903a590030300425107001c07403060002151482c42002c1200701d2103010126640c2c0c10001e0244219020b5442d8801d03002035004a001c1150107100050b004c8801500014080c086000142524100f400030405110b00380d40c0020502d03400014506103040e040220f42c5200c4d000350a0706143c070301030f984442003400d103103110741001181c00000216546810002614445000d4201c1d030003e684c403400030100320000b82c4102d006960252440380e0542900310010a5101030408002c561070640f80381d07940c29a44d040e10355211542000341d060680c02800c0103042c1c000c20180a02d0111585032401003a4418000392001d05180e4880740040c0a00004000f201c14030100039008020a19040c00c000380680c200505901c00a001c1c0c40001680d81c2c0c000460048130038aa001410707000d403410000b501c071680300d00449412600c9203078050003d65000d104600c131502d00e07010050790703070b10b42201a203104011613303a01144245c03010040c0880c05e40c0b03004e880d064a40070701c5406040003003608 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 705901645 1250 705900395 705900421
    0x8101d0c0906040b0d050f1b0a05040e07020d080f06010c03030903180902030915160507051f090605070c03020c06090301151202030c030a081207140a11060601050f0909 74
    0x601240c02c41e100080c0000c0f5805180c004101346009200c04114035220304d440f00100b00020f842d0802541040c04100c3e041c0e64805005002c211064248186403130750315410400e0301e000864140c1d000d82c018044e610b00c8140c01801455000c0c500c1140d0a05503e0702000180c06280f0005020b410580d4560012003098080c0700b084040d503622800c1c502006950714980c1d000780d482240c10241c0c03400740c41c02480c040c030218614580910020090184056107003c0d00f12803540003480e00fa07070f0601ca03550b0750b603000f041800541c07010140d10b014041140301d42400d00c04141c64000c1c004008000c0541251404242d020500060209003101c00701e5403511200000307405080c201c2d0b032002c998041a6000228400719101c0c840c1214070a805a446032454001016111901c940001c0c2c00c844003046402034080c400c20a443d4030a400e4100441c01c000c41860650541d08600c401c0004110700320320885824200700541035118800b4030f44203103000d50b901d0503580c20340100951540584074003804100c110780707092 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 705902895 1250 705901645 705901657
    0x90b07030c050613060c2613120206091606051b07080111040305010507030c210204030614150910090e010905032206090e01060f0c06180308101d0c 65
    0x1100f02c0d416410310401d5a205060f1032002183c100d4a050503449509010f06c1c0840d8081000b44d11900c5550211b0b02c6101003140e004045084205a8003010400036424109071150101c466000709903502d0b01c5040c040ca0302c1c004032401c0124220841081000c5944182119007014111000c44200c0c640c085540d8589130384c641119031294240255143d900c41810094008c59008000078042a00c80c80d03030680440b501030005c1d40024100c0d10b4800420103003410b00510440e54880018036082da04d880703490485041c030350707554201b000130020b10a0948102e49101185032080351310b108941000349c911042e00500b481102c2d20b40e500c0d10300b2142d16600a520416801b0303008010341e07555200e241d41511000f09002074036000c04800d18070208009100312080c2081e02c820200d8844180d0a02d8029281c80c10310459050800c540300c510440040c51320702601e4000444084608400840b0b0303d00980b02407801421500e4150012004001c8580c40c000c0c1d000f861001d9403044a801d885003620384200344034075 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 705904145 1250 705902895 705902903
    0x60301050f010329270402060f221d0f060f0d1b080d030c17060d170417011109010810090c02030d1b020c01081008010e01050108150403090b07030c 65
    0x403c010354082040c1001d0440044c00441d8074204070701003a02d4040c00b041404640c415008600400200182000c2005021007003c0102142c1040200c034403c40c0000b54058175010b0422900d00200030642d11150115000c0c0b80c00b2500718418504070483e1400e4010080c0082c1c4280c14001e07594115899441444031241c1c1c0000c060103101e01a02c1261102d98aa44038003541803151210442c8854440e01c82c181e0844040d0356103044d2581c4110152110260182910340c0c0643d600d070343d6000040b044008410160110f020f145d49641c274114040c1c141c0c40c86038426007040c0c0d0405d10344804012542045803840c1c1801d081400180c0c80780d260010300080da81e04441c0465150052211aa680010180803208114042402441c4070302c483c10f0352040d03024003080c015034070249900942e980101d501aa0025400e12608e082c0c5568014990035070300c070001c1808060b5501c1c070050146074020301070400b041140c0700403100e09085c665401005001d80e031140c036032051300100301300c020544110420b501260b00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 705905395 1250 705904145 705904181
    0x3010902130b06090d1a0f090604201e090903090d060e010204031b0f050d051f020c0d080906010504020301051c05031902060702151006110c030723030705060301050f0103 75
    0x172900d0010800c4000118220f085011710f40042c0b1240402070429214034a1413026200130b80f41d40d030f10b01101c0256005404070800180c82c41083c240c0314a02d0010b8112141b92043d5a5110020140720303801401a05050407500100500344454664903125124290301c08c000241900f50013059900a01464200a105000540341101104180c400c094150340051540c0c406d40d607540c10400c1501520090020b00e9500415641820007031100c030841c8401c0d01d050409850300035020301e02810800e002030900c0224200701c080c09904a81004110701400082e03d00310b01e1541460005070120502850b520381e034259060062042003814015900e4a00400700d02402988400002a48860084450304018418240d00e10031a15140030698003800ca200480d8051a00b029012a0444410a0701c0700315032080904003c4140c8040211305d0007040c010103144100c50b102241c0082998026030510710a41c4128024041c80e500d40d0200c90445404617503040300034041c1d00c0160040c06c602c110003408212 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 705906645 1250 705905395 705905419
    0xb090307064506030b010e01110f10090308100609032409080403020f01020d271a040608180606041d06310b1303090f09061403010902130b0609 63
    0x81c80001c41c58802c1c000103209826643c6881003241241c07800f40007a40082c503102c20340701c500d50192551001284008040d03484807103400480c10300c0c1601c01c05404030066034aa4410060680c40102980c02101d0f4102040d002480d1100050a02c1e81c140005403003035402e001c61016650f24504400d0280010000a100761401400d00c0405d81c0c201d40b1085e801907402030120451340d8408100c0f14a8400e60780c0b00c103a003100c080017030240310b5a44212040c100403d82070002c40e6018420314188803d07160038020380e950340e003052801409901c02600300d5412544412200401180224003968050401d0340e00240203c8609100240e1864001c1150141c1c002c04041c0300a04060390b480048201141c540307a140e00050078203005d0a80288031001e800c0000c9a004120514540240c00344010f01a16000001645030800c0010f0300c10a540f2290031aa55070504000b28885005100307a6500c08070000c006130480d64020980e0592075910f81001560b84848000031965100180c1c0d40102001e0110948a0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 705907895 1250 705906645 705906737
    0x70b0a0522060909023a020d0902010207062303150d030e010f0c0803060913020a0f05150403080a030e1009060519060605070f02040b1c06060b09030706 67
    0x58501880c00011001e010200f04800203000300c90102c00c6c2c1002c1707001c1034014980c41060580c44407650014101c4041d65090580c0010f001509222800c9040020200070910019182c18001d0780518140020a1000c1d18503022800901040030150001d041d621f40e10000050b0600e10103c8480303901c240d91280c0200be250740502284441c480a807100f80d0085001c140a884080f8054130007040b45e207041000400070f00b0070312a80381c0c204051a004425000703040d400180d40791190703040040024100c40080025242407120104031460650046140600316110000d240c806c810018007410340707480c04103c0e099801c10032903400c5440d40800700007910041c0380100c003810099031210281d0300c16801c5100c0b0a03c0750701c00c00044416684880b8a4a02955107400850481c6801a6445691490040403940320300240718170780d00e0509040341da00718052500b54121a0f543d04080000d030814445048161000900001070720702d0307030a001c81c040c0031204101682d005902a40943c00c00700320103c120b02 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 705909145 1250 705907895 705907957
    0xb031209041116060f0e0705010311161a060411160c0e070302130f0b030f100806010f0e070206100605090301020705011109011103071a0415142205070b0a05 69
    0x643c42135000f8800840c1420b48001655000e01040030a42c000010410030396000707034046c01a10b0b814205c280d08244003124070020400702c0750416138191042c10a4000010071010a0941c800c004840030000741c04420700340c041c107000c9c00510416280a00808505106105d0200310013007941100000305407801c02001006034020541d505c22041180c0c501103580d0100d40707051416140d0840f141800c43e41c50280c12102000041c00c5c010204644100c080b820000600000b80608481940c017007c40745441d08103a00000d0041c9680d003150000c0c01031180e6404501c114000701d41030b91500c10f8079124510f000034020700c21042c00a00d50340c41c11441e5120f1390440d0021704a0900309880e800300512034010401c0d100e21075000028a01441a4a00480030f044000300c0e0741c200d400754070844070144d80451050f0440d100701d8040c8020b40c2c032400c1044520b0614601c155624051105585043c00b510b9607511342e903000d40d0160b844d80f0b0b8400305580705414402c030142e5240f0841d001640007082d00e031106400d54 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 705910395 1250 705909145 705909187
    0x50604061505060f07060c0c06060303080f073b0604080606100906021519020304110f0607150203040305070b0c0703080f0f040609030203040f030b06090a0b0312090411 74
    0x80400c80e04000b0b018902542a0385514000108980c0b030320800b5910040180303e01192007084c003410355840b10204000f8400c8030059842900c9520b03581c14062400d0083c844001d041c60108032400e403040c8616040c10031100c02020300701082c0041310078642103d801c1e406802181c1504000c1c0401c0014a04000240281c001c9209441036422000c41440454a4124500a000150b8000e40790381c1201c1d10031249190384180c46a01c6140803405450303018059a0050b9800c1d12041030300500c00c4d80502d0490700d07258422404030b8803d07151900507601c4040140a0760305c0448050b038044001428140604c1c02ca5095039404226842c080c603191403900090341001c1070540004802d078001801c0814034032881030142d40e20046400140e0384680d0380d1400385c601400102c0031404188000140801e0404450000e5840b0b0b15561862f4070701031041c0304944200078405c41d01796040140e0035205880c00700d1002d061100c01907e5603070394201500858064000000e01000107000051091b1700300c0c00c0f5103c20a0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 705911645 1250 705910395 705910421
    0x40c1806050a030f0e1c0306180504060e0a21050f07080c01360f020d0c08101802092701090201030b0d12050c0c0d030309060b0a0f05100215010b1b060c0f070f05060406 74
    0xc8000dc80b85501c0c0c3d0380708a030440040c40030202f400340c55051074a000b07006195481c586030140c588108001c083c503030798101042c112407070140401c0300e0742c80b12028050700a0314485241207001c2810910f40300072001411100710106c0c440042d1105c002e008a100004007401d40141c08407000040d9440c10050b100714620800e0450301801c0140c0345040c0841c0903180307024240c003002c106030011340c1e0200044200c018003101880d2500d20800d01c1410b405d80c00c3c14101242c88400007446d8665030001500b0782da0302660442c07294a009801d800092116881652014400d1400903220400f0b030444074603000217461075541c00360150003080101907240d00301c0a030081c8188030501110000ea02070080313901c120b000b02c001050980c1d00910050034518180c810a82442c41141c038115014035a044086100307030001d10300010001243c0800c4070714489501c580080450003030025286c030055000c00d50041c1c0c4c800000c60103000500c54280b2503908008643d090b00714080d2481400d15141810051804946141c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 705912895 1250 705911645 705911651
    0x3150423072706051c140709082a0114030903070201200d0806040227090106080705071104020909190501090b090402040c1806050a030f0e1c030618050406 68
    0x5002119950754110445039485003103082d540c00c1c00000e985a800c200315440340307484600d091520103007181c02401c046000340b0050701240e091501c8010302c0180180c01c040d5060740580c40712241c0d0320310519001042801040005444841d0100486040c07000303245511203000044140b0444400c041f0050086a100745c80300603442c01c1c0001550340082d40081025056005404040030042c040d14007154060782c01000180303850303103a05184420040440001c004000c020380404040e0801c1c1a0a90241c266420000c4042c5065079000f0140d205103080282041414000b00c1c400d600d440d01940c00400004003501254580404170484500140c5045804181000000181580548203800d07480c0c40c054040d004aa8464007800050078071720308100100003000300716490072944424010081d01e565905e143d524980b0000060645201841c220b400e00c0c0b82039526a25804c00007038001c0000c10700c111380c0e6458100100207400030202644494148051403402003244031441c1c1c02644658480d550030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 705914145 1250 705912895 705912917
    0xc0f1509060e090c040b070303050f15030706050a180e091506010c0318090e1f15050d0c0506030702030a021009020a0e0408040504023702030315042307 67
    0x115440103051140d600807400b0810240d0150070552182507000090160551030701e59212a804556881108154001b955134002d1003c00c0c01c580c08003541144440d45055916040000040e49410b030510444040c40030005621800c2401343c2c0c10f8001d024411a40303207c1150740d6004084002004488180e814042c803094030b6040031084000c07a02034001a034502c60290b070b240d5020760303440d070440b40e41c4404c1d40030056001802843ca40550f4130002503032009401c8010085604a08105013000d6220007142003498080c8041244003018088a000f11400c0f555030225060407102520309070001c540007170002040100444e0000028a081d00469085403240c400d03501e5000c088030141caa00070b50028100c6d5041000343c2120a00c9504980a01d4030f1518040c0e4030f00002c0d00300d0303001c0e0340d041e40c5000c00c01075005841c0c40e000352103d04114051511010304e625090b0000e440341300041884000d0034401e20030b41d40948403607000d0801560302e51996003500c88442c50115819200301c507c0c900013400d000103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 705915395 1250 705914145 705914147
    0x50702060a0603081b0c04090c0e01141302031e040c0501140405061b190f2f0613030c170c19090207060b04021602091f0e0705070c0f15 60
    0x30b010101c0b50031400942c00e02c0740b2103c18130000c850348800e482c10362194640840d1607558900c61010070a20854071000070a282400203180c00c0790584c41300140480d8015094210b4507007a00d00b00307032880c540700d0040c6d0303076620000040b0848824004211404500100b000204250710f989a002d4403401d8072601007074141021001041d2046016054010341e042c45000e2594000f182941042c008810542d000e04106540034007003e5500c020a41d5071024864040d4180610000201c0407040d10703002840c51006400b03403582014005026141c00b41c3c000262510882c506400d400000e1039000010150030365582c4108030600344808052002405403454012052406241c005c242400d81800f8941c0549440503180094106042c02d81d2040c2d20b0304002405595144010314122079808800c2c141c0c640c840c01444600c6800038004440040303c0250042816440c41c205401c450704003007540748690b98050b048801b03016102004100d100310f03850114191103c4043e50381642e000c4031012003500c1c00154 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 705916645 1250 705915395 705915401
    0x3020c060414060d0905100917030705090f040608010606200a0c031217090d11010203011404180f030903030806010219061805070906141f08090c1003050702060a 71
    0x10078415902e61880ba03001050604070003400300903107044800101d103003081e00c6003400c0c10407000c1100c40141d65110078500b0840d64002c030680000b042000b40e0b055203400000a403103481000800d906c12b80c102c09403c14265507070f41000300a088208002e1184d9a5110006049904030300c0714207071072105090380040800c000185a814a90b04800d0b002c1c1103a01d1a01c981c1d0400c41c14500c2281040940107104406c090078070742c003a00a149440007020180081140101110510b0440301130b280d00420041003142052011810410b60403500010100c2c03850904507400307581000c00800350311a0082e86810316170481d10000c2220b0280c1c035044a16590070b80120386071034244e066544200310100c6948041580365020f071031051140c5000800c0c0510b07944411f03182c20003960000303001d070b9207416080c003600c1901448070118500a0300c613601c21403803030340d183c26020303011002104c204031402001444811041040800d10340c00904855080c1405c039100602412089818202520924010500444580c4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 705917895 1250 705916645 705916649
    0x3100e04060f0e07050906030102121605040906060509030d03060f061413060905090a0204051c020111060910061205030901081b071b061107030b1801050a0609110406170c1b060403020c0604 83
    0x2f288400070343e00c41c5401c1d01020030407200c10080060500c00070825140034851080601081c0d19102e2300c410103c01058606442114003104260030f081041158410b40c0b501d05003502c110f4200300c8000c241c03c00094400707000312a1004021020080009021908800100b065078001d07074021500381c1d182c03a82002070b407140c0d11425801100d0030411405070b02024801e141040d20515103c1c0c8841c00c0022140e01e001001d481042c0e0540003811400a101e002d0b203d007200803c07004840403904085a195107840e4000c422215051014a00c0090000d041074030100b0002000704002c1c989800320350503c1c0d4414021500001903554000f54040b48040c01840592100c200040c010182e0500703642e1503100103400907051210500310300806c001c3c9503000b0b0140a00c0388c0c2c440500080c0b030610300000b44040d1090790058258104040000380300190740f1103084004000c1d404040e82c69520744640341d00803032040c103036070b038105504a801d2800c031903801141050066009500304c402c161000410807007648218 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 705919145 1250 705917895 705917917
    0x920120d090612020903030703080610140405131104060302120618130519140c0f09010608092e0f020310030f050a051e0f0303100e04060f0e07050906030102 69
    0x1010400120740700e90f4007034540080d060005400c2c0901d40300441d255402004086000c9588541041102d0804017500304105c40d01c0d1500d2180d41010300c00240940c49103001c0e060044bc0700d50205160300845810140041211030705880c4d617a50784080c003c000350859158244403034810804240c01d482c100c103001084100c80c0a13141156124400c402c0c2160a41c0070003103a0354042c0755809031a809441c0301540399503006000d0310110502c041400b60402a602c208140b08200d20541012542c903900c52050649016080411103a107403002494a800b0140303082407401c080440094041082c600b56031500001d1440c000d003d652b0855200209a020460b290314180c0907070780040003c01c10402a20f03001c0c9001d8403d41e41c0c8d030036480e2504c41c2401401514075500d50038003e140b004488080000200c446800400f46096060003000352064507480d21074202c1c503c5035a0081400d100070b0303501807a181044848200042101e0100c15501c03040580f2480744138485a0b00012040e08041c000c07103e8403544 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 705920395 1250 705919145 705919157
    0x28090816060c0c0b16050705040204080a2910260d03020a0e0910030309080a020306060d030512090c1e1f0c0804060207170102120c0d0920120d 63
    0x200711080341c2d8052212010b9401d00ba54010010740b2a00b00d800070f1141171800f454140c04c14906042491601500354009409640704000410044001041c0d03851859800480c44002d40d400c08003842c2c3c4100c0c48140713002806114001d00c0200200c3e284240b046450030b02824000c0100321025102a11524120303a078aa00310702600349515100c1c0d4010403540c48daa0502c5516149508046500c000c004c55060311207000e959824400d060f000704900e03000303214020040418202d03a5010a4407100d020307218500030200e6406180030140100d040c0c80443c0c10014508440d45850740c540d55071210a03400784c0d4024141041c0c030807900c0d6018070040d81d040401074880107072028110b81c42c002402c0068080c10802c140b1104003400112144010070003450039070700900b101402c205a406003a00403166101136a8410090013400a030f65030300041c1d012442e1501c01d521001c03a00a0040904110040140500407200c3d80b05c2c10700c7c0c4d00090008102005030b0307402c402c02c81c1454045648044580001c03004c109 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 705921645 1250 705920395 705920399
    0x50c07140c150c120301120b0c0a05040302040f14090615010e090c1e0d02190e030615030c03030d140709230a03020a060309110402032a28090816 64
    0x304400083c640b1030511003c60302100720300382c0000010780013030300000d5404d034051a0070700901c0760402c1400d4000c4004042c0c1807800b29140000307011445280720090086480c0c603242150b10049600000005894029043c16490031400e0395483d030740c0480c0c4000090341c01d42c0d4240450352033003560201c0783d0000782800005484180c1428265000480903811203011940948a81e43c01d410140440d090080005038464408030462110202810b040a00f0003880da000a40250790000c0e6864000360743c101c0442e0000305820109046c608100203d60b0140b00c002142c0e200c5448991010145007621004081c05840c0d180302240c0410403441078840e81c00260b0044040080065544290f040e001010066995540e43c049101001c540d845080440e0380c40151109210b005400042c1e86d01c1c003113400318510701c1c001340c1d50101c400d0850340009290840d600038010072050b20307044800d81001b1442900c0000d01000c56040c402201c1801d4000060401c0c0000031011800540c55401c1080f510f50071407098 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 705922895 1250 705921645 705921679
    0xe15010815060d0c0f170c0d0201080a11030c0703140a0203070b1e0a14060a030203060c0d11030f010501020f1b0d020102210903070611060a0207080409050c07140c 72
    0x140c018180c0c40d48030015920700c0f800204650442c000034840c084400002510342079605071180d110701c01440d03540d084466a9005a40d507002004400b5509013024051511281d17a480010503a4100e0309041110010a11800340e111402410200b81700b9900e102c034200b0801c81e2059240285400040907074410302004e000104c0301c00c041039004500c3c0004c6025000d01d1302c08039a2a5400f91001e0070003130707940e00003070034021074106010780c1c00032041d90424140c40c91980840c1e503c1c480109840d01c1d0620100700c0c99203181c41c5030085400301d0303141549240c9900b02500d01c0306981c1d4083c4500e40c05440741034911a452180403807100e1500541e049200b00c806091002d00000c0346080204a046004180e144122a12400700b1120101d22110b8040e0f03d4030321100a051400c0ca8640040f024444c00d480e21000a10f0f00003000d40e4001d0071a0b0001d44c07504a14a00513045000355005442c8050800c42040110701901014040d010f0040f01c400c01d810210030502504c410004107403580090304403403a15015 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 705924145 1250 705922895 705922933
    0x60203040b0331060b04060605030601120c0e031b09060901030f02010509460806130c05060309060a050f1501080c090409051e030301230109180e150108 67
    0x4008021602003d15440c0c0f42c808071200111003201e0300d85c0d560100000c241010320480c009440e085c1400c41c9103041c1040043c00911111841811050304d80041103a034a10a00300055410300190823584c20584030400c034400544610035150103100e04a00240301842c1000720541207030341003501c55030b440300c0c00c1d001181c06610200e0803076045440142071245000c0d030b4050035a000013101c1c10408001d02600d100d040c2c02c8044c41c040c400c12003540401400b800201141864000082007181c4c038a140c4245040d21100c2e480340d01040d80504003008201540e0008241a807207558800c5003001151f5a6200d44420044d0030340391211040c954415003180380d4098601d080c3c2002c02030110504108807000064140e422000d0100d4164000c104003002c81607420b5500c01d0903c0302e01c00550705542c10500740c0401c5c044c2011201c4c2003040d9070055007801c1d0740541d00020140c44041e40d000c1d440c12090701000d024101d41001c46006100c1e00314160032080142000398117aa0300c00c00a00300c0009194440f43e00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 705925395 1250 705924145 705924181
    0x40c06030209060405150307080a1a010e0a0e272b03270b15030c0907170f041b060e0111190302010e190512030a0b04050106050c07060203040b03 64
    0x203d002008003156070f645d40160314542c82e00803030310a40d0301e01e03049600800c080c60251004080d24241a54502d4808507504d0300801908217107050040a9207442c001601c440d41640044901002032052000000362005000c410340d011041c06050320b0481e4010950707030030200308110300720002c0345610048400c0138109100c11358400e1174003141c1c0592110f10b2140350740115441100798610600440100038920f803d680d4025400301c14000b100c40b048020980720b404005189120f0a03132140050f210030701811504520403851100c01d02d40c0c0c82d0402105a041304140d46c2502c1c96400d41d40300d04040e6401808840c140c2e0101e035110745032039850074010764061100500500300c074040c12101002102c6403104242c842c81c020381c00410914000586181002f04180d01d042014403450b44600101b500050300708014401095074941d06d68072641540d0090034403050340c82c0d201d82087c000144040d8030001a084803c0c4080c2031340d1100d86e80e804166940e114030706c555100040d0078030000d401c140f1740d0b203200c900d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 705926645 1250 705925395 705925399
    0x1202030a080f0702030d0f090902040f030308061507030f0e04020316080a0908030c040e010b0309120d0f0e0d0f02030405152515110703080a1a0307080f1005040c06030209 75
    0x800d0990607130020341444c0346c00710340c1000118115030003403005511081e82e000a003c4d410085203840c2c10031481860741203050002905000b190000b09810b41ca4030501410709250203207500707803203404529004101c3e0a030320f41a4400102021035680c450700c0c0c544203c03030285880c07602c081d007a40c088010079140c40400130440542c5581c0d4060322030219880c90000d6100c0c0603800c02c46070343c907401c01c603d0004000c0181c00401484105100304000c4610004c0c40124040c503980c07000e515448007074001c4016024210040f9002e606001c0a401f844c1c00000d2100700645080d02d03005503801c90b481080ba03403400340703102e207503805000d441c0d000300e0803403024005005d01d11074828415450701220800541090b507240301140d681c44d441403243c0242c4080d106802c00820004122417038844a81c500070216000a000b2030111591842c5002c4a0118204016050348000e81510821070350358030394a03292805074180c8107950140d0420314030482d1541c450944102d40c0040e4005480703003000300480007500074080c55a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 705927895 1250 705926645 705926647
    0x7080705161e06240b0409021e0408061501020f0c010c05070b0a0c03030b0103050403050f0d1409011d0c21030d02030a0c0f0f0e0d03030b090c03040302071202030a080f 74
    0xc0c03a0b0810040341d101039070140704080344240c1c0d0030b82000c0d5985081040b80c2645900b40d41c080c0641144042250b00302c4494010140c0c6030b403150040707075540b400d610b0403880680710000b500040011003c43c50f00d100301414100305405294203401a6140c220104080c48190048000e80c3c80f907600501c11080c2d00c50189044480698136a10150340e2513000000400c0800c208054450425905000e10a1822801e00c0c1c10300c5542000d0350003814500601e525068515004181b2104541c0740c0e50258950212100c000d44144c100f504225000700500310a8550b1440d4814001da04d032000080c000301c80358800b03424a1840e40743c0c1030880c50345c04424603200300c0034001000b4049a00601c0c0c000b540c05242110000250319840d8203020b0411400404c440e0b0503c01c41484481e0420382206a80c001c109095510075100c3c241d031300c0c00714010400c480328554011585800d011100e4045800b031440f45e840b0703400b110724650711110000b4118080c03c2000391306038000c0303085c0c41c00206c010f0003600c05a80000019 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 705929145 1250 705927895 705927923
    0x1406150a050f04080a120c1109040f0b0f07110a0b07030504081215010801080118140a06020426070806150f12011a0409020d020d111e090708070516 65
    0x2103030341c0c81603104d050036034070189180f028420343c2c000320110b5619074140411801202d50310110b05030741c0340d120305201d014207400150500c180004243d440c10f81c4008031140600d00381c0007568030808180c5a410002c0c5e44480007240518002803a000100d4221000440036038840800b03c010b000b000b0002ca884002c20300c00c0030003060b0742c6a02c50380030b0070113642190031320401c0d8030006140300b105178045800303a8140303918820110300b030200400e8803076013004814104203ca05e403041d10700015844024240c500c0050009406c040d44507000307881d04130041600c140e054011000d07507543d20050190030f410f07800c02008904005081a075490308060040e1118825000700400a0301140700c610207002c41d0303510b823191000c9002200302040e542c0c0004035002c02000440e5000705034507207101c0700000e005050b610291414031602070502c5e03080c520000c3c4150300f180d0b49400c0848602c60020681e9026010800c00f01d00301174010242c040c400c428942d201c81c02c02c3c0020301200d000c802d00c00301c20781e410500c007100 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 705930395 1250 705929145 705929167
    0x90402040e0d0309020103141501200f070302130507090b030619060201050f010522090c05100c03020106050a0302060f090109090c030b120d0f0f03020d090b0108011406150a05 77
    0x110a00d00b8141c0b800034040040d800003400b0b5803010103000881c01c40c450700304051540c1c40c1c4d00142075161b0a19000d0f020b000800741c4511910302c801c0c18110544161803504002041c00601c0c0000d49200307490440c581c0a507180950242c2c0c40940d1f0701000300710320788420320079158a1070103550b0000c0d0040800020340e1821302000700c5003074076802540060351190100b026269007604003600508040c0c0ba0003040e20300d030100b000032205202050008940e01da16040c0140642c40d0841006850001c0203203601c52000c0002a0240030349034021001355003020800101842c0c44041c3c00110ba4014141038540710440220f21050b43c80b403103200741404800c0c500420142c2c5036104020f03814071161800240c00d581d500810611050f503158654036680204c2914a01991002e20941c2040c114104079600c0280c0410540290089115000c00c21b840c002403a801d12000c0a02541241c40c04402084000c0012000303842e201000c80d01150440d1652840164071002400101a0201c0d50700d0f0490074410013680b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 705931645 1250 705930395 705930403
    0x70b010b210402090c090a0302090c070b01090e0c10052b0605060301031505100803070b0a0b0907020a1b0302060705160e07020d03150b030a050109060503030f0702090402040e 77
    0xd003600510204041103070250380c00040202407154011259185810790000e09034004c020503843c14101d010036031640c552100c618a4015641c0104980c0c040d02d0008042040c0380c114043c240d40301542d034400012610454442e000242c0603a00141503e202e428050080700d1002d04218010000b040203201d04012400e40940780d24180c0d0400d21003459110780401c81541c240303070032103407085904000410000d815140c68408902c4031501c041825038400c0c2040c41494190351281c1168000081c2881c104401c0c1c00c61136103d503940c070608001d921201010300050184c12a12030005d6481103c0c02c0010510600802000703101501e030f6404020f40f40e81c04144141c00000d8102c0b0190300044180304402079030103075600945050810500c051030801c00c000d581e21100c0004e10309140c3d4171f1070381034800412a6440c0b805040300c11a4036a80742882000e01c5d00801c003d200750200340d031600318041400c2c13801000f00c540701074000400c90304043c40d540800c4003200c000f40049a00c03da0f2001e0b40c5000310401c0c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 705932895 1250 705931645 705931649
    0xc080d1802010225050f03030913093804052104030b1b0717040306091203050907060207090f02160b010e060108160302340c050625030203070b01 64
    0x1003a890600c0000e01c00640b8080e1414143d444400340c042c1c00008910070240358070111202103d46001c0c6411310b001003400c62092904258200d9071017030102100c481e0f02c0d08500e0015228940111700d050b000e901c807101021005413a0440c507103d1442e40e05c0203510302012030ba042070003202607403c2d0070460500c00c001c40e10722803001d00d203422010800b00b00f844505826258000348100b103103401c00e501c41d0711032b5819103e113140040020f000c0c42c01602d00945401e0550b03010f1944003404004400203410009040d298525a00000a0400b40010300c4004d021444508942058006203032040c2403d1072000642142d00c0c0300c0d440c1ca5800c1c41048640c46134901c00b500c80500130030b020001d030b5041000c2012034400c0100411b05001140042c80200c00400c1850788104419203001030701c40402a07a864181c0314089038071403e80c140c00f4400702142025040c08513000740b01e00d00c2401180c1e1380f203080c4a614012201031030000301b051424001c1c060721103410191a03038030900c1503070f00d010308594a202c80e4410a0b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 705934145 1250 705932895 705932921
    0xf010615020f0111031314011e15081e0109020916020f060c04090b010e12010b011209020607060b1504270e1b0f0409080702012d0c080d 60
    0xc80304090281c042c001c001c403001c5500c0092280d4101000390352420300c0050312010b00750625a6200d0140401891b0f40e00c036800c4400c000744010701c0322203150401013006859802d03556242009a12010424400c044200c4d43e80c400509022a41022040710080d4640e00b412899500e928090700140d981101f0725214241010340f00003050003420000340360454030300502e2026030004052002c1410a9000d8a040b40d0407048085003c1a0801c012214480400047d42c0c105100c11030403130020f541034100c0c5d01506821391307520071074070500c516140076a100880003a41103541000100007140c403503081405007060103400326551059460312180303184e015600c01150a0406010300f54421000d00c112100004001000c2c8030707408064515507100c0c0f0400080408513114150168010b0311903e088540c1564020410410002507062941190307000030003ca0004038007803082400d1007003040780000161580200b034299810f0f00e0005075151f4201d0401528008014040510840300b24050725a01200d4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 705935251 1106 705934145 705934169
    0x70905061809070207150504120816300504051810050303040603050a1107080f0a020c100c1110050d020904090f12080a0507050307110f0106 62
    0x10380120a82c1042a007020000d606801040c84012100d1030388124010295000080782c25100e45e02800040000c20b0b150400803d101201421401b802e90b514841c014000d91910004042d1010582240f1003580d0300c25510300d40190f60001404604d8109182040e0803c000aa02604961308603045680894009020387c4021443c50004040150540750345945405005002d0a01103908000071424640852a00c0390840210b4121680102da0705040610000c00c0d20101d50091900c20114403032030303d201000780e550b00c0401ea44e02d10389444460402160786448845a0007500c5010707c20b000c68503030b107a01c1a030842d0440702001c40a00e40180e4600c5203800003002000420300240281310203c580c0007c101c0030400e04074000d01141c0710151165070300700e007910545034221020400150b060011800040c041c501040403a640d01064403441302c17440c1800c6013110201e9000d41c0500038 = true := by decide +kernel

theorem cover : BRFrame.Cov 705755395 705935251 := by
  have h0 := BRFrame.cov_init 705755395
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705755395 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 705755395 ≤ n) (h2 : n < 705935251) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
