-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2724
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:33:20.23199+00:00
-- url     : https://prove2.me/submissions/b57ad0f5-b729-4108-b7ea-9b864509b880

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 489748201 ≤ n < 489928057 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 489749451 1250 489748201 489748213
    0x913020103020f120c0a09122f0405090a1203090f0f0302010908030f010e010501090510031505030a0c14061c050621150c0a0e040203150907050711060f0904021b 71
    0x6034405d80009024482c029640c141d01180c442ca940302000d995000c020302300320a98200000c0c900f01141e20200e01c09610711400000c40d602d8000700f01902c100721000140d580200440009008102d88500c4150038075150800c50200140e50b00d80c81141e5804c0040c0c9140500100c074010035000354407844841703400c01042d0b504da141401c850035420109025082c2c0e120040400007445500a100000c11b443e402029101e0707802030554110002c0c5100742100b54012045d45001a49840c103104d00c03191b85020381e5400c4003150910240c400c050982c4039126000d80c1c400c01410042e002c5448499501e821420804101a121200010f09091203880c41c60002d81038070381c131001c1d04400083c3c401d0000c40440207500c82c5030b40d001d0781f054050007240f07071810100d100000e10010b1450258001c640c040062500d195243c2403c0010541c2120101d4861002c030350300003201c90a00c4030782c05080d208184201d440718541240c03445d40d11202d00a00344a40d004d070340c0104403503540c0002ca400c030a614800003000ca480d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 489750701 1250 489749451 489749461
    0x14070503030f0907090605150306010201060e0705120609010317030c04030605011710290d14150903090102190f1403180301060e1815010b04090b0913020103020f12 72
    0x80b10b0142581c010840303120b2103400088000035406500100c4000400b0660002c80003103984030b0f1030b48010007041c11556035080101c6d80c000481a160701030b032841d41d1155150b04200e0202d500190000c0c04a511038680301e03004200240e003c10074a14420010040140c8948800501c080c6e6400799800040141d0700f01000411700c000c00c03601000b03807010b0500c2158544880382c8001c0701203d250b415407000803081803a0420159050660020f40c403072018004202c0a00310b034588204004545d00c244c01075400c030340e1569407813840d0403812580181208000d50700d8500200d0007c4c0d03581d503110b80b101c0201c08180741e01c1414440340180c26a1059040000c000e511082140465140d0b4465000c80c003a48600e05008040307803c0c144035410503504103404003080c40e1507600a0110003050845503086134451800d816203036001c0109590b009000150049854900b070003000c0094541c00c05840303009442c08030802500380380e00101d00910316020700b8010796408000407555054410741d8541c0d8050500141441 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 489751951 1250 489750701 489750721
    0x30a060e1009030e10030b0f040e07080a0b060f0307060c0b0c0706020d060303030f0204030f08030402150703030605091e060d05070911120c130b13030f0b040b09030a020d1407050303 80
    0x40c8500500f00c1702c041800d510304000380e049034440d60410780c100308881c4d03051001d401d00b68000300700344110340c0c03c0784c070764035560b2513450702d0a10300a00032108005000144030450a200d80f1700300321410100c006d0040d603400c20100810003401c41a024000099810214154000010032100307000c3d0040c20035036a900e40c0c4485500503042d11320040300040c1ca460b070340341b04514080c42550140d0754010169007810361203454030100c40e000588180da210134901c0f1010400d000040060068500c01e032804201c1500e000204080c0746401030041086815900440c461020300815030b9510101c22a203411419025042651418000f904081522172030f00c001c0e48e11164014018210b101c41d411810306141e80c9010718511b10303000c0c2d25411103402140b181c0c20b203c054034403001381c00300851804000140c00c0e62903e9501349265000010b482c02c654860034001800000314803240e10040b100025450220740c04002982d0f060858450000c00c0200c044074155409458101c400003604402200d403241010b201c18 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 489753201 1250 489751951 489751967
    0x16030921020c0402031608042307030b01080607050415140417060a3803030307080103030216140f0607060f1d070503060f040f240614030a060e100903 66
    0x41400740c481c0c10000e107101e02d402e000300c034030854402c484546110b2a120064651500c00f403c110380410580482c40c40c0340d003001382c145604108032001000010f14508000c0c01450341a003003054075070068010407520a4110003102d00312101d00b000324840342c91100d011224120381803010012240c00113000202c4420310b10072205e010b54040190b8010380c454590000888070044101072004540000404909800185400030500106d400c8010003070100c0000e81540d004850b0100032641d0f4000500915904009a400c40144562110441810709600101075110000f0041c8119525040f104003503d03400262010644d00c0101881022580c20b000c5001c0d0201d8083c00012005880c0441000c00300001c41030111403001e005881191101d140d03c059420000340141d5012814010800002d64460030960214101c0b00e0f00902042c1104101070a0718404e07070010710440c20081405102d0307070780451602001c41d0f01c00f4000810090340104107040c10f6111090003485840c2994103070034160030400c5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 489754451 1250 489753201 489753263
    0x102072418051c21020f040803040b07030801090905072303061e0606040303051e07050303040c050a09140c0703111209130e030d0914011109030c010c0308160309 71
    0x403d6031007840140d02101d8012610964010514002281200c07807410b5034020010900352882d49481c0544900b550303450344c0d005601c000070b6040009083c20501d41d000810070b0140c07031042028803940300c45807030b02c1d5520318107030040301c00c0c124180414609025085d0b284030280c0101405650141c07410130038140c8030b0680d16800580f504d8928001850920304802110b040d41e0785074a800b0300b400030654034040c0360302200c040e030081d5420420000022510420166200e0b40c41162440c0700c490804040c0540845160310003696a070510800103041070316075400c03548c0304a5541c1560746604250408450040c035041c2400c06501960615000c0c8a0520009007044e00c000d40b400605450f100c905d82040750f401003d4007805800a00c0100d040b16140e03044100e589002d004119010070b8904200c0e8215604080b0b00c0784103401c0000c060308982010700240c40070324800d0800d90030700191a1000b81c4030310401004420307000c810386403001c00c03a03010340e000c007140c1500400307201501c401d00d44000416618804c9 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 489755701 1250 489754451 489754483
    0xa0e0414280b06040b2d060322030504030b040b09070512030a05181503090c03070515070312050106030905071a030609180a11031c0e040e031c090201080702010207241805 75
    0x42c101200c0c1480c03401c41c1d000d0251650315012800c0114041274a01c90900401c0381003080c10040003011a40707003c03156014034050301805a8074100a01054540142e5501140c003c100342d19458508170300100036140c60504a00b841640d40b1140fa40704c0300204020350130359038000d903e40001c003c0301c070f40c41d030285100c1c112403400c0381c280401c4281010361b0740100348a46640030702d81d240d0120340c054001c4023900700c09200f400c0074180010b03c0000b02c000d50303000741c100c100040d03540d040b1001401300400c4810020300705000c0700b00748c24610f00c607410440d00c4000c00e03585c001e01001d030200d4001d00e40d44180031614110201500c0144041d0f1a0485901052440c07a6200707100c0c045a6141c1c1e15030250310441450030607218941092440f800340f10180080d051030342c0903800705010320542c03452a045e6901e401d1a00420000301c000303440c800546000f03005803015086a00c1841083c00003400b03001040440103036882c000c0c003000000500c0d0409440c8800e94044604084003500d000c0020004d208446403d0044c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 489756951 1250 489755701 489755779
    0xc18060d0621020a06030c0203090405070e030d080c0a030905031b0a110f03060106030e030706141f0b0a0e0a0b07030c1205090609040b0a0e0414280b06040b 69
    0x2d0610520710b0100c0006940030b9000481000100d0081d80040309542c1c00d0b0055909101c03100000404a440440e040c5000c00d690304010089882c00384184481c1c881f46080008681c101b84900742c80c14000c010b05030007415507a80c00070062010400580c0d40c003003403a6000b440016942c0b4074143c0c4443c03001c40e003150400d55140d02c0510920745001525100712001c0c008103c940e10340351040740078180040c24210307280000c00411003c254680200388404102c0c070305c1008542000d4500c40c5c1002c45000781074040b044c00348418032103000b1181c101c403030541071480c040d144000c5c444005a04410261301c11780382c101000642000309a000080885054000c01410300cc032600498103440e00d1150080e096842801000480010314065000782a0303598041c200070705940d00c8124056084400796000d440089812a0203600b0b80c004012031581c02c1d041021500101038141c4600c8100c0c1000c010081810010350005003191316075504c221950074009000a03a90306900781e822280580126821280440507 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 489758201 1250 489756951 489756989
    0xc120705122508041704030503040302030c03030406020604140111191805011407060e150907120c27050a02040603052410021212150a0b030c18060d06 66
    0x12502e4034400111400c007038050a61002150b4000b0000c10455402445800d0304010000c820050b00203544500011a652400c4d40101840c00d280014818400d0341308000520040e07034041100350b0480e0b4000a807580c0041c01c100d0741805049038540d0421140b0000c9031010701440c842c08110240c0c070b13494841088044940000c00c81c010b010307005090104407405164a5400c1032007000f800603034001c220000381c080959007802d00f8442ca44101e40c000b400c14409001c907104050191100903c1c4c0c6c2c1c1c13035403400c11446607100c405943d81c6116005115140d13090707a42424005544108920303020f824200060729203020400700940180c000c103400245481d00144d10944101556200c245c03a075000201607000c800200200f4603d070450305000c5002d0908400303243c45120010304011074680080203024034001d51304c10040c003450124a4070840c0050000c00c4213084420881c0e400066150300030380d44a0702c80a280e0341d288992204103800c9072001400d00320030b41c2181d0003002510746c100103c480b01110 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 489759451 1250 489758201 489758221
    0x2011b031a0405090316031808070e0c07020904080d18082d070f02011209030503010504051509040204050601030b030307150e0d1d0f0d0b0f0601180e0c12070512 71
    0x44800113103560041092600b0170010240c0071801a00c07038503001800714404540004084c82561241c2410341c002c0e91b060055080b4444919446910828424203000c1590005500e800c07010f0300280c514040020070b0341c4aa07886030042580c0000d0780400400803583c0c0d1804581c0e56010952a0900110318030403004802c071061130fa1074031450082c03011400d021850300c1d45103589110b200100e0500c00c0740d41c1901800c6c0caa5025080c0114080c0c0c451039120340c5060140b1096039001490000c81c0310640d03441c10500e5a4292805030001d4041c2e500156541d1101c0051b0020020f4040155151102081c203d040004108807071100e10704695003486080015030940b40e40b4941d18001c00041107060f095101040310303088080707400c0e501c0101100109060b82004c6001c1c10629007081d20081da92400b00b0060140c10504142c00c107401703103042200560701c1c064084866906000d24007820740c0c0c2d4008240c400918500b070b5032000d0702e2685581040c0c1801070001d0180d9000201600d60405039600191070200 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 489760701 1250 489759451 489759461
    0x613021206030615031209010908060108030309070509040b0a09050316051c0206160c050c040516081b040902070c0305010e071e1d100b0a020d020c09040c031202011b031a04 76
    0x10701a0081441e096020386c0d203559a04042c085904001041a0004000d40d080050a0084c4940c04c051070741da042c2008182c0c20320b07829411017402250001c0a010001c3c04221110707521175004103001883d0016880d0141c150710030a00485000d10341060388500b800408200390740d000c0d400d01c003003880348040b402c4160b8403000100c452001c0b944071303644460f5405015080d0b02d505d02d4070640555405e00c0e00c440c0080d00310340c0103440f02d42c800400d28015042d46074010503100d4202400c94140792085030414200c1c00244628003502c512a900411312108212280704408040c59101000b407120b04160b03060650750b05424481e10000d240c082c40d051804c0c5001645240903254104005000313540c0780441d44c1d43e1858040e01004410340000c41c009003c00c411005400035801039409850044070301316000b8031341040342032640d1107485042c06100000340c041a07582e0440354004801c24415a48110981c010404c4190f040c20100e0010b00400c00103038941c3c441c1041c09a00103580d02003001417018041220 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 489761951 1250 489760701 489760741
    0x11e15050a0f051e041a280b0f070b0f0906180d030e150702010618060b090d0c120605060a09020a0c030e130e0325031706130212060306 60
    0x1420b9000c051015082000044007061034044102501d80601c2d00400c0c22541c081d413039101103001ca000c03400060314002c4456000c24000d48002c0000c026000c494064076445880780403400100014012207059102007901c1c00290451079a9000e480e000d4080f0203a4802250b17150600d00a52001845102c1c80703d1075075941c40944001801c007038800510590040082008040440c800d2000e01c2000c16841d1004922a40c2c1c0382e0b0010410500e085a80b44034042044581843c031404c01d0401d11000d10040f081e103200010440d40070a80c0102d6081c50002182150006900000e0320307a07580050101303d030000383c040c600a482468480c0d6440c80c15008078041c9a91000c00038200d140c0d0240031030b01c9204102c010000040145074500a202460b90884039140a4504c443e0004203d00c102d130a0500040d0440500488003804030450310b0750300400c0d40000d1543c00d00c2c4441c030200844d00c19207810103032411282c9100b804559403e20f5031440110403508442041c400d2003803000003410040a082822843d07 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 489763201 1250 489761951 489761969
    0x1020f1204061206081902030f010c1e030617240402130b040209030a0b0103060605030a08040b030903040f0803070b150a050402160b01030c08070b1218011e15050a 72
    0xa041880489552100200c0c2003400c64070f8a00c00f01d6aa1001d100012020780b1b030040e0b031815601c462040c076080800009240750281d02d0144104100c5800c8001680c010301c103c00a000a2400a1010340c000e010f241c00c0101422000c4083d04250000021000300a0402000e00440c00825160721407541c40200d40084d0404545400301113018144d400c000400703500188054141181e04000c2494100070000a82d0420b02c0000100f0a01ca542e200b41400b800381039001d0030302c5aa0740d49842060f03200d184a040440200000003810412081c01a41e0180c006403035606815a69114065940e0300b0440b010348010049002107004107100c0e811014400f180640003680541c0b40c54204002034202c3c40d000c40000b803860085600240a034904140030758070940c040b05070380d401c00760000c2c50314185410044514008000741d02e48800e18804031944075040c0b200c00d2160254031052140506000480020340301001030142e641a01d89400918000761084043d881c002e586070104051000507102d0601300d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 489764451 1250 489763201 489763207
    0x702060c04060f120b0616230c100309020612161d040c031103010b03040b0106111009030c05100c0e010504150e0105070b130614040201080f10030b0f0601020f12 71
    0xf00c5000b492004084160480300061007100d0002140340c907031049000007401d5204141d428100021900900c2c1d6608540e8a55500c001380050107a07a18080065280e1251340012032008090780300f0f4005c5240581d001e8080f640383c101d20354804410500c29280300190702d9440481da00c246124031802c2c908405507c00c1c0c01348840c55402440b0003070041b841207404040d01c40c0b010000a007400c1c001503009291070700b000740d503070318260426a00042040e0098010010081020360141d01c0000341340388982c89085d800604c000e02443c0664090b0101680100b040c01030f907114203084115684006062195a2101c45014240b5001180c292059009001480d003411304c030345000c07078070580d0b16070b0019606050407481c3c07540720784030b8140c408000c40701c040c0901070b0002a20204800c500030000755441c1c014031510203040ca5030021b89000402084178090303462040c0000c114590a41d94200255088440d2542c075003030080c2c1d40d07843c0300b804130303225409407040e80480c0d440194001240640e0807030032500181 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 489765701 1250 489764451 489764477
    0x106080d0e1014031b040803070201030608120403020906120d12051b070605060409020d1b0506120f07120c170f010f0611030702040e010b1e060d020c0708150702060c0406 75
    0x60f69040500b484820348407612200048240450040010300b152100641c3c82c0d006d544001000d581c0309403c40f130b80320703004003661207070352070b69034050f070303098990450342d9042998541e404290101004060a0940c0c0301c0d904000e0106c50b0084a05070307071460040c00a001c943e07150b00c02c5002a2100c4102c06000100c00c02c5050302042d10b5a0100f50410402000403841d41c42603000114055081e50017540c4061200005040140c1101150310040c40c00b43c0e02c1905041056070b1658418500508d1040700d90303207030300000d807206100d441d41444145040004020450310210000d20000443d85840412042103000c500c000c142800458100c2d00030708245058103080020417921070654820015940c4014442d403401a03031030380204034601e1a4440000342c000445804c100b02c41055090742c4242c031103881108079030b07130319004119070800c0070660001d80d54019141a80e443d0408550210040340940c41c070700000314081c60895805071301540e084850b15140c81c01145d08034400d520408001c40c0303400300343c80c4c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 489766951 1250 489765701 489765737
    0xc080d050f090625030513080c0304090501080115031202100615030b041104120816060e0d14030109090f0b130219080d080a0f0c090f06080108101d0106080d0e10 71
    0x60b5110f45485034126851f11203540342c1c40583c002421040d131640011400f406030201a110301c6005000040c0280411a000303051070150b8102804058041c1d454840c00c94030090080003484402ca1314800d0400400c0c0d51820101503a02e4800500070009050807880010ba140501943c282400000d805528151414500792190304002808940c48441407101148d540b2030b60034040b22446c09078201195031801c0e0344500c0d0914803610700600034888414221080e4442e01c1007a64192054914000340b03144488c10202840703200c02800074414008142000340d03482c4921215100c907031007610681d89041600a11a00c00700b25805099125404841c882c040701e40300e070010a030003103151400014015a40c0c6d1201c016559154049004982140000c11442c0c103452405030040003103280200c3c0742d504100960b500c4200717620403800700c0c40e01c50208118040071846612040d81c0540c00800c1082d60f00c1e4011a194200700b440040403c030714964803456070070300c80c0034030040c91704607a54081e039501c11507400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 489768201 1250 489766951 489766961
    0x10b06130902131502150708091b0406090204030f0611040e06060d0e01020706060f05030d080f090c0307030b0106090e0c0d05040804080a08070c0b0c0307030c080d050f09062503 78
    0x4000003e40c042c00514040d103070340b090403d07070700d5031740600120103e4641905003c08040c00e00b00400c2028410841ca10740f0200b4920b6003e0944802301f4641800c5030000f801a00040e00a5030301d01f03100050002c1002049110f02c2d40c103901c10349040c1702155000440d10954002e40c4948007000034103000103142450700100424000780d0000000800c1c40903010301030b0880e000300741c0444155584031130030301c8a079074070861b201d000f082c0803401421001030f080c00c0208000b20103407503000302c40084c030b001c2200d04c113051005038400385002d811500c0860750390403c070b09502001e210b8000850314002c40483c0e2407a001540a12a16081e06110b1403e44a4070108008010041058a50a03024080481c00c800c00780078a401c2d01d80036419103501e40d1224180550710207104e5000b04441c80081141030316625000c02a41d8003d0f8040c20804000307020307824081101c1c824a111a0b81041c40d0104000741529205002806040d45004603a6135942d41c2c00045400ba8800800c076041c0d5821a00c0800170070710035008 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 489769451 1250 489768201 489768217
    0x302010906050c03060301060509061c0507091e0c180506090a0e18061303020c09100b0d0915060302010206180f0d02010504120e21030c0717010b06130902 68
    0x9003000c05844500032200141c0d501043c0038400400d10103d840c00f40078560151500b1250b26410382032940c00101582d080095a130264108054682c2c1480003e05c2424000e140101d02400503c01c4411446238000001d0380350314080d0b20305000f80c140503205080700c801441c00da2500c0385d00c25091008001c40f82e000348000742e40c841001c50300403988039083c3c1a07031801303040f86ca1007540255007440700b000c3c01c00c3c1e0b00034075598050301100c0000000c00d030f0000364402180340a82d1401c00a0701c48081a10068460360070404224000154038411910b0a45c0290949800344601c0d9000302c4400341d400080c1e400d40d10000e070050b400080840c1c0f183d00f490994bc6492070841d1308036000c040601a065003882010103090000d42d40d903074204400d010f006e1500c1c645000492a02e140f000d4a014006818503a0032940f2100b0349800b40b16100150008100721240d01c600307041110a01d65541070194210000c0c1c0e01c01d044c80c0c0d42040c00480d402e09098058405070749010042c503e60030305080031075000303420640c1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 489770701 1250 489769451 489769453
    0x60e0d020a080706090b090f01080705071e0b0901050f0106050d060305070f060905060c0604080906040806180f16150c0c03030302190903031205070e03071217160f0302 74
    0x50016594041080c000b002e680e0040c3c00c02030b142410141c0b40100070380c80f0840c4100104014496580c9600c0e920380121400d091032011600c400c6c1003100c1c18051030000610070202044926140d401c0014104511340c0300e0184404190f07a01d90083d800c1c1c44040e03411003940840754005018403401680603201820034034a000038200d035640c84092908600d07a20821601034000740034020150b0041c81e003000341c0b8064804519103441981c5541c0e840d40c008001410b0182c01249403030540c0c0d114401ca44c02070a0543c11202c1c01d003030504600d08001815028000d151042281c0094040c9001c95841000e50b2550310b111a0309281001180c90220f0341c8030324078100b00c0b0804100002804501107100510300071307a00142c60f903140c0d5841c0c0e1481290001080c0a000c940582000083e9100d042081c00c008004008a115204c0403401d4404c550502d800d15418040c40c5008108411040948217141d405540d0b07080c2c8034100000c0c0308001e031141d03a00b041341010101e1b850308d0208140d1561030200e5032180c4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 489771951 1250 489770701 489770719
    0xc06162319050405040c03090b150103020706020a1e1805060d090606230301021608180301320108030a050c0f030315090f07120c17040602071208040b01060e 69
    0x150310895461603441d01c60120340081070611090800784a4141ca40519040400a103811500d9045032100010010a030349622a0300ea000180d2082d01a2180c1e44c0d032142c0b007552141c00302d00c0c016000b004004042d0700b9040a490124005601c42c2041442000c2950240689a820b25042c4450380e402907085440030b6031500a100009500383c892400100580d000c3c0104201880081c02c02d14109140e80500c42d80c01400341c4110350268800b072181065101100c00d54801070b404510b0504000ba4011035803552820900d82140c503d070403910100a141c15241404805450030240d01100d802c1c0140038003a48180314082e0164055030003050f0420741501140c44460015591615560080701c4802600940110b40107032818244040e0f500241c1c0c01030b07640301a20f003895000b0691341e280c0032048a5951144810340c1080d01402400c40186c881c640030440614060818002940c0281001c031260b44030340c5041640e40340f05000e600e0056074072a00d40c1b401c903442c22600711400d2460145499102d4014 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 489773201 1250 489771951 489771967
    0x1b03270b07090f030b010512010e1b1801030c06050a051303050705150307081b0705070e01080607020a1203050a140723040602152206020c061623 64
    0x411006a5803041034080680d00e402400203042602d035500801c03503032040600c14400540c1501c05181900c00c1501c500c1c5010320b01c1c02c982800341107003250560640c0240f940c1d01030080700c0f40c1d01144684905541c1c900d1044020482c5010b2480c09210207400320440c0e135001d0045521a00040540462518080d0300f0041c2c81e0300707007030340600c10303544124ae00707511440f030070000c030f041010021a048200c044200e080d45443c40026002c140000d000c121038401102140c1c40368142c3c0004d45d0781d00e58006040f118a10703150040e1074440102805038034003a02c101c00c0003981c1244000703080840e440d4403802542611348614801d40c00b40c400645400300d62034a0f01c10b145603408000880c0340c42040703659a451040200700c5501191001030480c40c0894060411060040540008080100800040e516801941e1700210049698030214100012540e01a800703420700080340c020340400e00440f000c0d200f094441440406499212032a02070100e003c00901c032018010f194101108501181621480c03c240 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 489774451 1250 489773201 489773261
    0x20906130b0307080615040209010c02010f02241b0a020d0305090102040b0a021506011107061214040804031205041d070c05030c0f0f0c03060f070302090a06090503010c031b03 77
    0x842c0c10115045d030003642007012140300d000000f420200150b90440ca84801300700000e01d104c2000e40702a05000c09045107109403071007081007101d800c10310ba9001140c0300480301840160501034030600c5650398540c08000052800d00d007150403c4000360018200c415500c2825005440001d1050009550030f000c0054840d002400500302c180907940604030381d000800055040c02c1c800340281c0e040000041c001c0d813106000003120010345107282080d0704403c14608520010300300d103880c61032156640707800380820010604068402e9030f208a11200c1040603050086600d03000e01e100b04000035480c284403100104181c1032981d044056072a10503200100f544846246a01c15030040100764000016034107200c1d81401000388084001014045080c0b03400c0001e80c0c0c1c1d1401038201e940c6031080d140450b072114002d0341103480d50040a04801c07c1075903990006403580d4464402e16009508110102055502c00d00ca904a5102e6015600c40c00f0a140741044004102c180d1402d0404014442d2401243d52 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 489775701 1250 489774451 489774463
    0xa1e0c051005061305010e0a0e070807030b0906011401050f0a12110d1505030a030e1206090105041101030c120f1d03030402040e0325321207020906130b03 68
    0x30001e840030405003010070910120403c03c412404240d450140140258030029945507000108010049a5003494035081801d04450b40d0100780c003032003100c000200301b000e00c0030a80c0c400c0d0f00d840261042d1307a0340c401d06110081c1340715001c0e80c0010810459012581030080240c9100c812a15065070450301d0740499008407085c91802d4000e0700d001003510f4410080c18050140c0a40c00841160051482c0c0b00203e0354810345001c0c002c0038480c40d800030200b192208888032272407030300c600c08907022410034090f90350080030240c07015152411500e02da148254007900a0144000840c0d0b40d01b44038102604a880c01461440740548216840740e4035050950010001d0100312210b69000d107550341050300c10041128440300c8103218541080c0209516100c07a006c032822004890850201d070102c0614207a11000c0c0342011701d5208028030681c0340e45101c01c0b6610f116000c00034a088989070035002d0700800f61030040b918000e5200748142d0005100c4d003000484120110b81080c0c0101d9802c074541d00082c02c01e1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 489776951 1250 489775701 489775723
    0xc011407061e0b04020703020c090603190b041a15010c05030904060b0d06080c0a09051914040204060602071a090d0f0302030c12040b030403030209210a0311030a1e0c05 74
    0x7072200d09540685030014403654400d0001140d04506e4058039aa010f51141b07003c142032403103801e40800081c1d0030f0300d082c0001c140c0740403864103144044d022483e10b2044000b0998054400c400040d0a80500100c03500b105405042041600720f40003040c2c0004541d0840b800c04115a00d01060081800c65190340c040c05018103107004280751140003018000e0211103441d8896002540010341c408103a440c1c80c91450700f41d0f841c403440843c495540000340c2a221801600c40c0c0c0c81c05140c03e411480d0304440103181c9001e548203d909000d010b66401c0c049943e401240120503000001000d5912161500c5c0010000d07a9005408665050740d1602c4810303010410a005070056040020084a202d41c03d10081c011640385000079800e250500450a41d2070100030002010326a0001c2c1c0302040b0794422034000b5107661032010002e00f400b0002c15464035042c4458049000c80c0c8120511000b140d004016110449000d6a030342c031164440f0380075442c04044208020b0b0600005021040104e2006e2102c10500 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 489778201 1250 489776951 489776981
    0x307030b2112121305010915140a0506060d0902010c08030c041a0a09030f0602070f080901030e01050415090c15020114062e051611030606060a020c01140706 69
    0x4403004800c0c550629103242c41c074a600e18020005034090120004640d5084a42500566450140c91a040d401480503800c0031300800ca8010701241c9004403608099003081940c0728100745038403804120410b0752800e54426504c00c42c144800418608a0344c01700c00b11500505d0240200501a103400750305178000d40c0d41102001c070019042c08403104c010100020a08500c1e1441d14020034400300030031000035400020a05e000560b8400c05014540d0169251240c000700304031038074011454020050741c0245032041c0883c0c203040d03000e43342c01340611489114541120b04684003212600d1880002c1c461110111042200e50401145141e48541c00303040380da203a5000014040c068880300c89240f1002003400384520b4007040d014844c094a0201c3c03d1801d20111140f03007215025120544050040340404080007a038030940718240020303041d400900c2c8100760207035a05511000d00340f009030703c141d040c48005680030001103852540309110003130255140700805410b001803a914072082c0d5002a6000c490 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 489779451 1250 489778201 489778249
    0x1b0f0702040b100903060519181103122a03070501050603010614130506120a060501050406060806090c180a0e100b0c15060a0801060605130e040305030a020307030b 72
    0xc5050601c40c82000c03032022203200c001032400c850014503034481400006c1040352071f5008103200d078031304900503684050810810320468a0301d406035100126680c0081c2c620400c0c540d500a4941404210817480800c0e601619242c220005060b1000350a84004420080300310041080000701c04c1c000b9002c0c0c0d40c460130010605003803e40c105425a1707a1600012860b0f48104030104407681c800c00680003481c40c11030045150b40c4c0c0e050000360041d150000a8006000e4903017124100503035036012074103a0f0022102000020b858141c200c45801045039050b070004041400300f102032028038080d05942c6850008000600c9204011810b050480e620045100840b402880b811500ca91003141c0030f03202250840b801d0114001c031042c1e840d8101f2486c0c6038203000340c1002c5a829107036040c1400103880d00700001d1000c00d50b242d0004090340d003c1d141c100c1c440c604e051130110343c02282c6603825024a0300740d030781c1a0550b02e03080c1c203ca00961000c1c0c280024513603120183d5110703855010078825803c44c81845048 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 489780701 1250 489779451 489779453
    0x503030a0903052406040c020705090c070507080307170d0b1e0f0f011e0e030a0c0515070b040320011d0c03010e070311060c010f0203060117060d03081b0f07 69
    0x104c1e01c040c11011140080310215000318400181400d0742c0c1c0704c20201d801180c0041d0601c816420482d054011a400c481c441c0204480910300c94005d1518074400c41c2250503582d62950103948a01a400c0e0040211110404003104103130784030080c0500b034004d240c0005100d0348030301c002040c00d030f20030031b0b490000b01d03511070050387c00d241a480c00ca090071002d540b4103c3e4090303400c0c00200756591880110750380585160f40d0156080c45039407000f10100d00917048580207011800c1500c900b0130903204182c8100300703071060803402d4001a000d0b15401035000f04c182c40d207505c55036402c0c1e0301001c8940640c4400c40100e103c7e40904002402850804626500e100b819000c1d80c3c0342590030040c1070035100c1e000383c1c14940040c244c40c07000100340e4212500b03c1036840554a240300014030b60f202e111420341c03803582029040782c46075034245d0003103005c2c000c00d807201c00000c4c07000d001003100341c40c003210302c5903102e20390050a00c003280c0502d000701c1c2d215540100080c91020035041c0070149400c002c903a040354003400f0480074 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 489781951 1250 489780701 489780703
    0x41a0d05010f0f09140609070e0d0f020f011704080d0e15010f050f09041709031507021009080d0509120c03091207210204090c14090106090501270503030a090305 71
    0x10f009804020000d01c4840005103c14001602c00780980d0300425076440044e1280b441240c9541c19100003c051800c4100141031820408003684010381c420b807034003090a81251b00071404400c8184860078041225510b60301c039a415500442c0300042c1c916190100c56400c41410b201514850044d01c507103a160f54103041d182003100d00203811150240180e42030040d140d5441c6083c81e98400e6000390100c0f0510300b6001a62040c0c00780d03821013601481280c4408110112610040d44181c400342d003164826010b90150740240c0350801800761032010204441000040070390020750b4001c2c0100304503200c500305101014140c0d072003401a43e1680d003000c0b8900da001c0c94440c142c0a0795141c840e008041075401c0c03501901c032440d07444000c02e80b099030042608045481e20317000400c186e500119092204c543d60a090350320a00a500c440e03110307100c02c90010038100d028040c2d443c07d9402c182d4a40714102c030024008002544c2c003001ca500300b84c035220400036050b54108002e210240303280c0d40d0501c46c6440d5181035 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 489783201 1250 489781951 489781979
    0x3031214060d0807060b0d210c0f020f01090806090d0221030c0a17190b18130602040f060f1d010807051b1c020c040908041a0d05010f 59
    0x48100c0e91104003404071542c0c521108040d0581c01c403e40742d9451400d4541070b001081a100d82903000703414081510240000c003a0082e29481c8003402c0d483c404842400125139070044000010710240c00941f01c0740260410184040b007a44041c1400749071191540c0810340741c0042191005001d9208501d510051941841a42c0032460341c02e6806200c440e44076500703080c81c0802002c03110440c01c0810703080304c040e1084104808070f890700d2032000000e007460034413140e4446640f080310b14000d0070700704e80980e00c3c2800450301c5061207204114031600e403200c1120404041c004481038840f20f40a000104442c0c0600801c1d2005000581304c540604203045009000000030108580d2520f242c044c4960560360010325a6503c81854030306580c1c2c0d06001d540f0001500b600e0031080e002c621402840b003a820825010b410410700880e002c50b004c0b00b07100c004010960700110b000500825051004009103200c02c200130046a02075805142411801d80c01c54007201d40036800200008007100c801c0190707038600850707 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 489784451 1250 489783201 489783221
    0xa0b1b0a150c080c040603020c030f07060527060a0f0b03100b150a1b02011b050a02010e0f0f0d0201021c050d06090212070c03120609050405010e0304032307030b01030312 75
    0x40341000340351113000b0050343c0c00b89200381001c0c1b43e000600414a40e0701482181d440aa0900c2403070340301c046170300b080d10003403000b140e50762a0700002c0903c01800a542e099121184448074005189958540010700d0151140307a49241d0200d07190301c810044d9980c1407000c03071050080e03894000343d4a4198403c0210f0100c215030902d203680010043c000701964407080d00400f1804050014841c201d051004980000540d0320340041200f0800c00c1c0b000700030007c607902d04230a000760f8642e034459042c441040101413005e101554000131003460711502e410300000344840140140162510500c41815007190400e0010b80e0000146001940c2c4448079068842e1402800709200210704100710700500f0700d0062406054903041c80000c90440c81018031400c2010321000c1c40d103c00b4411140d0307800540c00909400d444c11030342c0394201506e48100c6600001698101c9400c000e64104040301110148003205c40d00501c1c0005003d490008008500750f01c0c40705008500c20340e00c0c00a9048200900d504817403243c90 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 489785701 1250 489784451 489784457
    0x1e0b040e060f040f0210180501261308030705190206070e0118030c0f03020a0902030c030c1b24070305100630090203100603020a0b1b0a150c 62
    0x50203040c6150015074180d10001e0340e84a035040c2d44403810540989480c50400039030140542c042103440719071180c43c03d521480004c1d0899002521103005413090131203505a4913111050005000b41a55008862508540c542c9551801e420240e141c00e10241c0c02150280c000c01e03000581c0c0280810000c0c0c4803540c48030188060000c03810301c114014442d513208511281005a20340141a08d80940008100190b500c800400c2181d80c0e0f918100d002046903100980c420000c0e00c40c0055100c1c02c0e8000c4030b11520030415118075560303480518500d59004810340c0442a442032480e204105e10822803020380f410001000007001c0f025000c200b40c44240205100308250806040c0800d01c5034400021041d160241421010343c056003c0c81440140c02091400b03032482d03c2405040b224005a029500640c025000e0300c0c0740b04800c9680e1000d0312103a101c001e40203a40c0714805c100d150342040203441c51943d0040c8469071007181e170441d0362a0104119040d24400340c0c0740c000181c026400e1240004d0068203003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 489786951 1250 489785701 489785711
    0xa0806060907030213030f02060d0c0305010510051207141c0b15090f01211a03070617040206250c2105150402030a08030c0d1406031f0b041e0b04 64
    0xf5101501d81103510004051f50080807510007150744900c01c0c0c9100443e00c1c1000c01c812519441e005002e040207106060181c2007028007000308a21400c200c450940c1450b5807010b44d03840d000c10450300809a200361601014040c001c0e206a0707111019a142100c60840d000305450000c1001c000c040103000801003600da070200140c2a83d91100407240e1060007007402d0460300d81c401041c0e503c40c8220350086804039949001300b07144482c074140300902031100040d811140c00030f440d046c0c02d0b1030351069240000782e0400312100103001450302c00000c5c18003111240000b14000354024481d07044207160310084400d000a03020602c90f0555214503410290b00030f0303800c031014800513101c45441d00441d0680380c140e001a4400102552030400c108001140d000928560340e00d881070004a5036041028200c0480303041c200c1c80c942100315807030f1480c0520001030280600700c80c0c6169a8a158000b0042044029203c2c4103900c07803940c907807144003040304002007188051004946001c0403078070b04c8602d180c842c61400c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 489788201 1250 489786951 489786967
    0xd0315120b07121118040c020a080304020307150809010e0309130209030715050a020709050115180b0d0209011b0c260a0309030506090703150c09050a08060609070302 73
    0x412500e18164200d121448681c03103452048410b240c10000e4980c4150074120b4a00c442010100100b0750800150345604c0460084070411040d114054590001039010802510100384c19400031030f00184021f04850381e42d40e913000d401c0f010700803000c00100840c034401e0402c10050700c280582d48103500818013541c5004209000603c40a40c0c003901042c40d0365011a0b841c41e148c80270402c0d000508180b08003105d24072030701040101160b0107103206400601540a002a46081900039503042e241480d65401410310420021a0029100c0a41e1085070300b0f58900041d0000001e030040448210580000d80d503070034800009040010304c0102c01c0c0d0f41443d1b0b505480c010818004d04841912552000c1c0304035401c00c481900103000043c070862480e40a00c038108410950041031450071248104142d44141c1d0740c80724000c1d09c420300d610000e400409106800341d0040c00c5580300030200c00c07007420500a410b455801045201f4070a4005130230aa215009005d954031304480000d50140083c80d055203041c0c11 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 489789451 1250 489788201 489788219
    0x7022413030903020a090203060112090b040f1a04030e03150c0f310e09060412051303080309010501060305060904150c090905160305180a0b13020d03020d0315 70
    0x30a440030854014801004242c42076402e04015600204041501a144c0442000a5106031030050118010000040c480c2c41240030f04040c030754011801205907504c5484084440321400b02c2160f010210481e03110f8500d902003002400381d40207070b803010008040e000a0505d0681d910680a80080c000f0b410000305958042c1298148042504100c0e242c540501104200c1503040440d403159808081c103183d0800501c0c0050380c00c46041c1c40c048200ca07214081c0c215291031b019900500124400b98146040724000c01c020450340c04040804600b8641c0d03038a600300d06400582e40c0d40d05994650340100642035250064a4100c942203d41288904190b9150003009808403200b5140c0b9445540f50743c0483e015210348401050091703c03d1119140140d1503821707000203007a01c100407901d480003062890300070b1800d003520000404004c00c10210305031103010381300200901461311001c1e010603c0005850341c2a4040381345202b9001800382c6041e5540c041c1c143e0710403500d9898005030081c020407205403 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 489790701 1250 489789451 489789523
    0x30f030915070f1406040302190506071d1002060405060906011805150a06020102090a080c0607080d0216050706020c0306040305191e1d040204080303041707050a0b0702 74
    0x980c07800700c0d0395a0001d40707800302058611560203414000a00c1c6103500b003810220b8410300c5103200380d00307407030b0380004000c4005030b03c014000c0c1c090400e62001000407901d0380151101150140e00503488005281a400015280b240c10b440c0100103800502c184010070100308845c83c3c00903c1d82014108641c127111409898061030081d6400c8180c031240811a86581d04654020b41640507040c4280c49840700c01c007901039804003e0f464020f881185000510707130400305000e080604028111450200307181c44100d0b46800c18084014400d608210b06a0040e18200c000da0b2418130400c00b82103042c0c03a013107001e0306140e245c415043c001c0d0014402c100009600408907183c110f00e40f8440b0749580010f6400b103d0000401210101d540243c468481555810a070902c0c8030341c11000c80c010f098607105042c00180d01452144452503072050011500045c007400c81c0e40c800341450510103040c082e094540034645041c0c51800c1d14511b140300c0034400c02950502c4440c10300300014040020b450700d441c1442c3d0003c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 489791951 1250 489790701 489790729
    0xa1d040902010e0907052203140f030d0c0203090307060306170105190e010e1501210c06031e05040c0e01270c0212070b090c0d03080402061c09060b030f0309 69
    0x140710744c0002079449000d507054551000e02000c1d81038041c5401e0410250f075002c103000036a07010160f0945501c46400014282c0b014401c1c1c20041d45c1410421201d1501400c0000b9020b0294003080c0305c07101c540d80f4200880001403516a40c0850030320318203904408030191001d001146a4104410001c40600b0b41030541442c840540000580c1d5989681c107600402c2c420410305068006d04e0150b038840448900100d05030f0b00c0c0603140c8100001c1c074801e0928130b602c04400003000c8603201001001410301a90110340c01c410000700540005c054101d4000440744100e0f0100c41140501c007007480501c04448101d0301503c5200c088407040a2881074407100142e20036242c0910340e490700b042c0400d01c3d100744941100794002480079600d4020514006840b81c0f0304031076840180c841c0d071601d6144c51601c0498030032041d0f00754039607911644841c0c0900c1010b5222000082c250b01c0345480300303104950710b80f0a041d84140107100000d401c4205500309800d01c0302c01c0c0e0407001340380d10600408190343d5801334035150301 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 489793201 1250 489791951 489791959
    0x30c0f0803120a060302120105071e0e090a0e1e0114060127090e100c0f09090e07150507060b060418020d090203030c06070e040501060f0c02150a1d040902010e 70
    0x1952000700c03403005815103400094000030a8202c0b10031220054004130f00903062b58640240042942000d0b58102d046460958000b80d0580b13004001c074104580e003643c0185041340007050381b11040544501d0006240c0072420f07910142607a460102d102840f440d81c50303004203108420142059070000b0040300c511004880d200046e0b840c038070510921811044000c100000c420702c100d82e40a01c0003a12160020b18660405090403030143c0094451184038602d0403503500d44103e02810901e02d0002401802a8111503104414002c00d80c00f4180f02400c40e25140c4d03035109076446038285003141c01c0c0c0701d442c001a03021318018801807040702011070060f60382801080d40140c440c0054000e4078080c00d00d0900294141c000040c1d0102d4245020401078800c44854a6002c2d41c1c81402c4180402c81d0024440c007000217020b04070802c1950303c0340d0018400680024445d102611400541030707549c0d448810020302142c0c000d071040c085054605242803c4003412502000082416000a00351003800142c4904c1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 489794451 1250 489793201 489793237
    0x40509190e06011815060f0c030903150e0c0102070614070203160b190509010903020409020303070b0f010f09150501141209031b0624040f020d06030c0f0803 69
    0x540400d562201c1c40d903840c008115111940d5401c000c5605542034201c0d40011424081a201040501215081142d035141c0d40d03503a02c00c0c18403208885402042070100c00f0041041c8000011540400e840d01d00584245000140444500d40c01e51a102c40f04c501c85066411071740040007010340081c400c1c1d0440c10075140b099a02c000c0d500c0084e080a000580b2201c134003020000106e0702246600c090180350080301c000703402002d84104103407018020a540c140c000359a0620034001810940c100240f088d1001c0c0443e81030039119601d2210f004d42c00c80300d800b014582000100700e100742c8403258000924001004225603000e03034008a003898110301030141400180300144044ca9506411290900706142e0001c0d110f0810700002074403540310401190000d0280c80072007001c1c04012801600582000c3e609070070b040104d0925103e10110410724a41c400da0314042d0001d441014001040401407030000004c46070b0031850400082c0c0f01d1341c1c0100000002000d002d1080d41e9001045500080c403c0c8c940c820 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 489795701 1250 489794451 489794491
    0x108011a190803040801020c07051801120c03061b030c17010e060d080d060303180e04030e060c0d0207051212030f1b040b03100e060f150904110301030512040509 71
    0x81c09052544641c000d40b000080001c3c20a1041d0301600400c59041d00351490300b940c481c01c104418440705072a070030703000034000104808240a6122110341c1d114040c0404096540d48035041110b221102d003900b0200c07500d041080065251265440101c404d0400c5c403c01014141810f11400e014022001c0450003440030410350381c0c40303031003034822968400540c5540c0ca885c40d1910000d00300314803003140402c5d294221094108080c0d0a41016540040784400003655940c40032500840481c01c5150080e804011419208909119204072901030b50014900e0600d40001d1181c40240c80b903405203a5080f812198038107100120449030409818000f98406440e98424242540003102040e030915000050009500b14248060b41c4036501c204056094580d4803902005400c20031151558080c41c1d40d51420781c64500f01a00c5030010440d0580329003422034100c040740c100d4440b40c800c0c03800c204004c80100700f00b000411202d100e2400c40d1040c0c81c03c251502c80801c41d21040900100c142180300400340d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 489796951 1250 489795701 489795739
    0xa080304020a05030a08040306060e011206020901090e15150918090c0603011d07110709020a05040302030102040603052409010501110f0607091d040807060b030a0b0103080307080108011a 82
    0x3003c1d210081c1034503810b585c0c5140010b4240d10a11046070401d0a212001413248161014039040305c1ca14690150240035a45c0c5030002984059038507814014106c03400b2451205000752184158007028034540821011b2042008071494617009038800c00b8100701451301c41e00d038200c880b1032080c90700588250341e403030310144070b17040481d850705450f00401c1c00b0000280e0038030f8194404480c911241e00791348241d218140202e40c0140c0300e6080800759070100d04100100045640107161030780e464617050b81415125400a400e90340641c4c442400240c0718814002c04a902031100d440b01a2940c80c041e40c01030390300c8049000e4000501c9014107010800c40000c51442c0305005a030841c08084040d18130510b44118064502150b03401101d610014060b50141154400c642c1a4002c0e40c2100b440ad007801c03959a00d010241115000b801c6d010f0140d00c0249000890008009000c0c43c442e010703142c1c50b0710f050a001014104142e0101101783e04110404003030304542c6140000341e46c420380c2d4007040203c1d800300c0d603 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 489798201 1250 489796951 489796969
    0x601051204030203030f0f37060b07021c0b06010e0609102109030503010509090304050a03060b01170105060a0305060301150f0e0709060f031509050408090a170a08030402 75
    0x103842000a000401040690100080d84103001a94002405498407d000400364004803445140ca1780310701c00c00004550f2400702100f541d0345180004001c0c0e0502184101038903d10b82c820380303902d40045000710461501d4807035103450503508220010300340581c0d10780008030380001d44039a0612221204d030495644880003210b420107005808202140b241d60801401480c0c060800212400351020030f00c6030401074003a5401051f0169034103401c6901f4142005a1150094981a0184010040042d0586940c00c03210000c5014050005a5042070303000500300c0010101c20304281502000107001d90707515041a102d1400382403500180c6561424080b80c01080145c024840c00b404c5890009040240301c640f82c001d481c00b204c0e0506058460031016501260f450084e07201203180ca561020081e48603520142244024031050000d0700d07a60505035088900968050350010000aa06030742820003122030002084080215005030400c181111b407503140e1480000c10000d17001011905540c0c99880c8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 489799451 1250 489798201 489798217
    0x1115040303060e0c07120e030a1b031a0f0a06060c061e181514060907230903150f070309020d0803180d0f0906030225030e0109090203060612060105 65
    0x900f140c1ca003406103241e0003e0f0001c440031144000c0c001c000d0380c035880c0302e0002c0040003032000c1c0007401c0c410781590303400e00c0d10b00d00c43e0040e5400ca94241000408a50300003070b0001d02d018a0392030b10354141880d00d880e02104070000c3c51303025882c1c00e02508008065000c42c50101c0107401800000302404819800ba512070b0100c0d40752514182000b10250100061100d0b54410b2441001700d0b0b071b5041104000702c000c2e03a0ba240b00c072012001000001881a042660300e80780c1c060190315080031025190302d460b505c2c01007003012400030008007141d28180ea007400c2141902070a188400c0340c04c185801a903c0320907820040c00e0b44101620f40420b80115140d1441c20035045502c4007880d41c03a441d280c281050180045480c3d07621a102e180624641d01d401200c150885440d1035582c5101c403030030400182c010b90700100c46416002030005c004902007117102c0d1460140e034440e5603461035824800d00010b080342041c0d000750160a204009025082d0f54200c1101c96498010442000560701d140050300d02c3e01503210 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 489800701 1250 489799451 489799469
    0x10821040b250303060602100603020a1751070f0203070639020604021e180405010609060803030a0902150301030807050d0302122e0602070e07111504030306 69
    0xc2c5a008068145d0802ca095841940c04ca0f000d98807020080000e0340c600344000780d0000303074805092040c0720b0503115540c0580d00c44800c070f540024100d84402a03204040c143d8180c00c04400380c1c8025180c030402d800b04c44916465403203034504404142c004110b4031014140c5001d200c10a86c0050301c040c024025201301540040c0c00308104020007036249144910741c42e01620310711484100000215000024006a1086a008114035640d0b5401d10601d10346400c008038004010405800517580c640414104005501d28003220504191801da801e441440c0c1207400c0746070600030203000480d400003c0e2030b8880e0b0079035800301d162043c5002040041900e403a18807010f840000010040c4920480200304807072140c002c95510040c44d1170114102c0c09412030806040c060300020811440490811000c40c001030391102d205103e4240035120341c03201d1a44641e000d6001454108400340445048072740c82012410042c000006014a01d901c3d41a04541c00141c40404404181814480e03071080024040d900 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 489801951 1250 489800701 489800767
    0xc08060906180411041a03010c030c02030706091a090a02010e100c0b0c0f0f03100e06060703050d0b04020a021b041a0114120117212506050708010821040b 68
    0x1c0011b581d9502c42d012030320301035030902140241d00c074424402d405050020394081c2d17003040390a94514014140101040e6000e003a16004c007400c4090165041d40115988002450304484030703c0050040403104205c41e2040d03020361103400700e040c0c024000d00c064a900010004896a03541001115401100e18540f8603c1380810304c070707030104101001940030b0b030540d100c144025942e031880c42d01c41030342c1210040d0300200d080c854a070000e40294050000b1058029003c1803104456001c2801c80c3c0000b020440182e111f08150303a500d11020f10382c400303101c400391030901c220032105110040f00d0150342d00701810012600c0301142820506005d445407040403003020f5116595a02040070018607600c0200880d00030291090812421a81d050401c0100d10f450a8148011041c12554103801c0030721400300d41c21000c0300040003400b1881010711030707680e030380f283c10280d4104200240307060b00b103401e40d0000d20307144000301c100c0f00c07840d1082c0e40880e443c52240b0341d91a40388560001415406100802e0074090750 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 489803201 1250 489801951 489801971
    0x106060207060801090608031b210405180402031b010c050706180b0306030c1c020306040b04050606030714060a0309141509010b0a14041104090c0806090618041104 72
    0x41840e00803500c0ca9603c041a690300c9429403021075800c1d10850f40541e00400c5144208048208204403000000050f102d0b101c00c5003080c90030800da004000050748100080500c158941b50303030340c4401403842441c082003d160903408a544c400401800044000c0c4c00c000340c9031603a101e44062408a40d2080684881c641d80301e0300901280400078041c039101e4031071000410010b00d8902528800c08008008211458203041800020b981d0315240001c4562169242000358404121490080b8460f010f107001e80d2a20f070a100e4101400030f414248079402807a0108401042182d1b200c81010049800316950700c850f071006d0340148031002004281a452000c041c0e25a4808503107048008100c6101e02c9540c0c0d0740b6112036080720880c034106644014101c400b41f00200314202580c43d07100001d000007900c9006104a5a699045a44000041c036291544070000030b0344404180c0c1c01400546615500f8140400000c1450000746412400d585035030740018144030034580190b0400700054010070015000c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 489804451 1250 489803201 489803203
    0x412030215070e0d02100504080304170708070e010303080a0612050a02040b010e060d0e07080105010b0c0d03051003020d06200a020c03070f0e0a02070503040f051c02030d0c1401060602 81
    0x51902640d0034001c0c4100015901409007008041c1042c00804c9980202007a5080000313030072005e80e007941000300c1400081449402000144042c0c850591417400c049034036503010346088181d030800f10064100c0e503c1084190300c40800c0c241540c4e4141080b091079510300c0d9424009200590042040b90366039040344041c4800441c10028903402940e050050510003401075072001186100076400c00420450001c3d648010340c418080d80c2c16035010744030829070380e220301e60943d2020b800400ca8040d0006000b9000703103080002c181c1b00381c000c4c01c0034001840c000d44815080b1b0020301c4040c3c080c0f400c5d82541c17420000755038400004448404d824200d03c10005000034059000000080e002d0300c0ba040c1101c8242c0b90000d161001c0741e10a410380c101c2e0b01d080201a0441400207803040d20f103140c0a2020a000032010300141c03000d04000d4410301034007483c0c1001c01c89030b68900540b82d02c200d090789403034001580340031424075004415400e1100118209140ca1600800010007204442d480c0c002d01140160b8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 489805701 1250 489804451 489804463
    0x1b0804061104300302211303031e08010f0b0702040b030d120c0e36010803031e04031d1c050c10050315010e120f0705120109150203040804120302 64
    0xa640307014503003400c1d54a0907a0400b243d400c240540035a22440000042807401c04c0e500e1032051481c1c0d8540d082000c00100301310140304d40e8000b103020801e14031044c040c1a40d01240d182110307105103440c208035450940b49008040c03080c0640200000300188510a40d180c503001020315440c040c08454110369003507c0105401c03800b003402c091841c10440701021891003559048800d0500400e2014040d4032064044a4154600c05054940030b81e81d180003020468428a14000e141c17540c043c6075240b420200c13202e08403400d03007044110000160306100100354482c80d45055010105000802c00c240792000810107401c6102d170410301e640c1c021514042204c0402d6003c41050706481408080c0901041560f550004848000318060100c40301e40d2198441d50342c64200d054050701074890508290529820f0181801d0505195413042c40100100d003800103e0406008194008003c00b41139541c1e40b003d448400300c203c240342500840400e0900210804450042a80204010010701680740294590b1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 489806951 1250 489805701 489805739
    0x3111204020109050d051002130b1c0c080108031606060b0403050a0b01080a03121a1203031b0f0703080c0408011b0807140304081c060f181b0804061104 67
    0x10f103841d6000200360402e052651050b07540400078000c4001c801e07075103000039041032564040390b00c00c0c081c0014071031451000030042d50038aa803401c4000c2c101030003020142d81e081d504800c100301d10000104034241d0040700791604290f480600700c521030030f5414002d02410580d000fa1024400000e000001c00c480090310b4144544a0041306107240c2c2da4101070ba4840200d140701502140707110710010840d8480350310100400c64602030300c081261000340450201050920b00a9840c0d100005010440050010340e000500100d90740034505100302e232030704800e80a42e59000b402c2c880740780040350138030b5803540c00e80303000d0400c010080181600260a82882c2651096020082a080004070300014403400c40300c00e200d4099050030f89103449039500c618455000c2c620001089030461152092a00c25004204c001c0444001004085080495030308882203545080151305103000d1414840c1481000010f0000807607040041507a41c580c01d00e1405040450b00010801400041c08140b082510741019014 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 489808201 1250 489806951 489806957
    0x1002101401121407030b0a050108011a03030f13030b040b0103140d0c0809060904090c08070b03060a06080415050a06090e0307050703110d0812071106040c0b0703031112040201 77
    0x20103403003080303900c14020038012240b100d034011030b004010500089000301000700c40e5040b150381c0783c2c1d40c0d101d10341c3e400c0c0240e0f01480044e4036000100100d0f502405034480e05003580d00d80c00e04c2405c80b440001e650340b20300c0020950b02030300410a00c030500c0c1075810100007140c1049611449180500d0101542102400211610329001801c0e41f11600d001034070178052401502c0700050386000d42c89d506126008880b90950103502005000c1040e00e403030040494030380c86402601c18490501d401141000440d4111102001c81401041301595071404120304603102814485025212410070480c0015010800080c1c0c82c1004184503101d84c0c1540f149084941d0803104000005a162040c0c1d12031050007406045d07944469001c4c03011640220111142a0300100314080d440c4460355480c009410090310007240703a4048080010080e042010521040c4001c005489145007640e100710720a003071741c040c103021001c022a0701000c05001c3d0b031000c0c403c6100c000768162604502e40f44c2d010b180c40f048600f2400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 489809451 1250 489808201 489808211
    0x308030a090203010c11070e04141e0601080a0f0f02033a0804120809010b0d0302030d0b09061e040b09090618010c050406050903160b0304060612080a08060d02100210 73
    0x4602c11b0150001c50035244014101307561619032904c0303a809019005403040309014804691075442001826007078206c064030f40b002908490f6000341000d0050340304a25640144004800045041d40340565450784003110580d00c00c03e500100c2c2c50100790030710b02c00c1c440740000700400c50781900f007000c210010100c0621810f569100d01c0201c0d26950700f550020102d80e00c00c1e581459603405030018603417000561000160000c008000500c846041c1d00c416005078000150320395544400c0c0c024115280c3c0705450345881801d0100101c0c1c220001c1703005180c40214140d0000c145640ea9070451428150300808003803240c1040c2c8405504c944098400310520340592440064165040c01074151900064541a0801c1d103841810388456210b0704190f5410700030f0310201a0701408203c03021000d803100000c0252070f441c107460684211842608210a01c00e505001080040c7c20382040301d0010301e65180288454481c0c0020940152001900940c4520b00810118015500049500303000007101c41c2072003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 489810701 1250 489809451 489809471
    0x5040203010e0a06060306120209070c021918020a090501050a122306180a110c0a0b060a1409060d060912020f0d0801031a04080706240504140f0a02040308030a09020301 74
    0x1b00300c03601441781980600210644802500e040c0e02e000c1d5115015062520300c51480b83c0c0000c50700201e040b1001d1044890340800e100014548607501d613800c40b038180c118901900ca0001801420640c4141410080c0024045510a2007043c202036004a8018280280c01c07c03943c042001c0ca030407020b402520801003000540a180c40d05101010284079801962541c8806810303001428100403840c040600030801c03002c5c1444200007804c2801d02440c264036140c100b41d410009403200307e500c40080c1501c42a01c00d81c1e25645c401120360813540490344285288541d05d0440c019000f0a8006404070304051450b84c0313450340102d40c420001d070510082c0c41c2070118031582964501c0080c00003404480c2941c10003241149082403107904240190003460a02d0100d0303031007400380d0b81100c1c04180b51000340e80c0043ea01d50300c00040076000e0042110305000e4180c04030840028800020840c10f001e40c0002e0205130318809a504a4003d1500700b00401c0d0b030380c6031070f00d096400b41c2158041280603610340b0f12a03072 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 489811951 1250 489810701 489810707
    0x4050a050708010e07170c04090b0a032a031401050a05010609030c090c0c200901090912031a0414011e050603150a050d11100305060a031b05040203010e0a0606 70
    0x18070808a81d21241510b03400c1c0352106401e400d00030200c00c103000045051032a010b041d008000d21504085114960326811304032010251044002264080d4a10708410701c00038601540001580c4104409034080c21009508140b84502d00e44c00503000c01864580840210019001184118030500d801d00c5a660381d00c030102c0f40700240344005040106c2c503101c18031140030b0541001c1d42840071392074200411202c5440314183c41c2c01640b80504100d001d18a48501070801180c05401003500f1f0300d003004100f03495100d020300c145070f18120900705540e039450780600107488040400440c10203042001081101c0710054280f85003802181d10401c10400d01303008500b032050b00c0909860026014504545603250031285011841c84800c2e40b1814810001c6226194004c2c802c501c10300800d0103500c22070000c400e218001032044080b6042504000412000b615005185811a64003058480311005901030416201c401d6802165109000000020b0001841c04840c0d0107001100c10400031aaa030b14010717 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 489813201 1250 489811951 489811961
    0x240305010f050f13110c070e010902031e090a05030c10050105040c09210506190c300608010606020304080d02030901020601090509030c060f1e06090606131703070204050a 75
    0x2c1d84440c440f0008030090070040314003082100c0d090030200d19106001c601d114541c01c20405a06140d02940040284d2441c024405005148402085140d400e01c0b445003100204401c42003401c40c002c800101d03090050802891f614544c110082c0c0c1d84400384218120b80703d07009040c071001118180400400c091070030b032207a204103241d1911074010311490100300182032021700c280c0d000c0700305486100e41e011403805d00605208501d00f0b0440032581d0404d042220803144905440010403581280b1444040f50142e02c0b01c4440d03502c8c5002c020300c844440500000b0b0705407030b040380007654200400000d4441d000006841a41d40680a40d000c0741d05a00702282c0c0d90080c0440940141e01020040107041c600d54400c980055444050701d03e070a84031780c0c82034600001551001861841001000036041d2a0320709500010300707081140304641000000150a5200941058441c0b0800940c0040428429142c1001099415240d500084117003c45688039005000240c0c051070a0100082c50340b0603034460 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 489814451 1250 489813201 489813209
    0x61107050603010e072307020406060516020f130e0c1807050f0f070210020d1e020a12020c12030307120209060d0f110d02130803030408030703090c240305010f 70
    0x10721801c5070f2800c07406424a02c005400402071101c4400422800c10750400209080c65604041655591092040c841100c1540e070100d410002d05000c6c0d0b0240240c0346107c41c01003030b0100d4a100c4295041400500d10003150480c4100e038914129045580810101d44120f04100446001546115020200480d50422109800010001c1144082c0800c0800113000448210317010541404c013150b0210390303680829050840540d0103803245071000f0764000440c0864080846440b801240c5e0b000c8042d6880c000b445008144524113486c1d1a01c15101300020340b0941ca0080c402d071051264a142c083d220f610030340d40d0328000b4030180f800f003807060001d000700d550700c9402501c3d040c580206d84103000010b05100343e101038041d881c1c1c00d9103800c108200300030380f40e071003101c000040c0ea40e1180c080003c030400c46a4800e00c1c09400600401020841394002d981d4810450308010409080d00d01c0e08407040500c5070030480070850703070301d950248400c150440303489028120741301000966214241c20300c44640c2480307 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 489815701 1250 489814451 489814459
    0xc021504080a15141803040b180a08030406230c01060308040311030105040f030507020a090e0115080a0b07050c0f060a05040209060306161404080d05130f0605030a021606050f0106110705 82
    0x1149170800704c100301d0700f0000102e1046e203007010b8840e00f01c2900303030b84101c031034002880382d807040101c05207010051000200303c4000211725007460240e0103007012144913001c0c041c00441c102420b03020039988049552000380f10008008844d102c1c0742c020f6031900540403d13550280c3c60003621005050503c6042e005503048403959452000e1560200c2c2c1030f03486000200d8020440040000f60040e5500400c140403008000106100c48400e8030820000072660103815164030200401001c926043c490603041196458116a19440003407800d00d0302d42c44d2030025615225070010041482c4003648054010362007152801d03030b00e407109403c15680701015220628640d0503015500307100c034060002402401c940280035401c240e92488082d04007030300880710001003600007425241d081c60b0010003501610000101e543c03080c0c01c00380c004056001c01445440300b9540080c1e2241941d007000098088140c0c030210074021751a0007816a81140d40030307c607c0002c200e0300c1105000c1f810f07010410301d00b514400740c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 489816951 1250 489815701 489815741
    0x20c0a02180f130f022205040606210c0b0a02070807030c030303140609150d1a0f010816061d040921030216080d0b181605090f010c021504080a15 64
    0x81c0070010102c081e041b40341200c4454208681041c03865000da54032403400780d0300020b9407a02d440414005601030481e84070414481e08140c10004000420880c16954140c80347e030b484514201041c0d01d0200c281e04066100d1041d0ba20020402101030b41d10805d0303038032036502802101080c8280c0c5010200c00d84007581c0c000514000249085011203415555407001081000003c42d984c69018850360806000c42241000404100d1304000401c80ca0740103002ca54000c0518070790105500042c80c40c5405910200860070b64040e10758070092248040d040d000074000c0104825038680869013841030040142c1903d900e5a11890481c06482525000c0596106021815914ac2c0d030381019039100c0e00144414a40da0100c8130340c682c40d01082d0b00300002070400403203003c2c20101c158207520110030b07042408021003002070b10003d444004100c0020701003820700c54140042c6100041c1042e03855020814440800700d4002441c480000e84101780c5802011140b18000720b0f900d622040e50040031550345c030000c4036 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 489818201 1250 489816951 489816953
    0x308040b0a200910051314130501080a05010b03070803071104020705030703081e06150c011b210207081e090303120a051003021003020c0a02180f130f 66
    0x11203031541e006403029400180c000d105550100440300e10100403030340000c04101100c644c10b102c080300d42090007a04140c2d051145801c001d240207030050150000000c0351890407416600c41080751804401004014405980c68521f1180d8032290200161001d40c20300c003055071141004075600003690b880d071010314a0005651201e02d0030650001c1c0f07807500141c0c02c121035000b180d4144090120184a81c0e9040443d0800900608c202841d51134803110781c07034100b810b01c171296880d0314880c86141009041c007621071000c00380c030074010110829800c001010070034031401680ea10010304074003003c0680500355500541030448040340100c0b0343c02450048104910003481d40c81c0e0f142c0c4040d04003210f031352619000080010078219048611f04015140c1854144250950103000e116448100101c408503414555000903104002080c1d5141c11701d81d0000d11003012110601502c61003580182105070b4010020695610310b02089564540c00484c2c0d00202d225101c6850860207116082108081c2c05003003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 489819451 1250 489818201 489818213
    0x3100e0c19090b0d0507090507090b04211110050309120f090103090c080106060c060507020d08390a0801080d050901030506040f140105030705010c022404030b0130030804 75
    0x50410750794131030000048a000a00d0401c0340001400724614080f40304e00302010050684482c0342c0010942902c240070034041022403404215001d00c0e0520340000340091070a200c40c42c002d680200b1078104403030500702c841e01c0780c02000a600400c01c1c08c040f540c1070090030160103a01e02440e141101c45000c00c2103000b209610175000501114054180c0746126544c41c0e0420342110001d9010002103100d00d0108030a0050501c1210b40c4001180007074507640160100c002c1c20014000e01080707245c034800301076041039000c2400404600412030062440080315512801090b08003888000005812100108054102107034803852104103032586030800841c90015405031030700030801504144e0701d4107030845401721401a522010110b0400c22030039410481418140342d510b40016052000c030160340c07c0140c581c0f604060a1100000400801c40781b15a8005468403580c2d10152515410300000300d460814000d4403d00e040905a0142101c002c1c0342001c0b42030f00404030003402085c030000005010440c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 489820701 1250 489819451 489819461
    0x180c0c080f0f0c100c08070206040b0903091c140c03030a0c03120f02090f010305010513020918070f0201051e040809130c05130e0c0714030903100e0c1909 68
    0x25024a1036818682408402c2445070440b0f00e05040c140d1221031080035a01d840e21034030508540034500b1010381e01e031102e0082d40c0c42c2009080108819900070008121110500c00c0e100898030040c504401c9940f4800e201e80320320031b400000d44008d00700190b2400584c50000d01006040000b03005141000d0b921407050320301004482054061001180716601010518810140d0f4050f266000607203c0b20b50320144988516100007070740c107144c50f1100600c055a12461000781310082204056681e036807400100e603a14413258040081d00399440280800c04d03400604040300c2481d554020481340e61043c502158140c0715090b04407059000902103070100d503001c1c0007441c2e02d500103080c0c40b1034034404840c40405c88406040c1c140003d00702044001d08040341600c404010302c02440c4600260620480b81084d921035044004e200c4a6540b41200c42c20501340f080e105c840034020180c40c15a00c601812001503d40003c00c1c04160051858401d00d07440e000800254000780c408004500070700700380580c2c000b05 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 489821951 1250 489820701 489820717
    0x20c0d06090203070f0e070e010e040c0c020a14100201060e040b0901150803030a0f0203041509020d08160201030b032b12020705030a080603071202010e040b03031201180c0c08 77
    0x1a1141d030703441d000d078800b0081071005241840d584020145040e0680e40c07050805001c0504010401c1c600d5030306d0742e81c402d0f101c40c001c10049030300041000d0207020a54808800600c002d4009014200024103407400c910b81c8450188140e0f000942c202c00d0900c00c0b0b080302c4d0309025102c100c003008404100030400010009901c0703203a000000803440745410100d50110f9070380d404210950700000c200b000401050003504400e4404c20800d5081d410079035200031040d000440d0101850b60b072000b84005660751005581181c6d500403560076030b158180c20011008020b0002c0c2a03011078100190311155090015203150300c3d803001e4101c505d508980c0ba140c000103481d25206901001800c00f8040b40426451005201c51840f44006581e078503c903501c003a111040003084a0b2280d08a0ba1701001700ca1401c01803010400d031309103010401d00a07a280050000c001d40100c5541610020034081c41d68100f0340b9103a4143c5403500782d00c541c0da40c0983c00d007a00b9219041b4212002840d9810600c0000d2480b2014000131 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 489823201 1250 489821951 489821963
    0xc0615030706020f07120c0929030c01020c060a170403023306090703020915070c0b0a0c0803070c0609200f0f0f13090b0403080a1119140f0403020f0a06020c0d 70
    0x5230380d18280e5805640d0144004e0140380004061411000c1d00070704003444400003900906032040b00540080e44030000d2036201c5014402c0000c4180800384501680880c480044684041504203418001d540700c000c091a910342482c00c45028114625413151511100c945142d2082c00790354007014400d6044001d40be030300906401b4000c05e050b035615911000c041d5440c28040545444070b5040c400341500d0340f0340c01050302c10380401103040d8083e444414a40d0840d00013803110b1b5240c541c0541240d9810004a02401041c03030001c00fa8108000c0201e200b0709407001001045d09106c002017044403041d802c0a5840e032050080f00b4010881c140301d8064248410010f007142c14456140c0322101c00d071903003c0c0003203404244000401c010580c02070720450f00700200301010001003a52034600c5546214a0034404a9040100c1d40182807511403a0410600d4619206807503d904d0000380d00b550310741250000b2071050008880c17144140c2012034403542240c2c070640c01800d02c2070300e0f00184680207040480503140 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 489824451 1250 489823201 489823223
    0x60d020f0d08040b0d060e09030702061315050415080601120b0d1401020306090a02031e0402131a01030c1704080310080706020717030c0606010806060c0615030706020f0712 76
    0xc070b052500603000a041c41c9210560360031143d1505001c881182d0400b454015002041c440d0b034120000c141d070316680d410341e82c1640c6d80080300f202c41510825540801041080e00d0800b2a0a0350300001038001c1b5885600b0041012908080c265100703042200d900b40000c2440700700310f00390310b1140c04c540d4410074090f18078081c2840700d8440a488502035070300400aa034000003404242c1c00d03c28001a4000c2c10340108500398205800c43c02180d070341c3c420390000a42c8400c4085825540c8210300f4545520740910100800d5143c00d010008111002c4140d41c086884c2c02c01c6400fa85004a440303185920419000a005543e00c1c0e07200030310360308050011302802000031741c003003501107080200001a0001c1c1e002408101e141c08030300290041d40784040e0304a81c1042c41100082034000494a030030000074289a4120755425010a0440c0a50843d00d850b600c52542442482c20340c5040c419280b506c154103640d44d0715103650003682e444d81c5a41c01040c03240d0101404024404440410f01e042c6441040d60000c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 489825701 1250 489824451 489824453
    0x201080c120405010b1206041a0421090515070b0c0c0a02120105011814072d03140105010503071e1418120d0f03111303030207080f0303060d020f0d 65
    0x1021640460b001c4400303a54800000b000c0d4540081208128070795400100754a14081d03898803159000b613440e40c0707484021100403908006a900000111070000e00003030800c406040c4008001200e5071044a0107400fa4000062410803010100d0301c00e50b812081d203101c20340350803452600c9030340041001d11a6010310016600160348401d9090340c025011302c0041041e504040014655a6800b01c452200a140c03a80711560481c0d0102c4a40d440285401d00d16031801c800032194501441040c203103660305105900d12444caa40680c00010620f880f800e41420300d80e2a0702c01500c10f407201740d41c140e010540003550300862046085c40000c003000c0354a849003800082082c60f0303029070800b042c04911468102103005a60030960901100645042c000b41440c405040003c0d00c401042d1004c81e04141e225208590416050021213081c0302d800c28081d07841c0341c1d482c10700a496010300c0c066030342c1900070848141092200041a40e0003040000c1000700d65000c02c1c4e00300304048949000b02a006002502014 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 489826951 1250 489825701 489825727
    0x90d02041404200303070c03081e04080109050f06060a03230304091409120901030b01210203041b060905010c143f04030f0206070b070509041b08040201080c 69
    0xb07010ba4810401d0500030b901d0502150030244014180c103019600521021002c0b40f071182800c3c04403500555500d946d0182d0300c001207140c4c001400b40c240c4405000a000400500561000c00b4090090707003564500c000f40c0b01c1e95601d9501c169010381c1d2002d007004043c4041221050155982c0c10385180c0c404015180000349411904243d0010200941e80c24000c07403d01054041e8540c0800c03010007038400012898016042c50146d400d00c03604050351101f442030a40d0283c0d8040602c0d8020743c401ca440d4071110100c5030061762003207e08541801d50025141089541d416103202030360940d44038a0343c1c0c1c500302001111540101b200c00e884401100e0705248004005100d001410b40030342541090f8140702564403415244030201c2000040c401da02040801c20b00c010944d03050313940c00140c0900c2d4010351b000280c481c0c080c0d440003920303106003901030200c20340d0170800a207094201550240400c040c3e002c0300e42c0c4014501300c06100411090800a00107600c074500f85544816201d682c0c500b40f003800d030205 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 489828201 1250 489826951 489826991
    0x604020c03041703090a080f1c02010f15033e040212090703120c0803061e060a120614090703110c0a0f020a08010b1c03020c06030f060420090d0204 65
    0x100032940002645d0b180034180620201d0140c03400400821002d010090500d6983d0700391206214208800c1d1400c1c02858401e400170000000072680901840758114a41480102075100071030f45030707034202c0c481d0740e51000c40b588083c4c58014040300503140002c510440f01e500c3d81800c0d81981c0c0103508000754155940b1840b04c0600540650b00180740542c00c5d4601036034001158413182c41030101f0b001c03d903000166541d08a039070244054405000c00e411ba000000740780702d01d60311010740c031860111f4448074460703100c55445540307004171000b072201c035954803039110086184800c1580c101010314005104e0700d0080e080090903d14035070707010f8a4002c554450a0501002e91402c1305c04001c061410015840c01200d0034015001b000c00820445603450000344249407690003404804061003501c0c41418001d00401c140c4c0e070b201820152752440c02220015900f0812202907202d54501081a200c3c980c9440c100d07000c030888a000305103020340c21303c1081910341d00c509049030701c103440308501840a41480e0f40 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 489829451 1250 489828201 489828239
    0xe100b0708070b0105041e181202030a1e0806060702130f060801050f010617090109081209010c0e060a050c0703020d0308070f02060f19020904060308040602010e06010506030604020c0304 82
    0x507031516400b46203066140450706a0140d4800d80c1403440c201c012400b95103070100c0e11f0000503000150030b440c000ca0907500240000e4082c01101068030ba442040742c0201c000d01c400c00f00352352a0021200c2c0c0c1203101440160140403200094400307000503086080400052140c04c0c0010440350484441d4071246081e681881100341406803518000c000741d5400340500303a00030309030002c0e1035095030600000802c0413000f442000240040b103004103135500029480100c1c010340006419960b00d280001005500b0015034070507441f5840e040541c50681e104902e490b03010b4000804c40b5241c0180b8410454468008140100b502d0050100000060f601d070414009528840d07200e01e80b6a107811000680554500311840040d07400c03081c200328215454028148d0302c40c0c111340e169140f9400b9001d52800a00509201c42e0300715140090120500c88c0d10000380080b140c15a00a020303158203515a03a485079400e1113030310b4004100784041640d1340f5054001e0146240d01e942120f05040c0c0e0b542150003403400e5559 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 489830701 1250 489829451 489829463
    0x801090b0f130b130203060f090c07080301120b010602030a140306010306120b040c230409081605150c090f13090c0b0d0b0a0b0d09140a060501090c030606090e100b07 73
    0xf444861905000d0b0316212901c2900808500f10714000c80460001080a0303841c5100d06050800101203151180075504059080985142c5960715038203407114080c10100280c901c00c0980d0000034803030348004100c030b00c00500e560300d49100c90b90311584007519400c084c180b1814141c90348c90100d0000040c884030103826010740e540310701e02e061606010009030b4094011865095103c2a040340c4016982154201e440080d90300144011441c2044207581c042d07030181e1045142d00c1c44d070403414080c0020b140c0030b6440442516552a89a802c495400c0d4821502e02640007048900500301500d4103440c41010100003120200d2041e2080d9200032601445401c030303046165012502c030203500200c1c411500701c043d056078411740c00b03405d02103060304900a40c15201d85081e100e103002420400d43c00d00307051025440a086880101191610030081d08090060142d80303031070a42c0c0e0940a83c0303e8003d450803074055407160303410f55003041401d00407184002d00c5038007036220030140080d4210100006000e5540103030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 489831951 1250 489830701 489830711
    0xa0606090509031219110409060605072402040308070503030402011e020a02150708131a03010f03260412030806190e040804120606060305090105040c050d050f060411010f0f0801090b0f13 82
    0x40603008c12616140c009508005090000500158004032030103811034100d2541941d8a15030480030019200b00d42005080034008142c00c0304001c40000511b0083c1c0c400d0300c955204000f405000b440000f0031210000041c1e00141080c00982460b803030001c220440250540e113455243d07114030101e903020f003004010f00e4644140030003900c0c41840044420203002000c1c90310b035514020010b2070004030b40c00080c1040884001c0c0000d241400741c040c0045180c810a600c0e103c80d0381d055800107031400480c0503404036081000050340c52402c18469003003800d038090340710450340c20701640000010b0700030310440310310b030003048081401806441c07c0c400140c13003420003140c80e5050140c020159403018140345116030410040c0400140c01c440014103035282a41c52002a11403401c1040c64228090501403440c00355409000c20f21140c0319010104110a8866900040f10500100d4071701d0011001400001d09a00c0107001c0585130b608203405446008022a041000700b20000314980000c046040701a9524 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 489833201 1250 489831951 489831959
    0x215070804050d02070602030a0e1306030b060a2411072d0602160b0d0b0a1d07050f0702040209041b030e0105011202030a080d18050a06060905090312191104 69
    0x10007822000280d40c4c400f92000514254019590b4010b9140301000d11814400201d5562561401c0d441d5013451a582070090350759038105040c2d068015202680240b00303600c0045a10407424400800702e4072640b200800050740104100d07001020311216414038081c89c03000058403c2481c040180824029007040b59068400010030b43d081003a9001ba41507403c80000000d2014980042c0c004903685000000d03625480580355038005c0c180360b040181e2041041d240070a03036419180d0f00e008188a1503842d9411511790304411307103039801114000b12684008102c60001803e10741c010f8850360401810200703a80d00c45044402011041e50309140020b607a540c00d00b101c10000f4001c05004044c1c40165110a10b001c0c3c001c607444481020000d00ba1781000203920301d0811031a4440c80403010049a26040c5014901e01651a161500415129a0705021000c150100b0510415024000d00380c0110f02d0050b8a00325528010307170092480d0008500112010480501806030462000000c1641e503500c07818 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 489834451 1250 489833201 489833203
    0x90f0f0806060103060501080f06191202040e010216140313060503040b0f07090603020f0f07050d02011b080a05060f060a030207020103061d0c030a06050a031a0f04050d0f021507080405 81
    0x4002e104904060a100042015903041480703150481e04080c20f488a555500c00450031104000d54162030113140c2c4800010f40e02c140d50009000f6a1085509103c1c01326800000360a07806180b08080c0310700c000d50f010000045e598580261440301a4040d0f90400e42c5489400081c1c1c5560f034408000318a00000300010800b442e040194005102640603c960401310001080c690070380c0a038109041c4c0c00035004162940c03501c00c4e070301c01e151902c506a54030501460010b4a4800300c100b030074050341c245040180c180d1412080c00c900420182c0c0c0d1940181d552684c0b4501405016110542291a00045010540f20b11004190b8040140c50259503500b042c400101207840c0350303000d45401128600d00b0184100213001043d08480e22103007903600c2c0d031a1449650001c0044e17601143d4440d1101d50300204006c10701550a03903c101c40c2000c1c0d000b81d500c5900d8079842100403200100103030171001512845074001c00708100220071520484051050701006594070020a07198000401c2411f0104810000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 489835701 1250 489834451 489834463
    0x6030503030403270807050402071e080a11030c1c0302091008090c01080402030a03030b01210606200a0201180509013b15060909040308070206070203090d0b0601090f0f08 75
    0x140c41d50700103045d01e050304e0903803141141d0103100d1145800090704406c0c003610002038807a14804500c01c040903103841c603200d88035031300803060039000c0382d0850281020418003100f80e80c09100220041c10440404200d40004201025841818540c0c00e118030201c03034407040080307082001591100d440314209021811720749140020918100700e944810000161404a210035255034181800304425003410016210100c003820300c0c40e000101c900400d008080c00e030b006803007150f00b00c2d204e4042e0300900340b10700b4106180000b008074030703680144030100065204070250740c00c60051401c5684255214800164005000c0c0d100c11014411402406494000b002d00e840c0840c0c800b0244c9914100082100b00350158000c1911814415030340510303040340c850a04071540c00d4001410030600d8500380c034014040c00c2d000e0b91144018412000040e861a000204541050364003c3c00c4000d0340107280d8811103001002080141001140040054110032004010000c5c00005040c1000d403800c006460b85010 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 489836951 1250 489835701 489835757
    0x6131a04062a03110a02070b07080c0f01140a050c091e040f0902030c010912110a0308070303050f0105010906020a0b09030706060b0d150b122707061206140607030306030503030403 79
    0x10104035100030035400047c0d42c811100000c4446450312540d04000085002c0e18034581040d004900513110040010342c0814010000400d0981003903d40c0481c0100b10b407400c4607003000c6080100081c8a691400510071401c1c1030700c00c5900084503507201c0100b4180c6a00c54104c0c1121070311980321070114034050062100180082c0307064003036079140c44421601c0c184d003102d01418031140400040056280c4800301800385030014242c6540d0441e03417500030005d003800c607980c0511500100c004243c030340c8903105c0304044400a500500701540c0545030201401005005001c0700d00c0200101d400289080c00381e0002440310305001078480c40b121503c007080d903180002e444802440501c050002000690582d034440e0300720348210740d40d0780d134858104882e54000991085038056280394000031000016420055841c595241110506d540c244401601c0140c000e44d9034a0710755502803801402e12001500031071b4024030380840d510f992512007a042d0390094030b040c0c001810b04c40380c0c1c80c0c21f5051440041401 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 489838201 1250 489836951 489836981
    0x8010902030c16080f030403050417070b221e0303020d02010b0d060c020c0d0c090608010506100809190308070807110a0201030c050c03040e070206131a04062a03 71
    0x514040710203940c2841540380f00307451040d1200c071a0040c0700203d0709403481c0ca6036035140590391b42450306024040c1d40081c031510240856112100c200c2c0c0c2c80108054003110101c50341141003190601038000c0301780d18074400c0b041d052941e2100041d40c02c0044142c01140c401b80d04294019030644c2002418000a10136a00941e13041c49101611500c0d24109020041e401180014085500f00c900301e09104100d9429541b240d0074070f009006001d4005420707411a81460800c000c4140d403989030a00341c0e10700b1601264440381c00500301c00d003d4051090507038802810010349403030b0b603048003843c440c02e88070034002d400241c4034000704462141c0100c1c0c543c3c0c0005190429040b00b88108180b203a80e0307070b1180c070000d0405071214010044140620b05580000300d0290540c0d883e10340302d009130b101d80102100c0d09030052040e41c010540700c0c42a0386800d840e40b07411001600c0c01c1500390803005111a4007401c103c80d0b56135075841400c075000700c255201e41090a0307440ba0009400c4815401019070300366480708418 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 489839451 1250 489838201 489838207
    0x20118030206011509151701061403040f080408030a02030403051e0d180b0a05031b0f070f021503250206070e010c020a090509100e01140601080414190308010902 71
    0xc6038002420604540c000300c0d103c502c0320f501e01c1c004c8620354102d40c00703001b10703540801400948030b400041c40a4039040101080440f681d03240c004842914503880101d402c0c10003000032030041000031039112640350081a4140c90960346015042c0783d948005025001a0404501401009801d00442c94030180c7c40800c1034030f00d0110702e04030fa221904c4514240030b1005000c0320b1703410341505034a18802000b82d908030780c1e10b8001e03090000d81142e0080301d0100c42041040b50090407900304405507a0b00c0f0701d800d40042d040480d20358070204100480a41683c0c025460000c04003940c002c10011442502402034424401d0308a110510440c8030f154012000d6400c40003c00002592000c1c4429802c1c609103403039042c403001400418030a01064112121480c00c0100b0030440a0001511003402071520004002480381100b82034203c40880c017914919100040c0400c0c8158030030398805401c0380c09a801031404003100c0d035407180713803e00124004442c0c000c0e03d03084d5418180c2121001340101138515080d46 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 489840701 1250 489839451 489839453
    0x14160314030901200f0f0106060806030d020307030804080d390813020f09010303020c12070b030105040b13090501240f060c08130e04170a2109061a01020118 69
    0x4100f038040c2c0b0b07003069001d0741544c4100d500c400c00c104a1184440030a48400510a040e0540a440c6034060440403036001c0d004184107040c000340090301492164080d509010155074202d485640143c010788070340c91b043c403058400c200309101d590400c030b00c00050407034046221081800315031102034100d542203022003c0c0c00c17102504802c2aa0344601c251072a103500031080c0c800102d900c40303a02c46c03568100d00c6000c00070042540000e50710005010866000121000034240d40740e40740d0281c05002c9440c0800d000402c0503007415004058000002000640050903e0b03000000b200c10300d0100307551980d100c1074030412001080c081d4170210101856404241ca09004d03080340c49103031360300c6804100000c800203d0248150882a121584ca03036103400c40400d999500c01c0960940f05441c1aa00b20180c0140700301000d030403408a07592070f4059103c0e01c01a6424098a06c010030b00345500034500c4c3d841d089140c001441520998003c460040c4084900c0101000020f003118441f142a200b04121016150 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 489841951 1250 489840701 489840707
    0x50f030c01090b07031e0b0303040e0901060303090509010b041802090607110901050a0515030a0207020901060822051b040209060a120e010902030a0b040305040f060503090607052514160314030901 86
    0x90500b280882e0308812031f80844c1c0b9503c66940030105640d801c10600c444240e0642160044034042e64481009503155810400090360078420744012070401c20040084000e405003803120020a000014240140c04c00803070545c1c1c1c00244215010010030401030740902c0c001415502421003500d0901c140742c10039001c100040c9400802006100d404800180000c169070129980c0301d81c00780495109503500c40d40604801e0050b1403c40d924905900c08080752961103805030f455039000320040440440702000746032058081903240b60095020010380031a07440d040000e100b034003c640d0360b0b9042d0a9440041408072001094030500e00d904146182c000740ea400034507040c502e5080502255103403564682640da502c05c9a12040c2d02c0ca000c0c181c0080d00903008400f42d8407591050b8107440c095901d6010441d510320944103120407012011440f101c920240340d040203802ca100d514950080c407102c2e440300d441c00c09502054500741042c440d0034030400040d0082c3c41c041074070f00d01c0110708110a20f030000e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 489843201 1250 489841951 489841991
    0xe040c0906080d0c0203030904020c06180d0504050f1809031c140610050d05040f02190f3503040303120b15070602130806070f2a050f030c01090b0703 66
    0x108040010132000942951340500c200c0d40c42c0f003001001190750b000e11080c0c440d102d100840e0760b0184241041c288540c030b4107022541d1500c1c8003c83d514145042d007007400304001540d82c0ca6160350080c0040b08040805ca10b4259007a004500301c0004503100c502031020b8911143c54400c61b01c03012070070403450411a2040c00e18141e089401102c0102c103180c81d4040464031070052901082c0d0340c0d41010280302c203000c204550301c1642d50003038802c01c165144048402024240320b00c10020f0000c02880104417141c1c0032701c40180fa00b01c980b4070030300c0e1410225002d8000d0129404900c06e45400c0002c0c00c0dc105900800708001e0b10011000078010a4108000542403841e2000590050040015583d08100302681241d685070790081038041c403103403221074141c3d4841080390f40302c000c034034480840000d890080c1c240002c1922000218140444202407101603007660740b204807210311a10381348000000d0148080c0c442014102c000040800885c01c6c1319481d90000380420003450301e86aa0019000480411 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 489844451 1250 489843201 489843223
    0x1b0708160302130203060d0507060909141009050a0920010e030f030a032a030506130207050a0219030b0403020a02040507050c0a021210090602130501030b03151f0e040c090608 77
    0x3c0180c80355600320118880303012a0364000e2242c0a0380c0c81c003080c42504480b03400300742c1d0a00e00b4100400c0140121142d0100f1043c0e1b6030801d0b201c0f0a01041000d100140c101c00d51201180401007150400c940c4c0c0c41030100e0402103180b03081d1000740040500b55a0044105940200c1140240030300200c52a039941c0b81d116941060040580702c0c000341c0402c03201086070300d0311070040d204000c0280380c1607000280203203c19151940300390410022810849030034000d80301f00c10b030000042d04000601d542080300d1400b1440a913180070303404c0440000800e0303840905601c00e90194001c0e08044201c1e10401048560062821080c01030a0082c80d13114140007076000140380e0b06682d00b080113076000c00040d10301394007101030104507418241ba4400300324158001e000d08480c0079018480e015114401034068408030030045406920840a9529180c0c034105203d400101d0480c00d2415401c48400d01c841103045600a883c0b080c0c4002c0601c420481d60071000b600070044000c041007000c1c14901e519458590100d1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 489845701 1250 489844451 489844489
    0xf0402010f030b15040b0a0906032d0b060f0403051216021207030b010b090414090a08031b0406031b020a030806010c080f0d0b090906100902030a021b0708160302 71
    0x5110383c0395482d44884a04c8030303e0404e00d000e03103441c3c1ea007070803c81c0f03a442000b800300021042c0c00c00040e07480c00780c050f880d0f01c0075503043d440107280e0040c1c40724880c210320042081d0b981c64803155140c415807500001040000e6180b40440d56407425403c010303140c0080107408502012040150103061040081107522a43e4100c1d100c2c01c1d0400c0c240d450a02d00622900080d00500580000003480d22544000703102203502641e003442141c04000b812942244219882c9d0220382019140b00c00140c3c08400440c1d0020f20070840104001c1e8164206002e03130410b82051010030303030742c0c030444250110150f060146024584018000c0c02e40c070303540050540201811007814003c522050708100300200c82520340311000c0c0c0349403903121406000c403800075210240e0003074010300003180403030381205010990302d100d800803101a0100324030f045100c400a61006141104840d4203000040e0181c0030450750980a00c0c810780140f00040c14110600d0801c0d0611544c0058440c114004100588800741c0312412400d40d01 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 489846951 1250 489845701 489845711
    0x320070f080d1722020102010209040f051b1806160b0403020c0a080d0c15090605090307020a0b04210201050904140411010509130f06030c15080f0601050717160510050f0402010f03 79
    0x105c0140c3c0603000c1e1041c803660060400e11121482444c5074405442244000c0420380f800c2c941000310051441810040058020348a203001e42a05000e002000c1c5070044454a401001c10307600d9180300508142e400302c005810002c9016464030b17080e64140c001e0019200600075201d00564040e1100310300080040c03152640854100c4840440d074000c0c01e5440d002802071200340b8004060301c1c0c80e50b2000504074030408600b04003154545e5804141c60996a000b54004084000740c0c0511701103901914080341006403c000c6882151554082c0c0c0301808681c01c03044032a41480e240c01c10402e6222a0300341e04015050011400541d10a15205801c950a500004801c1d0941380004050700a98001800303000f510240094451680d910001d23a1441e969214072003910b41412894506c003058500b280010030502990001c02c0511031200c400c1806110741c20714110501c48000d01e040a111820b640c02c0d009003001100250b0603001d110b81c419241c21000340d0074601503001815020008101e6030805540d4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 489848201 1250 489846951 489846953
    0x30506040b03030403060603120f08010612091202031c0b060d1d0a0b07030501050103050103080301090515031606080a150b1602041505010e0a030320070f080d1722 72
    0x380c0e000100641015050366a00d9860381084006070a40384000c035160401004c0e40d1407814451260046003003125a07c1c880940d00e0807030b0442c2c00c0d00d4285008660b5a82e200004000a4098546010380ca5415005580c0701ca2549051078811900541d001042e54102480f03614140d5900086401030070000d5000510303034410700481c4403007042c0110700030030902c19442d1460510200410440c4a20070780c2d5002d0110741e803100011025502c0a20008181c0300d014030061040c18901d421080d070284d00110403c1c5540d10740c0c00042e141242205880065001d0110b040c028560320285140d440403001a080c8075183d183d2180042d100d08521546080300b10200d070841949241c0c038002084030b40c008005011a20042c0411050642c00c0e00c0313018042880f86142240034104a21101d00b100c0e003603280d1000c0b0311301016062810900c03540b1109414014410081040d044080c14080030301140001040c44000220014141500c468400700043c0c4610341000701c8203400d405400030120009801010380301d45 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 489849451 1250 489848201 489848209
    0x7140d060209030f150112050303060402160204111c060b090f0d08180f0405130311160b1305060c03040306150e090a060b04020a0504090c0219081801050c0d030506 72
    0xa01c801c1da0f80d040c00340781500e950b680310010f5080281e10500a4810b00c0d80d82c0c54003014140c40058100912903041400029070b0362404e07034082c4c680b102c400d9400f50a2406150300260841d09441c40c14041948007068aca481c0c10f40341820300303001241600c82001b691b0b09103201000c20b4006d003503401c0c0c031aa2181e0041c401035204e4403c1503d070190701c580785645030300f558032034038900c40c4504040781c0c00b921079030311f0b241003903c0c4ca401030b2400754043e00c165080101c41518102c80c018858112824244191640421000000102d180042c0700c40740ba20350b211040541c1103008007500d030348864070402041c060000174600110403102200e500c4200004d11030f14840140380c080040303030300410445c1361a80402000c918040317a00c4036031620440c1c040140009400420080740501854140010f8040c0405d10141744241d010046440720350046a54204410b803140304504107951088802c5080458041040b061140f0040d00004007424414242820b0004940d521480000c0e00410180c85102007011612 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 489850701 1250 489849451 489849457
    0x709080123010e0601050712020106150912020d1722050a0f090c0e090103080901030e030301060c08030604060825050904020d0b13050d02010b0a0b070503310e01050f0307140d0602 79
    0x20344660586c108c16184e2002a008010b40d210344240c440344081e0003441c1e00e2080f1030300c50550f122044052000c0856800b132190940204100301d49420158104c0c00c1070391607072405003c41c44076003100304040d64901c204048091641d9400580190200141442180d2040e0010b005490800c400010f03800501041103815048044005412400050010090041760f2005041d0800d080c1c03406d10840264407001036881c442442444001a2412202e00000d8183e800454011000800110b0015100d10180c0d04180724010a4150588001540041c1d40750f820140001000100c0b5090728629241d0007007040c08640c40790081c009090400040c080002810b24807800c2070b0400d04844901c1c2902001030b00802c0100c000511490071844002454a10070301100c0003154000041e41c00d180040c5045c0304800350055a0555015400c20031000000384108410024407d5a002072401c0d4900402c4c00040303181c5a14990181d006480c003440900b02041140704010070507a411301d0703403462504000000340 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 489851951 1250 489850701 489850703
    0x6060c010f1409010507180b070825051209011d0103090c09060f0503061b030603100906020403020f0324100e090609060c04061202210709080123010e06010507 70
    0x741c903008030301d41a00070380380c03a4610a44a84008101c680c48204d0240c60070002c20b01403912640e1640010311044000078040c2c1341c105c0c4035a1942d400d00f00d1803007a40c0b4001d0b0807881000615440000b4003010301600b00311803c0c5070403420300000d1400201b14002071040c00c1181c0318003000f00c81d400001210341d200782d002104440e00040031501c0942c5800102014184511580d8205006510042001e20b0045407681c0192600d02402c0725a1050703481083d5581c00c000d28150303145c000d01108860214131070140b80c02444c403c00005942e80c0c110301c10001c404208a8149000c0d6001840003694030b1510890003008854025162607076a568000d80103c55000d9040000b11070341030020b001e11480006490f90003010350509a030071680d10940e24920381e005a10030000042c1031905000110b28040d030050040302042500001360729240a2900c02140096904400043e07080320b08004104081c80f803498510341200460007405a004200524410103001f80d40420080170003044003a8003d000b121720311 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 489853201 1250 489851951 489851981
    0x1205070c0b0a021f06120f03170a141303051b01021e040305070b03040510180f1a1005060405010e0d0501150e01050613090509010605031b01030e01021206060c01 71
    0x82c0b2241c10009480d544203d0440c1050030074035000750110302850244a05a403000581000202d40903140e000815060640c268188480341842040011140d604288111510240170031a41000121005102402030060425500c80c0d11a007000035401000c03103294014005049514854440f42c0d14024030698900802c661070503c4400715404c002806001280d01440596040d81d5503901a240c85102c111402805c940060208034809030540e4071001310201e801d41800d01400007551a0401c85070702d09400e41d51413070101400480011010207055110f2209481070395210701d4400420841d0096002d4036042c004e4080000c0b40f5501c1d9601400000c0e900103009000500c150111150081210b0003402e0b0001d010000120703c42c1842c00131200d04e0b041c240441090103140084800060201034909000341d500c135180042c0a41c0c0412408400801c000d1180b1a00550513001500302d030000d50b420803c1ea40144000c40c001c5a45120040e403094054aaa40e03030343c0301c007840c1c1a0042040042d2071080c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 489854451 1250 489853201 489853207
    0xc0406090f151401050318060a14101a0a02240103121b060e030702091512011103010e0402010c080c10050a09020a051521040606060c1205070c0b 64
    0x4010a190000703041d0700041d6030100b10303101c1e25080714080d41c070041c010705480100d202c03c000d0165205030011544800d01c009440c2041e40204c038003a0400a007a11030850240d103c400325120301c1210b110094004045a03040700c10b2a207420061503441404d400340034050280454407100560090010248040c0c002da01e8800c100101000440c0d240001e010507100d1040f8010540c0b10030380164180c1030030b500800b0003035004c12100e61f200c00242035150003440c0c06020600c807000c010707294031100e9400f0f072147d03211911090300818103009502d855000d00c1040c5030704180c1c12540e1401154112410342d1002d0076001e4050392540016940b00341428070080102e10001241c0d0070300d02d0041400c480b11024032209000c0354440d2945038050b0340c811240a98010301181c0e003089a468180c0501d18007048110859003400c00120200300401c1d000c0c640080c0c003180440c10002004000c1c400c8401a100c40d0400ca20b140450392500140d0745a0710803443e081c0400096410700303224101c0c000d840144418503409139 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 489855701 1250 489854451 489854459
    0xe0609181e07090506150304060903091d070305150112020906090307140102010c210902190f0509060603010609140105040f06030c03060b03190504080c010903080921040b09030c0406 80
    0x30342c8160070f1249001c590318100120709a4502100501d84520141000504685440e21940d00900040754118148103072554002000da10b0070144e5401159103001c0c120242c17a10a5001d400c0d50030042207200d4060300c007076003080c013603800002c5c8100f44150741c1001a106e59640010032241c2c03040903025585481503103800514459108042c51954100307030b0082c07110380301d0322205851154030344400c411203031039140d02e0303030110400d030383c40043c4450005102c038140c44100121188040c0e0150400500031205c074206101c80d007008407207941c0015069644a00d1985424401054501c01d40155110400f507070440000d6603100d20142c13805400340360f20700402c0e56944d140c0079000302400c102940102b8203201002680601520550707105024a140044043c107041c001100100030040040321406418480418440400d01c80c1c911543d200b41c445203424200340e8900c43c51b1040440718440c1c4105c1541010b481305500740e054508031001c118556840d0201c0e04002030500d0034601c02c0039001071800c60009 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 489856951 1250 489855701 489855703
    0x160803090a050111070c050105031f0803071a07022104031b06030f090203060a020706090b0106020105011e030f020108060409051605011d0307050108042f04060e0609181e 75
    0x1005244190004c02141c40103004400c00d50098076005803544c0202003003004154001c200655119001340141200158034201c00d68448000380c2050040354030205d40f460030400200381c84003c0014082c0c0d46050741c64103d90081d96200c06800340100710b182c00001008070064901560003039070340050484140c00ba0320300301036107080b464841c40300020f0400603150500301c668880c2c0c07101c00350050090045551000c845001a40c00544102c4070f581e034681200e40440d81e0f900445020380310390340c00403459500d0880d07107103080d40c21440b0b0701010760300e000010000502c001e07aaa512451342030910214546d40c2e00001801020300348000313402401400d030144401d01044980e003054620903200c00540601d00a41c0083c0007240700142d0781c056210070000d00803036001e061842c0e0b11520940821060143c00c441981b41e902c0300140c2900e02403406216200b180c5082d004100240c0204c9840f03005901e420000211001e8001d0001b0004c941860159000c410050000100d204807120b509500c000c4007150031 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 489858201 1250 489856951 489856963
    0x506070f051209011b030c081c180201140f1c0f020a1106090a05100b12070b0403060b061623070b030a050a151401020106030209180105010f05011416080309 69
    0x38a00182c2105aa0071403e0001d19650301c010346c250b0703201c0c2801c0495a580d00d500d41c0c003882d10003445c08542c1d136584001a07803901411014503443c0c040180d020549200262202c130b03030042005281c10050186a21841c0c03003409076031412009501420811111000d20300013022242c0c3c420540c20700005030900031540190072601c2c0107140c0d80440e98156a50001da44d19940300c400018919000700030640c8900099801c1190200f600030003484045415038070103460801941e001602650010600b0014442184191401d070001541c0b640c0c80c0060711b00303915840007440c2c070b07008002e480d29000c9105e401c4950b010b0081c849110008075100d403506d50790400015001100c101c0c0e8030f0b50600c0005600340d0039038040c4118014640c09500700d1607080001c00040224090151811076685000000169071038000140c01000b00b040005180d601c860001825103005030040d0320b80d48076517001000542da00840303c134000761b807449141ea12155040da40101680500e10040c01030304011081c0b04c0030302004202 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 489859451 1250 489858201 489858217
    0x80f07020622050306061806150415090b162405010b1b0d02071a120a0605030d08070206071d0303030f0711060403080711010b04060f0612020708040506070f0512 71
    0x145a500d29a50b5003059a281c40071110180c11200780c0400360701d62120400c1d2aa00b0a00c000c00c1502c10a0115001600c8ad03001580840900b5812a01008481c0e0700540c000d80500750b20002145008206c0030030208480301c0140007400c4e1340c058000d250004150f68500303a030600391040c0920055135210b040c0c1c1030f03035040001c2d0070400c085542400386070200000385524000c2d000b034001d0010360780b405925035588141d00a254003621000c004141e036031014420080c1c4101d100040016425080c0700034186042c3c0c225a0319401c0c461410248000c20341c0010b49107038403030110715000105102e0564484420901d43c45955014400441440b00c042115095288154010740c3c4c0c83c000c4a401c07011950b50b030701087d5400780110f035804010400c80ca21410304424024901030020501390090740226003150310540c000303e0212850042402039551090809000f0f40c060003066041c044a41c450700745074410381c800c00b44100e100244103000c102240170440039680e0003400ba91591032000e0152a01640700900e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 489860701 1250 489859451 489859507
    0x15060305060316080709021b030409050403140c100c171e06030a03050703050a091205060a0f1401140d05030d061a07082a0a0f1518080f070206 63
    0x2c045000c0802c454108422544c0b0b90005003559032801c8500402944204d003088841c61482c058074240d41000c02c001c01c01040c600b807001940f4506070400801c0c0c6001070311100d014190411214420480009181d40c00003960007000450344403902c070507112012001044e6802003103000400580606460103184c0803c00f0800c2c0b0701c51603584004040c6c4030055284000c003c1081400407102092088001e080341c0204c60070444429510b034400310f814240c2454080342c1a1323210004000190809016103074043c2210304042c4241d00c02c80380b2a0300101414000c0c1d0510f041900c000c0d211a07950034660701070b4207411600f901c5e91016810359090190000d07000d154021103010b85a41000c04089007201c0c1c4c401c1d040400700c0d0070700e40006945680c50030308046210100000004100340c200c001d0041786000c038800c0d88801d00400b0180b42c070240c1245582c074108081d5113082e1158102e45142c0104c50300050b809086a591030003103284003912030140d0480650401400306107258200b501d862441c80b5182505 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 489861951 1250 489860701 489860713
    0x60109080d02071401050a02070605091309060b0f0f030c0d0f170406030c020318130e06090a031101060e0601180e1306051003150207032106150f020304031104150603050603 76
    0x160040d00e040c483c03087d685005a101b03003402c010092040c009070141c0c0300002e00086150409540e2a0305030f50078144e040e10299a14043c0703000c0e92070000b01d05106d21605540f10001810080d00003074441c18440d40c03080c0503200170006072080005115800e040e29a00c4001c6c1c01c1c92448008407401c240d0064000e490110703240c1011001558000020b039807044406c03041c500c840031200400d100d03004600114106010b41c8402c0c45111140052203020302c545181030083c2442581c904004004c11801c21000b04142d2400d0004d010880c00340c00310590164080c203200404004451880b4860896075000c0b1041c2c900600c20b100fa040700c0e0030880740441c1e0065400b880162168200803d880d101031200034140c140290300740d03c0360381960700504219402400c284907041d031043c109a03801820303008100320199865005200c104109080c81110300380703c0c9032000c0c1c2c0701c00b04540a0341c1c1c2d04c141d001c0079014100301980090a907403140c00140d9481403d000741020941d9450026019000a880c024440d0040c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 489863201 1250 489861951 489861989
    0x15040e01020d1409060106030e120a0e0909100f1509020a020708060702071502060f1603090218010e0f010315020d060b1306090b210c07020904050d0915050a08060109080d0207 77
    0xd02401c20281010703006448801c0031840c1010450780f102c8100070a10080c018031033340643e03801d09542d11903205100a0641c14103016030791411a20403052428286140440d43c3c0061036802d1034010544003041e20060345c503000d28105a15103201540f14072410711441c01013111450b07011030700601b11110002030303003c8100c05e40810398035403908491170b42d80f5280c2c03000000d0039003802d81303482c828940481c02e00294913070403600490940210026140e100341540d0b4010005444524191a0302c00380e110007a45255055039501d042051146140078080c81e00842d410380c1e0300f0159400740000302105007203141d882c0300000000324010020703c2007901003039035100c1c0001c4400c00c100490749000440c0e85400030364400348000d100b0844000c1c1a0040002c800c0c0314080050322000004f90140740503500401000400314002041c0504682100e4404038160358040c0147e82c0180a81700000c0d01400e10075040d0b80c0d18401298050510340c02a01c00344034a070807142d8a00e0b00482e41c082030310b01031503003840940c100c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 489864451 1250 489863201 489863207
    0x90e060f07170a15080a1b180504020604090504050f070807060207060305041403070c080c0a14090612011a040e0a170c12131d15040e01020d1409060106 67
    0x421589100828084081c0b050107410ba06034103544180155000203c1c0c1e41d004051100720000c54000c21100d511841440061018000050020f2038a00045407580390801070b2040c01c0c144034610b00005103407104042401c5585d0b01080c1d5000e000d281d00200001c1c03034541032003680c0d0b00000074420b0340d6000341e64010485483c0410900152082900200380441c503000701100140380007002034519184c0004040c1b0701000a0005110242c010110b01800b175091440b141c2c1415071801d83c0522881a0b036408005140d49942401504082211303070480aa5529000c120b000b41200e40e8100e203540307030030703200b94414903498044020500203441c00c0200c1d8504c0f60300903554a0002601408800384100784070b02d440c409a000f840c3e03012440c8103a466842c119400f8582070780101c525400c1004028605102d00c03183d400600f50f9960200307201506d6401c0280002d0112648a00d281c0d00403601d4580d04940c1c0002501219902006c0110070440012a900040f01850702910041400d00480000041c0588 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 489865701 1250 489864451 489864481
    0x209011704120c0201110a050d140309070909030c0203060c03150103020f030f04051204090207141b0423090601060207230d02011e080916030c05131104090e06 70
    0x98007044200e003203020b0040c25544910340c444100d0411004510303240d070307090082c4105d50006214500a09840441c03070320140c000b03240c0620f402c0113140140100304c0c602030001107031400c0b2070b501d80000983d4141070074102c0340d400700c03000040e4040c8242c1c010300100300e9400c4000d600c04c18060319010440d040c9980114140e205100d1009087c0302d05201083c022030b102c20074036400611500485440502c041100005900a80d100b00c1980c0d60104120060124007003c6d80c030319904007005401d40044030002e080c005004a0715480c0129541c1d1074a010204080300340c008030054285d030207080b07454800981595441c0074003528005006000b000071f81d5820700201c1e10b02044c50010780307901c4c08400509100f034600c05540c05a040100185081c5c055a95a108400191169964080051414141107850103540c03c01c03000c01e0f12840d440820214000603080425103508598481c02a210415494084c0a50014613003a2075400a0700240c0c0020a0b4001e62950302d020b41070750301d550f50f81c80c04440103030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 489866951 1250 489865701 489865703
    0x815040b0d060b1807020303060f0108060904060c09170705120105010b0418141f06020c060a030b030a02100f0306050105160b04050f010c020a05060105240304061b030209011704 78
    0x79011a50100005000c2c1d002250501405410303c031040b40860381c1c84031586819680280540c00c00000d10403039003810f01002c0c2407410203017085d890320f08200d0003042040100500c050405a629401c08214a105403a101e0082c40c070442d401040381c02030704040703407124030911503980f1030124500b035801800e50600819048400b078a803014140307890620503d600000780344190140c42c0c0d0340c540e001c110a0000d0030060003558214844442108080c40450092040344c0000d015980144030040c41699007400304c888141c40740c50082203400710000868a032410000740294080342d22800700b001640d108080c0102c842d05a60f01780101e0799950019a52071080702d160082005150051034080348c0c5a2040d190014490000c82d8103105400c05440c0c00c480485003100016084560b840c01800020000180984401c80354801c040a40d07a5980c020158584911024942c2c003200003000d01c00141c5c01850384402d40c1032140d594025480c4014002e6201314440790100d05040c40c4090003c48020120303200f5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 489868201 1250 489866951 489866959
    0x71403030301171c0e030d1e0c0204060506070b040b1003020604031716080a0906110c04090c0f140114090904080f04050402160308090d020a0f0201090e070815040b 72
    0x241c1d083c450302c021065543c500140d4540714442a0034044140046204010305035942ca10404a0700d480801d801c101260005000b04603a1000102c4499101062070001c00d40d2070500c0d0344000418808140a06031560141e27030700960100314038051110030500184030340c0c400c044000713840e43c8000901c80c00e900f00c1d010194100e50148018000612106000180443c0801ea0b2030700b01145851045000751050074100c0b180c81011604400b01504204400003410b12400e04c3c07541e0b425551442031340c4200664501c0d100c0c0e504d130704c40241400840c01c40c050103843d0728130300000307120380741d944080d00e10048241c010b00040d08101101141e01c0b0384070a5801c10301b00182004001e40720f5072a00311305030b0404100c50518500c1040b0003c0c0540c1d55100030810024205140580c2015900f0042c0100318010685222500610000c48000340e0100d9400c0c152580029441c10b02d00c1e40c4c2c00100c03204c1d08a0741040362040e22240c28010426007200d40301d4812103215201c0241100c4580c140000da54007141c00c6500 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 489869451 1250 489868201 489868207
    0x60901030b0c07031e0c020a050d11040c0509060a020307030f0903030c0303111c0e010b04150303051e0c0c0a05030304080d0e1503101409160c03090905090f07140303 73
    0x3282c0e60007002071030614080d103441d0070061a5507854041c03504500e42d01c074004c04c40c1030700c00700b085041c804605802080e0441c1e1300903060300c1350340317401e180c040c4590445440780b6134400a48140c42c3c0110181c500e216806400c0c07d4a0700358a81c070295a81e40300420503004199003402003810503102d0303103004050340c0e0700d65203d5620690b02d54040d805081c403603940c04080f4030140031414800b0f102004010000d00e8442d00440c199080800190071605a008520300039418881054111130801603031030120b0ba81840c0c0140c0d1608942c22041d028a0007039400403540000080c0707815000c1002902810100080712401c0200b50f668040660380c5c4118440d480c4250400c10241114900544a0107908400a4404440b40359180c0369021290700c00c94060184054001c801e1110300c89203003280c0d40c101c4040e15546801d0a09141482800000c103a604040090021000b0201446200018001c10700b1071002d1090b4104018500e48407001e80c817841e01c1c0c600c1907107030004070700c42807100442507901c000d000380d45 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 489870701 1250 489869451 489869461
    0xa020c121018170306490b0a0b1c0602040b030c090102101e090c0e0403051b190609060b1201050105030c06120103020108060a1e0614070c05041d0a0501090605060901030b 75
    0x300f00381e24001c8680c0e0f0700c075108120701d0300d1071400700c0030b1a5446100031b0040402d04003850034480800300540000081c1c1d16180302c440c2c50380c0720350800700c0510040c01c10304140358405107400f00203803180b9080610140001700900c540c030494034000d40702d0791500741c0a0303a20541041149504407024094280300b0251038140800c0c8450480e4803100c0e05501465039009620b481d000400c0f90032500b610300310006007000074a0420f0044202000440b060603001070a81078022100e843c83c07095008070701030503e0740e5510f041030400c80203502c4054280760143c00313100010344516446000b0711003481407034003d010322a007140b21491b14038111076140d210400b5101c81d42e421500111034282d00101526000020700300d020078072210a0316488005606456a0010503050a03030003041e20144d0869001da00106201160004a10701d0042054460969002981d40d600c02071424180e100014900314602445100005108064122203802802400140415140c5d4010b000706024244000307400c0781070300340c0414 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 489871951 1250 489870701 489870739
    0x40303022a1e030a0203190204050c031003030302090a080a030f090b040f0e0a0e03121012051c09050604121e050303010b030709030605091e030a020c121018170306 72
    0xb11078628007030101c44100c122680464989460881c0ca140030310443d030401400c610305805804c0d840b949801050b811410101e140464041d0340d4000207003419000b084914858483d20a10380c001d0525000310307010030070316081c080c10b100211442d0b00001100e071403010640030f007510300721002c440e0503603000c2442c140b6080c03090300082c00180040155544030402d06110104c10005015140324031001c103551070801c05d400c01900c240940c0140101e4481840c3d0b040803a80110301ca040c3d03010a01c00c0d880480a64010032500c5c00c081d1741105900220218011402c00fa41c0d00700c415610703108619040d40d011001400900d1424a1000100070f54400c0005100036144100a503800c00f0715414441081a09c03541c0741d00c142d40c0100c0d40d200e0103501403840540b0302c3c8401c0d10602d5108103000051480c00d000c58000035218603806030f030b007801503009176003d200280303040002e0f1801c40e401c00003c01441c10701443e0a1401181c3c00300989901503041642ea44035280d400460b4050a0014a40d00046d80c5040440c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 489873201 1250 489871951 489871999
    0x30f081605090609041401090b01020a110907120f0e0f01111603050c12090f2d0109080d020609151509090a02121608070506030103020103020c0f03040303022a 70
    0x483e0b040f030400c1c0b084403400d171114082c45260590800e03061b1100c1d0304090f03c0310101c90550303105a0441d8801048030000c200700406084081c6000d40d1802010b81c1d034050260350241c0180b0040a0451900344d58032410300035030f404049075100e01010340d07640c07604501c1c0c22800d0351a41d41031f00c0b40542080004251811502d0a18800180b20781885030801a900b040c841c1056003454005502e0300c0300251041c260302d408040b06220140895101d505a017500604030720007151100103a03200d51900b01640709580c000e0307038000d004204500846610810f181c02c0251030741000d88070022188104d0b480152110001c00702d16200d1000e0450984880c1b52004c20800e61070b401030a03196484c0120241340740035032540c84c04140c080841100a22005404102c1034071542290b0b4420a10340c2c001070420302442d95100b0840341100e40900e40507171508940403001d82440c20300c0c030601d1554403002030000708068000c200b46c20401204c043c80e02c003001007000c04099500004501e95807180c070000d034000742d0007200c0244c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 489874451 1250 489873201 489873217
    0x10c090b122d010f09021309020a030f051311030624130c0810080106180504110d030c0203060a0b010c0611090a0603140c0c030f0a0c0206030a09030f081605 69
    0x11000000d10800e00140200030b21101554021007000b005204501c440d01080c0c1c02413400c4107046103440303a19608821401024001e5035405038000800b9403085100b84c01c04800c181c402030b810043d904001410300700000d00410101c0d00c00640801d0310b2810301d03003c0b541501c5400c0e01901d10940c444c500303001c6140b01102c00d005644c271042010210742d01001380c0c41060001d01d19500c440116051100610404400342c0e84110307050381c10280c0c03e05c00980e130b019404180ca40c0300980800d00c4d840d186440c0b022051204003480d0008444601c12003410342c0700d050741000500a50646445484200c08401612a003019040c082004030160200080056001c0b890383c0018966203801c108403100040e440b212198880c0b000240c0341c865808001c00c40a500366004814070b1500391906429810340c2e6200c4c0245400150340200208203078000030301030000c108240da8001e00060303480c64422806402403241d020f00341d0000364910b600315541c1d8020b254240c0140821400b01002461254048540c0c0d0f00c031080c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 489875701 1250 489874451 489874471
    0x9060305060109090e1f060b0706020708040306111804020a0e221d07080616180f03080706140906060d08040b070807021201020702060322050a03050c010c090b12 71
    0x68001540d4286102c0c50f034800c04100058681b82041e850303038050003004449120107042c034080040007105a44403c461131158042c1000d0b8450340c207401c02d855940039950015201c1814021601041c83d02e610003091403003400310100d28a085d00100740001c038041c2c0c076281030104200d5000c000e0700d4034150032205c030134000c541c44094007040e80802103003d4580c040005812407141450b4045e881c0d90034045030024184e940001d012500d040314271031403100c038520500d100b4030812808200cc51400b20340204083c100c1200b0740710303c00f0350380d1a064505500000098030501d190a2a00b0020482c1904081c09180c4550082c601a00c421080042c0010f415034100c07465001040001073343c0303900002070245c05004800c00b5848092900510044100d0b02c0c3c2c00c400142d10401c4042d00580d00c10003521303003202045400421080c619000074050040900011700280b0072020384804040d4044008c04811002000a120001c4c01d144c0076590030f003042c00399070720111050020400b221002001e09a01c035113109 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 489876951 1250 489875701 489875717
    0xf1504090f02100e030c03011a010c08041e0f05030309010905060c0328030e070b0304030509131e20070b04020a0f030c060f050306031b0411160b060f01090603050601 73
    0x150004580f1581c405000000c44d0f07201040159601d010b01c1580c2102c0340030360090050303d000c00e2143d99016102c100040c1485030901d0f0039020702c0921b00640d4080c081c07245404460700b1a007001d40030b0003501403041341d030034480601002c11281804810b8a40826040c0c684e003004d10709050801a240c2c101c0c80402d8514030080c4a0440394611100c040d00030030900e440020000c02841d00010107551030030291041d65030040e80100010340321340007244e5025402d45000381d100c2e105900010211100c4160b0201e41034185030503207064149050f804a09556109000c0100444200721a00e480311710340d407034a894010a0011001041100d0f20f1990702610080541418030340313624000300030105a40060f206001958410301c0102d420039007081c3c0e0407885062090844c07515000080e5640d40c600104041038184580c5221b0645540e0030900d96040180d1a441e15042500c01110800203288001d440704049a4089911400c1603c10a00c4085040e07407081542810a00c1c1035004e0170001e005503040103210 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 489878201 1250 489876951 489876953
    0x908060727180b04092301060f271109010c02062b06080715031e1b0e0612040b0c16080705010b12030a0e010c080a170f1504090f 57
    0x401012405030184030b841c03000c01100c424200c0c0894040300c0110f4001ca203003803410f101207601c01a0415805c9030b65018401025003640d002d9001d042180d000300281b259000780403030b03145c4085503c0b1061455100131a10004450702420b0240c4180401c001141c10080010300d0665109100c100061400038141ca441c00c0200b448107039258030200030725141c00c6072210264035a10128081c00b00280007101c0140400c5080c07451141051889000403800d0682d1003460389071521a5942da0507405a002da020031087c208a071444001401002c0700c0000520100c8a11280d4540441610205048540051000ea03641e80e16040800070141241c006c640c07007070144800c20368a002295440c184035540c01034945005280040c25076500d02c440c184100c44ca242c0002614000009032400000340f482c0c89202a07103210010b031016151054080c1c45004001840c2c80030f59001a481c8100c00c0f48014000300c20f03901d1400801c0031b0401510341c02c40e80d540e040307101821031078140c02c012521030044403c20b48111413 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 489879451 1250 489878201 489878267
    0x5030c130b0d020912030403051b12151008010e0703080f0f0d0603020915030a020f010e06040f210305090609130516081819080903150105040c09080607 67
    0x444040b803401d41d000503114040c0c0c01d1400982e103451140800860400f030541e07903080d80300c440c000302034484030088c241c400020b5034840b2000c5904c039900710141c0340c158500d00c402c00d4144408840101030907055200029142c1c905102c1c040003a81000098801c07681540d8806890390f201145001e111101480b0a49400c1c1e80e1000800d1001c024460014003a4a0742c810f02c80d5000e002824401641d0302c0c032500140d07688000c60b01f00c074402d42c111440c1c034032403400500580b110ba500e120031a400100118010600c695090000000d41c0d80900c58000c2000901c40b401581a28aa030300500059007072004140c60b04000c400380514080040115220607186a5242d084420868240d04a56940340f00f12211503003001d00141c0200041260441100c00da41d0669034408140040420802604100c12300b804401004d4446441c002400c2e902c4241d01c0c25614561700500303008280c41640f0f0182041d40d0b41d4001e202349400c881461000d00101d0742d4184042d1034045c210351100c0b140000303242c483d10042c1c2d1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 489880701 1250 489879451 489879457
    0x3040e040f05071518060806060d0b03010f0c210608150717070c140d090308090f061c0e06011212030e010c03060303020105011a030610050c0d0e0907090605030c130b 73
    0x7203070fa51203000d01105c4050030000581c40390721250510003100244211501c2d6501210001c07940ca20000c40c0100341540070038014100c07090120245071400b1000720b48560b200e0000200c50041c0c480c041800706082d904241100c441c0e2040c80034551020b40600040b07400001c3c21a40250681001c544c010802c00004150380021070708000004c100301e40803070810110040c0019542c94600040400382070408014021600368000589400004202c40240d5a1101150340d0b50b03010280145484c1c901c4030b268a040751403070250900703103281042403520004400095003030403640d40c480e9003105d122540c5c036403100b1823050801c02020140c42d1812001d400c0c10034080c0031034903a110340e400540709182d410300a085030702c180c000c1c080c4141040441542c4001003425aa00003104a0321013160342120320080d40c4034462460024154013407440c03d450702031307081081c07543c4030001910384070306542e5100e0040ba13003111a4018407000c240c081c40825a5a401a0044d04000d4078649c07580b1032943d2200c00e01c10440e0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 489881951 1250 489880701 489880739
    0x1219060503070329010501050a03020f0706060f18020f070f052118010203040f3c0e0603010b0d061109090901020306030f070b0d0209060f070302070e060303040e040f0507 75
    0xc201c0c02801900c0c10413402c196100f030511070420204c29410400020024401e1241301fa0415801003082521101c160f01150f600070392210b003c000883c1d5030101c0100c20b42d11481016003104c80100b0038030000e03140b402222241003070414542c1c502549961343c00680c40f50703000140d40f50b10a61070b00801c080081c507012640d1a1241d0303056a00d40c1070948080048180c80c82020b41150414041000030010080030740095901c41c10960355262407071b40c50302c800e1503000321801c1140d00800000645910095080c1c60690b00c5d0744190009650b45c49041c907090701c0b80000c00a400c10ac1d14801c010102d841a84140000c1c1c4000010a140c0b190301000a43d20741c5007520a081c05035400028800b60b481c0811104030400d800b84003600c0841c3c07402501071070600501041c2e0620b20340020b4203201c0d580e1a10704480700360300504013050310b0ba00380c1c0c14020743c2c440b19805001d009503c12030100e00c02e4a0004103417401c507800c1c1500c0d104a940d8981d150001d001a12604807064030440c94007043e40d40290103c2c130341d00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 489883201 1250 489881951 489881963
    0x40e07031127030c03010606021009051c0908100b01120b010504080a050102030f011a0d0213050a03050102120708160e04020c0a050d1206141207090c0c02010305090312190605030703 80
    0x10181507000c242c1025800004c19109a140c08410448950049001d00b070840141d400007d6001c554102036041a6a2915008401414013040c0e8202c81c2c00035480c1055561140c101c40e64801c40c0420300003140c107040e8150f808131b45401070001482200383c201109180042c5015402c103030f510110325180594100e82266141d4010081160203c2c00c5c4035424014881d4418100c40d62081c80d002180d103204503592081459000103000807a41103001030300380106009480e181030b0a540341031141c000d4000100c0203c0c000340f0030000c20315903842400c20034020072039951106090202c0240580381902500115a0415001d201100d40150140400802d490256000c1c10110001960080c2100080019189140d14001043c011840345039005802030109941e0154030400305103082e85041d04941c48614a50f003081e48003649140c1c405120382240e40700307072818840b40d101c2c0c2c1007041e203900618102a07442c010440001c0d44076030181d800810562004100000c04680703c0000c0b03410481242c1094410f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 489884451 1250 489883201 489883267
    0x130b030112021e180405151e06010206040507060c02040b06040f0f09051302040b22061a0726190c0b060402030708010302061b01020c1b06040e070311 66
    0xd50070300c254003411141c00b0310310800d18240c25400290110144411301401c40071424000380420804200710030100808910f9000c071442c21b9035802030800c0640580d00240c4c030306080840c40f00e500016509005640c4003005c0e1008509100301224560800542641c0c815214881a546034807031030010005071100c030202c81003250500c248989061010b61201100324505820444044580e00046040b0340c2d0440d4089172001e9000d00050170420b81c0058040400d801c0341d880003440100d540194200c482202080c84095851070f003003240d90040d01d00140550b41c0b80c1d140400c0d8418410320440d114000d004880741405903840c0c408c04224039107800d480109041c80f0454041c82909035031030354444000c0b54154554038110310014260041880000c0c0240e0020884400c81320b80981c20070704071800c50000b103440b60014000143d48171a104200c10392986241c1c0b0711403290429504941c02d8450b080201042c5442e140700c103c4c0140111702c203003200035406100f031503e180032000c41010040425204004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 489885701 1250 489884451 489884453
    0xd080a0305061008060904060f020d060302010e03030f03010e131b050112020403020d0221031206132a03140f0a0e010203280f051e01081f02130b030112 67
    0x411501c02402842c420301c01e100105900c25403100f400b0340c2c0164282c5050741c032611140713404800b810400484002ca640042aa159802003a90003802120700036039030002c00c0450302d01810b40b82c0c440c20111510905042005001d10340c08403640b03d8220705464101c4070751078070075203d100e40002020701c02c95643c98114410080e035070307203d486400c220000b08000c603e002d1660380090303441c1e0000e0200a01030780040e003030b92172135800c1c82e0300e55810007803082c050341e68801082d00a543e54480072900039104111210314084141028030408224415000c00071781d84a2039001a034100b02e02d4102d80100301500da019460380d480040c0545402100c3c10107103040c5c14140140218183c8000c1e84240c03072207030f205104203c6032000c065845204203090207800c4001240d486407010150104040820640d1b00f0301d01031104c40070300e03035554800703e0107400c020641d141d0720b411442c1d4690315041e151012109010110340d81043c0b1903401054440618098014175940d540c030000450b0f0804d9100009080e81e10113410 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 489886951 1250 489885701 489885707
    0x203190c0e07120c02150118050f13170702040c0503090d031401090c0c0f0b040b070e10110319020610050103060510080c1204112d0603150d080a 64
    0x3801504011000103a01c0c0340c11040100b1100b403030010f51918075110200584218028440032450050900d0b40c92880d40e1034601c00500111520340740c2410034034110000e11488441d04850380200d82d44d407074450000c1c0144c4c54138410800d000c0ca1208101404000440050342d80b441407070b00f441c0050321566102c1c54201c1106042039058000d98060600300010483c9041358421010b05441404800182100403030383c08680c46a03c2900003090303800c1119500040c0003031100030340d01c00c912900b600142c43d83c96580c2100c1100c0642005d80d000300800102d1a0000d000e1a1002c40d00c0504104490500000c030201c40703108108680740701701581103031042c054014410320300000504002e08044c030400e07250401282d070041891568404001d0240082010545100c0495007032030005500c483d180c0c201803c169262018440f038080c82815040b21f030000c10b12103006035140d0843c0c59841503a0744805101130021a900082c000c40003021401a540b64a58070300d13a04003e018082c10341540c481441c01c01c05 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 489888201 1250 489886951 489886973
    0x527060708090f120a0c08040305011a12070902030a180605010e01120c0b030901061a040e0f010303050d05040203160b13060207050a03030f12050406020d150510031503020319 77
    0x80b802c19040707010b107180c16a10001e0855440722045040c941d440041c08001c651003040030400034070240300054008117002c8150090700d800c130801904101250f40c0e0404011861103840c12265058104407405c2200944a5025550110348203101007550000401c0c0e80c1d040c00800b0804460752646d810050100720300c2200254094a0711007400041e0b072405440e1a0316100b03c41c030480f2400c86001001400c01803007900484000c1078206030503091203140103000001ca80060141c22242201180041d41d802141c81d203203030403241c164440c24a4841420490b002030a00140160b81500c140d15100c2655045442032100074040090202e488640450212034050079681c0a2021540001d40a11460fa07900295030100c03689800c0511015035800402e031043c00d41c941003c02480e107400100304c28408da6400602075860300200c100030b080714000e40403040c188240501500541001800030000780650301c4480345080140492001c1a56940000d20308000e40009000712011182d502d07040203400424 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 489889451 1250 489888201 489888211
    0x8160602030c0a140a170d0e0a0206030606032502101d150a380414070e030102130803120a0b030a030f120e011a0904080405040527060708 61
    0x51807400000010190f0390711408000540342c542455804a5401c0301049941001c640c00301e000032032020030000700c840a0300300c0765110120703a0408060301044070780847c210408036401015a400c6855010511107141c10041504015030101c00b030038500c11100314105410f0303c807590f00822041c1b6511240300c05447c240c80d0304441101200b04044103058003c11025584a8420704d0762840307a5030700720554043d089481c0059801020240c1c4240c109260a00c2d021031002d405a40e1007025409005110844028002c0700aa0078070385004601103506c60303c5008640d80c0014005800c0c210b2100040903004607a61103003000790b00015400340c00c4c3e0b041d641141da1082c1c84003403c00020a6010102c0d46404500c02d0083c10009100b1502d0b002c079009005080078480c54a01c1040701010340c2265034001c1480146041802c00e4980a1164900e0000000c1e03206940c4454242e007000e18103001d000260001078408442102202c214001003807a220200101c100004001c0c4218200040050700030000a01 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 489890701 1250 489889451 489889453
    0x509061318200a050f0f0408010c0807020a030909051503191718040f14070c02031c0c021c08161208011409090115062f0a0b060102010f050108160602 66
    0x2e22402400030314001e0300c2ea42d41070703030030100d54510080300e20300d101c0e00c10180c54001100e00420082142501544003001300e40260301d85101f2a00d03080b01c1aaa28030210380b000f00000c0302c424052007a003200d60013483d00008141408190042c403107000038240fa242c1903165411082c1483c054040c480002c103044030080d840705045241041c1c2c0c88601c1d9080d000c1d250761601481d101d002c11400174809521259400c441f00584c002a402c0a0800500e0b100340d8000581c07180c415020070150020140040c8030051303029889140c0100450750910031081d4002414841252800d036865006c01c5040001f04160044030001c8840018a850b029803183c41540003174017040071160051141030000c8407021b04496085400c03064554901c0050b074050100c4215401036034030700c860000750343c0d40c00c0302006100268240401450b40c001d00318503003d203102c1000352025540310304400404100070406454020340c040c40040340c030803581076410007a103000382e212038002d07880a018507001c80d44004000000d07080c944 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 489891951 1250 489890701 489890741
    0x301022b0b0105040e130605070518010525050f070f0305120a050f07021f030b01020f01200a020f0115050f03070b0d020f0c1507180501020d0509061318 67
    0x28000a043e4081c90182080344007043c2c020a00d00d0146203a0700981d203601940501151500740802007041c0c00015118044900e100320121440d0b000b1815540d4200200d12142e043c03c8510701c1c1001d642c080c1c00000d4803a1b001ea01c4140c11988010300c403520152030100030605415256242007803600d4102c180352000000c040c0100045181c1c0242204d81c0007010301c158940359096400080e002c100c0b56402c0000c69281c2d202c0408006030150869180e03684c09800340c4011281c41da9006003614900c20851141c40c44603c00300f00c0c1a1450006080041140c2c812600c449011050580c01c403103003030280302c24020510100700203903d0450904d210001064000d495080e10f40b49602c00349000b80444080c06540200701e245020030039105558003440c441040702c0c0e06d046100844040c3d40400d8401c100095481c1941c1c120503010751150404503039060b4001c04012041c00011070b0303107805c90641294014000c20480300c212321f04101400c0a010511200000321480030560000c0b68048007008c41912200 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 489893201 1250 489891951 489891971
    0x50d080907051e040c021f0501030b0f04150c020c100219110f0904060b10020601141e030a030906020f070303020c10030603020a09060905010501140702040908090301022b 75
    0x20650008030303801503e40c4410000311158003603c1c04414900581c00a291000301c04843d179000070301d49500340105e40c0d04814003d00301c1d4001e0954130b00340000f9122084d4180031030071007145081d800d5130003401404640003000c144004135058a004500000050f03104101035600d0f0b151042507075040005d64002006061034861401100c13081e1101c0150000c2c1071484855016106c1007a0354a02800080ca45c0300d0a117013034a01500240510751485024844c4480c0c0c40a006000252690694030200b59040341d400d040401c11101d043d402d01c054601c8883c00b103840389691805c00100d401c480c0b213030702c0d0a46000c4c20180002e24119103840d00001d164040301041001c41d4020a4600d201d0205942d9446d40150001094024025a03400290050b481c2c00300045da81103558019004c3d10001501031080e45d80c0c031801102c1228404450104002042040400510f0941d00059038144601e6840742021100800603003241c124280d00106d140c40c1d29115000685404030800d40301550321303400c00c001460 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 489894451 1250 489893201 489893203
    0x20f040b1e071110050c01020c0102070c050f0a09090f0f0809040b0108100e040503251514010e040629010206011a040e090118080a18080d2007080a050d0809 69
    0x10f605841d8050107240c40802e05044c882e108555207880684000d541e5a455201014000e5100403c1175480c0441c04e00003045620b003c01c181c004900e0000c1400c40d145003441d10071001000101d000b111030382e04c0c5078200c2380040c0041c2c1001d1422800b6400e4a80c07140010270520080e02d00c0400e440b410800c1100c104000c00b5220f614410540390306000480c4241c0e11883c0c143d15510a0000048041c04424080000301d42c82100150403548500011040b048582c1c18940070f440744104100580204e060044c01450501d004141d0b103c0d002c1c80010854003a1307294101c0d40c154220a4505600c5110000d1400700d580400000d8010108101103510854000143e21414001d40c0078428180c0000d00100301118000d41100710705400c40030304402440b0160fc6e01120765840b4842d420046031203803105e40d4690903000118421665814058004083d901500303c2d4030a0600042c90800c420388e124880d1030490800a4401401c031820007081484158181503140001d24982d5000300300c1420100850540 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 489895701 1250 489894451 489894473
    0x5042d02031c03020c06130c0e010f052e0809010b030a02030d05070309081606030c0503060d1118010306140c1606090309051e040e010905070b0904020f040b1e07 71
    0x1000c52262001640b0450304070082e00c0b855034149070501c522414004a840c0010781540c21034425800c9035201c0d0350750703540c40c4288882440b420000c8000d01800300410300381248014050070341c1d80412010a418001c000710120741807984140000c0d01c020400203030303031000d114000881000300c0003480c1c0c030069607000940c0d6001005e10f100810078042949803c060140b88160041c01e00a002c0c0c44203c2204502904a68014810040081c0c01c1102911056014608a900511024106800300c03840e03601d814003104804000c8a400084096240840c1907036240013038069841900c000c2680344c2c950144107441c1001410700b0000300700400c501001656926504400c095102c01d02190016050805841c5030742c5960190350060101034144100200c0720750140e061080487c1c08000486030744402c42e00702c5a0080c0002c1140d17000200900c4120454009080241d0000b000540381c000341d1810a43c282e002a84881140e09000c0b95140360200741d295075804041e41000120700342422900d41409140e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 489896951 1250 489895701 489895723
    0x1090807150b1c15090809010f0531080304051e04090f0b0601080f091506060403050f0d0201200a030e0f06010f1d1b0a09050405042d0203 61
    0x5000a844890044150010511640014500c198040c1c08100c0c600010b101c100c8119035012124030000c0420420344240c010182d0007154050420780d42d48015105207070403260007001c1c007505100e001034060032f00b2400015051a11101c0d46409801d030701603280c0d0102a002000c4640051206000d00e03160900c4410340d800e02c0b01541ca440c2c111400200e001001c0341000035001008203540d403010320104030b4034640100c00a070f8030a0000ea4070b034041a040b064084e07647c40403076080140e0346100d09006400894200d0001802c4030720b0300e55280d4515103031a084800450841e0032040140544a4080c07107800828103c04400d100c110a224607043d100c0e01c10803101c4000d06644610011121100700305083d01c0509500072202196159034501ca24102c0c42c0c880c2865034864085100011141083c2e003901803c3c112400c0320710640c0281e020800d60300030f20441002c2110741c00001415070366070300413180210301445c01c550307062030240c2035611f14070314001c0301c2c402002100c00841d00507200003900000c44 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 489898201 1250 489896951 489896963
    0x30311030c03160c0503060705070b060d0b0606070201140712090b1c0519060b1905130302360604050604090c0e1e0a020a030c0207080a020f01050706020a0c02011101090807 76
    0x42c52031134001c00d001d02e950091500740c031036201005882500440104422070182d2900c0745d1656400c0c040005170040440c3c01807004510001107a01c03428414050f014032481410038800d07500403100306c0c07000d40d00b0002050ba40591103400e10b101146e000b000440151000010f00c9151503010a5016003011004079008007069591340001d010f98891189588440c0314140c05000d22a60380c610007a154000303143c20f40d100b07a501107003480010702600440d40700c551541d001c0b01d40c0500d540c08100004220903044243e51480d80039100003080048240031924200020b1103031a0b06103002031004803200107050602039440c1100758004a514090030408403844403044124941e03601010803d06802c0007500540c8c0c410480030b100c03010800c0d401410080c61995410000c200e40600d00b00d81d240d90510808119400074507101000d428040340c9004010310604105140c000507983e90000c0740e1059a154000503143c044480071503900029090740441101c00a000c5010951580d1030303203102c3d800b401406 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 489899451 1250 489898201 489898237
    0x280804080706060503010e0c0a09020a080402100507080a030501081612061a45040305181f020d0810140a0b0c150a0513140a020a0f030311030c03 64
    0x70060143c104402521016009104090381845195658602004114410f54003010041100c0041e8030031740704000b8940d075560159854603020b0060101402c24501c0030000c04202100100d41c4c400000d028040d59543c0002d8198501040d003420610b0300f0b0700300248980010000c0203404000c03900b8440c0c040d0481d400107200d0f86039909040340425039469540e045501c05c1c40385441e4002c081c84400f17210f200c01c4103050104130740c5141841c034032403607402000e00c214156022402092181015040c0b038144040b0031040c074a04d80000409614881404031102c0c170b503640203081c0d01a41400482c2003d006404d0036800c2c0d003410001c070203216419018005841407400240c1c4025950040c0550040c211a011165a20308007231140d521881510b02c41d034400c06e211004201000514410b291007403c07458503045019056650b22110028030b00d92a0b0303c1440741d280d640000d0b03039070012030000030451170300b09001a62541c5001740401d0902154000b5a40062040d40701071600031048900c0400c000d048081 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 489900701 1250 489899451 489899453
    0x17030601030e0d030905190203031c020708070f050d1404050f01021c05040f06050909061c0b0906092a104d0d030e0f122808040807 58
    0x102451480c0c810b0610841440410311a0958042c880d454000e20681d0103a4400b06051801d05652040081d0107500c2000503114032540380d034012032414242e810240c9402d140d6240c1c0046a04500429281c8201b202e0b81c00040241c10400b1000c80c0c9031034103100e1008002000003034054051307449411301986c0b07510f420f014960710038060880884510300850700100030209008000742c20500075100590141200414914021070940300d04d4640207150420039580c541c01e101d8024580c0824201c9000c40501202c0000c0b124122284500c5010b03000300820301d86045941e1030145140c42e4030291002040311140800b0040c0d40c00c4a00107802c0d44c8000c12140d120100304c5160a2108000c845001c0d1074030700441c600800341d801e04850010b1407542110b80c0c098050000f03440200c2501284030360095181d000014000c0d0840360240030b090302a01e00d041e404954250030180e1900c0030607800b0b00d0010b150b400000010007024801080e01c101c540c03031004040c4003c0c081032005031000d00901c01c0481d8240c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 489901951 1250 489900701 489900707
    0x1080c09130216031407081c0b030a1a0709050901150c05060103030f0e060307080a090303150905270607030504020f0a0e04050f010c0e13090b010b0c0706030917030601 74
    0x12003034000e03a004540c1c0700003c00e82c0018003030b90490200d0002d00350712a50200f04e010072050350080703070b0048182450302c0a0665a500b5620030303240840d200a40b54222684542d60500c0782c1038986000f94804604c00d50b60384d049000c500e500410072018400308000030311064940c400701c03d05444c10000b41c903401a510300d030150303443c640c1002c00406520441d8004000c0640c03141e0984010b04860b00d030481e4a030300c05010003819010864000000070300080000700c00c484541c002070000d80c0039081c0050300e03010b2500c41704584480c3c0e801c124500c1d038880e0103010668070f9a0580c0305600810403408000c01d103502e00300c50f40320721018210008043d200d401040642d690144450401e01c8000c1c4211041c13640c031510000400002c5805469034010b0301c2050b01d482d034040c002c000600c1c04981e00c40d00c3c0d4076a04810040c403100403040c030031003059440c4951000104080b00090181130648005038444015200c1070b40f510619801c66810103040545000001e110000705d090030390301030984a81c40b85d80d020012 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 489903201 1250 489901951 489901969
    0x3050a0b03033a05010f030b06030a03050a1b0203161403070608040f031e09030b070c020307180f05070c1712071407020a15110c060313050304170d03061401080c09 72
    0x841620f40c5071100018007000c000c3e038114112446a6030400b9a0b5550340c0815407200c904075400390200c0c0e0304002841c0f005126503100707903002c0c25090b40c0d003408000d144c021038900440d0b020422404545201c040c0700d09084130708104d81207581100100f841504048000708403401c0034000400001c002ca01c0003041602910100420344403070004820544400701c0d0007080701d0405e00c010346501e00700c5400b00c3c0300340b4411110720040c0c94000d0300400500e03203484194075955040151550b025a912940c0c5411403200d4011607004580965426890b00b800d41850602ca00084254100701c800c02c00000d01d072144400c1c0c059600a6060800a0800c22440000019441740e8a4007e40c4a41c4074400411201102621901500f10569803042006031260040d80c0d1034200076082d55100c0800d00004a6050360008050b0815126030b0036641407e90710104a8805651901410b4094020740702242c02a540b512482e0014289546030700303103001142001a104901c0501180c4060f41d000070486581e444441d01e03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 489904451 1250 489903201 489903307
    0x30306291b1e01050103061d0601030305030a020c07090c0e090405100906021b0115090b0603040f05010b1008060103140601050a0c031112070210020102090105030a020d091203050a0b0303 82
    0x2501800101442c0794000c100902040714205d2800790310546140500d41111800e00c241ca00605269007151010380f09500f0091644d080d0640030030007500307001d50922040000348141c0300e004c41c00820440000e025081c00b4484140240e86a200301300c04150000745c800d520320040280000c81c494075041250191084c5010b01d000c051400e09903503000c410540c003440e103001100c030ba0500040d0b1201100b2064036511030785182d10090a101150111790030780d0034550801d1003900001110200b51717001c00c40281002245401180b8410104100c1e03507054040e25502e20064142000145054800a0014020345008504101c00140340c1d40c20103005488110108400804480c51521a6403005000d5841a00202d00401c2d0007058100c2250050091b03418600c4140c403031904554409120f00c0083d084014406038041d211100d0001080480b180035442101694003c129843d062900c502991440d640650280e8030130441c1da4504508c002a02d004000c0402c00c1c3c101f01000105500030030400111 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 489905701 1250 489904451 489904483
    0x3090f020a061d041a090a020c070608010312032007031710030606080708070324020a030c110a12140931060b0f07031209030306291b 59
    0x4000c80d4903a0040014428030304419540000070450303c00b800252814103840c0d01220b0100840c0208a140040c121a03022401442c0142003442496046141c1601c2da400310b000b01324024014801d02c42070000386003240c00c181c01c0c10711401059501607206803500c1c84450b1411440450810100751082c10032141003070301818010364600300340245240c21001440100c4505150510008030720341c01065a1040710a81030281c00614503503242d002c0c01c2d888050900300d404454110b4400a50340d42d1020b031200c0850b50f0340000705142c0451000c1c00c2d0401400e00002c240d0f1194900f200010605103510000c4442442c0c2a007041902d0081d42c245401400c00700c0e40d00c030b40038000c40203a150940e06003858a440b00d810f0607041000346c44505080710041e00955566500c10048000349400030402007480d04d100c1d103485000e0480c140018800c40c0c007090011400207403140c0041006401c0842a488030f0303010322a41c05103154000c200c2542c3c03071007480041502d0740a84c400c06941c00d002404441c0c42000002 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 489906951 1250 489905701 489905719
    0x5010e13030c020a09060617090c101b0b07090506070209040201200703050312071d0f121504050105011403100903172d16080901021e04050f03010203070f03090f02 72
    0x118001c0240c03101e0b010747c00002e0f0b01580c3c640041c0d0000d40401e401282d02501901103212120280725542005056580511141c034181c403020300c03070742140c10005600494507403000b4140420300810901701a40a036208110600524001d60b036034524850300036509080220012103217003d8864500d0201c400c0521030b01482c60300109000c8040010162410f0841d180491907a440314213451180c0106004525450340b807001c0c03d85420194002d5440c104010082d090610302c2000701c1d49003a10910785481000728003c1400b0402c00b00f401520f01501c2d18083d24070b207420038070022030342d15143c940e0b80c50240c1d030719540741205241c05410740c080d1079001c4510b8801a850701c1e048039154860b0101400d450401804c0412988045800c800c43c045c103109010701e2040668a4404c0310710680c0a0205034041d582004414499901110302d200804800098282c4492400302084144078403000054000c0e401041080001c0c0d034440e42e00d40a140e454200003980900d541001060141c1c04480250030803081 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 489908201 1250 489906951 489906959
    0xa0b0a080d0305010e06091b0903012c07271503080708071208060906040f0e06071809020304020f060304050a050115050405090d0801060f0c020402070311060a05010e13030c020a 78
    0x5410480c1070741c540700300003805512101b0a01c0700d000d404071400d41155180c14800b1590814860060180c185d00600105041b108a800001407050a140d000c9940042c2d900044891b4010b0180500401c400000c01c403e081041403004120026601e04a403042d699249412081d0407030350f8001e01645d00040040e03264100d5244c101500c1d40121015551000003d145c010603c1c0315550b050701ca402c01403e07c90050f11040b0034840a0900d00c40c070301040d16216144070311010403c2040a01c9000b00381e8420080340c0411f0710350a10702140e90080100710380104100005a180d20a000400940559203582d0340c0c0c3d12070602600740542603c00034802d509041405000c0c440960900050741c1c8220350030003050700c890240c182c0d0341851035001c801052400300100113090150104200d880f45904000d403481d8219070001c4c007264803000c0120003260400f0391500c55103400b00402a802080da903010401e07541030500d0584440001050208109144803008041600c01c83d511394880d40c0c003604c801510307912 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 489909451 1250 489908201 489908207
    0x5070602030103120810081c0203120f0601031103090c0d0201020a08210112030e040218060d0603031b1703040f0f1a0604090c0512120d0b0306060402070b0a0b0a080d 73
    0x20a1842000007441400402da0318084244000304603407c14004199500318050314008500f2540040002d40c0414080c1021105801e90814400c403000c5883c46864601b103030000d01103a1054410404500041c801c02001c81000142c4411120007110311803074007521840100e14100a91800400112010540d10200524040d2401c11242003584400c402c0ea218802d5400a4007400005400103044444c3c0b039606041642c000d000b071050a07820728034072010000110f81c65600803c1c0203c4155900c01d070810a1540c4407103108581d003410741c0304100030390301511403002a21000d4001100c02074000041402c100098600c1544154044860351106483d41007101e0f00c01c070580407024174004060b001440324a02482000c6400d03600c0795290381131508203024008401049100d006152040e2080c0f1264446400050591a14507001c00315a22003a841414100340002d00050300880c018808600020f0300707909510307400b5250110001d816400d080001e400203500d5031054017a8050b003030900d0340d4154 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 489910701 1250 489909451 489909473
    0x608150a0b0103050c07020d1104020408240f010b031918020a092003040204020702030a12030b010507080a0e0d0212010c09120807030804052802090a060b031605070602030103 77
    0x30504410458003429100541c140c0302e04881c0303004015000c0200d04018a420f90160440b1030144001050040e5401d0116080f46e200350080c4000d03030f001e46005035100da45c3c11400d00d0381d0500b105070b258203414501205c202c5a00103000b040d10a05012000415840e81c1d90310481d0044840e04042c03040303280705c90210560500312101a4019050440081607142031401001b9513803545000f2644901d40b000f00c502c42c01c0d00b002c1c01c200c3c3d00540802c49240566020401c480d4220702075170070503022903044000981100c4042d80c107141032000a00502001c81c001c0e03001d403540010541040710a100e82c0744005054a40402c030000d520180180d0090700350001540000e48054170358584104503500ea10f40c0d0108549169001052418200305601c0041d1040402c0d84d0824811802c40306c410748110b15001030424a011061000c00842d640380c82546803e48030315412030f8001e0720810400741401e451506d0780c44000c02c03c410210820080212103449401141e2445070040811500c0b542c4034903042c45418 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 489911951 1250 489910701 489910711
    0xf03020c12030103031808100911091e070e03060414160f061b0203030409111b01020a0e0904030f0315051908010b060f0a1404080115180204060206041104060815 71
    0xc0c00460460391340d400201b040d182510b80c0400206004005201080081e1441a0044500d10008a0700d0f140684030740c41a03034002c0d100c12011410742450849081400503006200c0c1003008401c000c82c43e003070b8401103810750700700e5040203102e0300802000c40c1d01da251240d140520468040805000103080c80401c0c085416034081d9610031800f192001e10140c003070030124001075415042040100320b04e074515800600305811440c00541894448003d0b03054825654450300d0040c3d400103102e11031998083e40c41c2d0044a0308444060090a023900c0003004daa0360030042030141030399a07407140d04c0800d0301441c800013080020843c20034681414840c1c4448101740c0b040b03260560900006110601d0240152140d026401c1809800c000410000300d03841c3d07a01e00d0841c01301e200d0401000c0b8602e0340070b0044c0c5841c3c001c2001220550380c07030101401c0000850101c40280d00384103000520240e03030302190141e0050780100d8045440f0001038009001044203501500c1c01d0b1284403c2e41c00642090340d0320b01d20031 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 489913201 1250 489911951 489911957
    0x30a0305060901060c0c0510030e0f01023f0c040506070311070803030714090112060e0f060a050d030e03010e0304060903140604170703020c10021e0a0f030f03020c1203010303 77
    0x1070b03640c031103042c0c0c0c111a03e4940141241c4500f1b9003400786007012070603440105c3c0285408548010544981e500f41040c41809242da40d400050030210405a4404109002e00201d900030001c130310000f00c44903da0452501d000c0c032060180101c1c0b4400100b00541c1c0c007802c0001c1c0020303540e00342450003802900d00428404c030180125840051190004070a582c42024161201840c5000da0020003d403940300944441c1030008401d840c0304031210f0b603c102400742405800c1d1b82228100a42c0c10511290000c110610074850b0380303030a2146450b50070a04c82000c1e85030800a1002d20900006800752808901150191102003400508241c0c401d20802c200e038043c20300380750310310b041030041511140200c038054601c0d600020f41c1c5440d038100e040213144550092056425800c40000043c105848440680700140d100c6065441c01d5105800034661040c0700b60024000c521460355040d41c401d00c1040b0203024003d65200341542203000e0340455403038447c0386003030310981e5480e407004480d590804c3c0415000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 489914451 1250 489913201 489913219
    0x306020d06051305040209180a0812190605130b0105070b130218150904110a0b04080c03010902030a080318011812020129041d061e0c041a0c030a030506 67
    0x41c00406120304d60003240c01800c400d00941c1d030501401082c41c01401540c1d80e5114038080100030441c103502030308a224a08203000754508003d802e5240f136107080b03540c0b40700e03051400804000701c0e5200503150b9142d0822000c04034640039840e0040e0b40b00e002d072503000341c8080c254004210b450a011410b01286e030703100321243e0045880400c00c2d070b4103125045864400d000e1001c00c07200c1d01840e04026941c0e01910404d2034031000d202c1c0c440810300c0f2025030f5005851028000c602442090018451483c1040c419802042031940c0e540009035034582d8400c000d8200100000441d1610783d080e0029525294403a00901c113180c44551102480da0a10b101610802d0380640e100135640d106000e60480505d074041905c86000005030408141803010414690160360340e0b176944003200e02103a4000101e55610080c044a241140c2b485451b50044525245003006500401000c400e03a082a00c0580391041d50380e00310381c0500c4410000c1da101e540302d890418400420f190280e523605402c110b11130003041c1c621a007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 489915701 1250 489914451 489914479
    0x60a0605091605091c14070504060501020d0207170304050316050102060708190e250f060906050307030506060403080c06070e040615050d0204050d051507050a0f180306020d0605 78
    0x28041d01d0b1202c0100041c07040203821041d14001c841c054018080c040c0f501681ca0081e43d0b06014a4a000d24500b001d40004008010500c1d26100f01001482c00780083c0a10305c140820094076040030780220705029180300801400d00d907080090740c3c003510018044071400e02040d41030203281e2440b441014018820f202c00109898494000980204c0310402c204410b083c00304034002c0580590311040e1000c0c031600e110f4544c100c1c068a07c0254204543e00240c81080c10f0604441200c401c03500484107001d00107004100d540d40c024102e0f0f0f8800c0e80d034900001c590320303120002212441907a101031720190010659a400071004500c01d0301403403040e00c80c070221340442c40a010551f080e44c03142e0070081c0c481a4940090705d00a4004000040354084c006242c1601c580010790b203541092000d40f016402514941c0c0107001d5082101d4010a4900b003140c14414260750091800d50344a100100308441d52804004c44000b8401ea5801345505c48800d41d19142c44103240c1d0011f2019114403445a01554081c503 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 489916951 1250 489915701 489915721
    0x6090609010c09061b03030b06160b090307050309190b1c051b0406180807080a0b09011406010e04020d06091a0d020d02040b1203030103030503150906010f031a03060a060509 76
    0xf03001c5078001d80701e81c818071041c00d40048003005865400e030241500d07a50004070302d40e03400303009000c0e1080c00100281d0b0074840d81044240850000e00806442e40b0400400002c60000420745848680c22078020481d603080c0080d2045030140340d0b005400c146d401103138100c08000c6a030800020b4081c180410015075958504a00d9240780e850941104003904000034803406103d402c1d98014200078503400850540e841141c64501a07143d400410785030010000c400800060060391504100c00000234801c0007170300c81071b14036500b8000d84403e05222844085c41d0250319690140c0360307801003400042000d41d544039403401c06441c9990303202c00c41141c1c0245001e41c51400e6044100c130160082d00c1a100c0680071350900004043e800191940504440310004408004000850281d4840d94402d512800c02aa18000f80039846032103a00c250443c504005060f40e1021b8248901e0a107482c020500c0008110350100d03110141001c250540101e00403c00e13140c40b550020300403503030f0584540850381c0d0303024010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 489918201 1250 489916951 489916967
    0x50f010f170c04180e1203040809010f0c020d210c0804180603020901030524010b031603020d1109120609030a111504061409060c1b0c0306090609010c 66
    0x50400308540c0354800070048200e0300c100c0d9202101000c11032a007070311500d41c1e00c864501d6034807081e0001e45401e42c54115103000d015001e1989603020b0420301350309065072212513034014040c4440c1041800c800422583d0320442d4030101c000d8002c0c0405a144800c3d0400b20009012090300d02c44c000008150407480300d219201d003c0c01590015005800e050801110500403002c0c4408c0d0003070181c5440011016a884034545402584148001c005072a2403901d14a400114012060849501140100140c08a40f0110380d401400368064006017140454260028010400c001c05e205181c00c0b04e0410080061009145a407421280250070000890700700c0e903621001c40380042c06070002d00550b9013503130146805a08800149098801c65002210500c803811001c0b0b0b410f0f20300720b407107074070450741d11101601954219940301c019181c036182c0300d006200580315103007076070080e0038840030b1044000005201e0807802e14070007016500d09040c17905605980d40d0055a051080c2c0d40380021040801d406810a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 489919451 1250 489918201 489918227
    0x140f1e09151801110a1101060608040308191e11031303052107030204031104090206031807090f0b01080a0e06010302060d0f0e030a1107030f060b0d0b0c04050f01 71
    0x2400400300a008202807001d01800d100703000440440601d11122080c0201101d103000d14007420740b14120b140004000c203107102070070304540c1d240800602c80c1aa004070281ea00035014100f42c7c00d162145101c80c0c0d012000b0220995140d49031800b09042d90f41400030741f04400d60b0010007400001d403c103010401610040d244203403d0580d2290f00c0002900582c058a84600b01e4128040c5008005000341c4000004440040001b58005802c1c0108484105504082c00e006e840402110145602099052001401c0c40726070003070200450107070310340810450010b4543c909080c0407002c4800081c13800762130f884503004c3c0031891200004600000601c12003004248040042c100c030b910710380a200c1281d0001c0c0e610060036880e40d6400101001c1405480aa01c3c9401c0045a64a110040c002c000e0a298900d082d280d800805003000401c0f8000380300c01351190844400035420814900142e07000145c6d030401480c1c00300707020800601801910141044440503951030707050324002d500440344a880165 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 489920701 1250 489919451 489919453
    0x40b0103060e01260303010617071107090b06040302030f0a060e1603020d03030912020f01240b18090103030306030c050111060a051b0d0501091107050a030f03140f1e09 74
    0x4118206942c400025881e2800c3c00c038010004c2d40c2c1d05114210b0340243c1000010443d03a0002540c020003280400741d0100e507074580b1098070404012400d45844240c80b40c07400c45da40b9069802e82c1707903030341004960041d03a004007162540c20703201000039120458103c0507900540380070b4651946840204002505418803540707a98001c0c116400c01c03102c2c00394032401f0b03010180c1d5041620b0000701e11414521000d1003a80003442046c4001e1030f140d007940e1818810354060700301108121841740a0b95050b04c1528082e503085602e890b14034060455151a25142a0740721101c40000400d268060b070054068034000d0b01101080da4607000191a942c06480c02c581090b07200038000360182000d980413503085040000b4003181d00d020340c205060150040803030b404100344d503440104503208280c8540095890590066400d0081030703110782c0d80b0f80d242070501409010b03507420b84404040c4280d2000c1944a94020081c0090a28246000e208901101e00110030844c00b2031a0406034100e65489108580c2a0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 489921951 1250 489920701 489920729
    0xc21150609011401050a0f170f1f05011d04020d021c0e03030c04171005010602010b09060a081203250905180103020f0d11060a08060109060801032613030809040b010306 74
    0x410204c400c00f40e507d00100030086955602030410040d40032440c080d8461102491a609103000700312202c179a00a108009156080010426a60800d9141d482641e4001600d085500d400c0d01080103481080400d012440c80040e20940a960503098012200300500c400c100c0c40d6500d0380d4450f0759100546400b0020802070000304041041d40c00c0c801030a40e1484142c0e078594540c201c418056800a07000340000d03075112100344502e03081c0358103030660000044a10000d01481d1a074619101c146c013100950480100000141c1410708500c1c6140c4811640465440325021010006001c5400b80c080d8038415214015264036030300c840d03c5c285068030b40081c108034036072078084100f2200c00c2007904201c40490f0340003001002551006d014140540040e102e9610500e0404001050303002d503030b0400814402c00d00010f00110b8a007403001418008120f48210083c0300021842035640203802d1900e03100804000044104500302c4003070011345005407414001c1e00103240040d8280ca106e0b001c0c18418034060 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 489923201 1250 489921951 489921967
    0x801020325030f051005011407020a14031c0e0901092009031002070b0609060922111f03181a06150c01050601080c070201020c2115060901140105 64
    0x1d004400780a1031941400144100401008000e46408890310044c50b018110104480e503008600c1061a401c1c00c2c803030f18070b030100d1a070014088810794060509a0752224120403103070b403010000c0700300c0710010011101c3c200918810082410f8000c0c40c41c1c030302880015000007203500c030b940501c0c0c0041c1849030f81401c00703a00c1c2c1d00011000b0b40182804980c1803240c1a07110a2071075044c0b0051440728003c81814a03c0d1800c1810f0001c511400b07801079020304101d00401824485004203104524030007515068200c525007403540900c10300d18519507100042c449281d140b0111f00d2681100c1c600161030511050001c210748010541e0603040240c0300400009201951100d80c403d0154003c07801171051660409007001030190313030415280d444181e90b41e001030004070340c0c0151056a01402c4146158039101690b40001e4840e0841d0503c24000c40c407088010141c80c645200c0078111030300c8642102c8214090b8070403410014401c1c0c420b18002c009100000c03c030040590f07084158454103860341c40c84d0ac4d002c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 489924451 1250 489923201 489923251
    0x40b0d0f02121029060c0303070c060b04060801090308010f0501020c041e0e07030501060812071101110d02031e0c0307030513120b071b1e0201021603061508010203 72
    0x1003040b900601600b89900c200280710303c140451801c2565039012130000341c1d800d204000340380308243c2d03120359424455414405000011039038003c040340341c0040c56030ba580c40e0110141604602d451317441400d0510205458005500c01c10019000742e803140c103142da81d500c507400c06a01c280101d90049c0c20280e080115801e25803c20580445220011034480e603400c0c2180e401ca0b942e0041d901180d401c415000c00c1408024014040640f160034003070800030b08190700d81401d62158507002004160782080405840e030180c0c101e500c003003030140192000c0380f1fa0458003d4807680030b01e0038941103150389540d1841e04c0c01248182c80508e0842c8008519022058a0564003a0440076251026014540c00032900810840070390104510032504800c0f181000c0c140504080f811a0b03501080804100040b40410220780c039a5505e5807010070705045521032400102e060a90709000107040e128120000010402c540c1c1c0a0310030700d035607650502211038071001098242c3c070003030740c0841460905544005001344 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 489925701 1250 489924451 489924469
    0x1b021005160506130b0108010e0304060c080d090819030612030503040f0c080304090501060305240a0e0c2104030824180603011b050316091a09040b0d0f02 68
    0x25034060120000600b40da81a2074a4000c4078004030310700185071a88100081e64013024094403440c00244501e100410381c2076501c0c015849003000b0810b10000c101c0c103000e1403100302c50204010480a0005d01003030300f41012240d1007180d201c041e040920691044046c0300f4425507090307a41c40404008000c800707803022a15500003900a80d01203100e80d039042d00094400c0b04040c002c000640140d038a9900e055041d00031101c2c140d20040c1494100f6003001002c0181c2468444001000c070a00203622441e1808126810302036000107514001036010300c03c42000c000c3c0a0034140996100315542800039544100741004240c4005011840e0000414030002180505c0558000544501d503a9540b00d6000216404034181220800d46010b01c10b10a0b141820700981756201a94880000c0440b0081c00040052200801155400d0040212040294420104900140310480d64104c0d04040400045426444098072a10640c500b02211003541001c0304034030595900311029107598034036a006e1040d40c00d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 489926951 1250 489925701 489925717
    0x16120c200604080607030504021e0f040c090519080606030c150904110d050907140d081c060e07020c01090f0506070212100911060304080406110a0c090902011b021005 73
    0x81c034280400b044000e800c1148620a4910380e9000ca903c1c00d00340180000d0103a020b40104c59144900c0d04d03148552504200c40007160400d0b640060342600034082140d9102032a00070642c89040d05503032550403440c04400c0700c2038032480300070380d0b006031144800c1642d100c407070300d40240c3c200150207800d4011000410107000080b0000d400400c0308042e007420401e281d0b201c46803401900e983c0317605100d0203010410034007000e4207500f4048a41100c001300000c040c40307111400240340700c4c00002c0111002a40303c4209006403484402441440d0703e0716050742c1f560b80c00701c1f541c03001880303045030303408003903110302e0019048503541c021481c001070526090180b03983c01180d00f83c1e00b0a410182c1e1620001703040120b6a100c010040001800300c00f20b280c0302c128a8044d04a05105110500a12011910004c1264102c90884c100b85a60202c417081706400c0000c888030152451a4071180001d001003240c008407104c80c400d0b80e500403c1340400e006110748090160001e50400e5000102c000101c0c00790300105180 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 489928057 1106 489926951 489926959
    0xc0212030a092901031202010c090504090521030114181501020f011a0111010926040504060801060e06030706080c0a0c0816120c20 58
    0x9010140054100c00d03680c50110b000c111011480c0c0050b200240141042a04a014080c0401c6000d2100340e600e103000042a00b1400d1040c46050b0441e031584c0c60303030040d4030304240c1800300420141c8000c60f52413159912525624512039400361340442900d00b096034135810000840701d888401c9919a008500e14000c1280c210900f10382d00c0e074004040f00b0300307000d544100c2004074500403032014514420f518040c1024031a02001403203180c1d00a0a880c0c080303020072141d9801b42200c807860f00140c034845d6411607452035007041203d400f4042e5032002c40541481c0c1c0700e400103402c4070368591200d50140e640d0903081112000c1704102c507a21007000c902810070580b070706d680503242c610300902ea08121100040c000015502500d0f00c80f0b080ba4200c0340740d41d100c47c002e1030200c64115805106850f42d10407519034001c003c1c8902055035140b58040d4003020005910303040f001280001d0030308250b00c = true := by decide +kernel

theorem cover : BRFrame.Cov 489748201 489928057 := by
  have h0 := BRFrame.cov_init 489748201
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489748201 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 489748201 ≤ n) (h2 : n < 489928057) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
