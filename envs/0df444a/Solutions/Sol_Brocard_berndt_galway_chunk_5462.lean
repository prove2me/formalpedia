-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5462
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:56:21.444858+00:00
-- url     : https://prove2.me/submissions/cac8cec2-f95c-464c-9a9f-c652564f9678

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 982194244 ≤ n < 982374100 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 982195494 1250 982194244 982194247
    0xf080304090c050f070507090b01021b0907030f050a090c08070e06130207060e011d0a050717070b0a3f0b060d180b060108060d03080606070f03020f1203130b060303 72
    0x2800068006011803400b410040c5402c84c18480030b02308403201a041a41594404184810400080c1051002041e01292241c2c16a40c0e607910941c040c160440d0211140c5182404028030000d8a81c0407008403401b03040c182110030344415941d40d54200501640840001c00c5000651620305510240c10800d4440c4025041c04a550f40300019500640030766078059440388280c0380b03a018042204403c02c0880c070024112145161038030b58460a1038000c0862a042442001c83d0001c3c040007000024246600340c41e941e5a40c03400001c1a0001400703a02c0f844400380000160030003d07007180046031280d0400000214002940c1e4a8020310499117400d4001d041480700b0008881c140c4035040300070840d02490440c41342146030400c0e28400c024500ca050183d20010300c0001d88400280c80051541814101010381382c01340000c201e030160a4008040c05034510b42201015402305011905c1581d05c0f00b01d5880c64411b0a801e40790740400c6485010702c6243c0c2c007550380130810019219030000390241c2900d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 982196744 1250 982195494 982195507
    0x2102031e04030c03030503040308160e0114070b041a090c090705090d02030601060e090109020304210905151b0639031302030d050a0806220c180f080304090c05 70
    0x208003c562940c000e5010441c040104420315400401c1c0076404110307141d050030b00812450340507140a15102c1003904100e100403501100240000458036441d0700b08040f14014a442d160040840704911147c01151206102149500e03400040d1074001140081c201c0c5c02680d01c94000325140d80094982d00d5205414407040005601d050040c50301800d06c5031703039042441d000042031140100041e440b8400d810310400c200404501c0b21400408541040f00c1f000e41801c03400401207c1d142e15a42003298030a05a0380079201750584180105030544461400c100703035903000441261034010440f00c800340c41c10003100c04582040510b03100510801c0d4103400b20f060080f004101005030300111210b44040e15428a000b0551900300044609003403985803c0307107459010107004012240140c00745001d2500e2600c440000e4410582d15080e40380400001c000c035801481d0010000c1c03480d103629418600070204040340f1845d200e0b00703240545240d58001c6241500e040a01b40040c107a02058800700f18040c0080c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 982197994 1250 982196744 982196753
    0x4031a010e13061d0c0a06050f0d1e062c0402010e060a03150b0a0801050904031d120118020415030308011401090b0c03030604050c0403150c12060807032102031e0403 73
    0x1081d12034800e24004d054640d017100601c50520415040305050004c03d1150700b2440006e003007110f8220400600115100301e0200191f09031103174424003400b026081a2001c03941503654816001c80d060425400d9904000b00c803140c1902800540d40071f80060611080e601c150300300b00e0003d00f09002c41d4603002030715111004030691040c0254004100418000542512044d400081907000d007204569522040c01c1540c0c0107000781402204c0d0382c44900131900b10070302c0383da154036820300402d204070001c3c40301c40c0300200d0601010ba40704404031711681c030740001500a481403401031010380b9416210345206900341000080000080c6030481d0400c0300040000c140007000501909624003040d0080d9100e09080f400c000588000601a20030908144400c10100e09080e1007101c1c04081d100d40024443d000392800c540c00003e41950101c4181170120004181c0c500041e214126400744144807a45001c3c00c240b43c1001d900c011891005a0080c404034042841d83d002c0708041030686c02000d460195290b84 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 982199244 1250 982197994 982198031
    0x2030a3005030405010606030e06180109020d0305120f1303180b0c0303040b0106020606130b010201060f0f0612020a051209031908010e1b0319090501020301080304031a010e1306 78
    0x340100203000801840704214090040750080c1140f1705052190700507005815030756043c0240a249510203030b10020202c080c0a5000e40d001c00d40141032000001c0141c00c01814036446030020311a0030942000281c45036490f0000c2a008000142092100009030749044400d400410074400e0900c0c915600000c10080304001050185800d030701a544030300c1c05051110300240141e00c0801903400a4081103000d40e40d82c081940768510705103000689408a5004034010700c502d030000307125601505400300d0100305941d4940c1c21141244da40d1791318603400000c10801d034029220741f800031581c00e10020680c88180741c13245034801d03480000c5a080c08080a0481f80441d207160a000128007000300601a03100c01480380d69110301d80148000980d000e419040c0302d00e200c01004200340f841031180400204c03913160400c0002075003200096490b540c550007080d403030341c0c4a44811125403400007a06518110b80fa2001c1b41255102413800010b565089003020714401e802c0ca003104d2140e56110fa821030f9205445 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 982200494 1250 982199244 982199333
    0x1b0d090b1b0709140703061404050a0b0a17070603090c050906031f1a010e03060708090102040302190905100b0d0b040209031c080a09080f130305100c03050606030402030a 75
    0x1021a244003c004103280c4d500c4081c00b5070b0300309410901c2c14090703140e2000c9030703078903031001928009804c0c0c2d28500c17041d00078100d40c5e01081c0c0c40f01000c0f50004061101e9213001d01c00030391300c0b000c0da0501a5901d405500700c0b40b840400503d888006c500070001803810711a0950300160140c03d0700c1240e019030f41031607020840414a10000c6540d04040c2c2610034440200345201c25080c20801c1110140200083c1c0d40e030340c018092030400c0a22400140d40300c1082d01910000c55010b42a5050b61a4080448c4480020381c010b4601c101e01d03210000780005500038159007201d62844000c4d02e0000b014103c1c00c00340c507038200040d400540800404141d81c604001d810364401c5000088961401c9003400200341c050054149104035003000c012402141c0000200c61078500025605a41c8581c1204003034044022544040d01a0103001e91019040130030750030801d10400079940420859031b03500200240ca000070344029406a0003aa80d03000002d100380d10050f1201c40c000034000311400000242c0000d503115a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 982201744 1250 982200494 982200509
    0x918021215010612050a05190509010b1002060919030909020307020c0607150e030913050414070810051608010302102705090a021204080304060e10021b0d090b1b07 72
    0x8401d8180300213140c414260046108042888103092110148080405110124062540d10004a00b500f06c0940c4103103c2c0070005007001456184403030010f901c5800441c0e54800900071034030b0448030b01d0158540d00c48441d0345500c0740b100c502c1c00d010112000790030080050080d4443c1c0c4107541030761307036a01014003ea184102120340d1300c50010807100040d6465a0f2110f001d640c030034020048950340e500d2508031585414000080e4903600e03814403a141c18405c0701c00ad02203000329000461380b85000f0a42c10361074030b0400f81c148120388911a0101400762120b40c50320006040400510044c5407403094a080c80940342b40000814200e44450004100b0900c1c1182d840c000194041005080000b00c140d03100c2040705085090800c085010810f2210080c13000305007050002c0010104101399104210400003002199501d8581c60282d070001c0d800744c0a1040c6800519981c0caa19010000c4e0a406c00e02c041d030368107404d491400c814034440750082c91400344550080b1100d203d10300000c111040040020 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 982202994 1250 982201744 982201757
    0x206030f191109040b0901061b1109070201060f080309010504090507180e091203220f0f050732040f020405062d1801210504031809180212150106 64
    0x300e9040100b01c942c2c02c0d40d00b80c01b9035080c800410113039070409a003000c41c050f402d00111007404180780190b10180f44081d216030121008040c440c031164158008820f8807111040032170600e4450724070a0f40ca01600d020f0b1800548100414041c0b9078880d0040c0780c00a00500706589005c03c000a03c0d8000b0505e0340004003050ac600c02004181039041050f0915541000ca01c0c52030b506000003600c09146070981c4001840840c3d5000d07500b00400382c5440038000e5048400c0d106680c0c95403901c41d4030b5003483e114a030001001d03546021904500d0303110511403904442c200310100b144945c1888040c0aa042068103a950709100001c1c0ca074036000002c001a90811200c01c1070800d0f20744441018540c00d90b4ac2454541041c8242c07600d0301c140d04080300c10b524007400c0c0b05918401d07c0c4001805a040200c00c00b02a50600d02800109034000030300444109041e1044c1400030f44450161040340c1d60b070000070034144442107012002d804c0800841c000303610b0305010341d210542e4650440450314402c0c0d12600c0051803 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 982204244 1250 982202994 982203007
    0x71a03150a2d1208161a0903041401030216061a04062d0501020604030e041b0302030402012a020108101509030c0e010b0d0e070302031e0709090206030f1911 69
    0x1400e2540003920800c00e010541c02c0f007546071051341d801a040b0420041c05070300700107024000612901d000d800080911240c0a140031401641c90346c1017441011015000d000c00d4100b10340c024020303550350729440213070704030b030145140c40e0000500b4803a000380d0f05109001e1075811503034850740a054040c0075001d1460074014203198034022042504001c030511071103040d006000c20ba03408211150001d4040c40c00142802a0b42c00240040c0380e22001d00500216006085605c3c5400d60007440c400d5000340c0b105d01e400c5030108131000745003032802008009585031103a48030041d8000c203040361b08142e0740100d0042c050744030318107081c1e012005800000850700160081003004413048c40d40c805010001c5e81d50140d94548020300300781e40640060441a291a25956540d105003003041900a5030002c0444201d122882075011001e03040a04e405901e0242031400319074040300780282d40c2000c2c0c1c00743c1468515a1454032030500b4602c0a40703040c001c0402001c20182070760240c0580c48101c185443c00668515 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 982205494 1250 982204244 982204319
    0x204020c15060d0c0608070203090a120201120605030d0f0e060304030306030c08010207081801020c041406120a050a0308180115090e0609101a0301110903071a03150a 73
    0x140040c81a4443c0d00e9004480d0000b900468182e011204941030000381ca44803000e06a040d4003030398199030b40000035840c0000b100307a228082070084038001e07210555042010402d6906446590154982581c407030070489031040e104140846480490b460250101c00080c0c0001d9050343c810380d01030340003030f403103207401e005201a142d041001070010f00c00851400e41c10b0750b5041a1405a10484070002900100142c2d1070303402848880910000100100b1503e20004600c00044409462090060306241c010765902d50000a1070004244c0250003416140c0c940ea50480c0d200000400e250882310a40c070b00403401c1c01090103103038100b0740f0203401690041e0a06a001d406c03988076241203000c0354406414081d1070480450038220500e200140810b03a07000c45e80003c5900034000001e1034048d860117103070b8441c0e010f80300042c10080d18224207a521042e650385414004622010300382501070000c0000c02c1940b6140f00d045100c0c02c4003d04001c004958804400303803100e42000030041d02040c841c1910710b810 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 982206744 1250 982205494 982205533
    0x110f031603081b030307020c010e012f190201120b1801060302180109212a1802040e0a02070501090b0a020a0e371710050702030f030a15030204020c 65
    0xc040c3c500040d815407900c0a402543d07000d001c22920305200d01c2000783c401c3e50b48030760510503843c01080000001803640c001300148000001c0e0301904240a1a45440f845c0460024080d1950790141d44041584110620040c002c00705d001e506580b26110310841030102c482c80c0e07005802007003903440068440c1c0000c0c814100d0800505900350401914580034045d850415048550043e01c10301c44d418440344501d010761203000780c0b00014084a01c501148220168145e611500b501c8010151640368581000d60300240c0c0a6409046004e10314280040c1094200350702a040042c010400410824000e0301c80115500007034402e000d5031900018614860798010381078602151041e51100501d44042c0f0a078000502d81d44095440c15000b0b84c51600340310120719580015048000e40604502150b043c00380c4c0e2071001e170180303021a0b03003001e0003c4c6070180048181e1325160a0140410318584e50b1501c0c05000700b00c800c180051000a0307003804409a10f551026140504212004007001240242c200400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 982207994 1250 982206744 982206787
    0x224180a03020a290f04150e1609050108030a0c031b0f02040b09010b0a0c0c1a070b10050a0303050a0c05250801051603021e070803150904110f03160308 67
    0x1501d41968000602040b21003d40c0a0004000c0901544962034445c1f1410212461003013620f051040704c8012510201d6070450710f1070117041c4080010745d69003001c002d4030800d10443c902a002840311601c2d0602544107070407007a10030303c0c18001c09074080286881e2605070f00c600b640c26500b070003400c0f011803c1c98414070045034401c40321074005616080d071264681c03094061440400940105800411000720a08005030400d01c2c0ca440289100030100c81103034001443c00c1c0c4401600402140e83d2605661645040e10030290005403402c2c1151019266507026001c05410030108010482c00311b1130510080f09000503500c942c0b800b42d9070748021080c0c0f8581c50b40060010380d14204c00d00000c000c1d03100294801d44214100541c039040c04201d00c0709040074140c050449110b00140050030084407200070741c4151081026004131016040500441d000100c50040651010b1a01003c80b0300c1c004600c1d0344400c0c0003c04840515078000c00c0c175844440307030764004c8071840700115014801c10081d0045801 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 982209244 1250 982207994 982208033
    0x60406093801140901033c0303051312180806090a020406060e0a0311190303020f011a0d0308150a140f0301090213020d0b0915010f0224180a03020a 65
    0x410f4203580380040d40b0701c00103101c01001d10000050400d0754019186a6500c03500340900c100a03c60fa407105103483c8245402c1007100001d00c0c040000305503005584010340c00700e030800c403285451448260255008c600403070f07415110100705000011442c03020810140326000010140607402020720500c01547e0154000300e051000c1b0900520003034441080701c02c226a008080d62404095600221b0b0903d1206522408a0044050040306047d0000745001150891800030007002030595110702c072000011862a034070455001c112404240701d84261504584644c010b50b42d80602c0c880011a000111b41c0420850303c0c0700c0083d002c107481c01084840c584001907009000c4502d0340d0740090344c841000111141240c0d8040362011709104c45600601e0b80c03800c003811000316401c01080320142240c030016564002400900f009051600c00704000c602100d40e2503040100000031f0344210740a171001006024041443c00c1c80b544108400c00082f010300c0e00170780280501c07050508128514140301102d03e007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 982210494 1250 982209244 982209269
    0xf03090f0c04062714390a0c0c05042f0406090308070c05040c03050a18031b0f0f1a070503091c120e070f0801050405060406093801 58
    0x410355103d0003116015401c90340b8600311042462007458020f041d0701255600b45805038080060a00c400c0000c03d603003141b110415000b08440701d002c40113040d48441d80860070541071003e1244107004101040446204280c0329001c10f0b01c82c004075040b10095a030480801c800b4031032403170f00f41540c0d02d030000f05601c000701003d160030709010b40901422018440100020800900f40d42408011003803803014140082c01131010402d00403004001d4142a50303000b503200d1030450740d2000d610b4100d000c22010343d4540c5941e18181482e545030200c2c20750b8003000362024501e00344071400103190304444d00d040030320131550501c100040c000780311031894000f48104240b000030000e01c40e8260002441214669140440c03141b07058988900300e60f0402c504a000e53300905002001c80044404030340700d000e4031000801f000c180e40d510301c1802d00707941c402d590161180d004080403801082c4103401001245000c0e5415034203681d40c4d00da040c3c480354250100808071203a04412071a1103035181c00b5a42c018180d2a0741003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 982211744 1250 982210494 982210499
    0x71410021e0310120203160803040501030e010c1418060408060406050f01030507120812190b0102120729040507050a050a0602030a20190b0a05040c09110f03090f0c0406 74
    0x3c4000510b80d001e203045104040c0306810840d9030400c408400060305442c81d80310261390f1a5901c0d5641c1003402880d001c81d007845a480c03440070051060500c0180c0c4c03603640c42c601304d0740004000e00543c0207400f810720000a07211584115103900009000800d42070000b8116854141040b500700d44016160b5240078203c0001040451400903041382500c0142c4454082c0013401e1422000c507200e03543c211032842d5131900400c0041d98241c0c0031214100042c041c18021652180c00498071803107054422403408500b8000c0c4008900140e0034000314816501e9030f0b071800401c203842030148800c00c403000c4505074002041440f95090488180009000999080d0b5243e410108065201c0c000d44200c0c07020802c00c1045440c2c1c9100d4412110780962060703040d00d0707248040c0040c10b801100c0084041e0317030040591002c1509c080092045a101d9070b000709203402402e040c1044140504085203119a9215090002180490340030700114007030300b0400f0080803102049a02c2e83c3c1032645104c01e61340b0903440d04504 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 982212994 1250 982211744 982211761
    0x10f0608041704330201020a120f090506040b010317031b030a0b0a09020705010509072405131401170601080a0e030423090a1a0105071410021e03 64
    0x126040341c0c1c809004581c00c0c0001019030708601455010000715500d14020621020012691a110540840d191342d200d004500c0107a09034401c115440d0b00042c611034801c588403034540d03c142d84c00941803801103080005a2507140c6896015107050b07882c414501c00400420102c0910841003a902c64259802c41c54074409001119445c030145c403501010000010350040c0195004554030100100600300054469a0305002904100021106c40d07203000045440301038001001c07801c68105503c15042c00360b602c240e000440c5041002c42060200a001071180d400d4040815400b0385010034190345206041c400040003602501a8440c0300c00c80d80c014090341d80d034041c4405034006441b000102d81820005a85841d5100303075800300b04894020030603100002c6541e150360782c11080c00c031444a0076460340e220707410446d50390040c244120840d0900192055000700007820340e15005402c4540c0310300030080000e080c08140b0b803588503500c1d07000800242944031441040c0b1210030700070001c0e0852034200d14 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 982214244 1250 982212994 982213007
    0x8031f080c01170a0912030b031608030f072105121e0c0313140303090601060f05030a051003080d0e010c050c06011712070b040524070c020102070906030c0509010f06 73
    0x3107204401260800003070019484d50001c400242c3e218110000c4200e1086004000303112141c40544a406030440c040c01d104040100301003907801d204081d51511310300c05c40690455200180c216510303a45118a1443c0c000850381d4401901d18580301d83d07030340e040144426003411030010075800750922501d05035080ca443c84094103510048920b081030341ea4a03290000d82041c106d8020082603003080071000c0b01d043d41c010000c2c40c090b2840104032101350342c0b110804e891030400c2d03180e2900081d9050000800b014019040350360000190244440348907107036161100c242d48145107018a0b1034607001c801d900054248140c441c01b9240c2e00c0c04500b8603070300081150719040184a8549110310401c95911800b03014841304205080b10305d07005689030300ca46441d0b84814001c440503902d600407480156003404186202042c20000c1c1014040e46035640d6409072a2943c0709281a4110320841e00c000c100c10006100c1c10013b54090111030111074600b40810496080c1600f000b143d0700c900200401107142c1059 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 982215494 1250 982214244 982214267
    0x60609020f0a110313090603020907210f09080f070b310501062c0f250e03010c031a0d121d0a0f1701090203060118060308031f080c01 59
    0x140442a658810081c5407550103044903440714510360200029404c1e50079070001c1c7c00c0740d10a6a03a400c1c0d40e92854000c0e80c0719084440c006400c440d00c0103201010382d00980c8110b40041c241d62002900c1441522581400d420148541c04400c50000c0d0030001c3c000c2074881c1550118680ca4600351101c200c2c0c042c501b46882c810701c4100c800e20200e8a4408226081d000840a4450710351003440c0c0c4108641d0b94040100e502402d0440c12068002041620008140c031900c1000406c41140d1080e4248132850103100f04418424100a00c2c64050011640e0a0150310741a070700c02d0740d0105000205e0840071304807120b01916035204098015240002811551450688201c0741c1020000d00058212031101c1c1c80f4844101e40d40404150004102280780c8462345043c0c0700c1d00c0603144410507521006c1400c0360f140c0b24002e075050348044010044001598580d030000e5141f4040422060f03038076903409429030010341c1c4404c8001c0852100d070081c140c444080c00010a2074000034000d6000070340000c1e00001012 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 982216744 1250 982215494 982215497
    0x4060f0e03090d150509010b010906050406140901051e0c071220031029010e090411030a0203030c010902030c032e06030203100c1116051216030b04060609020f0a 71
    0x3c041c08024080035403000350207842c10701c4052003540780c512032041c02400c01c450414081203040c940861600e11450030707541690295120f041440e405d446049041c0d41000c0ac0040c10810200702c000c181a405d40111039a0a020611043d180e4503880d1007141044007503000000300070200510100494071800c603a0300301c007171364600d80580842040003083c200052688500307031660810800342000019008200c640c07070054a9580d9a5841404c011107801c040b14082c00e902030844400b05005c6908000c0c2080d541c18010f01311030360380b94168042411a04802907109103a59900c005505605041c410709442c900d04401905403007600d09140c9013503407110b1051401c580030000103004040055030112016613001012610380700f108041d00c001400c03c0c2d00f542e0300091824030210103110310001c0c0ca040e061100359400e840755410181400034000c00b850746101c40e80308a060300c06050380d104120401550003580400d1440c6850305090043e103541b0380c8007100c218070401c100b14031004e1000995001c001c19 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 982217994 1250 982216744 982216759
    0x16030306230f1011060c0403051507020307030e0307090e0f0c0627032103100605130b070c030803070c0314040f21080307030204030c050603010b0f0d0f0204030b04060f0e0309 77
    0x3464044a25070b0542007829061720aa1060002401560000c0c0c070403039100d1022503405501c0444d80307010a0301c0070340d0304c000940c1c024429a0700080c00707005071001c0204040c0031111456580e40000c0161140034007405001c0c0c006002d0300030301803401e101c0380c03641d8001650441c1c5418101c000d069542c15800d8840700d402030f82e2458a800d81d54050282107502d03448900d04102081c3d0026055245034025941c2c8078951041c1c1000090103406071042e91400891214ac1103415482c0c210007520b160b0105408503200040500088001004880918003c3c0f402c0c0e502e6000d0803141d850081c02e10014590b4240c483e10b4140010009420009800810b0b2002048210000c01c0f5204104860000c50300004000c0310000c070400c2102a1306a015204481c001c00002c90816500c80c14086140300038011150a0107081101e6507415503000e00520001c1c40407400010081d01c41c084060807a0410381044414424505c28002801003501905042071281002081480e8203814010382d28418440c0a5008a05 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 982219244 1250 982217994 982218019
    0x40203042604090f060806070207180c0201020f040605070b0f090c0d021c1118010b04050127270c020601030b060609030f1e12030106030b0616030306230f 68
    0x148041da002020106414000d80c41001944c0b030203000c0c0d50060b00c3c0184290b00000300030070720014840c0300f101c1d001c0343d15030300e08103000c0050381c080d21044900780f0566400b00b0074010420025402407006291070b0f07540a403507111f03620700a425040064000681c00f0902d00c10b210f80344201061164000000b12140c00c00700a80d48041000d1100b1400716030304039642c803a004c0043c0030032070342910044d00f021244d030001150b1440401c1260f050070700030b00d580c10303d080c8000c0c01654000c2d503201e01c100d071401c1c680318000399504031114518545a040079041210340d1402c0c001d1070914030340c480358503591041e0038042080004c400035583c14052001909000d80580811440c1c0c03980c0f81120310521003c0e041e24401d01003020344907624001000c1401d5003c4158100d2011100007050300b40301100c59003581c2d469a4030b0008203d02411906045580c001c80402c11052404520311441440503c252804224180b4105907c18078142e02003803d4230740d0361945030868070360303075403503100031140c0c04c1110750755003901 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 982220494 1250 982219244 982219313
    0x2a02280806070909090c03060e1c02010903080f06030f0a110108011a19030b06280503010f0317040b0309210910081807180b030d050d05040303111801020c04020304 72
    0x81081d400038011271b28200784058404400b14060f01c840040e5421190908640c1c44200d0886607031036800740004204002046160b08104851600810300400f06c80003403011000c86410402c4880080700c070b4030110019400956041510903004110700c0c5190006204004c40100e064400d28442c80c08000800c0300c02903030503000398230401d803074600500083d0702e500346100f00141142c0e001118007c110035200310220764902c10801c590503510304425400046146036201d0084101c00980034500c11024040480d03c03104030800307540329503003080040485200c00410b07040c2c015120812419201d904020040041c0c5404210001d20314140c070341041165aa5841310002c06c100441010300ca0107a940006640031001ca10300244000004041040c50115020941d03181c420313440b820040391040c0b003d1364400b105a8032066005000342004500310b5180c09503103905a1000000e65049020485080c6503941d04108807124490180d40031031a604040e103408070040001c9901082503410340b002082e031003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 982221744 1250 982220494 982220513
    0x2413150308180906041a12120d0c110105040c0b09060d05100e010906080a120c020904050f100b060906220e18030306012a0228080607090909 62
    0x15500a207800e601c68200c4410000000c03000c400852040940c00e000c90f01074640351081400d010000c0c0001ca0141d0080030502c1100010b14400000701d0090b404504c0c0408040e0b8020203611641aa00003401c1c0c0c9124409030440010108440c9141c0c5400100f20001b60400c01040607908030a503840e483c0d803290300014440303120726441084000d0422051084c00005028014240c403c1f04090860310ba880f002d440c0200d603902c0c0b060020310740c0081d948202180c45c10340d0700104840c042c80c00f81200c078400e0700032a03213800303050701e0407604c07980036880c404400a0180030500120314605000d0202c01104000581680548081c4611490001401c0150b580703040c0300301042607100344640064075070788001c3e40101500131542e80da80c00e44004404228080c0100842c2c2c82040d050b1075103901f80c3e2000c1003040142c45801580003881c1e05200700f606c050f0341c1e15400001d082c242d080411040214400041e101c8040c5544200784c90351201051005041d0050000400d548a8410000c0c04545a0034600c000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 982222994 1250 982221744 982221749
    0xc03030e0c12010506040501050d0809010e0a080303181b01090b030c0408060a06061707080a0e10060b130509040f0b04080405040606110705030613080903100e06241315 74
    0x40700d0803040c02c0c41c42c0041900098414081101c3c100310f142c1c0d075042480f07010929030400609400c0100700f030144960044241c01004c150140000310040c2d190a811803440c3d00541ea00c00d400380300c15408490280007044564150311403002c001d04505010000a44042c5840c0240c080100010000030b90f1120030000f0380d802000c0f4002207500500b800c1c2501001400340340039417030020b669604121507107010b0114007801020f195944508664038441d4240061504411504103406050480c02d1441054058100a01203030446c19a4682800031a440c00600f075901890240e0010801c210110b2241d030000100c054100c45c10480582c0c851a0615683c842c9400c2a94000d142100124569a2000a051541058408032402d66407903200301071f0384400489281c1c007a042c200f0b48101c001000d000241036014000b0742141d07400034040386030005840019215031900c3e031101c0d082004c905201c04014007215416860228018900c50100c3e101c0c6444d524080c2e580c5450700711100411707070181e155800 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 982224244 1250 982222994 982222999
    0xf110405150c0d08150411030604020a030605030715080a0b01021e01270303050f010e011403010f02040e0412050301150c140a0605011707080703110a030b0a090309080d0c03030e0c 79
    0x180002c81c0000a4203201d003c0e1002881c2d00c3c0c04405c4a2000c0c2003034494680303424010f030b0b902c41c1966500030812012350301200c02c030303010161a0750001940d5201045014090401190005800c089140300103155140040c00602614100540c0020b203076004071f211039895403000040703071220340c0d01c50549002d440c0540e40030380f101d50482d11401c1c60060644140c0303442c43c441d5900f8082070319600c0608100c00002e000780e0551401d408010000354040c0341039150b44240150001c2192031000d0100c6080f60850741c41300c45105445403c0004021620500d9030131401a42411030440d4107001c006000501210300d850180401c800d014400d04c04d6040403211a0f00c030810403200100d0b40b41c41c1c00c901400c02072003050703401c0c81c210612042c0c4c94004201c02d0282c030140401481c00a00d5074031050b030300010b1135081e40c4e04160400c01c080042160001c40b144100c15031600070994104d28540101269050b52181030765400c5a8005685541d100c40c070600e04581504c2c0c003007262003180d0031090400c11841440c95 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 982225494 1250 982224244 982224253
    0x90c0305100b0f030c0901063501090e030a0801031b0b0307020114011d1b090306101a2b06050d0501050906070f0f080709180f0f110405150c 62
    0x4040341c01c42d0800c44540c007041d80d24903141c2d00f0040c18540e9692172035280780d52200da0f400043c400b242c0310702400704103509011034512852282c41410854000b5400c0b46044182c0c407900180001070142c042c3c240c0c000c015000071481d10051a50080c0308050600004082500400442c016641c4801160000c4c042c0c000c0120796034100f8040c080e000b010042d26070000511000c2c000514124810040100d1005400c26842c00351343d02d6030103941100b0881d508014981b814010b01c11389850800889100ea80054881c662085c00c080c3d601580607030340304144840c0c50f820425140d9041240160b19001e01100300414110b4900710f6138200a00119040321360051a10319503601401415005140103c8403070064801944070305a04a84100b008000d42c0c0201d58500450141d0030b201c0d180040d402160b07440c050f0007040e2078517040f00c1109076145c02c41c01210780350010216190b8240c82500500d050003042041080032003c4003100300d000d18403505108681c803259030108002503800b16840745400c181070380d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 982226744 1250 982225494 982225513
    0x1b01020702040e032205030718060e04050d110102090a050402070311030d09060b0901060c030c03140412050c011818090803040b0405070e0f0f040203190b07020c0114070204090c0305 80
    0x3d07580d401050b01d800082c0c0b172422a0600010008000c00e0555002801503c01c1030708103201c1500303280481c1c5140ca2001d40c1e40e000084d824186500303d6000794460009000c00d0305103000c1c000c04008032050510740c00d0344104000b00c2d0320b0303960345003000c200e030390907a00036841e812581410f8a0024030f0320480301580c000080c4440b50041560300110303005102e4501004004040d07014041510b109008240116080280140c00f1a008125076924203119203004100c2a5a8000e40c944582140c0d005402c201070034040c400030803000388900c0104220138039000c04100700007068944070410f180300b003040f0182203403084814128540c11111800360000038090303aa080c1b602e000451003008540558560280702c2c408103000711170988850003500104180c06172515150307400042854040c2081341c0c1845048210714887d01c10760100c2984a01801c0d241c102d51500304400703820320080602c001c0c10443c0c1d440b1a9040c441341c127010f0b10105a01130350002422081c40c42c140e8411303030762900701420f28400c40a01 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 982227994 1250 982226744 982226771
    0x40f060b031e1005061605010c030209120a03080a2414090108030304030c170702030a1b0f03020a0306020a09181b140703080c0d0e070302241b0102070204 68
    0x40d80200354106102441034040b50201c0d00070311003a60b10500100205100300032070b24010000e441000400c4850070301ea482241d682508496001d446580407030f0f00820a88158174081000480c404410b40203411301d034000d55001055600000e0521a82e16502c00d5412038504041c20030480c142c0462100e440300f00d4880d0b030110004440880340038442c01c0031000205d214080482540d0145070306850f600300072002680c40140001d06800c044850002c14090300004d650108100e0441601030080001e0701d611a5105c044544095006407180703407240c081c10801030301c07070460b010b0840c1d8024030010b031120301155044603444515403203198000010078582c0c00c900160341c00b0b0341c051903010400a01950514030203590000c0b0042040070750840074030076240030038040d00045500002140b001c03442c190a048043d8116090041e400a29900100e024000c605003900651145400c03010030100c01aa01e41e04811140320f040f1600700040744499144028580c01d40603600035940c02041440703001c01c00400c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 982229244 1250 982227994 982227997
    0xf060e1c0903170c030a1b0f03030e060c09102d050a09091509330e0112050a170c01060b030603100903053411010210020423040f060b 59
    0x410b440e280d588800c0d160f0b1814400b0f00300d5500d011404081c5040c01c20041094400032950354441c2d0140080c03d4000c40014480b030400c0c10920f10070384001aa4120f4460254038000d00203052409040042051151560719140c050740d503543c09140c0401010041000400019031500d122610401d01c40c40400040760000003829840e01c2c1680c0e00303d40103907509403103019a904800f01c4107030340c60004414030070fa503115082540b40449400010b0f004a002144840303129080b00d5281a1003086030100b400050903042c5002d004004111b552840300b2400d071107a6031a030200100081075081c00440c47c091a015035010f49079071401d180020401241d407164040e2151340111200c43c803a00541513007104901503031003260400d0382c042e61241d041c40e08070b50035030910720901618070b503040c3e00384800814686d006484501b8101e100d002e007070400c035014100180c94002100103004166005100a1001c0c0c0000c9007850040084802d446840c0045840458024542012a01c1e40141420400b00744081c0050 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 982230494 1250 982229244 982229249
    0x60b1b0c06030a0507170c030105090a0e060108031e120f040309030b0f1503060f01030602090f0415080c06030910090204020d02030f010501200c0f01030b0a0303091409040f060e1c09 80
    0x2200c01a00c11a0786e1510203804030101c0c1e03d104106002d0005116505110000315806040342c03000146140814100c685060005d0340040a594400501024407100d4400050000e580e01d02d180c03400c00031900c1408481840c010324201548580d0f41c0050181446036803d00011908440b0070344540c00c2a410009010400b1208405014840e815014030340c240003490341d201c1c0b01c0d4481c05040366401c65403524069800901d50030b5000c02c2051100c9075030343d503500c00d031000e5030a82e81c520101c00b03240103052170801b25503080d02071144d40148208108040081003940005461420020320f490305032000500074000d05201e809410b10200420400da810b10264a060303079000d8032a86006240c80049100410741800780c2141c42e0010144c810300c9050040c031b0092040350504000c1150030701c00c004074070b508940f94020740014201030010071088510641610a001d002d407640d1405242c55219032400e110f84050081c201583d400e84c00010000906c9516420f540144255a2110301003100515146607130 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 982231744 1250 982230494 982230497
    0x30209030712030503070e03011d0a0606050102031606050c07080d020901110f070e04170309030319062102012a060b031b1201090b0a0f0e01060b1b0c06030a0507 71
    0x241c010903484411800101c45650541e02c1520b55035680034220340600c6501543d0b40c00d0343d01d481c3d121124101105094005030124001014006620f0402000752005944180e0543d0020040c114500c45a081107860345600824042026100d0315141c44d85032041510140405401140441004403076030001d04000304e0990b9980300745214500f840d9243c10140d86a200c0c1c541c401c40c8200001d1043c44c2549500602410880b0003800001c208010243c1c0101d40c5400d56030070020420148040c01150a00c4121b40a4030410a103404c2c001034500c0507160841c41d001f25140c6a072020304582c441c0c50880c000c03a8152007881207043c5148180034015000b050203c8859082409400c914140001d902c1540829241000c1c0c0400030007042c0a1411101c00301018036548a00b01c25005c6990804c800d80075403100c03180000c07180e051030301c0041110394000300e640f2035904054081103074000070300581e4000403000301684450200d4142ca0391401c0588860700d46c00c42e07404420090083c85a40c0142d100c0e10780c6 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 982232994 1250 982231744 982231753
    0x825051c050c0c101509090503090d0c06170f07080612011e11070f020105030603030d060f03031e0806010806181e010807031e0f0f0b040c060509010e0409020f1003020903 75
    0x3150600720a981c100703403031101c48201000c01080050b13030513001600028019429240b418242b640071800c54403c0c1d031f4040d940720300c4068080003584c0d40041c0418003520480d503065844d050403540c5010b555405004401042000008105c0503510849400c0d45503c04c0c40007000758549a80121681440180f021480e403840e04107811422040c0204451140e0360080500700c02c0d00c0142d005403006d4001404081d0148402e101e10a06205144074031000f6020101d140a2620300d140b6000b4950b90345000f004800689600080c10781030307088064550411400d09008007a0b94484000c40c4849030203c032440c0c25001e54406002e20705a500e03e00c0c0180c510300070058140d50782c8480e0034540e030f803002d440000c2000c801c1c2425481c2859240e011088108d02c0b520081c0c5d1603640031b403980c2c00c541422038801e603852a054000c0c0010042d1540c0800000c0009040c0345081807408000a0007900c85007100e58002c2380c0fa00765000440d602c1e41a04411b04100070004441000180e000600940100c1a41030080c840c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 982234244 1250 982232994 982233013
    0xb030f060108070b16060f18060e21030402040e19030e041b09140a0e090609010b10140f07050115060e220b0f03060a0209010825051c050c0c 62
    0x514100c03116170b2051010410800c0d0944d89030300051119040041601e580c2d0441c00050b0710003100c041c0c4595010314400f18056400003241820201c02103580f80e10300800c1444220b002c028001541c1c0d0007a012030300014540100310005041651108048034031492600c1183c0406800c0392001c0c550820030385003001086111002c402c240740b40350f04914045400c40c4010031a80351112400d81c84124042d20a40d00190768410b0800b5403078007079402200c990003078400c0011041d024404d00009038011101d1055850340340310044c092070480300c0b01c1024950000303030301d18001a880007110183c0350b1010080105000380c41c07030341c003011380540141c1d4009080f0030040c1e54a450182401682a95010b00030702c6000180d20ba00300040040e009600d8114100c880b014215503003d0240c01d10a241e030756400f603038130318a0100041c101e010003007041c40c48403450705003202002e440591191b00f407001c0d814402c2c1c4d0b5a0130480302096110b000340b40118414100b104000120000b00042c250705407018080729a401c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 982235494 1250 982234244 982234259
    0x80f09010e0d1214090601030b09030f0a050405091b030c0a0e0a06020a0308010801050705120717010806150a0b030f0403110708070312110a030e0a1809110616020609040b030f06010807 81
    0x2c0082c2c481d00e6441e40101b00610100340040308554222051404891a21a0030402440c1c03e8010350711f0480495400b290800c1142000b194040c0d01a0110340c50782e91a43d131014028009000117040c01441034400309290a210380180d080c1e4070905401010007003210781c4c07140c00035034034511703501c003200080d003114000901600140281401400035486a9007000e901440d114040385005010b1400c02c10f401d111103c03116030004090740a01b080030003404407032408181c48004484035510701c40c018681c1d200100200384550703041c1c079044422500107219580b43c606045030a403240101741e2640c0d000f0300c5070000300303594000344650440e485503d00700c1c5854291241078509551318501035045400030180b800c006031003200c00050400006041c941150f8460f20030301c02c115031200170305041c0c5a8135500601881400f42d942071034030307004846281c074110300515070a0081030b640350024000d480214500840da991900010003203071002d42140c2701302440b088980d035151800c1c480ea007440d0098001c04129070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 982236744 1250 982235494 982235531
    0x40e1806090c0f060714060f01140105030f062103070204110403030813051c030504051009020a1211100e010f031808030919080424080f09010e0d12 65
    0x14450034010b05514038880d42480701c0e2001000c10254802010000d010000e01c4c00040312010300c60400051541381b401032061440c03004113800040000c00006500d50742c50b0b0b441021039178070604d80201950705403904804158402030515071028103048424403154011000809400914000c4400b400481e840e41813115681c03243c1c1c0805000205403000084240c00d0440c05641020300c102b04503a200007440f407a0301d103225441c20440c1d001903103d600380800d200040283d98240300130498204450300c89075000401d5005e0343d10500600f1030701c20180d10203000c0d100317903421182e1101070301d0b00c0d03a801c0a85100030300008078001c400d4080740440c101412040d10034401c1c8401708420911488031001141c94943c084c5c1c000800070b084500c18000342c40c0e0700c0700c0700c8514800550300c1400c8240c0ca941c20030f520030085032031180b01c00444503040e240e065641e82c0c2c04025580c220f400b000004640351145a482405030118020101007840b40d0b20003d0482c41d0301c460640320b035141404c02003046400042808800 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 982237994 1250 982236744 982236751
    0x607030c140912120a2d091a040e040c051801030c210204110406170708040f05032109010608060c030708090a05120304061407140901090902040e1806 66
    0x495040c4060b03140c6050181401044030f030300c8070031140c030b126090f0a04482c1d6880250860700003590f001555240010744140456800a074016030004000c90000c0101062228400c1000c01901c07816443c001c100d46004650140c1a400c1c1192214507250a042c182003c3d00e02c07032280640c1c4001441c1e0403481da0841c10314140c1c2e5011114040140c6000c90044502040c5660300c0050700303505880c1d03001a5250f1003100300c44c42074031000c035484030320f08140a01407040742d103444000310a61600b08462103a00000c4294095408228209100c5d0141401d500d94050b2400421a03248840801c848113180c2c1c01d800da100382c0300c2400030f00007240c89103881516284141c03410904d03c4010700104400038010592690301c00150b40c115003810101d40c0740c5525040c60494403102c0e803003000040c4400d04c40d840c0112881400100841c44081c100b41000400da54114090307112042c0000c80c0d0105079a100303d83c01401001400c205545581d01d43c0d1078801c9024050f20403030f01350080c042c0000014240403034410701c03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 982239244 1250 982237994 982238027
    0x30606053c13020c010b030c120a0813090e060108070602010212010e1305030307180608040503070b0a0b03100e19022b06090b0901060b04050d031107080106080607030c 74
    0x5450103144220440c0c19801001d0780d101c00d40d110065449005840030300041c03540c10002007031000101003170505152440c06154054101d00c0302c10f0b511134000050f5070f1101588032008941d01c103010549007803030301599004003045500780324007007142c00e00003e5542e041c0c41002059800e082d6441d10180e080348100d004085190b40307540010010000b0f00d00382242c2c001c101c3e94510501c070421fa52800d095620440d090300c0496104130b01060080181c0000201a00f8282400b0342c0d2814140c079002d42d64040c6200050044682c9800203045103600d0b0010f8501003005011581403045924084004d0b04101c3c0800d8072620410801c1003d841620040b1305085402400360170b41401101418201c2040b44000100c810010210103c001121407023110910b84c06036001c00e560342080c44000d070a450b495031001c0181181031000303002e281d13242c1600b010911f41c1b50421800c10701107814268284105039110380c01d42e5284c0200003481c141c01042c0c0a2144080342d800308401c8103440790070f03162004910503144 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 982240494 1250 982239244 982239319
    0x30f1502270604051c111806060a02010e010c0c3012020c030403030512061203220f0801021903090302190f020a090b010e041e150e0103060605 63
    0x801c1102052210814102505291502c0e0316035000c6210410010310348104540218000c0041c0030090408050000044401c04098041d24038081400c00015011b144944d800080009205000b540071004101040c402404802c40c2d80304040c100d400d1a4006844c2c100c408111501030214284182c6d0200d509100300c00001800ca000498050f4107843e0440c0b00b01e0340c01c001d00700c004902000940000d61196031044c1c1e0356540d01260380000f91001c0c0555005c0c50f0050400511020040261740c42c120140140e40c1c03401946c01909145504c981e886103c442c2100040480c4540d0706400400c201101500b11100402030b000d000c030100c2d21200400ba0050700051100002c40d44490040303410b042c0a50f031151003a02e0740d41c0000d1940d4096034803c200d1aa80d840c1c0105131960800c4043c0c8200000b150b00300328248070030000c800b07070380850320714800c0c80c540d42c80d20000213440c0d21000d80040d00c020341d0141c0c0c840da100d1a10340300610481c01400e11901701107405100c40d0f03440750804402011b2100a04 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 982241744 1250 982240494 982240537
    0x10e100503060102030c0304081b2d150d0e07150c02090c041509090506010504030c1403120c03070b01050f01050703030b1c0f062406080a1104030f1502 67
    0x31519604080c1086046010401c200c104103402000500040c20024010303113400c5002002d0001001204c15600740107120121188e24003940040c8009940584510220070660070307040010000031918401001c07020300480c05403400c14165014420191100040350724103a00c400102d41c80d100340c8030000700080c21003010903005003050b918141c0c0100111076607509042d1200c101000c8040882c15640c0003510807a0108480703c4a030041640105080c24140d160074110f443d88009060030780a0b01c940c5540100d445801610704101680e0480b1181484a41758a01c11420329140d42c000780066801d0f007034240011540d880c020b540e40ca1a507005841e00c41c9007103001d41d0164040c00300500c401380e00c030455050081200002c030040b09180c92190f4410000c0d40720f580350500896020010107100f1201e036001d500c8100c0385600c0ca02058519a0600c03180c0d580e0b0301c41e01c0001030603c5c21008411060082800001c000c14114032210551040070003507141c1812900c00422070013101c1d0b82641c0060310740d040 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 982242994 1250 982241744 982241747
    0x40e0f130f060e101a01020607090b041703040503060f150103020f0d05090f0f070806090a030e01080a0b061b0d18150e1f0f110d0815032a010e10 64
    0x100401003032000c280c0e8103d1403440000f03c201e82c8051740309141c02141160450361076a05005403640056141019001103003801040c0449019034050f03142421100050841203000402c1621b00605004044600c170789020031b80f110600c2d00640c0c0904031484c14041d181119030190080c0c40c600e06d00341440508050481074032901512002d1720202d01030054406030034482100740000c0074111402e8004088561804d5641894101d0003040e16032107400c8800f800001a500003440031403d1300901e416202d40c0c5030464844001c00c01030014036072000c030000324415100c03e100596450054483c1c02e462102403989000d40780a08013405071000014464402e0181c2001e65210019440305442c2c034440340c04104021440040c00d103120303030f441d600c1070400302034106601500162500c0058548400141c5400030344650f1481c102e10b80d2014400510001110400029000000100020121034010040c00310020348180b180c1146091580c521944188950081c0344110115401030401450b64458280 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 982244244 1250 982242994 982243001
    0x2010204171e28060e0109060b0a0504110919090603050d1d0d0204111e0c070807031a130813030605010911030103290106020729030601030b0a0506040e0f130f06 71
    0x1100c0d13040e543c000c10f0601c59005d101d5008000d00c2014001200800081080303450201640103910903070400018207480400310082e0303240020103030b40d20280502c91042c4880e140240c1e40041c200305240140000030302400051015640c2020b84a10b2042080800080f00081282c070003103400043c8030503000014200366200d400c043d80d40c00a10f50030f00c00070b44000284404401005076402102081100c03007100e0034410340d0020100320009011072031656468110300c0160103c00c08620204200150780c40c0d501013811140144e101c00b0666950a1f04003d101d00704209000c156109864903001080040c218881c0f003006140d903000d41811a0318540e14441d105103214401800c90214400c1c200d4006640c01c2c2c075138041c16180c1c0140004c2c504100640002001d080612911500a0391024400007030305001c882e0021020f1801180d030748014408225803600540c44030340c0101000a0000318007618804007030140c6410b10a212058454071662071800b01030031000341490030920b4841000981c1c0740d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 982245494 1250 982244244 982244323
    0xc1f020606210111040e0903070308220c0e0403110c0328080f0c011404080304120908060709180209030c01180308040303030914210a02010204171e 65
    0x749081040c90104440b03500b03640c5091800403010602040500c00e1244118400f5801440c40000718140011510010600701d00034000d064490900480d88100e52080d44c01c5042180c3c02518080a451b5505501c15004104840607400600442500101c50348007040480d042307940280281002c440003004004441e07903804e5a0f216841d0300c003464400152941d406003214540090780251660501d80c00c150a481c2208d40c034422400c80541004002642c03881903e40043e08252448848445d103082640c0c1e01e1b54030340241000e0301c80c14003081031650380403404c10103640444220402800c800b0070b004044e170160001c8a075050b00b00317008a420315446040c1071810b55021610011400e41d48ae1105c0070107a101c0d030070070350000351903100000501c0351400e804281055610014280c459004004103106010000b5045a540c400036480e001b0710300c01d4050b02d004c0d09801e0910f14030b80c2d1607441c081c1d5440031b02524420b483c0b400c1240040200c500803600c0901c0c03000e240c400c0b40b250014018602403508080 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 982246744 1250 982245494 982245529
    0x30e0607110309091f0b0a05250f061a010905090703021c090503031e100b0c0a1a01170d17181506130204081504020418050c1f020606 59
    0x41c0490350a513540c0303070480e60180c9400007001000820000d002c4d5446a2103401c080c80b926800c0049080b4a0360140c00c86071070640c9a24200156214075850702e043d8403410402504000700b10078034205010403640213041400c403081108040e41015001921a10000e12550350300009210000700c0301c50003a001000c103840d000b24610031080b64100c2d80f0b0111030074200c0035145980040100000900d0132030300800300307011141d030b10000f5103070045a03020406043d001d9244200408100c9204d022710410803942c0090340040064000301d020b010b03401108200348244900320ba1065007801c1c4948005c100359426400d2580c41021110181e9155698690090400f108a03220b01180b40c09080c0c080c001c150a1044803441c01d20f076130401608014490001c3c0b00076040d5107104000410003408000790030003008007414651009a0f403a400010300400040002c0010320203e105583c08110340408c4480ca18042140c1c0610b20042e400c54205403a440b03a9501e1001d6809400412001d141c10a41196042e054 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 982247994 1250 982246744 982246747
    0xc07020a0b04031a07300f02040b0d1a010f08070210050108150105011e120207081603180e150a0305030c010b01120507170c160b060907030e06071103 66
    0x440d010703504180d026a20640f0341c144440f06562040c0c0d1003401d025000807451410041c40c0251260b0f00700b0f01c2501c42030b03a940d9100c0e4094806091a403641003c3c440361032540c0300b103407110f0751403070039407890b81c444d07036140d501c5500c0c00203090300024000d00c40000100060751100245240d212081e14222400703071119082d845003840024030700c6014050396010709800c501400829041d180c91807170b206410380009050000415040140c1c000300d401507110341115141001d0749a0b00c4134400d40080c80f074010003400d400340c00540d6090f00c2c0c13010765884000d10310954884020408070260003411349150b01803003040618280c0402c80b02e0310303820003044103400000c100c0654556640d94552655100213200340069440780c44089207517070861400401006c401c0400e0201e0319050000401e40d484940e031048421034a80d000c00c00d16a42e4000b0380b82c040c1c0c10403074220b03d0b84c035160030914943d2604441030791054041e080001c020310702c64041c580a49181500426946d00d640c0070581e8020000740109180703100 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 982249244 1250 982247994 982247999
    0x807120807060906050c0a02010c020a031e05040f15080a0603080a030902030f062a070b2e0e040b010b070201020c090a140c2a0607050d0609050403030f0b03010b090c07020a 76
    0x40c98462030307004800303d603200b0743e0711850f0007c043c1c02d40e00c403a011001550000706800340800c0e00452102c1045e0030200307484445611500f010344550040c1d800180088030a0b94010440901d20750800e00c1c0100c89417039006032603451404890a40320755001c01807554405000010040b4001e0b0005003006100909031031051847d0511203140c40300845109204035140c085c1050b40440d0110000303130f521040ba585918211450300d0700e0f64408030240c590a001c1020040c1d000c101c0d0101c800030744629001d100181e1459a560001014138041600c00b0794010440d1070000510380c5a290490788483d6040c0c01900d00b207042e00b410400352540041c41c080e00030b61200c0a0810008078902d10038465804620340a44600121710090541169a094a146807138801000003c0b0030000814036803207105860b040c1e80d138203420b14000c00988040d0384155851400c207000d000070590503070092404000901c400304444005c0004041c207a92005009980050061300410644010800104440c0c2c2c005040e0b4000142d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 982250494 1250 982249244 982249253
    0x10e22170714070501030c140717090a03121404121b090f0203190b03060c07030c080307211107060203060a030b0403170708040803130501060803040b09030708071208070609 76
    0x40b09003108600340c118030014007166030103104003598068507152058110414000011541c400c038103001d0002c071140c0b020848140e90190407691a00400380a00c0100795482c81c01c4003499024003030110101711070031940b100c3c1c0245c000a980450341c0d103411800c1c1620580d1240002c0556640c1c02501d1a820724101061803074040c003480c3c1c452000604010380da49003a42c0d003610060404025401c210b41010742802850340c0014641e9004101c0d60005a40e0b040c42e03140c2030b80d0901000c94001c1c09100e000c4200312042d038010207141c110100c1640d4401d030005034401d020040321005050071415110a114000c040f40666005e144d000301c028002c1c2110035100e4170b4100c020102110200d000a07004443c21800c00d401014680e003210302814410340b03c0c10310381d640c3c400c140402840d0059110b0b400440f130b400d002d02504044001d00b080700070b0b0782d51981c4501c4545a698450040103000b440354030400511040005296001c969112000c1a030415041c3e0302c24140c0e07800408147d410540f26050350001c40e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 982251744 1250 982250494 982250513
    0x80a030f0b060f0711040203100e0705160b010608070c0506011208090a090c12060b27180a0606090e070c0807060c03050103060f020a0c03200a0506010e221707 70
    0x4443d8105002d482c0d416a00c0c0140501c4030020700d40b40510b006000348000082d034a4100c9041d1940042c40704940d945448007250540100c503960001c201c0c04500c071b1018001451400b906a52403079845024a9036606010703181c00c0c2000c1030003407995102c3c000400401c840c102e51402107a00c01c00015150054680000383c0c0a070700c40d0001c0c9241d0750b40e00210302e080c5070440e00103095840c2e882c01c1070100390f01c5c0800345150390241040340c59000d00f07406414043c011500d5034092104400400c10004400814068145094111110b0410900d080b4000c0340640c01080403100304c850030903171120140e441ca44111140c10304603e045a01c2c4038240080c0e0700044980c010b100788030a55990010311589541407407010794500e80c03010440c00c0d10400c104138809501c00c2091000701c0c3c1605100c407800c4000e035103060101034503980400440c018075100e0010414042076442c101d44120841441d5070b00c1e800c1928007143c000ba034030651100303808200a0300040d08803800e03e12942500c161a407e010342034840f031595 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 982252994 1250 982251744 982251757
    0x15040e010c0206180613030905060d050106020c030115050d03030e03040b0c070905060906040e07120b0a0b18071103040e0901090605070302180f030304031a070905010507080a030f0b06 81
    0x6075100c1c980e8184096040212550190281111039002803c242c4900c0d181e03000640040401407034142d0080c141401100c841d8018407010349001c6d51050017034074203001014280101c070300600402c050304090f49414010124414801100c50000c0e61610041003500c840d090ac3c1181459100c00c0300080385002072015000808844140e659a205031266040c146001e0342c01c4682c486141005001c016215207941542c030007001c2c0c030006084218000014030f081da5552214040d009030101e600100f11000b5100f9008955210b401d0003441d61b25030422158200304851004544412400100c4052080c0038007080c015070071703069034505511410040d92850317040b5000c03882a034490192030108106441040da00c441b084c41c0c118100301c0b5082c0b0b5058010038102c40188510015440030750070b40c0e03003802207400841d4003000141d049283e0b402c0d01542103038122109404078900c04000540c65000d07034101c5640303542c0050a03500d448455002074000b45034102d0401002d0350780b14803040c003544640300103045 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 982254244 1250 982252994 982253021
    0xf050111250609050f0a050c03030307081f0e070e0f090603030a120f090b01080d140f0c010612032601030203060406020318103312170301091d06040b0f1504 69
    0xa0301b00c2d1303418401d1405540d00c4402d03020b03500800400c130010780e00c6a03039580c00510664018850b0031400302c0c0000500303a00e400c034074802d1203007505101d08180c0103200f02900304c0b8292174450001501d84104103c04404451413a016001041603950291054140c44410071928800284c2c1c0741c2c42107504401c41399005000c4404405900051000a030104624084150240707046610340d12801c84103545070007642100c80e01d074600403d40d1003010340c003900200003500d1b642c400d8403415006800c000f0318500c00b0524005584110703108010310030050103081030680750040c00400142e00c80d60f070307104001e41c4024003d21130311000b0740244210183c14007104101c0784d40c8600100714104180d080002500313504101000c00d001d4040105040044003049000701d40780721010880381181ca040c4800c000a48505070000968004004652a20340d0340c00555490300a80310740d4040058210380e50352340c071010398000e41001c1c00b8000003140b036920b10340e036141d20051000e658100c0c90303480e80c045415500d14202001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 982255494 1250 982254244 982254253
    0x20f0405180f0304093b1f021e030c07081303021201140105040e06040209150d0804060f080705090909030d0c020604120203040609060e0312070f050111250609050f 72
    0xc0b040c0034011010f00940798038a0f5540005078034042040b054015a0340711b80d02d00300f2900c2241200303050003a03c0000c141441c08100080440300707001c0003540400e03503a4012045500e030200383c041c0351900f901d1207034125040403894002c01d80c541c0c2003207401121003040a01304201d0301200503200d00c2328141e03000c00d200c400490b881e040c079000d10041d0b000503003003303004902e812807041d0001030015005401503010383c1d0300340305034481c81580e102d03429050481540012104c8400410400280c0003041240d00603a688040e5081d00321080703694403000d403110b0f00000e50a000000042c40c00900c0650003008500c11030b032810f001d203d03000050318815203100d00036030000d10411040c801c0301144110002410b101843c61b050500c03002a100f0242c1d80100c10030440300600e0b40d25240ca0800265907002c82403c10340c1d40b5010715150041030b50201c01c80c1102c55508104800305266505020750b812191505106030352000c03007004100070300021003815a402501c61b42e0400120740240043c0c80d40004000141 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 982256744 1250 982255494 982255499
    0x60e0613020a140304061b020a0c0605040e04060c2304090608010b061902010603020d08070318180b011404080a031e1b050c03060a0c0e030703020f0405180f0304 71
    0xc6100d01940d0311104009004220084507141c0c0081c40c20506074458080d1516510f49041078001012001003460400c500d076080c800089400103440b02c4064030840710f540110351608030884a60155201d42d0a02200020118001a40c6508410010405440d00010075150164008216440100098107062001a0600101d040ba008100151908000034407041101501040141c4901042c5461f501040940503210b58400e41240c401950020445070f042a100d003802206a40050005c50114405410840d108181c10500000b11010303440e0501d0340d0300400101c003000c1d00da82c082c070904000500c001240424940000b0300003400045000302140d05c01407030b024102113440c90750303210001c103610a280503541c0e00c160808c060f0010240c2c00c111586039458100e00d04602017401542c075004040c200f20b54508250b00440c180c4103035590700c00b41041703544140340d220340003404042d400131030050300d801c503a0800e60130441d0800724550113403144803c01d4003002e0400108014440385a007001408 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 982257994 1250 982256744 982256749
    0xc080d0f05093702030a050f010b0f10020a03030c090905090c03010e1b040207080702120606030c10080f0603030c0307080c0c1f0c030210090303230103150905070504060e06 76
    0x498010100080f45071a842140340072440850300602c040f90406110b03102c60b00464805028a04049a000003114074030501c143d142c50103011098000b50003041d004079220307401d1802c40ba403d21a080b030754016020009d19910101c0240150425410510440c450f0000c0c03120014413940e8440c4880c40007a002080d001c808041c25500b901011440c07607840881a89030032141426007103466401240c006a40707a40b0352901441500552401075801101686074110000c804079059124100c1202980e0210885e00100a2940d50700c06094000400c4000042ca0700c03208020390b10340144000741160b0400d00c410031242d140d82e0220404403652080413890003550300c010002c08000c00c41c1142c203a46020031070441800e0710303006c01100c03c00300030101104006050013444504448000454184199500d42c03d0140241100180703541c6840304114204010b1044900c10741d060703e9000030302c414540021030303030000600109003043e07500e4011201c0000b00c5a450b17100700001054688081c2103a89001c804 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 982259244 1250 982257994 982258003
    0x303010f08010b060a0c0c0504140f0906090307030305151005180103020a1407020a030c0807180209010c23030703030608010c1d010c0602190302031b07120c080d0f0509 74
    0x50805070b0400f020075956607242810f41e00100207914080386807042600744104064060ba216580280c60801d2060783c000750302032040e2290320301c00702240c02c9884296100fa0341e604111045e0f030040d04107101400000e882038021940010101c60b0904030000c040c000103640d40c0b41086118081440010200101e1140941e074100928003403c0840c2008c103021782c081c00754081c415103042080f8000a0040842d505d1103840c1d0090740c0c2103107a03100784540f07600c0500d0b41c440d105e0003558000107000d854000a0500780c000c64002d40b406954664011265980b40e0802c00c1080c013550b408882e01c4000c4e0144a81c0c00c001400e111400796902045a61900040e40d00f1a0240300000d020131201118514212100d2840303400300301030030710380707641142181d04104c0c0c001d00800107080d00c00311130951504082541500558007030701d07c410f20300f1524001c82c42501050b101d00e000044c07210320403210254545000b00b400c5031103240a9484985060f81c405004030454542c090030024840c8d5510a00810110400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 982260494 1250 982259244 982259249
    0x4110304021f09060c03170108010e0f031305060318190614250908011b0e010c050d080a020c0102340b0f0901090c030506010302011409060910030219020303010f 71
    0x2d4541010410000004090428074007a85090010402161040610690078100d555064040740109542c4401c15180a0300d01008046c0040c070581c04854518540031046444449810425a070391524010a01090703410040107001140d20041c030301104a03d050024054100f0111445400e585592818404032884e00184640c0050f91104001e180d00c007100010a81410b000342b8144645450401191401c8080d0003c0080e035080c800d409050302801001490b01c0d44882e20703905001c40c0901e004589056100070060701941c042030300c00390003600483c1d45640140342880302515008603100f080c2c1c00c0ea8071000440440b2000d4048a0342c104a07000600c0072000b29140c07640d0742c2185284c9807626003a0020300440392010460700070842641d000d501c1442c48a83c0505480640380d84d0742885a00d81c2c2d802d12059003c962415011189280c11004589030300f2401030256003402c4890b010711010402d54003400303091643c20440148140801c1c606002100741503402903949604048085100b1421503 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 982261744 1250 982260494 982260529
    0x7080a061e091a10081f050f0f041107081c05061305040c0302060403050f120313020108101d160e0117040c0315091103030705070302191d15010c0305160c050411030402 74
    0x120001d100710b544010041e043c0c03500440d88003d001e40d0502c0020000c02f202c07465020503a00015241c401c001c6084c001e0720f100d40c1800303d00c1d481c02c0740740c64a003416244111079180c1e1182904440c284100031790f510058120f0b02038a83d07002480e440e5030105d05603520980064410390711040700040126810800c0001400140301d0075400d40c00c180307a1104071200d41c8507000b41440780110020750400e0600c00c00c000140100b0280c440401c0f50000c240d04a248192110180c00301a50341a56009005216480010f5410b82d154021a940c09008100d9041e0207441203405407440380001011410082200c5040da071300740c03030014080b40e4a1070102084000401c0a40c02034005011a001007940420382d50116601a04d00d000310340d000c00034031035a807421a046440a0b40c4a0700800444240009a00f4816444c0d000d0041c460f8845100555031215018402000a43d0400645070b5400c040c4d008002654403814200319100e44900028040d070304101103801080c0d50110402055140ca072090703d0318151807 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 982262994 1250 982261744 982261801
    0x304050603101415030604090f0602030a060f171509190516050a38070606060809160605090a12260a0507080304140607080a061e091a1008 61
    0x83e01003a04c42c0d0100900e010700c04ca90f1201039030103000c5201d0150790f00540c401e030110b589103130500d800c0c8010070643c00b42ca600980942c0002c01e00c102c640d10100c0140d20300c0030080c40d41d140803010007420008001c00c40700c2c440c0200d2410500c0004000100040c0c0c034411405002407240440346404c43c0304142d0f101604c01c1c0d280300403c0160601d242182c0c0340010031661b030801c5441c40b40c031420503442046140c02c240d00304006104018032885502100c10340f0744503a10301020b511840d00c0d10b0394910900317801c001152281c00080010600980040c500c284001d480400823a41d50045110301c2400d02c071084e2144042000141d106240e0300c0d07109501e44c0d423641a16804e0050709500101140601c200060980b08008081800d00400b003003078440101d52170003100c40034986054000d040f440103541c2003c196050000115400c0e5400c1000800072195800e904c2066291041c00400303000c10307495540601c011040a100c0035112218944148162608c0b07071440ca041801306030007851400c20b030700410100c4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 982264244 1250 982262994 982263019
    0x1b0d1a0115180b03040201050403020913020a06050325020f010f0b12070e04030e040902090403030c0e1e09180d02070609080105040213021b0d1824050a0203040506031014 75
    0x285442c180150f603207042c202e5859507114401a586440b907904060342c400d00000c1004a40c4071101d596955480c4240d078a1080c050b034403130044da1700303000940c0c1e850310f4041032400c0c0c400e28110000043d908901c1c5403044036102c45078001d08c9802c6a9140030a8020315803500390b81006030418a00c100c54071503204000b01080c0b071501c401d02c0c0d880c84000e80000e003041000e80440300070340c1d43ca81044903100e80003080880a07046c01e1034003070002e0200700100404104031220000e03240c90704800048403081c034070a03103200303040c080070800540407001082ca4013032410101855440580801228603960f0058005102c22400c000c00500080440c2e400342c80d60781c0c10300c1c04001c0141c60344040c041082900760340250321848066041d190320401c5612618076803003031850401d021a8003141200048c018186078101250b19542251046009000c4040c2d20007940d844860000d48108002c00140e500c80c4107607400d01c1d86450001c0d91591080c0c680c002400c007400410300803a09140e1800d003a440c8100c4004030081c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 982265494 1250 982264244 982264277
    0x50f040203071a040b04060908060708040b0c0a0315030b041401020a0906141b010510290f041e0306050708060904062301290c1b0d1a0115 61
    0x2c02e1401021041803a00030090001e2080906130350207003545c1c030700154546480302c00041412a85100e40f0042c3d2062002043c5124000d0341c0303a41c0243c0d08404080c4050303640921305262503000c402010308140d40e031003545203084444d030b20f044061440782c9003205d0f0605040c1062208560f09500604290b4810000c08070803681000e032810407501241001c10005400c00800c00c0745014003000000d0020030710100340e00300e03801075001c0c620441160b135040d58455103420000302e07400300e45c10300b4182c20300d003502108011080c18001340141d003443c50203aa141c507072903120548804000c85000c032410541c000090003000024014558403203101c2c54000900d141840010702070510285c8090101c907514184406d08000504d40c0c590940300703940705100385580d5100341403410300c506400c0490010415400440e8124a2000c07034904400c14002490003000802c1134110600b0f8964400fa80203100c48030f194002068030585209040031000d07030007559850403403221445002c100081080025402600c007094 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 982266744 1250 982265494 982265503
    0x506010815100c020612010f0902070203070504021e040f1401030203041e020102010f020c07080d090b0f03100317071b08070605130512101406090a0e101a04050f040203 74
    0x1d4408944001545229800c1030781c0c9400c602d04041d4000100090041803600e002100c0c41c101d0f2440c4d160040e5071561980700720100d0050010096164000f0301c1c0401041c034050300a030003d1101e000601e084110440d04078400d590199011009080011500b045518136020107039910780007e0909601d546015510042c04040b50095661980c41d04030294056900c00d5100c00300382e03c00c07080115503a11002034180d83c0d1b60780511074402244101c0002200240c07161030001d044540115405040982e44140c64407035400041420840e10005040003001c901c400480d0100c41181c0d0711419503034010b41c1000380c4603c031200ea440d0300d5041708a5042094070000100c1500b160107a00c4c1190321070703984c8000520300d01d0710355001562080c00100b8601c3c030321502044881800c50013020400881040d18080c2501010484e00030750f02646080002c2c10222113038101200194200d0242c407070501e429020302c4100c41420b051074099030104c151500143c00d0900c80d06410201140740204286001d9002039540c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 982267994 1250 982266744 982266781
    0xa050c0d0209163b180c2503120506040b090109090203030c150f0a06080d050a0c02150309160305060a090c0b030a0225020f0103021e07120305060108 66
    0x9406055148400c0a201302d001000c00c1c8911820f890380d80358900d151896001c085071850440354401c0840744841e180500844802c40c1880601d100107030b031070b901c1040041c3c000c41c0304a09958020000c40c0752180c0710a0b00445014402d45841603000910503146040780c00040009005900e000c07801c0c0750b56903441000a044448612002c91201580e10201e800c501401d04010441e104129582d0203000e10603058501c218040300c22949281d546140000540705a4840e4070076503081440c42003201d512402c01440102c1d66400c0000c00084c05901050fa00d001215072800500c0021042c4115400c09111070f0714106440301c5e07074040c10790951f00c4880d1030b8180070b0050355070b65a9032980729080090916030000140151014a9124600054450042d500241d0101074008101c10f4007520f20010441c0c14940a0b009020a02803580d4480154029801203050703040c441e4201c1003e4030702c0f0040000034140d0314800d440081c0e989180340c80c042c058481c068001818001d5400820400c107080b8841c00e0300 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 982269244 1250 982267994 982268011
    0x207050603131a1506031b070c0806180f0d090b0705120703080403020c041103060d0c09060611010c0302121513110705120c15190606020a050c0d0209 66
    0x54984a07009000302842d00c8040040c901d444154603a040420b040e51a50310501640a40d2002c1070000c808000c07152204a40d000000002c00740b540c15440d1016010341111440384004e03010042d11116010f291500444810714003c4016201044011040c0041d910880c504001490226400d020250810f9030b1070060711101000898168144501040320f141e201c42e17003d102994030780090070010500354045034141c0162040d0b00350b40e030540c01c2601c0b407181002b2480d8103407402d580350300c0300300100d00e9880038090310810302c52180842c110041c2d128807801002507440b000ca4002211150b50300390f80302c4000720818144140903080c42030a400010561120910340c00080381c0034070100098280700000f034034900c184c3c6004001c071070b4a10b06400a00419006004946500708010074019991281483c414000c0c0c000844a400411020040c1508500d211000c0c21a100401212204842e42640003000507844240b0290500074284212034a0040c151400c07512910281c0118003002c0d0054141c54 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 982270494 1250 982269244 982269247
    0x160f0b0d020d020403143706020705010e0708030a2c010c151122050609040c1b030302070317010305210d05160e0415032a0f090b0607020102070506 65
    0xb000801181d04580146074000c0160003e01c070381c8550980d50f20510803800490b02c0541d0b140c00101130b0003e0441e00c800072034a000d150042c6050fa10344000e504440c400322001c1d03485200800f040701c028803107070010302a003400071a264106004000d0118041c00c10500c00d4a4001e10030f4202d41e0421903540401d01820b007004800c14200d40760004582407011070080e00c1515100081d540714140c000284032840c000703c4070b025204040343c81007501849902c14168014010441c1003864107241e048802c1000660401c6800602c42440a403940b0304101d90840020350300140c02400c041d0802c0100c0b1081440340700d40981c640c15691429074802c6010211890004905804010000c50320200c1c2c0e0007044102091106040c207100c1c51100450318284100412181505001e5038181032240500da0700c0a4030502d02090325680329844082c005c111440010580c14056403032040310590032200400c120700514a140385899104400c44061010045c0305482c10009440543c1c0c1c00540c90054420403900b26 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 982271744 1250 982270494 982270507
    0x120c0d051c06090f0c05130512030c010203131e030906080a060803070507080613150905030c0d0503011e0509040b09010b0a0602031e0421060b090108160f0b0d02 71
    0x20140200c0710600c2202150030072401207610107080d04080c4034140d010006002000281006449034000c44c3c600c1094401c40842c10001d500c1c4c02d03100810540920f809480c80c01418041e55400d9074021100d5098405054201504009a901100c0000d580286810301e4151482d0f070010210056807042804004180e004604000e505a210000500001080300c0c0d0354005458843c7d11000c1c28851911035005910014011482905001c40507030380c00403801d0800c040460000008291400094030148802c1c0600001c904042040c142c10541e1742e19000e84942c50821154142c00030070000c004000d201d000100510b032580d111040d0065407005070340c01d555942401c01c5004052038259280c3c01100081e002803581d40100061080d0540c80180c41d41d4004802a01201849540b0130800d03203040d0400503a4191141081115520b8407035400858038039181c0b4005a0781301c00c00e80141405030003052401e4180002042e65400918250b042440c01900c0c05100d020303070b8010760703a40e20102500081c40 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 982272994 1250 982271744 982271767
    0x70b0a02121f0f080a020108160906030221011e06020a030c03030902011e0c03021903090308160b04110301050604110301050d080705010608010e19113c03120c0d05 72
    0x10000f0348500c031402c10780e5030b44e241ca03440e0307403400c00c40400d81c007140040e400308030300960a040c1104a41041e440300c1d041d003444d10070300300e0003980003200e6440720849040701070580c041003134440c0c2d0082084d2002580e001000c2c5610741003000c0280d10403015544020300f402c000942080e40c0b0400c5075010b060025030300100b8001a15015a1402c0508002509a92a10756039400210050816004c1da007115849500c04807402c250185091010f00415000d1070308100107440c1070001c00454058401c11461400c03a0b0b520003580040907101101c03000700c0e604459a8500742403050785d92114048030103128034400340861448511060280350700a0010015030014001c41070111401d080d40721000b00700455452000718000c1c0482f000700c1100380134103100001c040e20110820ba002581152501c2003840c042403c0001000d600b041204640d03101c206514441c4241d625541d0003502652940525a0100f604147c14100d00c00720100000d82c1c1132040c5501d0400c0002c03001001c02d0981003075940c8008002ea07 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 982274244 1250 982272994 982273051
    0x13051e190f151d061009021c150302100203180907030e0319090519260d08070e041e0b04091b06020705120d0f051e070b0a0212 56
    0x8000c0c000c488100b03503107100c41c0340540c031022815602e8a001c00b10f40280c1c0c1d080c07640350541610807200c04c2c50705500501103d041a8000c04000100c25900750300c00b0b442085070b44c1a110340b08584000c40c444490b00b0020b41c20514810f0602200c2c510156241c01004d14000440c40c90840031107004011240015480038026400755076420300c184200d82d165051041102c803070084d56601500011114440040c0794203003d80c0095404001010309500702d03041141ca20603103801c401c00e0300400e442c0021801444802444400074645041c1e6400341c1c0b6241200010700b81c1011002c0d07a6000e0380c60b00e44172305480076480500f007103030504414012a030300a16000240c09040ac44001500003e203201d299101c0400000348601102d282d60207640c6034a51f900c0c02c00400020600012010342c1069041201041c81003500d00403528031418402d04224042212078203119420000d440c04040c00540355003401801000300b07030f215050f43c41c190310b03218804000914440340074254a0342c051101000300d207110781208 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 982275494 1250 982274244 982274273
    0xe060a0905160306020415030203010302010c030c0c15030903031505030c12150f010612053d06051c02040803040b03040606030f06050f0708090c2713051e19 69
    0x103480030b06668a03410403600951051042c0c41d801c0241982403800c1c03600038000d4a048a030161140c91180280d500c056800b8030598008a03049541c4400c0811803d40b0030103005800405075400244540e41807401034100c0b50807000c8001030300e05c0704008103d40d0780e0000302c941061740d0542c2c9086a5004075810030f80361040e08002100200134440c02c0004540d007242d520790407110309540344096400090400f10803500199020a50610041c0050540c10070300700405208402c3c02200401110325044d5100b2259020780288000460019402004000e80d0103504072f035800c640c60461070140380107100c0ea502e104910903000703c1000880010103020603540040c005641285059003558624a05207005100480d0410610344121020882e02d40c429085640328035130100050074200d604a0401892803903c101040c00070301c01c030201c001d501100220840c003a441484036402c00800a2400605005403540e80c0307880c0b000780010440614400140a900010b100003000d0b402c90064101440202c5408 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 982276744 1250 982275494 982275523
    0x5031911090628092f03072a050a0501051017060708060307090f0f0f1b0509040b0d0623071e0c0f0c0609050609060306090606090a140109090e060a0905 67
    0x1108400300045140c0412220000103581703014985407040c202101400203a0701007002603402c60818046165080c200e108088503095030a100480540d00d00d8a0104401412a1142d440b0400d0005203500c00c0d1a039400340682c415a11081c008141c01c03103a4891004100004011680c4003261480c0c8060090801400034403400b885035414011042010302428075501c40e24626100c18a2030f008214401c0d40c42084545180d8004000c1d40e880407513883c1c0020480760340c01a40c403031321101165590482000300501ca400c01090721001312121800c880700f80060880b80916130410040e01c03581c8481d0146c424030800704060900c1050760011202c0c071030603007002420640386071018418008003e28101c212180c550b039a003801038070303902401251702688c00402d4000c0d209001161079840c1042c081540200040c1c186070514011600043d0180c0203030703000714107545e0803014050240d64002204030184c04510824094800d20012450380d03400020031036410310b56280e250b6002c100092040244010b00d6 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 982277994 1250 982276744 982276751
    0x80c1602030d02030c160815061c06050a140603030d0c050f211501140d0f091505090304060c020d030908060a0218090c030106180503191109062809 65
    0x3215010b544e903030003200011014031820402c010103119031800d03481a80c0040014200d6a80d00d40c04d851003607840902202d512140d802e804144410002e9400001c0743d00504010681d82450301111048a078401e801e1110450510300b00403c47e1030020031211103c01030300300005c5000100808a070180144141c0b40d01c200c9000812540842ca01000c00c540300700403001e01a443c2d1107280400140c0408240b01502103880341e2004a0394507071340c0c005017088605e024000304c1c91907a00f41c40141207a19004048580348440c21a01d8019201d603c82d55500450580041d40762905000c00505074002941e4028426405085400c0c20944210360030001808120704407081c50402c5108c1001039003224504a60442e0082810201c920b400c240fa01d0044418462541c03569003000801c82d108006983e40c500d20061401c00003e8603241040b07038003a2404400b600e100320001c3d51510603903140c1c0e0101554451002c4205100030b0380e03102c0000400161101e14200c1d80451101c00e00c4020701510b50084482074074 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 982279244 1250 982277994 982278013
    0x3060b0a1205090604200f030d020a0317010308030604020f0d0c110f030f030129070c03022805010503070912050606031608060a1107061e0615080c160203 68
    0x40007119603148100c0d2107028010355444062696443c0411200501602d165013403010521950b00500708007998042c2c11b8014440200d808285442c05256003440164006241d48040c0342e803041d81e0488118411052030080d5141da00c54281a0101030314440c0328990001d1010b0307984e4554012281c241c207410005000025602c0c002821001400103c4807a030f00a0b03000e150b0000c4400f000b210030f40110a4201c43c116400c042d00f010004080c601083c0c40c18810a1a44842d12103c001401a0074450307061044414190b105000f240000031845080c80c0c0d107d0140317641c02d403041074154801c1c5c0d40203190081d00d96403159000ca03550342c8641d00c540c00c030100d1120401e0600002180b614030450040e400c5030285079001079404200b007018803d090b49904014080f505000190304030402c00c44040d8100c0d8204906174490904071020a58515490004180400051411401100002d004880035045165100e0002410015006001042c502d1000a03d08a00f580c00d0380130403d140c1c4c010302203908142 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 982280494 1250 982279244 982279247
    0x1120504110a061107090b15041710020405060d050421080f07021614031c030207030e091e06130903050703020f0607090302090a0f020c03070323031603060b0a 70
    0x70020a2814054080400d0104000e4042c0c118024000040001011002d1626080c40b0081200e0f4082d240d02c80091400c12541c4103480b000350020b4809418480d07400e940c00e100d001e1404000c1e040650044e401400108156580c40042e10b40c0c5081503000450b00350ba0340d152400c407074402c1c0e2107010104600400911296a4000c02580c07160003503040c03c010f107131903151082e6603d01c01c1441a030449048080148528031100ca0100c0414001504858425412a040e030010341054801c1c940000d034003103403030803c3c127600950111205070180e510403814205981d0b44c0c1003031001810300e031245022540200340b0b69214a000382c01060b009240070001c03407600b49001860b5511680342a0014440d0008603090a0800f0a11502502c0b6689992032554915400d22205c01d60051500c0a03040d0348954019080385140018824402c101c0069680c9070400c4c139003c6d0401d503803d09902c41c4560140b205c7c040c2c2c1061441181d4010a0f10440c0c0485014400d40440161005801c0303c00480b501080340075403035 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 982281744 1250 982280494 982280513
    0x3110c0304210203032a0105010303111507020709200a0807122f1201060f030f0506092e0f051c050a06200c0a120c0510050601120504 59
    0x1590010802440140886042c80b00d0001c040006035042e0410042080c03507204a00030160854a0b8030401400c0c421401911400c48009a00130b902050050382c03400f1240b2402d1200c14401d040414201c02141054007009660342040d014081d0703002da8983d09009411481c170104000d0b4010b010150356a1140540000d103516001c0d0740d4500030030203240b100c04007a602d501611203401886502d003a50078a10104c12080440040c46001c09002c003040b0025846e080c8282481c087d00c3d1549a0075000d0420100040480301d00707490f8030010754544820b200140e4ac60404084d0448805000300b00f22940301030b824050f210b68407000c10080300d0281000a9083c46484902048650454030010310540030004410510501c10b80100350782c009000102c0042c4081e846070415480030700c006008030709070200d8040701e9031150f104d052040d4090a110020003034900c0c1b90194070354051400b102502c1d0295a01d83e500c5083c0343ca0b502030203882c1d0700058441c0e481001c1068640d650000184254141810710714540b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 982282994 1250 982281744 982281749
    0xe010b090105101704061811010e01020307050606101806031e0203090a0204050910020a2a02010203030109050a1401090207121803020906031009200a0f060e0103110c0304 75
    0x24045140006028500302e542c40e8100303034040c1c03106008209184c0320a00c030a90010300440e0401e1755031810705c10b500780d6000b844003120700c1790f826072081308030351000504450801025241154002c0281100040d00421410b0300141d06603035040300714503841d2090343c6440800c840288851121100011030a91503000240c180d00380240780300500030042e102500b83d1000b00c4000700c0503401a6010001801d082d4803060780a0ed01d00b003594240e2001c2d00c80b41d002d0340c0c0401c8401c400203115039080000d11040980c10102a05d0307012140844090300da0010391680014400d51140694402c00610529010f81051040e134042950181c02d543e111180360b0000d400130320303060382c104000600420056011708100e051034802d4180240102c3d00e950300b00700c02c50800500064140c060710350700d0303c0405218000d007010300744540c1c07010350941500c000000e40e13488100c5d50702d4441d140b08070041114402a40550094070498640703403031120481d10040c0c025000348000d8440d0040c0c0001c03110210030b800300c0a03006 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 982284244 1250 982282994 982282999
    0x90d080d051003110406030c0e07210c030e0a0b130602041a0403031709030d1a030a030e0306090127140601090c030f021309020307090e0405010b0406050603161d040e010b 75
    0xc0034450f90a1100700c91b0345000c0140910a841d00500040103801000c0754082d540e0300e44a82c0c002d499a900d01c8030300500d8a400201d00703489040021166416008068611019030000d107041c0b5584d48601101e6540913001a001002d0307200721f1f000f0b11000703030100e40207480c2c980c000091501c4042c81200d0603a000b8801a0009000c01090112030b80c180d04d25503010b18000e90082d41080140511080280008912090545001d0010305030580b018454581c0c814040d0700d41c40004041c86081c5414440000c0000c0940d902d03082440282034420075038214203003004a03295054035801d1804c2050305944030010480c0d44540000018801002e801c94030703941030603139420300c0314170500307104030099004513a0048660700303241d071040c403001e51150b001c2d43d4008001d2030080c44441c3e840002d0221140b00755010749075070351602e0f01407041e4202405a00001c1c881592503070b10714506641c000c407800083c11420703000c01250b40b132812406600b45112401a180003801000b100d4440400d1a009014001600d130 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 982285494 1250 982284244 982284263
    0x30c04171f0917090613140103180b04030804150911040e0a0201050313030509060f040807050d1113201201080c031209010c170a1211090d080d051003 66
    0x1056802500a10000700d51282642d41c2c01c0c410352240030f14642028441c40c1c0c019400348499400c03900c0d01c61410b17006045180103a1005541034000400340d5100500442c88003c40c191110b0001d00f41d4059240c0c02a010700d842d0f5655140c0c0d203840a91803904a00d82201c80b4205881c440901c41880800042e01e00101c40402c5100001d060403902c440500c540030380464018400991000220b144110041d81701e03243c42841c2440c03c00000c0c05c160840000c8103481c040101d0103104078007041000d00c1c05000112000c0d41d525a8680d074000c0c510b103203c403006018a00880074040103a0064104070489425505207030b030602e1008605441540220800f07010500c107400c00000e54040218101040c0140500944a04100c500042d0300580c03111000324100000d040d6458046481b000300071003c114448410340d9511102200109502111031340d80440c0c615164140c1c0c920b02120049980c0c000d801d4a003d64120264100480c0b035000d444000141036090100308454020025440d10690b032241c0e2646 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 982286744 1250 982285494 982285543
    0x905060a0b09090c0f0316030f1416180908180f0d030c02011d0901090f05090f0c13060b030405010203061003020a09050120101a0f15030c0417 63
    0x11004040503110100190414501e070021802c099a4002e14600c0c0502140c801ea503810790b8080e0f1507081030740149c40c2d04480785404002c000055810305224401078005010040840c9070b0742c0c2030700d030f4030b44202e140c4039101c007003450104181600301c005100c0d00541d03141d032501e407a44070b041e60321030307622200a10231907c01e0310a800c90302c1c003002e030700080c03d0309583c40c840480140c0c0d0054403e00104000f000c074040b00d103034494000d50344070600d4502801108034089164010400314030241c03400502824002c1d080740c581c20451500c00510314012030022200040124015a0101d000340000e800c04840c0c420000100410711405400650007580300380c0301040d1901c03142508408a00511440d8000182c08140800c07403903100d2004c06070a0101c00c0d50702c0070b0316840020014a844895002d21401030788844450000803122014080c0c1210107880038034521014400050038822681e540c20030140b40440400d02c107954140a07100503090b8810416404010383d25103070b42c0d911030008241070000040c10740d0b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 982287994 1250 982286744 982286749
    0xf0516110a080301030215040824370b1320040b040e07121a0114130306050705040b180307090b0603061002100606030e0c0102012307120905060a0b 65
    0x324031054100b840300d41140d0840e402c0182030491043c411100c10703414040440e503842c080c403800301154054040c01d40c0ca00980500401c140200501c002d8088405602d030100c010641003012004420043c50426400240042a401404240000c0303800010f040b2070303003c481806038001c1c8041188207000034015003901441043c4c5108601501d050314000f4001086001c940c05016600000c403070825205440c204840d443c111200c204d19524902012800d1140f0b65802c08a071001c6000040030a600d001100b005103901c0080d0344c400108680c0da104001514035108205990140605114603540d8288085030a6a041a61840c0c80c3c0710340504800081c2c0200c041c410426031800103040300381999150740400100c03d001044002c11750095002e182c080c0c5840344502d01c0035120301e840015200c2e0b48507442506c1c24240d41704817819a89805000402030750501201151142d0f82000c2d0030140d0781d2960304452001410902c07500b254101445d14040000200d446413160107445010030041511108 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 982289244 1250 982287994 982288003
    0x13060f08070512060912090f040908031501030e0307110f0a0803030a0e0304050a0b0901020c0a1d09011112040f0203030d0c030e0a020627031e120c06060f03010f051611 74
    0x610300c0303540e07001c6e00c6040030001001010300b055a200400c1ca900c40c942e0040850140c440245044950600c00002c00c00d00c0c00070044400030004c828038042003d5140c40003450758074450f503440031f0996406181d5480d160307500c4080094042101418890a8a80c1d80740015540d030003e0350110280da003000c505010300c1000205850032104000c0500300d04c1f07450304d505280c1c26401a4001070441c014a84480c0e1291101c2604000505a0103120540f41c45541d03e42018880e003d0b050040d0b030303418001e4940b07030714103100c058555542020203407011070385541c60020036501c6c1e00c1d0700080d0540008a00503405117603e601c20b40d50400c607900c09210340c035005c50321607445020402c4d009521480602c42c4003e80d00c1031106405000041c0800340a600801d000000d1030503840050f51440c424003203050301c4803410701303000c2000035008142c0b00a00b8444000e040c107485a070010900c074041d120010800c1017075902500404480003407450100302c1810882c1041501403080d90084000c5a4500c0141c1140d030700006 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 982290494 1250 982289244 982289251
    0x40c2106020a110601032603012303030c0a060f050915040b07030f0f0203010302012a0605151207050907090b030604020c15130c09060303050913060f0807051206 71
    0x14590840199a955480094001d107106004028141c15440840001041094040d60064901d203481040d4800b03552180c0c0c20710022006100400c0c070041000d40128030092005050344108400c241c1405000310f80b542c0100c498802d0a441443c440c01d00b441015880902c41c1d68504a0600941e034440c91201d50300e0022803d181400c9404d1b42c001000304404281883d000f070340c90b18010681014418201341681d0080c1c110a41040e40007004004540c1c1001002095060200d10040e6207070a0711241c1c0d5414404080c05050140c0307404c0001e05c41c08415003801c01100c00203215600312003092502543d201d2007402502e004281c0d400c045080345025055a008488100725200e145645146c00e01c400394200a4054489101d507440c8038070001d00c02040380d03204001c2008205214000703424502c600d4500750303101d0b500d994640401840401c0e80042142c16003c0c0039504180c1d007824015a60f40207145681c041b03c0b89a121102c0401c101c9070101e8084202e450440d180080c4090900712181c0703958003039 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 982291744 1250 982290494 982290539
    0x40b15060c030a0c1e05011d0f030403030311130801090c0501030b0d14030702062205040b0f09040f0602181e091914010e01061106151e0303070b040c 66
    0x780710004103244181c869008032485174009200310400c4032030724020342d1007600c01115165121400400414525607030a40c00c42c1c1420001c0010042c0c0c2c0d005252030b4410b5000c09000c25445103c40c200e00c8240500300c42c1542c1c6095002081d80d82d07035503c8a8004c04007558102e581030407442000485620a0103505804c0d0700003080c401900049554103468040e8016026000c1e0100b0b0012501590324070002e003c2c1002801040c00c14280d440c1001e5070310001e1a0050780c4101c7c9000001d05090b110300417003400001c42070310303074544a44071400c3c54202c1c0c0706444401030a55000040c60145100403490294041c00160341d0b01c45c860b5a607d22410480031007107800e070303000035500c0001483c03c000d842501650000c003c03000141c25100d103203080150403098015900c080305000c0100081d5901650034042d03094164047e2030b1506000041001d412881507140b88038403002c0b520982c080c100d9500c8400c0e50900101120b0307482401d0b10308140b01003401c5405aa80c0b908030741000075803050030340c0602840c100b030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 982292994 1250 982291744 982291747
    0x140d0503091c050615062506020a020d020f2e021e090301110f07121205010f0e01060305090601150e040504060507030b03030406231b1f200a0c0803040b15060c03 71
    0x5103201c54000c4003180901f032411201e448000b020070064402050880629130180000072842c40c0068a0b08a5107d01c0350810b62080c21061122980d59840d1255030348085e40389010b540c14007481c1d401074007603003200c00d900e030f41080c040b501d03101120002401c01c040f00b80c1c001d21040031807070105011405030ba00c0d48095004200200c1000480c2e80720444803032440d50400120901030312031544100c0d074090304000c80c031000520040c00388440641c07070580105907600d030601043c904114060388411040c45841c030350f801500c0941803128040c3c04002842c0744003334010011071130141051809040152440c80100f8502940d601c090708002c03044405403002d6880c1c002d203122101f600100350032501030806103d0b40092255080c5003640c17a0100755202c03150700013052114402120181c00a040d02d007141800741c40c10b004140607203240050102c1204004454503101e4000210958400310071300c40c020f0945d140001004100b10403226041d01607808480c00b0200380c6c104109000781c920031490445002e920 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 982294244 1250 982292994 982293007
    0x21c060c0c0c05091e0c030901110307050702010c0c150306090605030d090b0706110307050a120501060f08060d06020c030c0705040c080c031005030d0215060406140d0503091c05061506 81
    0x302083c2d005c0d0081c90040c0103100390344d025050b201010105813803103400b4640000078041941c02c24000c032182c20380000d201624604000e00c1c06809849078040003410312407056140014031654114010040032014841d50442090b058002c2c011b128034043c030b4402910f82440401c1071305002031015041c200b5a00e400c4500d509226854085800001d012075443e921070124400503511400650702400351038030b9054503142d00f190090403120a000f43c01c0c0030f092404004110582d40411a0261440305c0d05140c0030940301c9101141415052042c0038100f14000540207075140800401060a1044002619030580d01e403810841524442e5181500140312000070828100310f01c0011900080e1300854200f115a071031020034144901030050301c0140e000515207a6942d10384180055008400700e0b01008810704045030b01a280225446880c011107034820f509007000340c10000c45040c00002010b010010064404220704245050030803105406000c0110300104190440801c04a10042182c2d041c4403 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 982295494 1250 982294244 982294249
    0xe0f0618010b030a0c030218150d0516260303090d050912010606050409060e0105030a11030a0f080304060f0e0c0f06040e0c07020940021c060c0c0c05 66
    0x1009195101220355840803400e00b10343d810009050054403401803e84020300d5401082500b90f1546c10222130321140c1001c01101001c1140d1044180004403a84450440f55041c8549424440740741c50484141c11980400c031002000007501044d050b010703098680c54100442c080e200d001c19661324a0990259000200090180700a031000d40c4000e0804242d040c40d071401c1d58251000c41d8080380103d0000502842001c0c694041d00c000760240c442d100c40c455142c00e0100366102d8071008040d0400c40c0490f41014243c2e0280032212503240c2003800245400d03411300304402c860b0704c2604d00310b640c6842c04c83c920816106500864401c140604041c11112002e1001d2000200e40c03c0806075000d9000c200205d03003102c1c07182019010716003504025132500c4481c414084840c601401e6026a0700c07060340b080c1d668906800300e01c10082080039810710701d596420009202510301002c0250310000072942c1c11b110b0750290030b580b003042c1e00914080c000010b0390f1034213890402607202c004e8500d2008a82c240000e0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 982296744 1250 982295494 982295521
    0x30f06050114100806010e060909070824010507021309050f0f061e07140c070e04020a1a03071803060504080c16050d021210020c0a030908030f03150a03021c05010e0f06 74
    0x7c0d03501402c0d90b0b02d0003040e41c0005001c20000c54904010603800d00030b000481c01c1e08000b004080e2404440d4000202100002034001d02540400900c9884c80c1c18441e100c6400e1500600c03000d030360080031500201140c5421548400c0e91142603100d030301ca8480081c206803240340400b100070340d03181c0c00c00180d6100c11004440406d1020121a00100200b10280e011070b4208a0780008000411060080703081500c10880707107800d203610420000da4000d040c07000156141341100e410540c42c0c14a0b00404a40144180c501086940050041450003081000b403050180041c01e41c04c0c0e500d02070312100030040c2d071a001c80300e00d80d0180b590401119080721005003002141840e94889200c12202e078200071110700c800340d0303004554030309a2f07400c02604281050f80050100d0060400c65020318141507854042d40300902000f802441010842604000252220140c0c40c02a607005010a140c42c1911440d0480481f03c80e0401c8032a58a4180c1415800e000401c0344604048804060041521040981c0c03011 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 982297994 1250 982296744 982296767
    0xa2d0f020103090206161104051509090c1e0f100e10021903090e01080601050f061803011410050306150d031e09030b0106050a0207090c0207030f0605011410080601 72
    0x62542c0c80340241c0269599001905041703103040028449091241f404a1459880d0081c0601a5003460b00340b2080e1890704205040d84107083d55050303c1680c0d020380c041c2c64603200c0030120390003000b40c1020a4800e0b48012000c1018a000c1d02c01d0300342c44180b503003888180502c3c03640b58000038203219008842803400b402116242c0281d40b04907000d00403604804620030b034126000300c02203103c8030002c0140501d120741c154010094071010304a55894a0049400c000f8800c0e0081e01c6030a0000301044000d041e000c6045000b500039000f00031080240c0d4546000190540381c3c0104040030100015441c54000740c410f101b452000000b80c41254148280300c611144040d0071024032a4642100602040070849520324004550b100300549207903083c220051041a004001002800c00034491040d400040c0c04045801551000a800000020480c1886101e81005007042440761800040c0142a001703a41070b0340713494030000864000402000542d940100ccc040c070200b01c40c44001005580904c41c0d8041 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 982299244 1250 982297994 982297997
    0x16150e120c1302091507060c090e010506030709090203090601062015101d06011209030c021e060c0319020703150c090e040b070f05030603120f070c080a2d0f0201 71
    0x1d000031200000c450b0034400c0c503a0b1701041c4022904500f840703c140a84002032015040084a0b182080c00c822030060050058034001c03031001000c104883c1c81000c0480042810010846d2a801e1031480e00703403136031801c3c458480041c214a03984001044581302d60100402d800c0d00800b2001209240d00b108a040109500d00f0a0004540000d02010180e5450321240c091440c4868a04c1c0c04000500708078000c603042c04c0c0142c500400000000e0308a09540342c5160100c03815100c400340b201e0062038030b5100000b025000000804e2070f01e00e007500000586017401c000c155010310121222402c1b6174400461001810f00021a100c00e90580100d5000f0700001e04030b840c03c02212500d80c1c5036150a44030584d02226584542003c100340b540d0f000d92205842c240701e240c884c0c80c41c140351000aa840905624000c80d0070400a00604400090011208410390149107661000d594252042d10f1315240f040640d0502c1c409500a107003044211710518603054a20b29104c018a03d036141c644c2c44a410160803070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 982300494 1250 982299244 982299247
    0x106180909020f041820130504051006120201031b020c22061409090601061d041d2107050a030804021818010c0c051c0216150e120c1302 60
    0x43d0039407114002e040381d40140b0a40000b800c100b516002043c0c5041c000c014200d10840d05101540b90383d8020b040310017007030b900c80200b0241c56900f401c0703080000505030f640c0ba0501c1c0c5200010046540309002d02e41c1ca000340c80030401200846295004280e0180012005070000e0290000300d14195502c5100d6110400e80c2e51104da40301c000800c11038140e50004100c10500b542c40907110702d0b010408a510042800203003110b13502d0410042c10050000182e49040400e0100f100c0c0962235540c810310754842070031180300c01001100503440d19540181c102410b01d11030446918002c01c40c0d20101d41c03c05600400608000300262400c1300c1c41400508101da00180c054107003d80ca19403500098040d01c40408580300e0b205200c0d02d40e5085036000d1000600b48800a9081f40206070042500d548540c0040103600320701102e0b10040f4141420b00f14042d01d014042c64020440c108440052010b000e0355880d6000003490400410500801d204611101c0f07a002c24626565030400700d61090343c1103100350015 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 982301744 1250 982300494 982300519
    0x3021c06140603060a030f030c1407050a1e03060221010e0601020106061809020f0c010906060603050a18020f010201061e03020405072c06090a03110306010504020f0714120d050f010618090902 84
    0x100c1000b001045200c0c0c194bc400701d001e03c81403911003840701c01404d000381d103080862283c400035102000244809403045a01241514070b40a000b20400982902031850011755a101c000c0700b040c802043d1207060042d842d004020070304501452803850000c6c280079141c0700301072424505070040d610551015140020502601091010034000c03038803100d214200c08a402400d1250080460700300502c5481c50700c2c00c050020f04c44078810100350805139016901c0956000c41580180d0152109520840c0200c41e0304620f04c104243c80070000c000d40b482103400780503a44502804640401d02414041c1d0079800030b120f21407408000030306004100748042c00041c1081c0d14a400282450010360060700d410307855030004035052400b481680d0140004a504500304183c0e00e150242c11701840ba0000e0100c01c8135107050b441241c007002404c03d070101d1941e400e92786010081e0b800024110903582410550f64030340020683e580070340d14000311603000166401c0079034a802c00717a002030020302c01c06030780180d030a5026 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 982302994 1250 982301744 982301753
    0x203070f1205060a0b150f0f03010b0409061d180c0603010b040314060c0909090109020604090b13110307030902010c02060c0319020d0906080703021c06140603060a030f030c 76
    0xa020081c65003401c2461540102e04002d420500001c100d000054601071010502e6940c0301c0d48000c140b58029030264903000c042108a1503071103106201031446002200014040d80644010000d0721490740d014040c42c0c1d902c2d0b04906080e484408a807007494589000501c811030140070342c001e12641c020444081000c0c0c0c50100b581640700ba04900b80e42c003c00a400c0c410311410481c11081c030240140200901e05c1c1c0200c5000741e5000704011244140c0c2a03a02091050300709402100b2038540090007582c0d40e650700d0b800c0c40c000b84403840006025032000b2816a60081d61031180694480e2000704072440c6940707e00c000c0340241040c2d40200d060043c507075840400358841902900c041c1a80000640da41c01d400d0364032100c0312940c040c2c040210340c0180585810326621040040440e010360400b54166200c0e800283d01038044c520b03454082d03022a084044001d19507030849801c5880b0803110a4088124034103022840c8400c95066030042c3d41c84c0d41c1080000c141c90b038180c00c414020310700130030910010340c0c0d13 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 982304244 1250 982302994 982303019
    0xf040207061406210606150d1107110d0317090312040c0314190308060604080a030c0b010f080703141e0105040b010f1404050406110c0313080a021c020307 68
    0x454250b4240c0b8804029150814064140c80800a210080c2d0a03108100b26940e44070b9006103014001e0030618617180740140c110050310300080d00588280000744000e400b040158001d05001e581d0030782c505481020a0420130040c90069401d540d82d411180d9847d100c803460240040c0512105d80700030840c1a001c1c69002201c640224401caa04800341807a604019a5003540e50143c03a600350403289040810074143c1a8810b0165498105940c1d955110000940d10303000b02e0f402a0343c5401455030100406070b0002030074400b24858141d00c2440d90b220b05414111189901a0303822991040e0f10900201d9444292804200350301012151040703180703002195500754501d02c040660307440360140702c1000a82d10003503014109050444441e5450078604120209c859554103000d2039a900100e0140485070b002813201c13a001c499401d0303a540c10310001c0741e66544102c003202141070300c49002142e00360000c07401e503040381e40050403044110100550540491490780f0100c1c0d05209444000491000b8101b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 982305494 1250 982304244 982304261
    0x3030316020322030c090501050303031503070f1502060f01120308151c0605090606010504060e120d170a02070804180e011503051c020601060e0105131220010e0f04020706 75
    0x409400d500740345181c80004211317150041201c40d0704207c014031941e2000800d5039805a6200c100316601002034000c02d0400b00c85410000c0084c50960300030078541100038211210303d410350308480a50380c803003e82150005084c0140144000040e5500020134880c0e088103820040d055441007282d1901c0c1c0000356480d02e184022040d10710f003030300000e040c085035104181d840b8064070060704113460501d00080040c495401036405000d4102510070341038464854649842c072615007101c200d480c003e01d0103410392050304100600c03000380100080e140e842c81d0090b01d1503117501c140f465091038101002d007508521a4203120071415139500ea8514034503024021102a840d10b1510740126509508020342000707510548a003007825000346c0c40604950004856044a99030710f40783c0300104412004946034070407440c12074001d108210011449103c0c0d13600740d801861045111200805010035100520003580b500c442c08602010030500301824405005a82024001c100520b84061551030108451195 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 982306744 1250 982305494 982305547
    0x6050406090608060c040e0609041e051e03090607080a0c06062403230a42030302030d0b010512040c1a0c0606041503120c050714030303160203 63
    0x4400402542d041413180c40d80090881c00b9452905040c00382c180c49082e00982428010800c00000805018081003d210009a007076852101c5140b80d007021307562040500d90510342030302d40c000b00c101c0403480001112406200034140a0030a00b03282c403a120382c0d070068000d413428495031055100c00110944607001c041c0c4800308094000c40c03034082c00080040c45110130b41040c9850210722034040044040e200e042900a421261156911100500003a0115141120440c0c4000100d2041c8041c00084c0e8900340031120703d8000e04036128151414084001c1c0700160241c2c00400a18034a080a81c000c11125107040c14641c1c5082001c2001d01c030303000c40031101a9400a4024014481c0000110310301140c100c4124141d0b0401e0801c2400c1030711401c0140c1044d2040350394950b005c5110240c11510402541c00500316401041c042d040a000042841012145c1b0701603a440031074140241c400c90114441c0250043d4155610440402184002c182c5c5030429403105020000c00403044507500e10042041 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 982307994 1250 982306744 982306751
    0x30e09010605071505130f020f040e01020c0d0206040b072d051207020f0d030b0d02040c09030b0709060e0105130b0a09050a050901050f0105030c0d0f020c1504030e01120605040609 79
    0x1401e04c0000c56190a0002c0c9002d070504040c848450b900d203002a04d2103800c000d40d203400305140c7c400610b088a00f45c966642160611440d800d52603c10750141403240c0c1c42c0030a80e41a000a46001c0703859010454009203541005c0e0f02280105d4480c5881d215a01d243c12069480650b040280d080080c5440d40250300040b40001c4410544030003030b90440e003103280341c0010701c019886100e038a512407010000800c1090794a400000b002e0380e4215034090400c1d0054801c10a8401d80716000340f649104e400305565108058020882143c0310306610021510a9901c2048000090004503030070343c400315030a108003015800108201041400402480702c203030700c84111152815051005402040d03010f91b00c0350300390500411554031010550340c00d414007443d141d0764a9903201c101c40745502030074044040c46854110780c00310f01e0043d0b0b0700800c7d441000c2e20440d403200001c0501e01b881c0d0103085800a0000d030351440785105d154002c0100d10100e000c04200440c0b419140d40100c0e080701c000b540240c02241c2c4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 982309244 1250 982307994 982308007
    0x60e13060e030d1b020d120b031f0209030601060c0f03050a0e10020d0207240c0512130f08010c1202030a0204030605040b060108220f0c0504052509030203060a0504030e09010605 78
    0x1400907030803d5113100e0b0300207402d10100c00d15001d02001480c10b03000454988402c072003289540c00b400740505441c001c3c9102a005141400694001d40004046600070301c290400401c0041c05983c01e000d01a41c0070702c01c1c2d50752144aaa0859580c0c220107404028015514048a119520715080d2100d401140d4014101e4440481c4001c3c50103110f648548481002c41d49804104140307424981e0644425003811400322006240207494040c14030813245400e030000c1840302840c075101020500300c882e0307900c0700b01c030868803043c0321401c0f00c1d0380c0d001c9071022030200c101c4003a6421554018640c071020001c0014201a900c1c0c84d04030603140b08071401c540d6141c085041010315078116000580204420591b1280b48645009401c5034046554001c1d11100c0a2244030701000950a089405450050700a02c868140840002034290400380070285c4210030890013032405104804210860760020011300c04c94031541e0480004200181082d400c0000c49081020140c80d003000d032600a00c1d5558030541e440c403 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 982310494 1250 982309244 982309271
    0xa0507150e01050c0702061e0c07080607030f0b030307031d04060b03090f0a02010918230601020c03061006120e0322050a051818070803091201060e13060e030d 70
    0x501c010807002d1500c2091045e0f10140e00c46606990712041001007800089040d1407020b4150b005046403000e0b548035101c00844c100e0070210702d450080c1d01c507880900c80c1d54180c2120005480500b00c0e0550168014041d030f40119100700c200b1820003030308078984800c031905003002c68169811500145480140041449204401084088410b48052024000c250a01d41c0002c0c1400c10078428401c0100300889140c010101c19405600340c01c8902d49594424811030800114210044a41d9409405104c0a880d142d08000c03d58903c9445005856034455040c100c082d15290603001600301e805035150391200c0303940010001080300b24000222010740c1c80b251000142105040d40007240500000002000f640e1610350103001800190509040d8955071521145440c58140031403402510405000059803003010005281040c000c1c0c40000c480005160a80c0c265003240c46010b0b001d128400000700e0440314042501003c0c0d120f807030041035130a0410409031840d08118144000306944600e090b5400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 982311744 1250 982310494 982310501
    0x403050d0e030307210b041a0f06040e1801020904020d061706220303090c09051008070305070302090c160c060f030b1014070818090112020310020a03090b0f0106090512120a0507150e01 81
    0x6008a440d20b00e050b0900c03100029100cc0a400218505003040046804a07800e40507a0b8203404064411500c848002031460041d020911621144c1d1170040e107804504d2b078012404520419020484403044903a0032252004011903c0082c2c0416030b0382c01c428000034038442d000c80000c02285202240901700454406005507440d1312645099100c06410400036002203549011250112a00d0f009035660400e411254860b80c42c4c0081d0b0040b03815a5002048401910b000c00e4550a941d15949000c4810044d0104c414041e1002d601c4074810603d8070510348540740c0034004104204803241000002d0340c2d041d6090308406038689464461151010305400d008942e1030041c0049456040b002d01e55401082c0ca40c03031703503c40213003000c1d4000030050610303406508901aa664020b400600d1490201607001d0026028000c680015003009800265803600e44000c0e5901c00480c409007841990b074640d0703610075520501c20f0a092280038041000461000400030400032407a035400310f8540c50304c1c440b0f207084 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 982312994 1250 982311744 982311769
    0x10e0a0507050a1407081b0a05120a02071203020f06070c030f08160e1207030f06050106020d0801092d0b03060c1e070c0e0403050d0e030307210b041a 66
    0x1002401e00658003ca0b5000c2d5240101d003410240b403940da00b0083c2050703800c81c480c0d545103a550340c03a02c002000d10303103100084007079000d4044d00036120340c12200c886812052180f031290400580c0542018404001010704070740c1c0d081c2c800e00440e0041c0e041c582c40b050412504655031b030b004c110240550818150400414018985c0300d1410b4a10b5103001104544140703a000b03c5d04041140c079640400694540d0307490580380e1846841110303080c0b0758900c0c1900304840700c07a804844442c20000005600c3c0d0002481302d4100c0c1d610f8981074600c3e800c0c40d507408000e01c3c00380c2d4442803a291800c680f10468800c05500602c0e40266072010806860b0740003071501d0305601a0000025030407c21501c140b20f91040400424203004181c215610512400d15040f103043c190800244021000281700c109a0440024410085111010f209001d880200a601da0204585c1f0714040b900e04d4485c10b4010142c038100200c1021f4101e00000c82d054030f000410100e451071045090410907002482c1c1ea02e18104103000078 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 982314244 1250 982312994 982312997
    0x2307020c150d09020301060b0c0304240512042f1e0108161416050d05030405060c0a03200a02011415041e090b06040b1e01080c040e010e0a0507 63
    0x1c081e060081145607100e07000c20401056901d4071981c003156006e42080d0024401c0305001070f224001614041c5c0c403a4454400e0042203e916001441c048201605c07030403241c0e6040e15160b05000f100000c4a0704008002d1007112001c407030100903001c1e803001c43d0b2041c590b001420b150354019251075050060308a41d040300f10340c0244201641d40d80d035aa02c024641d0b0f10400e0700883e00d0501703031500000c1d20b010454030703c12010840081841041140c1c040000014a8040d2044900c00c128281040e50684401e90340900560400c40004500a03640760041c024040d10346400903418000000304149001204080081d02c00001410300501e9030900501e84c0c0c01c5500440031510382040c180e010b040741c4030782d6490b0340034a840b01c05c12802d08107222029064400401414060b0078161302d00101001c0e0201c1d03115125a00d01039000005040c6000000704448616031f440349c3c4d10f46a64019610060003c0041026030020400421942d102e0b00d4014000c184058007403500c0e040941c42d00d41aa00020440c20 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 982315494 1250 982314244 982314259
    0xc060e0108060d0c06270909170705060705250b0403020f070509061203091f03150605031305030412030206040b061503010314070b1c050105011407080d2307020c 71
    0x3030200f18014840f90403038605080004881c6400603886c00080b040c010703054011642c40000003071a4003107404c50a00ca510a0088107a000700700c00d100b09090003030b110003506690104000441c0c09000d00000c241e90040d5400440c0d41a810707040705a691301400102715228640c0c203003070004164040058800e2524540080c0103402c0c10314022500c10900241000d10070b101c05420302141240070b10403500220405028040002103000c564443c4429661061000034640352812a40400c06810f01058070b0155492a1464a0f592540545060707860b2040d24640400c101c0060910020701e40082020f110341c0150420340f80c541031982500b60000c0606014003800c8451070100e080000403241503e5000c62242c0d080241c602d0014038208a6820011a181c0d0003d02502a81800b4101c5130f60b480d0408024481030f03882e080110303581e24101520240c8600140301c4600094181c0028200484600c1c00002d10048031086603000720f1181111412200c14490901034281d030305014490555805980a5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 982316744 1250 982315494 982315519
    0x70f03051510031505030115060f02060c04050d1a0a060f2c070c0506040609300e010c0c0b07020123040e071707030518190602070f0c060e010806 64
    0x403442e41411450700c04140c0d4400c8401440000c0b21340d84c00c003500010340208000d803c40c0c8264a43c90b00345004043c04168000744080340384d0b10008200344608501d00c1050308051400c820b218422801104c11928041180c0322214098120f4961612980070008080741c4245003000c02c031000d031041d0300821200c910b00145040e9a40e801c6c0c00403c248102c84079242010f6079036080448080c034100340024554040c4105004c140300103030700035201250050301c42031400403800d80f501490340060800c821f80120100884810308e80940c41c0803620b40b070181030408400110f95500c5090151a0f0031001203e80003040203421740d41d2101c150180d024489040c82d500303090000340c0408500961040010019105c00020041446420031501e505004200020307542400300020303020f070604039807100c5409480c075096046810002000c070b0711007940b8001c0309908030f460f03111503010307507c800f8081d55401d0096884c100007520010300d8030004c250365038625a0300039407440010310103680549544d21503d13100304d04 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 982317994 1250 982316744 982316749
    0x3040915030c03020108090f0f06060a05030f0c010f1106040c0e0c040b03040b07090e07090801050c0702150c07030210050919030b0a050a1503210f0504121a070f030515 74
    0x20b15040d02d409003010507165a4200d0090b1030541d92101c81d000c540104e200740c002d40030740004d0180c00307008200c41588a00b601c1e40700b4180e80e03410312402d4a0700ca42c00005011081d5001c2c1c601030064003d80d10b030800c601103000a0f000c1c54040140d4048954104202041001c13500e410720240e00140700c0c404451400d803a06405401030300010340058108800305001c00e2001340100c030349100a05540224421524103400090141b0340c42d4885c4074800d500303240014820a030341004642540e9801000862010642c1031440499004414409070718400e21002102503600c1c0c1c0314001418200c5d07540c103a07483e91010184100780c0280d007507100450340425020300001c2c08401101c0d81c820080f040000b00c5590b150801c8c1d010302040204c031901d460700b802010007881400701c512003040c00c40c2e02948007030010265040300c44412140488001610502c81440a60500d40e144041d060007011180c0420b064410781c44407255007035070110301041810281000158050007056407009141805006c0c40d9814000f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 982319244 1250 982317994 982318013
    0x705030a11070f061508010e0a0f05010b0306010810060f0510030c0c140d0206010803070c0510050415030501090e010911010f0908011b11060105030a080f07140304091503 75
    0xd42003005403195018840c40001e1400e0300d9540390000d441c0c0044980a0500b00d00500f5000001010020400d1000c103200030140180c03403180460200602c40078900f9210141c108000984c1100d2070b540341d00c0c0d903201c141d80800c180d40c040c3c2075030700242c0404d00c61002c280d001c642040c3d0244c40c0c100541041009103175103490004040708514100401d120607145011200b0905104000385500745819656001200c005400b01c9004455000c0710456621042003569a004648004181e60b200c00c1007440f040c204405c101a00b8881e03400d000b0304060b11001e44140b44400e00504c01b000a55400040010060364081c150030001084002c101e0b5800ca51201465002c00740600b9042c0001c841c070b1400d025126a02c01d070010018800204940c500307820b0365012020407003070204009900000310210903c00458080d040326802401042d003212140d0f2021140d130021401c41c040701100780114008515083e0350241e41e40000d4001d940c0d940e040085c490b0444500080d4945000c000760f100b0f00004403603c9 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 982320494 1250 982319244 982319251
    0x110405011a2a161211150d0606020304050a090b0913050f0a0f1707122f0a0c0e152403090d020607090b03061507080406030f1a10030b120f0a02090f070503 68
    0x1508680704110264102c2d483d031140c7d800042d003c80c985000042d21a074080041e03c2aa00211058030300282d454410302c090340e610b107034080d0303202080f4408160720600c030301c184c0d9654a2162065603107800901070f40ca400c00d107141000b81c81c9500600102000c000621603851203c4610302d01d16420011a40c8410440c240c1c01c00d202c600f0721812980083c1000d000c07000004d0b003c010b00d07200c1c3c0c81c149803030b0090585070209003c0031288100021404a0700a51005603a0300c110325452000f06801d4683e420031492a103600c03400c120800392032214400000300b0b0b000861103000c004004100c3c0c59818000280f52100003010f004c104100c1300000d10604135030200300d80d04020201c4565050000381a40c05103140300d5000300401c103540c00500020341c2c1c0d8054108880380d030f100e20000c00c009034000014088800d65080c007075921014032981f010f040c0340264046180302c440500700c1101000144100d034903010050040340803d80c0010141021841d183c40e20a506c02c200d00c00c122a24103180c2c201400313502014 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 982321744 1250 982320494 982320499
    0x1103040b040203010b330906121b07050604031e0c02040e102a0e0108060103021e0418150509130f0b0f04110405011a2a161211 56
    0x40114095540035001290640380050181c10f441510265154031019412020501c1602c3c440f0304030445402d21b0151400d444c0d02401c11403900200b400f0020386150010031282d04804d41482c12036030081100302509440d407048005041d6070a083c200501107442e800500c1100c8010100000e04965001c04c0038640c50b039040e2004500c41885070f80c203a04000e503120030b034800a8642808050500c0d14180b440013110120032003904009a03010080b604036804550a070301140300720001c0380c25540b0940c002c18440d08840e2a03a403000040c481c00500603401030740302d41115400003a05800c1d401003881004c400d500c000701c890340340c50701d002c010880b1003200510b0302001c058550001300502c0480304922940e281e01036545000e03803404910700042800280c40a8401c81021620218282001d1107424140c40c03070307414003000c0ca0485440d040c4481c0c0c42403141070b20080031007880007802e00f020044000f02d04000805410404443c00c90441d0b010f4203a03101842c641c040312010350100b40300b030054110303c2005 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 982322994 1250 982321744 982321763
    0x12030314060321130e0709060807020607050a050307020a2103271112010e1b091e090a0524100f06030c090816030606081218011e03021c110304 63
    0x500340b01d2500d12042c5d522a40801c1c1c244d00c02c008015500c000c0001c01c0c0c03074541d1100ba065889440c0100d9580070300701c0b00c8a004c600204803c0c2101e6001c0c8016580c488810f20482c0c41d85911a80c403000703030540c0140c14104180320b001d1315231070a6426003c0d01d0780308001070f010021800f00715a601e000314500d441c000340507200401110801ca481c0d518900b86032025034002032100021005100e0b5030b4242a141880c9556504480100d0902e80000302d81d0050004407050070010803a2000c1c0a07000f04c014040e22a82c4c8141120280010001e026489001c1507030490440d9001d845070040f91540343c0200082c01c1d04131316402c00e11889030a5101101503038014500040c44c4401a8010f0fa40541e0907000310006104a00902100400c0e06400b00c09403881484144030750b59490804655445605440c00035210090056446901c450140c0e8038080805140c012024101c80b01281d003c07034003090303814000035000100340d55038407106211442d0032040d62008201c82400c400c041051400080c1000703010750701 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 982324244 1250 982322994 982323007
    0x90e15040c030f0c050f060703051e0c0a080c010b041407030c03020f120601120612080c010207230d0801030c050409060e24010509040b160912030314060321 69
    0x10a5254a000d10340c011112851246981131151200c003491040c0c900c81c640d101c0d020b030100e0400f842610501503050705c9250611254502540d902240d030220b0b201e00036402d102d01010390784100600c1a4080c01030744a259541c482481640c20368a00c51480da02a03410803221021442900c0f100300d41c04080c52a0005441d58007203022006849061000340c1040b4012802410100b0106650740c0a0743c1d00b600d45c2d80c0711082820041e01501e01604c51484000d00920048011034507640040680c040502d00051514000795914801030000d814040499052242034070a209400c2154a450308540d0505500c190b1450744d40008210007405400e001c1e9032551100c0040118680041d03400144100a550a02c8690810319450381045512880000d00503000000d56090034044a400346801c41d41580c0941e0300c40f007041c05032800d124204c608020b40c501c03000559100b89000382d020320744250f5000c20a0410100161880c000c090403041c440d80010364003560005600c041c0850301d900e90740d129502d819 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 982325494 1250 982324244 982324253
    0x110a140a110a0b010e060a032f0406030302011b1719090c151211030a02030405100c090e0c0307080103030e0609130b1c05120d0b030d080a06090e1504 66
    0x1140c0600703041241c81404101e004000daa584080c4c16143d00754403503003096a0740c02c1000041a0248005821003891b0b20185070b031560300ca040c0011490804002d41c0c1c201030414040b4044403107550046d40181d554102000f0300030202002c0041c881203d01d803070008a10302900c20342d00c3c2007014189044e03c100030490f80204800e16089040b20f2500a10303820515a660f40c03800d45604d2005c1d0306100055440b03504904045040e06c83c0d015a0201055402d04603076908101b0402980f000c3c02c152744521812008441d9400c0b103000700034206000f60360b1f8142503032925030145502c0c00e006e4280030b03189000340204580305030f1160005044a8240c40c0480f1400c07003036002b0400038440d00403002c3c0c00407000e0721000081c5d40c0d140c000070011078042c3c0e840c0d80129400000c1c00802c61000700014095040200700c0400c1d80d000201030001ca45c01010001181c2070301c00d002926003044003400d0720119500f50208260821944180c0c030007014181c0c01488440043d2821030b840b010411584a00841e6960118080c807 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 982326744 1250 982325494 982325507
    0x60e040812060f12100606050f070f0303020c0303101401050711091b04090605030c010e10030902150d0e0d08060d0204020f0c011811041505090406200904110a140a 72
    0x6103c058100703850f07410b0000c0450740310000c1c0121250144c0c101240050072a11510844d41c0620b0350580060410040b590386258804000c0e41c1542055000d01440780103034070600045010342e15009020034014580340c59540d445007901c41140c103000c0c06115281c08581c106c00440e4441908541c0307420641d5896800c0c22260b0340e5246c090071400000300700843c07815580d90100d02941c5040b0200c03071114221400440302c03022040342503030700325200da01e4031181640a60400400a0b2000700400c00480301c262601e0b40c190000c00c0660045600c0e40384d04082020180000b900010b0341d0b10b40b40005150010110340204c40c01c10000b030080303600080742114007020400703940707070380f86070300300034000d03681c3c1080c81107080340324210f0603581080300c0183c0745050f203041e20400f030000c1c010203c4048564500000c01ca07000c08010001c1e1000c503250001006207000e00101c09604070900340e00e044c2c903000c00509200c11681c04800c0b16825580820440c1700c12034020003000c5150919882250742d4042d4a0811106d6 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 982327994 1250 982326744 982326769
    0x60804030c140c0f030a1109041a0f01060e090108030a0c110301110909010e090a03030f0b091f0608040b040210020f2407030213051c1a070201060e04081206 69
    0x1031900070b4800c1c6014502041440050404503880302500703008400309505d4042e4070a00521260300210241100d0401b110615407290048003018507003080c2c0d0401500c940c030b0071642044c0305100103005100359a040505d8610185044c2c0f5900b40560400c0c8140360760744148010f4030184401d801e402010003105803014120141d0207002403203180c0c0408041d404541002500317a01c180400000071680b01c954801080c4186000303402042c2901d02034a080d4000c000c0c511b5400d60980e00c40c200c449858680f03001d2180206040b002d0a00c0c020701c0c00c0b144c2c0d01407141c950404020412102d0500001c40c00240240c0d03041a011a0040f4100c591880d050b850221041c10000c03030783c0039007016100d0000e031940b5200003c070344900340c007601903544030f401718120700c40d030316170380000002c2400c013071001d03082098020045020000c0007280b031040e65107034007000c60307411550110300c2803c100070044901c1e07080c040c1d0002070410080d141d500e828559100c00450003070b0324404c2c5240c804800002c500390741d503401285c10f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 982329244 1250 982327994 982328003
    0xf1d01090b13060e06010201050739060c0c02130c0203180d29060f0d06110d06090911040b1c06021204030809010c0e060a030f11040b031f0f060804030c 67
    0xf92a40c80309209003c403021503110340554030340340010b42400c0c080c100500340d0030700800c8000c4003002d01e000c4400383d064420300b5400e003c1c0e5032410300600081c101e01c510b01003a1003503101c407041c1001e42d1040008442010060b102d0320f90806100405558001054400c1003000300a84052100001e000c10705120b0705030f801614413408900c400f40c85c01114450314400c6941080c0c140c0490762103005100c40c840e014402d85800000303803c03a407000300e091540828221545041518900070708800d001082d02c0a940052107095640e000340300401c4240744440200c00700c203480611001c1908030001310410220f1150104401d0180160410003405038101e0b240015a0201d5001c40d00703103820b0003803c0013401c0300d070b54105603e800c0f1079500e00c500500101210100c024601440c1c03810905044010b070400030001c0a080352607016421a20349000054006400c0c8102002d8503868942488158051050040340c1000d409400502c44440088815005d4030000e08000322192150314046481d00c41c4e500002c0d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 982330494 1250 982329244 982329251
    0x140d021507032604120f020c030d0f12060b030408070c05060a0c1101080606090d020103060302060703083909010210110d270b07050c0f070f1d01090b13 67
    0x802c05030801c0c1401044810b44442030b03800c0240c0c100c00e01c204501038401070720901c500a01a40b00500c140041c10b600c2c00302e071056800288044001c01c0c54001c1e185544c101040c500040d0852156002003200740c01c0d00c17800001e00409181c100c416a5900c0301401c00350003d480010398105005d20000300788000e11000d403803c1e1307681c600810008e060088076030b400c8a80205681200c0c0140d8800c000d50f5008103070080183d482d10f204603040044411650340101d06058a507403001000d61b5401003d000906d000e902c0d011002d160101451150210a0030000016036401004582c42280c048001031400082e9403800e0f620544c400040c2d00e000a02a41d10001c642882c62800403016048058005c1024401080c0005006a05801d0006011011002c2c450b0400c0d00c1e841c021580e100d100940000c2d241c01c2140c6052181891303103003401020180509207910110040004c00840001c607030043c018004201c0c4000380700480c2280c0c1311070604c01c4054080d26a11074160513034501041d061174412181081 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 982331744 1250 982330494 982330507
    0x12080a020a1a010515030708150a35070b1603120e0c121f05151203090f12031c020f210109050402150a020a0614090d0207140d0215 58
    0x8120b166007401003d00844660340b03c08610144902620f00070f282a4440d20707140e6a5108200e050b01c40b5440c40315070701110700c40c00051501e10024840c4032800742c3c407000340380100c074041c40e040d4a46485040e10900e44e206510402102404030b0a45c5e2070581259800b85810040e400c1c1210408425003030026003500c2d200302550149000101001484400d5589000394921040c9054552900c070030444201103d09101d51308215a544c000c5900520700e203000800b107068000801c000d1500348041c1512507100040046440c9000074011025150840340007038503100015005481e40502c410403400caa0002600c20701840554050302c0d50a001c4158840d200e07036078010030020581e072104080048400100c00490040c0d9680603181c416500030300f01d94619034031220302401c2580420fa0810840c06001c0c258800250280641d07040f49194508421040c140780c05203070308080394007c1c1203055602c42c400c00c0200304245804204c1c041021941d1209004150007c10207032000c0d01030140301280c000500 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 982332994 1250 982331744 982331783
    0x120d09020a15230a18090c0908100204060c08091f0903060b03030711010c0f1a0403021c120e07080303160206070f050904091b08060a140112080a020a 66
    0x6925201d0b00c1c40e541d1445200018071414801007594490f070395044010000c1c03202c8136000310b54046040c2c840c1c1440c0c0070031681e40c01c080c5003221802820f402c000340440d030082060050803c00b01502c40101c120840c40e003407130701c1c1c00505526810603000b003d910000c00c484c101a03482100c000b41d0019550059111407074484001001d01c0c0140c041110021b242c40304000c0c0038103002040e0350105038407043d12422468020015504034014010484509101895110016041000002e12120b040501040d0360a0500d0301a05140c04503a0032080c000c610300c05c03044078035400140043c0300810401c0c0041c1c0d2030080340e4014203010050f00030101c18400002440068114845e4094043c00a0741c01c2d10351a4881d28011900308915244640008034140400c411914141d8442071303100344110105181c62000e4240c0d031100304015030200103990011000c10540144074001d00e100c05516991086003903041c088078402500b0100c03400380c00004045040040e031030082100170511078001071000702400183d041e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 982334244 1250 982332994 982333019
    0x304260702271602150c040909050f031306090816030213020d020c03040311010215070518030a0b0f01120507140324040c0b071a070e04090c0f05060903120d09020a 72
    0x38018490f40c0c080c520131894251810f1b0050715010001c42c90586449002d50180c0702d814426a10350003202c1000000d1001080182400c00c40740d0a0101020318105026141040c01e921500141c0c004180e50000c42d00c101d4949019290304840e440c8240c00790500d050000c0c010b80c1140d28005100290540f080c1c030001010f0011244208200d00207200341c0d400480c2c4843c6800e40899900441d00b01090f01036014602801101440680340070030f41281000003480c06c90160f405031000080312051200c1c118610940ca40540741a004001401c2d0180d61980d80d948054071501520844120702c1680a0382c0521542a050340e440780c0c9140c400d40700c501e040900c100d00f50343c110352400800c2e0f40002c0c0f80d0143c10586503902e0f04020041c52440c0b0640300d80c122a40c3c002c0041e0f041101d15800040d09680707521501940b18044c01e401c1c0714290420940c0c000c010080c0e000306100b54000e00c40d1242039540025a070703207000700398002d698a402d03040340500d01900c0c03185402980140c4422000c540c0380e10900c07 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 982335494 1250 982334244 982334281
    0x120515130e0111040504060f0e070309061416030e0102040501271d07080a0915051302060a050d0e0109170a050409180308070f020c300102030426070227 67
    0x7141040220b59408003002160024492045a6100100000c3c03e89000341c2c005c034482c0e370140701e0104092441d4102c20808801c00c940004101301c03980303200d10034281c1c140b1608100700c000d14001c51074103090000186c1510841c0c0074190b4031040c0c16a45804585507030341e030200105005000f06ca008020070721000c0454034202c030683c0014100e0310001d040075583e8002c508945400c9a070818056981da80a40040d002c01400c2e0307440c04605052110050700c42d003004040008166440946400ea01300094042c3d0b81005150001d90703041010b00740104e800c0b41543d00c444400c1d1001640ea90341e490400b074a10780a241d120551440c9080350a86105190f0340048078824800d036036201070b40c0d80303405c410b4800d10301c40041e080050307000d11410701050070300101c641451101301c11040c07014055079400f1501c040c507a0b41c080754aa500401030104100304405c100744100e50701c41c5c2041e0000c2c0700660840040c01903440280c82609603640040c21802c00f821401603203041343c2440055850304511686c0e400d032940 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 982336744 1250 982335494 982335499
    0x20a09050a032307030c030204020a050c0f071d0c03010b091201110406090915090b0607060906060302120f120d02160302010504020f040b090f060a24120515130e01110405 75
    0x10f80c905101804082036500c03d07a0340c0840c1c03a52105040d81c007400700a4020140b1b40c0c0500c80c00b0400801038410810110500c8461038000b042040d0070404d426410311807884ea030702e4505d4020400d001d140700b036040179641035500d18105540c0f0740c603a00001176a2800c0240c00c40b4819440c082442c00740645070030080040d204251a41541103030380b50f103850304445d120b80c0810b14400d1003d8091101c00015044400e1140004008500340011602e420f82103904401040350404e0f074034181002141132002105207070b100181c003c2c01c8042407425541e9258a6a803240c00140e240000d2203d10360b0300e860b4140c45080d0280b9001c03043c1000103190282c001c08003510168811804d119000c240b624140c0190f180d560320141c0201181c0c0c681142210b03c0403005800316500c203541ea8408078645a4102d5640041d14402000180061850348090501c019000c8256119811314081002d00c102c9032600001206095851100801d9150400401001010b00320001075081018061a039581c80c0098001c0d036404 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 982337994 1250 982336744 982336793
    0xe0612010e0c07021f02120408100c02010c0206010306090236101202150d020a120c02060f040f0c03080c010f18030c0209180a0f0b070c15020a09050a03 67
    0x281c050103950b80c007444030029849140b0844503000b114039070200402e041800d0040300c4002c04a861052080c0e00160440080c070342c0806050800c0c684140180c01100380c050008100e00e03142d0400094444505006c0540401c0d21805000115100d000e920f00da840b018618551030310030741420016400210159411803224403030b02141d0815500d200d00c1084900d128019418440c00e0317070078003009a4010f1481d10008034203200012000b2002e00081c000d000460f80c961032001c0c042d0221200310358692038164115402881004803441c07040c1206600103130060b0a13602c030564245450f409900c05500012310810010a217024450b00540000c40980c00012003407014000c2002c00c600d0b280d540d00d5010300010048004500581002c445581e04200c1d80408420303c440e1179842e681c50320b21819011550803500d1701e4510284181c400c0ca66030001c1091420020001c4203468143c820105150b8011019a0006e0213029050040180b03500500019009900d42c81c1e036810560341c031622014121030405031 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 982339244 1250 982337994 982338001
    0x1202030d1112151f05040803070317071404050906130c1808061e0403020a06020f03061305091b0f15031e1603110d021201031509050307080a0e0612010e 67
    0x1843c0310412907050054504024150030700910010012011140c10a02000b0030002c503070700006000416000c2d020f40c50729603041070035012855908030001d188608100f4010076007056824501e04450803900308850a05098866070005200c07021000040e2941600d0000300305105a003081c031844003000281e1892100340e076154810364641104494041104101003296818214181c00454100d4024030450300d005030340e596504100c1e4020441030314040f0000c0200071192070303c0d844508003d0070504080c012410004d9420307540b480048103244503021005011449030b1074004c034141240000815602d41416200000340319a842aa80100e9860101c8041d03084d03800e810b030070107010300da01d0907401d424484200c90445c01400d6841c50b48541a03010498404403090074005400368030a03800422009501d145001c3e0300c10841d0001081106040c03000d180040b510100503104510b4000c107003266914040e42e01211074855080155501440214094901c007416031042030588507810803066503901c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 982340494 1250 982339244 982339261
    0x40b060325020c01020c2b06020405040c0f1d0f0a0311090603071a0c01020d0608030307030606030516050309190807140a020d02013906061d041202030d1112 69
    0x2c5407540103000d40d008003003c00140c01c15441800840010780c0050307504e0f00c047d20310a58100c0800b1001c2d241a03802180c207010b141380c54071070403000d490b0505001c041c50590400103094074480613000c040b00b40c502d4499520607100d4030003240d43d203200248112a09610b0340741402e1522440850309008890400c0004c8172030500181a60a5076005500e1030b00c4503415a100d850968011a40e4000c295024082010800c2150050f4000740c004000903641304c1ca04400c00500b220005c0d03000408040c10f0009001e061603e03400c0070710322050603140046d540d54840700c0ba1460300d96210104080c001c0407811810038030500a01600c2d69034400c1100c01c9620749281143c9945419803a40030350700a07407803c0040015030141c1032880112a92000c0c2ea1034036611002145510220300b14030450091043c20288100300d181c0c070515001c2e0180b03007280705419542e1380c85003400c004002d1000748480229800081100e000308103946218540032001d01400611900910054000c2c1e07800100900e0720390302040805 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 982341744 1250 982340494 982340503
    0x3100f06122712110a0606050f040912051b06010b03043f230c1005090c060703090308030a14090c0d12181e0e070e040b040b06032502 59
    0x1075201c02d940d01c0d41d1101544401c9a000e000000b8442404400e000b003410090042c02010440c3e030050f440050f04900c0d090a000c3d54031004410795129915000c00a00080c213058420008486c0c28582a0b85075050322200d5041c90f04c00f10000710031845120000680d140e000302c0214400d92240380d506003d21862844558820000030340ca42d01c081c480b8003007000d45110414982c1c104d0516141005419106410b0701c3c02404000000303a00d800c40c0010394020759142000031055241620308200007074680740a403c1e81343c03800f0051042c4038400000300c1c40e060500c035078601000b4507048030075541d480c24280d4100008001020702001c1c9950604005a0680c4004c58080b1210001420b4806144011382d02c14409084030a6144148038001d00c0c46030403c9944031002010300043e0380c80050040114074030401d4801660701203105940090704101074154052004400346600380e40c045514611003000034003034412002056001040882003244020343c101c030180a0091304e200c561090002c0c1102241c44 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 982342994 1250 982341744 982341791
    0x20c0a0806150a030b1608101406070606030b10050a0f0627090e01020c010e060c07120e131a01080c0913020705011401170c1503100f0612 61
    0x441d08614002940d0b80c6070b01c110780c0c500c8400204403015503034032980c560200940554802510910b0300d0031101040d90091813881e0003005903003003418513070f1a1240010451020304d1a060145101003800c2041040913081503000d9a0311000c603500070318000d800741489414038810b02d0720030300904c000020350000c10304203441950b00315075800092121042c01007100c03400c800f030313001c003034501c90000002e00082c00e00c900920010b400380050707078407003010a038582920405002d0040e0b5800400a110341c0134141c5049403c840d80c00f80d5070481d82c404000040d55904080740c201c0d40c01401c001d00c810382404207540203142c0200380340f000e54080003504004440b100b20480381c0c01c4200d101081401d40d0f501d007903018135800c01d903401c0000d4540281640e4140c2510114a107d1340c0108048006018011000c2c01e039810380075440b03000384134000c141c900141d80500080043e074400710f000801b203000300040c5e600d00c03000341c01f03031134404100540d48800080c01c0c40c8c0d885100e0b0041a00d45611240d00c2002000003005 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 982344244 1250 982342994 982343009
    0x11d07180905040c05060f0a080a02040620010209031b0907020d0e010c050a200312072d02030d0203130b0c15060117010f031218030303050c12090c01020c0a 69
    0x303030346090690a100901003d8030a8071814508100000e456858500074400080198903260b20380c1c88a071790180015034013a051046031801400280000c90380400b4152009114900b0400300340c54040309035009200c0c00b5036098150080340303018034440309e031110002c19403031040e1103c11107944e820b00100d8484001a483e040000c2c07000ea5540c51640c400c40c0d003a500140580c007600c0140043d40c6d44c0207800c183e00c6032210b810b9004014064202d01d0305125650002e9108485036103040c42c80d40da40903001c002005000320196889085079440040503010130001ca601a04550b2090304d080400b035941e402000300034800c80008000405d0800d2000d043d07620301e4583d44001d1140c03403105080c440d040500104030303504014a07403584003801403c0030050744c020021100c0f4a10000d08605000b8038080d61a02c40c1814009089032180701079a81e005110b084a40601e00000c4580354440900520720036107010700c440078155400d1000d034007000301b0307040c40c1020700340c08481c5400c00780418405010f07043e22030340c0d8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 982345494 1250 982344244 982344287
    0x1003020306092e08071509120609080c031c0b1e04240603020408010f0b180c163507060f02040909060209010e010806060403060b040207050303011d07 66
    0x41c00382d24404203c0c034920103042c2003241c101c501540b402c20550702507880050983d10a66040042500c1c10b15504a107170841e00d00700d4a69401c01b000c0c038070b00070800040141100d90342c1503180d081c80210419241d11001400c00d40380d581c1e13400c04800c046101c4104c00b8495961030300302284c00c00c1c9003811290030040d0320351178060301c958003810400000748805220020004003011800714070074070410960300989519280107803524141003081d401c540c412444003440c945440c101c0412541d4082c2c0d40500550703440304900d1103a03101034007000c00707000e10803058110100949a8004106406202c0300719100600091344021018a0700c15198001c040604505600100201c00109000b40c010090869030580e0141c5030039034030703a0a8412100c805001780d0b83c19074080343c9a1160342e40111402c42c0c1c600c0900c0c040200d42040000a01d140c4030b1351200600140d41d55480040580700c5806442030070b034210055035125a501c40d889800c42c4000410910500030f82d1000a072113900406081001100500184 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 982346744 1250 982345494 982345501
    0x10608120304050c18011503021e1c0501090e100504030c08130510032703120e2d0f030f1603020c03120a02010c110c0d02130207060605100302030609 66
    0x405240d40050029552401191070007100d548414884c565030084045145086600d00012041184103ca48600805004002000b521401084840864180d0a00c01076a6a5140462f10200131007070070b00350662400c0500008450200350712615400a000003580d0710f002600c61814111081150014041120160040d001c00c84610207441516842d004000460381ca80c1c1c00581e44c070300700b48a6640040d0300d40055044111612803100d000303407078003c60854210300d9580c001e840c40c1803241a4088240c0d582d0401034070320404000f1500118446181140340d50700141c1014401e00200429084501c00e182101d41c0e40c450000841c0c000d84002c454440c18103010741c0d400401c445030010700b40c0840c851440300e05420342c3c0074049011400c9941c1c100039a20ba4481d00064207440b46603170b40c0014800d6800c0781e28240f20003c2402d8141c680216804402d078001840080d500e0b495103400140700a2000c500030003044196804034082d1201202c1c90082d5928482e03003282a44000c03100f070380d049140304010 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 982347994 1250 982346744 982346773
    0x2603040e040515240d0b070f02030f0403060204050906030d0c1106090907020d0905030d23070f030201020711222013050901050402040308192618010608 67
    0x86a400520400a484070100300495000fa000025100440740001c903103c1021480d030b0203c804d841442c015102d076003400c0c503071362104103c1c00c03001001d08007848541e50018030314510900803a0400038480000c5a100d40e02c3c2d0801d48020341144c000c0c98045c0e031900011580e40d2400184195500031a0b07600e066200d031050313480400c1034881540064001c0400d0201c200103030307035100586104984bd64001e2024140c5844000c0c42a00654016402500310068501d122980103c110041c0c9441c0d1040e400c0342820300380200200d1184150151944101744401c0081560640080004500441c1d500e0300301704581d010050138100703000814200380f82c80010b8040c019180d400500042448121030b0120b04a00310313980c4c5541e400070341002195000175005011614000081034050035040c0d03030031801e040c190b56456001c2d1148a0540c00c0c0e403140c581c040100d0364415049401d400e000c00f0001914800d180303000180b54a13003555469402407034151001142c44d014030442c0f0848102c00020440c40290503030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 982349244 1250 982347994 982348019
    0xa050d020f03030406021e0406030f1a181005031501080c03030f1204030c021203070209010e10060c0c050402040b121e0718090e031e04030209062107080106260304 72
    0x2440d402082d080c0e0341008106803006023000700020b4501169603100408142d048070245442980380b405200c450004030749405003182c58800c485080003886c1e450f440302c0100062041c0e84200d41c1841070340b40841074000681143c60481d0340300b0088400c0380176424200f580f64000d1411709050720400b440758286003a03044500c00c1e0414000d003071020700b010f120740200700340e440e51010458456100148080441c20501a4240100850000c441d4103040203070882a248101b4800e540130042141841418820641014001010014821543e55030f9410000c6e655412403000f10105201c54400200c203501c031510700c2188009590710129a5035544101a00c03040c0c45022070030111449483c01042c5c8030b4883c03080e03003036081c6464011501c0f4940e1102165120202101d00801d00030240b20810040c1c440c1c041d11034100320110303101c032650213440102494044928240c41c18500c9038000000b00d120341075026074203803122411428201a8101ca044103420394010540c69194010041007003c2d51140c2c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 982350494 1250 982349244 982349257
    0x1203060e131a04050304051203030136050a05010501141c02031f080a1b0f050103021605060406240b090907020106050303070606050a090507020c010804150c020a050d020f0303040602 80
    0x5000c0000c0309500360b00301d50403450031901141c850780f00107418890352910103000c51042140d4401586558100302607101c2d2003580c203d4140706219800420420001c59001d0160703c0f07503414008100500d410100c0c0340290400307108060104e20039401c106403180d0b001c0101c0c0d40114095180b40c8400d81488072940c025800240410b901c0f281c855440701505801000140042c52248000e0404000c541803803040c0c0402c1c1d4613840040300c00030208101851894003a881110070900b40140c03100c010b070380c00c50446062400010114007440041000b005610740c083c42c01c8181903c540340e9241070700c007181d840c4070300e441c001c1d00340791704c821302141c00c0c107240c0f8054940e8064134500c0003040f400d0b9078102182c6140c0110100b240e9554641c041403181d814011480c00c01071601d410244200d007404503001c1d44462229880a0410030a0f0000809001d410740b05400c070a1800c850400880ea4980d900135220260103000300c1c0d0600504c0300303212549100003620314406405402441c80c44d1a540d549200a512a8 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 982351744 1250 982350494 982350503
    0x90c090906010e0d300c11010201021e090607020604080f100203090a11310c020a08070204150b0c0a061508150a151203020c0a03080d0b0d0602040308071203060e13 72
    0x940c216009040d0307805c3c1d0543d00306441c1c5542c4241e1005140c400215951140e00b681160310501800300e6440c205006803000c0303a040a007441c1c0c0da23680800481e116104540000c4e4210000160024407020001160700308611240b041d19041070400b052001684016210510660310002c884408103400240b01d0943c908020402c40a00d8445601140203501c07400720300c502102100c02154160440e401112180c01607880a49042d01e03895407100498003a0203c0640910b68808014030010004c03508400a40203015455883e144421051030303440d58680d8040b50b0441c10183c0031400c480d80c00c40e41509541c01d900180001034070b141d120f99441c00b0024505210303e0b8480007507448035007055540c3e8010700601503500c503407100345080181c9080000004280198560401080414028030a9500300700940e540410000d0311030f000034441200340c48024054510006000040001e000020008140300d00e00c000b108085141c0306030300311b4059109540c0002d1040c00010703000c0340e8641402c1c4489100c0c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 982352994 1250 982351744 982351793
    0xa09170904140f060109150c11010e2d091923040c03140a051b010e0604080102092106010b0d0905250f082802090c090906010e0d 57
    0x3044948903501c2e41594803005840a00042c0006940d0002c0000064a030100e8140d030342ca81c4280008041070024107011300283e80600044015038464101240340c83ca009000b0a510341201c0800c201f2001c4100c01d203e07940301d143c0010030b0941490b4025601c1100510a0203d03140c18081d8500090b0070520300c90f003030841000c60106000300d5903040720385c010350040d041e120503e0b0444c42d20780049260b14038040716640c0240510400200002074614060b1340b0011030040750300c41d140040e50013952011003164000008070b8003144194055001c0c00341520216031000c1c40726a880318a00c20180707142d95800140c0c20440040c4411030452000302001001000c3c00074001c00542c0300c80d400d12055480360040c1129883e03481c0350201490580340007800c2c103485417440701442c1c602141d5950b0407091010651880c8048070300015021141e0301603c1a4002e01083d42d41e250400ca451302c070380e20640b6080c0c46560000c010032010b5201d202540f0f50384202500c20b603903c0f00f10b40c40e012080000100c50b0a94004c8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 982354244 1250 982352994 982353011
    0xc140c07050a08070e0609090303040f02030c15030a051003050303011a07080c0c010e040b010e210d081909020105040b0c1c0e041a06041203050c010207030e01080a09170904 76
    0x3a1640b8000080030444050180c06003000707030480320040301400302c2d8412900141413080c130110110032a03811680c0000802080e07409880407a0503c42ea4102d96644150020600c14107815071070b0095107e089032850070031059031042900c141d426101d000140031680140f00520181d41500b00480c042070060310b01e24201040e80c0d65141d11984041e4107200d2a800032038000d0000c0d40c2082e9120350b408000c85080c4106004503000800c0d800c40351800d14450f541c484500e0348500c02c816246013086103544140c6034030407500400908080c6041da0340d01200880601446a180140d1044000d5158165100b6140ca4540081e0035a183c00950901030340d40184080e8600140b0000550305c800c18850312a0b203400b15414003080100c4416954054007120070355940c40499503550100e03816161180107602d030020381810200d4850040a00381d40456100240d00000c0c15080042c0760030405c803d0782d5543d0155204106642a20100d08004004050200aa400240103140036050280d8003500000310502c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 982355494 1250 982354244 982354249
    0x1032307090f1418030901030f02090907021f1b120e1b0109050d0c0902220e0612011820062101050a1409060d050604050714040c140c0705 61
    0x942c04084503800650700c450040d071041c036004003140d0010741420411031950a0080d007030b03242c0c40340074000d604040d500c0401c184402110350595000d06000744c10480946000700000e91b0360090001c0c0321403038290302c90868100d0340950288036203842842c41c000b841c0101101e82550724103041310a840c800d5803070f01c5521080740c03404c100c0381c800f0100c4403040d42c00800e03d280001d00580482d401150241c0c510028400204480b486050116500d04c1e0006aa0f00a6002c0007a940070340a048088200310541b00040d03280301d08102c41e40502002c94010303854041c4035034600d00701d800c1c0003101000060100c6400e40890b001e02c206210114070000c02d603440c0120003000602c55409a0300300c1c1d02240c01c900341d01c124085103007860340c00b40109481d04200c283c103100703281c000720751030b690043d20800d081d4000481580710340500072416179201c1e045568608241c61b00302e850b109240110b40640f6260342c3c04210030b03c2c10b80140c03143c0d10318507101d2400428045560394100d07801492102c03510700c1010320004468 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 982356744 1250 982355494 982355501
    0x319050c060a05180d0e0d0201030b120309030d03050402010806150d02040b0c16180905010f0204080309092511070f03120e0102030403080306060a090e1f0e0103230709 74
    0xc1c4440b00c000a203620308482407103161032641003520300903405100710740d9030300d50064000000f0240031101200b80b04040e00c0103e014041c0300d05030342e4008500c075000010340d10002015000f0741c082141a02c0f0543c40c55401242160001c403006400901300c04040703119420312a47c0c055503040c104c0340d944d1402140d20a040c060780d005034809040b00d040010200c0501300c092004500c039115085074101c440d49041c0d210f90041c100b140540d00c1d215035511098081090940c800f00c0c912807429025174845a480d120180c5a80100070a54015103440000420b203808140d40d07840c103000300d8034003071a040b0140d10007204c20140d08400040b080c0300300c0c02c0200d4010700c0202940d00840c0b25220300200003141600041c49601d07194440d6065510512003130001800490035654466401d0f540e00f519136054480860344550140d000c40c044404070700c18001460064000915541041d09000c40315035542c05644d9804102484050314102c00d540d01d03040011069400c0328403203041401264049515402c03840d046 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 982357994 1250 982356744 982356751
    0x115060906020f0a11060c070f030804090f050f010b07151119050310030201030902130c0816020f06060f01020f030a0f0e030105190e0a06090c080105010510020319050c06 75
    0x8145040c10411100758104426030040f40084040e0084203200d0f0780d003036003100c10f010728a03100d641c1c08501800b00c03400402c2800001c00c0140140310240c0d680c1e003402d0845130300900510104c035080110b428020002406564000c00320419803c3c1161f10341998482c0640001000f20b4491040e0002c5101040f45806083e1000c010000003d0b60f07145610b1380290f0060003400b003182405010320400c00341c54903d1401400b125028207000ca00a40544001191410000c001001c0c00c0d01d06003030301d29a80d41c41400f1f544030388414200348200107100182070380d448480713954564180c0e014000090351818140540e0050550600480f00400c00c940703213190841d00701c0340200d0000381c2d120328807407042c560000c44101109000c0d402000507051000030120307c180b0b9800c490402540b10690714034403030020030102d14541cad0408001c03c00402e462030807803070144d40c80c4283d0300c280d07007410004038080c5007400c5040241c0006400961402048282d081603680c5103641080c20b00405100202c480141440701074403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 982359244 1250 982357994 982357997
    0x20f010e0f0402040b0406080906010f0312110f01090201020d02030c03090f0604150c05010c1b060e07120f1203230a0b090408070b09030903100f020904150e06010c23011506 76
    0x41b030394100000144404001002d400e03c592210004114100102e480f4100ba83d4000c00c0780004860b8125040d946c0d445041034001c800d12410341c070224000c006601c4074242a200341d00351494080400022070340c038000e5450240b40c40d0810072541e412840c0c000615404c84001505e0103003060b550f140c240070080706403007010300451501c1d41488100030081c4078800708403003241004203003581c1d0741001080c034604108008004070303034645808130b542e002000a00014034084d100d101c000a07091801108081c01c03070b0000c0f00c10034001c20f1704190060017030061208074082040c0c0e1110700d0131903908840c1c01c04401780452107416581c00204103551629601c5921941c0900c194030703940c001501d4070b505508001040b000f180e0b0414031103144d0355a004101156034844070000451030440c41e0781050020710800814030b910900d00b110783c19184004400c241c04840146c109602c540c1c1d02c400064580622411000b8500e01d031490b005080948024504000c80701d2800001a1850340e03010140e010010680184c0c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 982360494 1250 982359244 982359247
    0x209040f140a110f034b0c0405030604030c2d1115190314040302010519090305040e1905040516120b0414030c060a0213060507020f010e0f0402040b 65
    0x8503815029580d00d100f0b81d0b2120514082400850124500014024440066010000328200b6002684c0603502c40c1c41c0c18502d1a5100d55035034040146106445184115030300000091f150b07010010a41c2e0031150050040c2c0000e941d2a0b1f400c450304036210001315104100da460f103c14507051146050f9508a01e1a031004c0a918181404060355040044551040c10200d0350342001c00c83c0c65060b200c1c2d0707040d110b000940e486074000064003c0c041c0400d803440b1009880c1d00300001d056054010902441c0c2c000d00d051500c554600324079065078141d1001030301051080104003d0540c856075455401f1013121010000c4030002c42c16401034480039641a903141c0e004505c01c59035440700c0d43c03081c0c004144d040c0d03007800820001e0f5144100c0800080c07010303042501004014045e074009008903168884800c064034124a44010058001e410520600950760080700c804100c683c000c4084031025034004007158840c906000046a11a501518003034220888040c0a1805c1e01d40303001810260107450210f5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 982361744 1250 982360494 982360501
    0xb030415111803030a0c0b18030c010c0e0a030317070528090503010612020405040201050c0f0607020d0e1e0f061201300b06030a0f050105060f04060b0d0209040f14 72
    0x11006205030b000d120f200c0d410400402e031415401210070458294080c1d8180c820382d0310000309401d00425602d049030240000507e880001c1019880100340d424a511050016000501442401c00d51400000e02040c0700d100e143c4c6448070b12400055201d20186802860003028590201c1107100d42011108500e40081d60092610b4002c884000030304015002041250b10b0704102e03a04587c400714001e40119590000b260540e40301d10122552051130300c0032907000c1c41c0b0000c052651400105c40441c014040c1d11400e011143c440c4000d180400310040c8105194049011030300408021070344d00e15405242c25601903400c0e114000a00b50b800184070ba00311040d850241c070302c100c17801d90200741425a94070a010f540314500245900349881d8002440c02420b982d01000300f860181002c002402070060320b03281d02c0421605400042c440d5009a0b5001b000080d04028042914100c1c003a001c4a031105128843c260000c80e4050507500c40c00410114550070403003568001c80320308070000c003070405041c01003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 982362994 1250 982361744 982361767
    0xc0103050106050306030a0f0c0b031f05030a0b041401140c040303090b03010b12071202030a0603120315061b0804170d0c020f090a090203060a0e0c0306100b03041511 73
    0x9241c010495402e10500d5450301000007910f901c4102d5005140140c0c0c00d00d0750051181080d1040050240128200e40d03d0906001c1040c038102054600a2162211100803500342800724140c11040d23400108860103855554444000c01140c10910710590359402d12482101550001103000f142d0410102c2e0b40c80341542001088204c2c240c204c0f2400325003c02c0100041d401d00c0084409991690498020f40e0701c4510040f40c0810580b0070400e40c1c00e002005102c204500e03540304c0c0c411248078404080b0025006801502511000400300e4410b0410030020854a40500c0b164002070300038056007914643d0365a40d03090300750859003000c4850720310b488401048001c2003003d14101140350611402e02441680000c2414200110403401031000c200842e50a10070340c0c100e11074455005040e142c542c03915603440c8004000385a003032a03491084c0e14042d2450704000c00c9290050b0080d0f451210900d051140740100c036807010708201d64208200003400d004a50900c52030660701c000c6c1d1051980c42150303545 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 982364244 1250 982362994 982363001
    0x318010614030d020a2307080321070314010513020705250b04030b070e0a09180b06010908060103060506060c161a03010e06041a0a08030304020a0b090303070b0a0b120c0103 76
    0x1102d0f01554800c00100000c5900d001a0041c0e4681e40c1c1d4185c54510100030b54242403030030036803144c0c155202c0400c0c003a0003102003441210305808802c028407800e40e90088200c094a01c2c0301441400079003002c3c014015800e10ba9120200d40b07903034040252420006030b40c0c05180008040d07011600e0040d05001d501e94204c40350f01c06009040d51940107082c1819502c3e44c140c0e000000e4486406d104e0100048a02034554441401c02460801c20400c00d500c02ca446e46408804802c4003111440e81d40030018003a0360190340840d0990318003a0041c00c0301c2e07081d43c1d01d00c0b0051502400b02076000030140010740d00f0030820005001124003044505907440d11701306031070070300704c0240021000c2c0c500c042c001400b03501005030040394081411500403405d000840440d840c05800e0106264000c0c03000000820764480000c0114002e52003952640c018a981d0250309400b0f010318829203038550020490103022030a10010550030034100303100010246402c0c2c0008001d44010700300301c4429003004211084942e0140f2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 982365494 1250 982364244 982364263
    0x30d0e0f130e0a060e0606010804030f0305071701150306060807020a060908220905010801050609060d0f0611041701060b04121523060f360703020301170d02030906031801061403 78
    0x805c481a4108bd60f0058241890f4040400c2090ba40b03000144646200d61110b1505081506040c449542c54000c0320f418008040f0b0340c800402d09088001034020711502c00107108042c1580500710014580d520300b4050b200c450029211aa01480030811502c00d00c0b0f5041220f41c828445580301d0f914040c608010707904e05030f10201c8144d150034100206919106119540503001319900d0341da10040d8a00b211000c0c0c0010006424603241c900c2c000c2c0c8244400c001002692400389c1d07010616808003500600b81ca805002e1140883c00c1480f0410088066441258030248512100d104107041c040031101142c904c04000c001c60550b03281104101c01100d810280c0014081e605010480004c2000c9042c2c0c00030303502c5003000340711002c8210a011114a540000c21184c44d0350817141418603a5004000c4d40081c09564500203203045040001c8000003048a40700c0c2c1c06070091810441000700f0440242c02c0140300040d1824188000c0030785035002c0c0f248401a20b1000c124400069001040c54903004524 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 982366744 1250 982365494 982365497
    0x40e100e010f0e160c38270709020c0709050c03090a2d0609140a0b01120c03060504050a2006160602040f03030e030d0e0f130e0a060e060601 62
    0x1401c050201d0040f0710b03001644460000640c6480d6641d0313500803690b640d03a10300b010305440070314542c006000b41d01e0f01c00042900441d68064071401a80480c2400310002a40c0003640601015000c410f000900ca007000000320145040d00c003a5a51010071800307076405105029650b40104005001020b454883c079900f08060380301c00d900758580300d81ea09903280ba80020103028800d6501c401d1103010b01d00c50205400100c0e018007280444040c0c5440c4014000c5144116180440e0030030718580310000207213507a10030743c000b0041c4050780d182c00900e204d0f00c0507920054500e04850503010000c11201c0c000d06000758418001062010348908243c45d503004120411041a10a0384050805a4441054821004901e40e080d035188032b540c43c001000303103c0c990101c54400320030303640081456000410307180484d0065081d54102c8c11114030407a1841c00d054140c075404540d040d191125418008000d140410001c0c000086084520107110b1030112240c0c0d085070074649410308950740600074454a40c00401c203 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 982367994 1250 982366744 982366769
    0x30705060c0d0206070e240417010b0a08010903050a030506011404080c09060f0102030a050318010504050d030c02010506100c0212060a09060e0609071818062306090106030f02040e100e01 82
    0x10f101c00240e803c400c480c400e10400044400741e00350a031f4054200ca0051510528420f5200e080340c00a40c0a0000500303103d2003404501e4001400300e5060043d04c03105640f5940b00e500e400320002c03042d0000c0201616090400003001085043c007000c3c0d1b0b0090010703181090061040100400800400c0c9a0092450780248407a1814224590700042030f1003540c0c2c4207040c05500c03581e83d004a0b000d005101504080258207100a00c400d04c900410700d00c01803042582d06011820030710310240d00b44c52081d00c840c2e400041000b803500d1414402c070307600006248010b000c065a03400c45410f103850917209840a81419aa82108608000c1640314010240049002600540c07030400e401300e03100d00f014483c00c144400400c802c8a130380c541652081c00400c50300791078644205050b0401c41c008044114120b140890620710700500c94520301c0c020b0344911300092010a060b824a5011401341150280d84070240da003e01000c20705141c5100340c1c1e072080000c01c6003c103a140c07a14403035686840040e442602201c00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 982369244 1250 982367994 982368017
    0x120c0b18030d020d090510020307020d08100e07020f0a060c020c0102070f0e0603100f05060a120f030e030313030506060a06050c12070819030b03010e011802040b030705060c0d020607 80
    0x401030b11000303840d104006072030300c0e40300003410701500700c3c0180140103015440300100d40c213070a40d0295005007813503400c88900540c410003c0c3c0701e1a1040d1068803000c441c12504102070740c140070f13001d41d00030ba8a1040d590014044840030f4603000c102c2004071080b03619051504c0300203034100949903020400340300601c4400e14201c8051407417070342030103061131002c018000180592420030024080708407045e401c114264076400044001c04050340e1a078495886820b00040c0c0d140541040c4140ca5040b00494100c0c0755541d03016540203002d444010b42501090100e450740b44a403d52140045002d04003074200ba00d00f4500b0041011010341144003409802d00052130036050000300584006e05210b41c0726030780d050310300301819180180c0d1015401c40f541c4100e218aa01e525800806500c01d095000703001c090201c1110900341d610304200c8400000c042070b41c7c0005490940c2040b01c80c8100601600e40040d202d4011442a5001d52081000e99100310000d049040d41080425402011468519403440 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 982370494 1250 982369244 982369291
    0xb04030e0d0c05190e180c0a060509280f0302040c080f180709110a021516030f0b0306240a0f050103020c0c10020a031e0804080a030207120c0b 63
    0x32440c1c0950b41c0110b01346040d2881c0303480c0c2448804003600303090014284a1401c80031110b00440d48000f000c0840c0188140304400c0d040100d5110103645003034940c0f5041c04071200600150032520b48460b00860010318509810901468805e0064070034000328201e00c03802d5005010541c0c495103c0d180401c01e081c410401d0205110b0403031508581c104c1c80e41a2104596841140ba000c580c0c1c129140c110326191f6001001000c0300d00802d03008655400344e40034401c00c0d445d4208040000c8900b070b5050311410050f0503c261180e80030f8131102d004c01200080840c00e54002c20301c0d026049440003501115064000044c96075044d4041003400c0171a40c00110078240100300c419141a4440c0c03a044c56001301d521038540009100191104270301500005402207d110001e40d81d203420303201600491004007005025911089500580e800c1c280ca0f90076460f00c440e41c50a40781d034400c00014040641c00d1007102c1c0010140c441a0700404200e66401d02ca00425040041503140003401203a05202c4d00e904c05500708 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 982371744 1250 982370494 982370513
    0x3201504030f0803040501091209050316030506062103070f14010c02030702150c0a080405040c052a150c04151b0b0601030e10050a060f06170a0b0d0b04030e0d 70
    0x580c3e1003ca510f440351980c4c45e1060240074900d000803e141c0c20f43d000340643c25400b007064000c9a13022001c41e00465007600c8001071440031780c0005020b64001d840085c090703082c00301000400c0c40d1503616002d5883c4c04860901e0a5400c120402c540e068000341da800248068102c015a000e800c500c020800640d0304140a9624458804001c0c001c661a1001c0715004070b000c0d003a41d8078150b0080a5880100d40c0e80740c40f1601e0b5203e802091702c2185031525008000e071191059950f101c3e03401107a0025880170481c80b03800340c02030020b1101c00d4440c41b0522401d604010b5100390203003052515083e1902d0420744201114070366801b4102c10400030070200f4031501810506803071040c0e041205500c9584402c40101c1c0904a9800c41d43e45501c506981c260009003590710040c8110415642007000c681c50307860803448031103035200e202c00041e00704000050949078a00115000910010001801c0d04140b02150341c1c00c0030340805031000b8088000304801c1c907800c0b10300302d981c1050440320701032003049170b95400c100e0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 982372994 1250 982371744 982371773
    0xc0c030828020a20100801080d05070f110a0b1314060309100902040b04060e040b0f0708040818040603050d080108010204180513081b0c030312070e01090320150403 72
    0x100c00c84810002c0e604131941101c804101024040c103c001400b134001034030011080c4140051440360240c0454014030503010340300e565501580091440003da11648030f01d00e00c00407c5a40900d801e03c00085150400c0d00610142405d19080080140b80110780c0d001d02070030811050040d1001c00030030080250116059102c00c005500001e0044c0c0d0700d00200340102030780c1d0304445e0054036001002c05e012840d100c46a00c0345208141d104040d6850401e040b041000544541c008100c040c40401c5c00600e42c04003401e004907980d480c41d80b003403000e400064269070f07203076205440c0b0783c0140b42e21000c0790707500c10304d602e0140c540f010080d40303032501d844100c10134058410030b440c200f2907441c00400da4100110005213034458010710300399116a207540000c078106d100741032440524403403802c0c80d406030704000c0140c0348140444070780f000ca0b959403804151798501c0c15025987c10002c1a00020000071111780b8801324424a1520100420415506000300c004072484e8080c50b400c024003007080045c00c5c103524120f4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 982374100 1106 982372994 982373003
    0xe151c1407061b140d0519020706021002090301020706060b030105100305010b0a050c011409010608010b06040b1603121103061005280c0c030828020a 66
    0x340c41c04540301e0200410740d508814580c0c0b0418080380b0790300c00d019050818000d950f640040d420a290b14151030081640407628944404100100100410b114001440b105080c40400303551901d02a000b880c11580005a00819403401e4040c1c0d21020ba2102c024403001d034407510004510b41090240d00d0250801c0c02c074480f00603200e40241812980048841e5142004054049820f948484d012030641c2d905c403405011514014210640b050801c2400011a0f40c2005500c03130a6a04100c46940f02d09001c1c00184015a0400120350851074000000c002c11001c1d460103844158112001c040c01d03d2400e50300302d0501d10000001d40c800c00003214000c0002c0b0300c14400391010300414201c031095021060023061144902ca441000f40040c50600d00c00c002c0d515a2205120703400d6800881d80e82002260741c02018071151340c10f00b03106000031007244001e440d25000030750f03840402401a0 = true := by decide +kernel

theorem cover : BRFrame.Cov 982194244 982374100 := by
  have h0 := BRFrame.cov_init 982194244
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982194244 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 982194244 ≤ n) (h2 : n < 982374100) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
