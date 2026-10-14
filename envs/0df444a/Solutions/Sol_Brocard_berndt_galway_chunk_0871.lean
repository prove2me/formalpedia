-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0871
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:19:02.101026+00:00
-- url     : https://prove2.me/submissions/6c64a490-d589-411f-a284-7765c9b0c1ae

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 156474820 ≤ n < 156654676 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 156476070 1250 156474820 156474853
    0x1020f0910051c06140109180507020f03070506151c080a050d05160e03070b0d0e120f03041104050c0405010f030912170f22060209041509050703140c0d0b03 69
    0xc09031040b42c05c025000120710300040d26401454443c000c0d90281c11071400d04070700851381c01070703400200610583c0c01c0f00c1d00c9180f400c0e1658002540c2038034180c000d481403008808a5108404140d641a40c0561406103a05103030a6121801400139140741e4001a40840c658030074400c558680002c000c0421450400035007040d45841c00c0b04610012502429240a40d4500003c18408580c050300709545090380c4605800c029016801ca030301528440c212070813260000402c003030841c42c0d50f012201620707841c103401c00300c064480e40c03854a030049142109104241849108640a41d01c080c240358000601e482e0023240240580070010b13101000d0b0020b40d000441d80640340b206c168400d40d050001a8450f5107554000c50f03000e035203270700b400a18070520341010300381324491080190091500609003426040402c09a4040d0004010b00741d400803400c0c404070300644142900325046150802c030305000e40d10040c610080180c4030f100d001c0740203c0c1b01c1400809980042a428001a003030b103c00f0300a00c1c0e0b842 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 156477320 1250 156476070 156476081
    0x706081909080a030c141b0309060406030b09070e0604050603070c2001120b0306011203110d03150e060d06020306030c040f0c030e19151b0c050f01020f0910051c 71
    0x60006070401c0b2850607620710628414054200b403403280c625150401f07101c403201c421401d41900300d07400240b10307042c00d5643d080c4c007400080203541c4021804490700340c01c221400000903c25414440381071103824540e00c0d4142610180c038400d690340c5a032916000c0060740c18525030400140082c4903e22865000624842c800e03075681c0082c0c0b10041c0355511094540207807410300081c2c131b405601080040029044040814000c14005e0038244c1c0c4034581c024a05060040c00301a810100b40c51b04d880c4000c8081d81001e1702c00030a02e011002180d0304048000a0b05a0f11065016044036000701c0402e101d030385c041c0a81c80b0f40450051080040105980e00d02e804ac1c88200041c00101b4502200c40d01c1e0000c011036070500f0601152500c07034142029a5443c403a07094100d080800712a654005503070008130708900804001031641303541d00e181840386802441d01030301c5501802d25900510049400043c0f030403d48000380c100312425003000b45103a1040781d9500409502200426082003400911000d56205 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 156478570 1250 156477320 156477337
    0x50c1006090605181b190207060e011d090a0f0c0e04050108010905070303030203040503090418050f0f100b04090203120304050c0f0d0305030405011b050a08100602070608190908 78
    0x80c0480ea5441c0304100481e04400c600300688034428001580d05c000f940701c003008038070b610050281414143c00e10850344125421001025921a04040c0481034110411121500c400d203040d007001050340540ba03d4000c886159540602c410301c0104a840d1820307000180e150742c56a20800074810700c210f0041c221620029000d0045141000206181c3c0041c001e000d0410f03004802040101d142d0f03a8203c0003075200800a0b02e60340014003400a990307072140103000180070240f1790300c4226601e42c113202e400e0000b100b091300d240d9448150020f5007120301003440c3c008400b10785800100d03040b001000c10301a100b03010009505028024203c24100c6121000d940164024400c0b10041d50402081c00750f0f01416026241d4030000021103000000e100b4001940e100d4410000070500c8154980350400031061034107440702080d408110b00b103601d41d0006100b07901003481ca84652002e81b500341301039120b2819000307000800001900245a4110581c018050540041c10030424080941040c1009800400a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 156479820 1250 156478570 156478589
    0xc030e060a020124030305030f0c04080303040b041a0601081602070b03090d091401080c03065505280f090507020a0b150d1502030601030501050a08060a0c050c1006 72
    0x1800311442181c0020815642e05403038188c03440c0c0b0340d0282065041030040503012030030010040031800840500c0614066445284d0800322401c06162907c10b40640c1031028084003654000c118041c0c1c0c1c42401c0b00d411000c5172450a003244a480c50032410105584c02c01c42a903a400001d01003111000220305d5080340541c1c0d55998020303241d20505500070100f41d207143c0045c007160081800c02000500568001074000c0072000034400c01039403a0200e1107168031220721a40c2050008032080c0c0312140076800c03012001c04041c109004190f00e18034807a958040c07075000b011a0341e014150b1a80f5003941d40b0800a07603e11480d002c5a60f1001c008245900d8054102442c1c2002c01249100d40005017801c045039003c40b107015207030765246010310304e03280350b0348a20742c40f11401c22020042525070000301440000400d01603a01d20308070b40017409441d4103a00c01d5018110390340301007007500000302d05280c02c5821480e0118a04501c048200c2d4980a0411400141d004402890031300c14582c0c3e00410880f5101070 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 156481070 1250 156479820 156479861
    0x4140108100609061b121706030a0503030109090203031210231f0212180f0901031707060902090f0a05010506030705040905090307060203010f0611010506010c02010c030e060a0201 79
    0x10351880c1090041c4180000302e030b49400f060201602a000c003001071511941c642d4551040c0f40c5898180c00b500064403800705000018903200156150b080a40c000f400f5801440c0079821651480d81e01d110502c980851566201125021541c040c01101d21a1100c420f900b1240d0500c0b40d840780032009184504000c203003000980100c2d80104245411002c1002800840314851b4a0621080040340000103c114041e41e456a241700320b00d1800381c150441076008006516a2040c18481c1d000103c8400f035100301c420000400014524400e6074103040d0340701c0a0745440d0002460314401030461210000e5000001c9010000804c000c2e840c0548a40070b601818000350361b0f0380e4144503c1d4070007626001d00140b010801440720380381ca0f4100303030340003034003070045a00d844803130303115a4200d07003003030700040486170503103104100781130344440c1110200001e074000708907034206400040e020590724840241030010f92514103052602641c180800380d14040c104a9441c082150020300030726004c0901481e000303111 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 156482320 1250 156481070 156481081
    0x80a230303040302030d1a0a0302010e013e01060b03040f0609080714210306060f0d0504030c021305012405091f1b12051b07060f03050a05040f0308090c0604140108 72
    0x7c1c0d102d01c03030800000c1c01951105081d500111054400851410305010209850660801c00c03a1407051079450300002d4491340c4e100c4004050504001d40c40c0080b032513810000c0500005482d941181e401c55030081200f480b0031141d2800c0006000c19000292030250003007846014880c0d8075a8207400890100d040c1c80402003986e081e000b03620326081010501000c00c0c4001555820940300601c080420380c0200b40c204000d8101c0c503829a50112011000189440050000c6003409001c0c2c000158003500c05200035030401000c4050b00c4004504200c40726003d01c3c0d4103d450740558210344c2c0c490700c050a000c0b41603d5410382c03140001c1007890b0b810300082020140c00c400c038002c00300c0212415801400381910508052044905401c4884807071840318020300d80310510311003042294001c022a88071a000510301c06005011680000c00c5481098284810013000940004603c07a2043c1d0504042542d0380700c0c900014540800f0101d903507001000054040b8445d004909004540d0304242d0368222544e564 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 156483570 1250 156482320 156482351
    0xa03150918030f09031e0233070201050408010203100503070909020f0925020609010b09130311010204090f05010f0501020a05030318120d1a0406080a230303040302030d 74
    0x5165031408201158020070009218640761865a4060702d45035039030980782e8641a0300c210103004024030041c40100e0000450502128142d05e0540b03142c1103000c20b0003030110001c2c1946882102c440c0e0464001791150440e0b008805403000741054200854603071a084508240d14003050203054805d120382200066090b5442c0603045030f40c4d41c054608a42c1400c08c4080c440e41d00009002d011112052989400c10300e8080034580c0141031132640207014030b0074485001401c5508071421180102848002c1010081003500941c240c598146032280ba108502e030000350082c0204d8003c80c2070a0b041202c1c0303030700c1d01c8181c3d0485130580c4e10b80b0b00f0700c907841c0b41c0d03500059070350311800700004005810500001e11014600276011000f00306000c15a4002d50041020100944c854842003400680d01c0520a21840201d0380c2d50014035030685003009040c0c109a42d00d0781d9844410002860100b62884a0300b11030485001030b140d040041007183d40740c2c1054640079449410188260001c1d03858010031001d00c408 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 156484820 1250 156483570 156483581
    0x30708060f06160201050f0c010e030d060807032a050a0f060e03010501030c05090c070206070f0b06012309060409060e0103051b090601050a05070212011a09040515100305030a031509 80
    0x810f8460741082d24a90045d9603a0300728006115946d0018407091600d03110030300030401d803c0242070140d561181c0a04100c000c981e41500480107c0c0d0017024180001a18003000d0001c10010300c10f40841107000c16401d0761540c00781d802c01500a00c0550000902140041c998420b0b0b6101d511521820b844200034127080328824800500181c2c404c58080003507090a140d101e4000d88041003107844c0c00d000350007084441d4041e075412101d844141c1150802c0c0201d07600c946411240c00d213000700c0d81d01900441000418071102000c520003c0004000209680e90802c9800030802414180b20250f518401a80740c40350903c02602ca40c0030b450445480f016072100494282c1500810599842c0c440c4401110310b500403601c154244001044040e015940d01d90300c9000740c5510710000702d0300f0b0f0701c020502d882c0b1080d0780300020302414400e410300000075400708072042e07010900d4607030000300e039581a41a10029010740c8060118080055124020780d4103400c885402d40042041c1c084581e90390003c10107c84 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 156486070 1250 156484820 156484837
    0x1801020315040b0105040b07210201140a0515123d0902010905120706110a0302030301120507050901061205060a03031b06020903011e0b0609010207030f030c08030708060f06 76
    0x78501c19034091140390680c4007103d0f0207018500709040035255500c0c103032103a200700383c15690341c615600048110030b0602088069621644000d2092590445000d10600c0f4003034448511180c4071000610b03105c1d858801c813900200b00030300f40400b051000c0540d980310300307101e0043c00e100758107082c1c00d421100124035001c2000c030a4900f440c100380c040c841184000c25030480c0807410010ba0784c1e00091283d560a0901980b0400c1401410169286c400060055080c02d148902c003030b004000508040b0b9008410380307045841c1050600000119464902d00b000000d0704002d44c010301140002c82c0c000e40c480128407030a940d0341000c00c00e5488120030003050024600c801000601c499036252144400f0ba81d010007058481c0c0e40150402082c540000d0942e51060240030b8404491080c100f0203000f28000c5007a0868291106032401c002c60340001d4884816001c0a41580000b1401004040c4111400701205801200e06174407410b02e000700a1089006850151069020b124424030a18046c5c045480f0718 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 156487320 1250 156486070 156486091
    0x120f0e0604031101110c030d0c0201050105010509060d0f0c050d06080606090a020a0306030503040b0711090f0708090c040501030308060102100606021c020c03070305030703170c03060f0409020a0e18010203 90
    0x7541da507034003100c41d4030107401c150394295251544e5422000424010708044d00030f060244d03803913602c0303018260102c8100b111004c00310781c10300b00100480e9800c17100311403440009a4119983e44400d09400002c0c01d8900a01c0040f03516240c4a16400c5a22101800621001c0e0b4020b01038207941d0716a0303d076254001d41c0d01940c80b40c220030200b00d62160903401061040d9440c1404280d0968a4803802d085030020740c070810510400141c09400c02112038040c0810420481e8041c08505181c0d8142c001d8032070007480350042c400c202001ca240e01004006151408000030001d20096842c2e01d4003c1251000707440c021f02520403045640034858080c002c5405544855004084548481d00131207500000c030b01d680340c15401580900d656a171802e02c5542c002d14003d60080d0303a5600640740082c880c0400c0c03019090340805c0700c1e0900540540c01c0e0101ca411500841c0c8155a5131424400140141a0070381c000b9801404000b0020f062080b00d029648134402e04003660a01000d0905103500341e2008540d00c6458 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 156488570 1250 156487320 156487333
    0x180f130201170405010b1003050702010f0908040512030706020d0f0509010e15100f0e01060806101209060f1803030b01050a090317070803090307020307050103061404050402030c10120f0e 82
    0xc115031940c1d82e580c450301030390020400082c503030041070400550004010010340c907801004103c6809010b030050882008a0411403a50327241c40388581030107a80180e510071100690042c9607880d0420a40b1580350700220215501d2746004443c1d002007142c142c81003562070038140007900c666010300ca076130202c40c0408043d0001c0440400180c5950360002e01071055460f80440204851001006841c00303050003d601449550400c0e902420185006003440d201345602c0c00c001000943c0010880001c2036a201d010400401d1807502c031025107004480495139034600342107014030600e010901c0550900a407010440c02407900011100b0748a5a00c418010400c0c80e0350030400140c0105a0040c01c604c080250760401c980d90f55840d48070750080d14000c80c603610108141040d85414081c0e0030040000b401c04100c0e080c6801880d213001c2c41d0381d4031400c0c42103948100240075034900f448651540c08000781146550130610a01902580c0244440c20280e4580001804840350328030810000000b800001c140 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 156489820 1250 156488570 156488597
    0x4110702061603051b1011040b120c04030618020f09010f031103010e0625052a0a080a02070603050108030f040302060a020703021504050301150b0f18180f130201 71
    0x802c000d10381d81102000002c2101c0101c0c00c1c1468440b504c2210312001030700000c805e4404203000e5520000c020a400d0386c003040200481010030003100e04014403008901c5031a52580000210b5001c1c0e0390010f03050300d007411181d08a6854800c000c100f45171088030594464501c00c82030040700d0400340102c0ca400d0761082020300100700412010011210000d001141900c48100c40b281040406d503565140907180c0c2c8801d800c450408880f0b540d4080845c42d0490400014205940d0189101c044161503001c140100d00900c1000340410001c032a0012031256840d00c0d0000000c0d035440d1a840b503000013a01e400300208039204040211402c0040a01d501070405045400b0080580c2c01001c82e4019403254510000050312800004044c0e040211144c50700c45103000c1c249030135510390901004a1607460b00040c0311880b9810203441150340c1c0c0000958440c2e0034008000040c6102000a0b58042d0b0314521040046d200c007020980318013041040400d01c1d0f154070302502e200003034110000340443c0c02c0c0c0a9000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 156491070 1250 156489820 156489847
    0x9120409021e0c010213060c02010e150d0501180609060b040303050901090911030609090f0703291005011b0302030301050d060204090c0804290f040611040b090411070206 75
    0x81142e4803510803100e607810b00d4074145003644441d003154001c1c0d4021510450b54a508511070004017850304020440d00711550000305080c1d4441041e40c8250300301c9820b02141c2080b00d055840144100700100002e50319900351b413900c0c2441031041ca0240e802c01c8004200124180180812200400c02e120300b0a41995026500c90b04088101030420030301314000900b0b81030900480503450341070900305659003402002c0c0002118000c20900c5030b40d0284c82000002e1500040c180200c81e003101300c00540c9545d4000c40710240c40e928480700b5002c0c0d80340043c4003102c00302d8141c03241120001d80703a12150760004440000000c146802c003a02503002030004102d00d05202d83e241400c0b5220340e40051a2039107509400e42121030502000c000140d0703e00802041100307000c0940394104101e189420300ca59529805000900c00400001c0b103031100304045400c00445810020490410345025500c0d280ca50300411010b403c40c00c00644241d0400010038048480c1404503510103070080e140b246450a01800007 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 156492320 1250 156491070 156491077
    0x2120901110a0b22050a020f0609030703060501051212040e0403020709020406050a141e0f0d060b0d0c080c0702010509032104031704050306180703080708120912040902 74
    0x80d05001881c0488080d101c000d00032850300510600d1119618240107440c01c00168040d08005455403242c503804003c6613001a4181190303070304840c4021081840c00128036940200d04000386c151107000004400c01c0b080da0805030594200359043d8070a0b0350001003441e60360480d500340040003179040009000c140414200194480c0c0280112501184c1d1107044800301d80c401d03032103c5d000400101d44841095400000c846045100d10781150801c0c00a0050008145400100c4e06104400042100e00960f03240280e40c015440c04504214043e0791713410103812540070b18840d502c4949041b58040700d950113507200f503000744004101f1504140d9540c0c01512150b0201d0f000070b5140c4a900c0e48183c1c2a04980605139801d40c00d488065241e40c075500d003542030710300741e0040300d440000240800d002c0740c0c038001071040e400318070103070000e60484030a004a410190350f604068991040000d4481c103011040004004c00b11520019255039a02e000000d0b4554030494084641140100000c00844000d40c014 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 156493570 1250 156492320 156492337
    0x30105060108070c0c080a060203060f0102070806070e0a090203130b0a0207030207120609051618090206070303110f040909140105060d060c17090f0105130b0c030406110a12050601020d0212 83
    0x1c43c003481c2c40705000387c54429840300c00c0326111340010401400e818415046020444280020071585040c051419120000205801d0402c508a50034090035610700241e907000b000b103034408540e00c1c100192070320420319543c04251007014076140807981c40c0c4014802c58100c560164043d2140906105020342500c2041c90203859040d15202e4a0021603000d0009140d8009a01d07080900d00c0d260ad4202c2507044a5110510040c9240c02003802c00f5071140821210300607414940001d00c1051446240e0781c074082d40081d254124000324001c02c2c0d203a007035807069600e40c1c0202c0c402c3c007101c0e2565012500741c91b801c554181d08403651100701000070b003c1c0e401840440b00a401c1c07a21103501801403142030414200d48400240d40070120b2813050440c06e108641e0000c40824241c02c154045454003090864040c05140d00528008002018003e02e40d10501ca04141070980c42e176110514400204100768010703e00d0501d518100101d41150300000316011400441c0e00501103842d9014544401500031040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 156494820 1250 156493570 156493583
    0x60115110303070e1309080d0c110a030203070b010f0602030901030e07120305131706163c020106051302070212030c1e010b0f040c030b150703020606030105060108070c 74
    0x820038a124000d00141d486500d196445080c1030340303800200100b0f6140030070b04003441443c0c40c040e80041100d803c01c440c480c45140c40086955243d11750700b100e0b40c402c0c0c00400401801004045003c2543c084014000c40340101c0e0041e0440e40c82c0d007900c40d1001f00510941d80980d104205140042d4000d41020752100000015141c2c49517450001c4407411083d244c081b4001078000403001031580294500301f010380b02d42980594070301c103400b04a95031250041d0002034000b4100550403281442040001c0c480c841c200882c11358084400721010b0300000201944142400c6042c0c2d0700800c070310510078a41103800c024005114103d0307440d1510000d40c06044c082c1e1b0015225030000349402010401049542a1080140049400d02140004c0d070600d44c521402c041c0d060041b90702e0a0b40d140c3c0c10b041034800d001c65000a004e03802000c254010b0031003405080d0070245040403e60803106840140021314002c3c0c0984e80c40b942d89000b09801c030f91b0125001404101400d02041d182c520520419a42c280b0800 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 156496070 1250 156494820 156494837
    0xe010807121505130e0d11070906090606020d110c01110a060203070806180105060702010807030e0d020f010b04150e0603070306050405030301031106031306020c0703060608011b050705060115 84
    0x41d100c00030364550001d050300142e9452030800c85810002a601d03e02c00100c030040004900000380c444d281c2c06941c5602013003054100c84103400c1a0107100940040c1003140040120390313503070040c00b80500410b00c00d5102601a01060a1000e400b4690500300610b00354050203014044034019905091700b500e400c001ca00c112859640020614402980120740a0321038801501d010001c104801c851100040e00188a800040099440342d109980200340d09003822807040e03650442c118001d06180302c0201c04c074800c2d00141e1075000e40218507258400d00c070400a00c14081a04184415201009820541c0501040042008020400b02c061304248010306546165036a42c83c0c01e0b0070f0711004d4400b51443d8000000400810088000295401000359001800c600d032218017444445042d400140800d1b070000348118a041c1c06108000103141c3c009001c10040b038030361a0050081c1441d081c64112203055940d06480c0c00c1c00b81083e02c400c2a404001886940c1c24982030b001000c0e04140b40406115050 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 156497320 1250 156496070 156496097
    0x100f080910090515060a030809040902120610030303060605040f030807050102121801050a110909060102120a021b040506031b030a0227011502070e15181503030a0e010807 75
    0x9002c1d41c40c00301c0c061402080f1400751005180c0e02e0380c201901c080d00c1002084810400281e0420940e03c140c03c085400003940403060010650540f040d07640480c40c0e014000070404088a08400c0300305980c040da408202940d140d90080ea55403086004403d14481c84480c02c100242012000b130030900d1180ac0058101103040c01d41601d00402501c4144a01c400710454034502d00091240540c04035400005220100003104c4060040c400c602180f405610103800003400380c0d00800400c1030300344036910010340c0e4400d08100203440e20416401014000203841340b031962440d00f409042e00443c80140541303803941504018184003046802d101d90035006a002e040d000d6a1030004005c58000004500d01040d010301c40445440c0380160000e14410f0780c0e5590136020380c0c0d4005102415111546441d40301e03611140a400701388518035000350703030090342c0c48010003100d410304a110780501c6180070b00795440dc08680800d078a9004450102c4006514003682c889250301c60003a69802482c0ca040c0100b02c1e030202e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 156498570 1250 156497320 156497353
    0x120b0c130602030a020c0604030c03020103020c1501080313090e03091e04091a10061209020a0803073f0f0e0409050610090209060904020a140406020615100f0809 71
    0x40ea0710a070056000840c10601198060060088001007215040d10f0582995105010b4080f03a00010341095400700c2c1801249008100c18900707510f01012002807582d461044540d40d0740101070706100c040500d817000900c00041d00800e00000a0280513504200c41c0c0c030240180f0481161080e18010310040c20114151243e00c00c070401c85000f03880350303100600507018030912480c000d854100310040f9800100b041e10b92014000c0e101d120006030114000083c1e00000782200055001014070b4000025007508101c001e001880c500d070000740d1140040100b04551601c8180c900100301e602400f40b0822003112841881000d0045103281480f85111174444085021115410f1003280c096200c081409114820034000b03100070503107035070194a0b0054000108800307024400c01e190060390003013540c82410380907882e0b054003102d14200381d0303031210b036500002903031840e0581c1c00c040240361242000940d8101291040128922900c0311088140b00300000c50701008010300000f4240076440049914070320 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 156499820 1250 156498570 156498607
    0xa0b12071b050d0305240f01090317090a06050313030509040e060a15050d020a05040b04140c030f0f041e080c0102041d061206010b030c040e040f03080f01120b0c 71
    0x61070007042c0614000c10041d04a0f080034240d51503081c110848440d21b58881d103980320000c80240c503060014144c8400584080d00250002044003603018403403d100300b45000a41004542140c181c0710303541c0c0d1070009884921042d138203c1107600403843c01d003000c240100c0040211a01c050130000b224140b80038081d0408806031601881070b43c8a58040c0c01e04c681c0c0ea1268130203080111034003d040c0186078005070510816210322030142e034442245031201e6450f9840300e4000d000c824450141c0349048032000710150f10440e40c0207860013852011030304100304102d1080c0b2032944601e14240025640345100d00c02140d2503c11520301400708090202c2c1042070010340300810b03011020038155581d00c411385c2e01c5404010141c5001d00c031810b0703146505420000d0b02904503450985c446a40e41c45000001d011441160085880e02c40614184020040421401e440c401d01035980c0700455100d081c4203070071400b820b1044611030002c5494500c0480c415141158000c00da4020b120302c1d004248800200191 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 156501070 1250 156499820 156499823
    0x80d050c070204060503010614090405030f030414100216080904060513090c0e0c0f0c25031104290310140117060108100b0607050601080c0f0a0b12071b 67
    0xc00128800c41142400e010740409810114020310503281044118001c00c040c01790800d03c10309121000c41c09000d02481124544010a41926038a107400c1c200f80a25015280303101685110701c1b881c04070b10604500c255014081c40c2400511810b889880e4040c09801444000d58456900c04000965650310700c081e0b1041090400c02180441242c01c0920603540f0b01d0b80500d11001c01d610400070780304400300460794100707038886005848e0b040b034440c224603012034008000411141d2004160811046640b003c040303034481c1900100c1a2240000e0009480144152003240303051800303c0040c65004403003c00d0720300c5010b4112560350400c100a42c05890001d020004072242181c0140a00ba0441085202e200c006d03400504d05c9500d451a0250b03280640301101c0c50041d51350b00d0345125980e940e0119688035410504a07803555071988411601d84090802d101d04c03e9441d86e01484190420700d401100702d8421580460800010711044800030f4001030401080010f91500700d402094002000555203 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 156502320 1250 156501070 156501091
    0x9030604030801080f0c06030406150b070507300308060105120114011e05090d241a010e010e040b0d0f14060a0e300a030b0a0603090b0112080d05 64
    0x551402c00d025042408805070005250400a00400d1a1f00c402086a030066802100090074220000c0301404070545600b006030210b00c000707440c80074014001117070800c4c1c07540701e20b001012840c52029180c8000752074a86841c2070030a40003d9012900648020f5809039042c1072462905100802d800400b032001d811400200314400300300d4a640d40c0c0524010704580d100741415241e6004000050818081c4000305881892224055403c205009030700b400714554011074012801c2420910303a02a0030502e81e4200200661070112029600c0740c55410300056040e1209000015080c0a210103000c5441c080c641201451200c00700207010814410b440600405c41d400c1024850014181000301c064602405c050800b038640621840206041e5401c1c1410161044946401d0b91901050031000e8585035803d034000c2456211190190003801e01a94121511400303652106400e8007200ca8424001e00b40c079800303000500ca0070b08170f030f50024156409008103e08000d8004003050964100701c0b0801000d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 156503570 1250 156502320 156502337
    0x40f020403140303100e062b050d05030c0f161a040606051504090207050f1b0a0b04030b070804060b0303160639120e0304030209090607091a0903060403 67
    0x50000b980d84500e41c1e1042500a180745040400d0a50009010383c02103d510010a0300803810fa03686500b0701c09201715200300031460280c480001c1c04508031500d4026200760003140e0540b411644a90222849620f1480704281013865084211005411610305681d03001501403d01300420b14560401c4a12140f003a0343d00c44a152a10702003040c1c4405502550007244000540b03003840c2e00c21001d440643d0650740700180c40b000c60f802d12038503002c08000d24460600400403a9040c0704011840340104070340548010400b5599a048107102d4402ca1001a1620915030040f904081c451002c1c0b941203405200b0219640e04080f0006c0e0955104100140514011588440c20000c40380584031204003d01d014132058403440480d4884c40780b0080200c5060010240d82990311030064040b4144200c920600b00f0451320340020340fa549500c00d01060748036400e03010005030007190009200b4401e03509907a502c0c981600c5c0420965500c40d450070f24a0400800380100110f42e00d0070005140700d18040e80d5000382 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 156504820 1250 156503570 156503573
    0xb190e0c0d090b0124030612020904060b040608010606030608060f06010807020703120207090e010207050607081305010501030b0f130c0302010e0105041508011401051201170c1302030405061e06010804060b040f020403 95
    0x1403041445c0040070300d030419008002e4000000c0c0200080c0d034054601c100c40d0f41d210724000e0010826804201e50181c0382c6040421030441c1548101c0c159190b0380c43c100070301d648682185540704000c07111900c0b01140341d800203800e5482502441c0e00941d250044030121500c031380e235100c1c80f0b081903c2034000607800000d041000700c00a024568120300850000c5142880c161503503030300d9240080882091104200215040d5604662000c041030b03040b10007000f5079616032400c00500c1d00182c40102c00622080c002c01e50060140c003850707003540d030b0003501410854034584c019501e0760b582200c0281031200c244000201075880081c800c143c18545ea4402c0015810f04d9207503460700000240043c10403000340000604004810f0b1101d040d510718540402608812041c0d4902e000704d034449040c1c002c0c00c280d084580349030964003c0d5004511030760503154242e403410318049900035460701c1e0300900314502c0041409540100345241d00540102000320703ea43c0014081020b440b01c002c031044405a00103030410 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 156506070 1250 156504820 156504869
    0xf04030f1112060619030f060e030c15041101140a080a02130303020c1203130e0901110403050706170408041701092915010203031801020d0903030b190e0c0d090b01 72
    0x50141c5034410354200d45c242180c6508240f0012141c0040c14541d0396800128034403400c205582d803951024040700d4520012060034014520709580440d00040b5440c50868a0360080c2240c1403161a003600d09401c0100c001d000700e49110300030f4154007840e6420480f640350b051400684070080e5009400800108188009005058512000001d83d581003400b040700444111050b0f00210f50040a098416071549643d5a004050b8081800201d00307001400004200001c00c1c54811a4502d40300d0400c50048074255a403801000c460083c508401004103220b1100000384a0b10704840c480c00004d401c11320740d500d4880d0500e4403403400603030201020405000c81d01d410030301940039901d0802c0410420300b000c0040e540c2e00014001c2200701400e801180e003000300c03d5069034420074100c0010f0040310780b41c0c00c000d001814a01e81c01401200d06402842080e8090310700d480442c1d4050004030b0071039840c02001c010a0b040904140e030300c56103c0704488041001c0b0303012140030700195401d40b60045180c2040c403 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 156507320 1250 156506070 156506089
    0x90f060e0d030b09070c17040807182a1107091e15050d0201020312070903020f030d170606040801021b06060307060207030f151508070504020f04030f11120606 70
    0x500800d828a4042c0f0303001d8403201902ca8000c841810101e00c007184a00e842170000014030162008034002240002c0c141400040039011126080d410102c4c0e04410701d00350055450b215a454144084041d5900202481030864007106110b49049030601e45030241171800d00c0c0e00303903000c0b418441d2104042c10007400c820450001505545008000142c954164907544508a100c0d56103d100c00031400010369000707004680c40107440b2050300c18185050007001e0558415408143c1c050442a400b042150500241c0d041d0044c0003621181e0000344580c1c02d902c403941000309107581045090000040b00c440c240043c01c4d10801c04110154442c1402d03984528042000b0007141c0300f5801030b02c0410507a900400d0a81c00d03660000001081400142020300f0755091100ca025002c41c50041c20090040d80340c0b044400b902e5010007500c2c283e40e0f8604c1004107a01074202030003600b03041003008100088142c034619282e284070ba0041a000c2014070300161101e42040843d00244c0c0000017040000c3c98000540f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 156508570 1250 156507320 156507343
    0x1050f130501080114090f0703090209071119030503060f04020d06030305031506030412030203130c0e190501050f06071a2d040b04080d0608030309010e1c0c15090f060e 74
    0xa42179140b00940002e08546409024a0703958215600400c0c1a140b281d044107000720707000350106da44c50a02c00801060741d40308070071301c4006018004440e101c01c00b03807003214007496800d90b8030340e070554403280200940881f0303642c140b66002c0c0d4200945503e041440c000d40c0700460280d29040d07201d24004c0c0c9450b2064000c00021407285200b003003044006003400140400035421450010f03141d41e00c104040000c602038a00252480d4030110000030035014000c42079202d40f00300c04041d40200e014038041e1081d11020301400741e208a40c0700c1c5051b000d05201015140d000d01903200c506503142098500420f22700181e1b00f1031a41c0e1107008816641000b10256890084203c2072101c04074034180c1c480030b0f0b441c1c03030103072000301460800590a5114004c0c1c0c1c2055020700b80c240103407596030801c2c0242900804400d40300340494010350740b04c41c0501500c02c080110742c0525441b00b904c0c0300c003183d8900000f07041b050109440503030303600b858001040d5030b60f0f9210a002d101e80f80008141c0c66130703001d047c03400189184 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 156509820 1250 156508570 156508589
    0xc0803040504110415050a090906150216030b0106211802030d0804080a0309050a120201240302090f0702160603140a3602030f0c0f0904050d0e01050f1305010801 71
    0xb0400241c585c1e03440071000c006032890001d456003c006001c031800308180d8498180682802401300d0f84151000c0c401e106020744d60200c500103802c8805110810409203c0038104840030001001014016204101e00e48901801c2e09249190136003420228cc60303c030b410404d41c80d1501c07034503030441c20304005200c404941400c0441041c5000e9a4580c02881460070342001c2646420825040010400c88074018944c885010249140811070090003070245022054400516146074401c03104100528020380c3d03005001140300d9603a803011442c2040001d0103000c21880b480400c40c81d4082035085180280c2007668000c102c40940365482000b06001402005d60146014810803003151013504c0070b124200d00d44010720400b402c2e03407000288a90b1017a0701039018020703003110002d582c1022a030380f50001c20071900c041401049500307200c12803d00310b60040070f0b40d000341540e400203401500000c201c0c80c01450128070342100c1c0720b001c607016000820742d8031525502c55414000d81d038002c4141d9024004291 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 156511070 1250 156509820 156509827
    0x1509070816090b010302070807150b060c070302100903020d0f0b0a0c0507110109081902030106080609100b15120406050f09030a210203010e010815151c0c080304050411 74
    0x50080020401c28031400c1001c903902e095030b41d00f990280c0c058400ca2030300b140e1455100c0016040c400300c604032202c180d0341010b03c2d1081008040c40c01340207a51013a645d0b00014444c40d82583c0c01d001603021a41701038801e01005190020040ea146505641610711071000c001602c41c2c80e1501c050140d82c0a00305041c080d0424901d5009181c1c01f0741078902c220340012143e22a444d41c200180c3d05440190800710550181c0d0b03c0210101c0b60001e1142803051095008000880c0c1c0d990700240c036080241e0340004180c11201c410502407840b030300142c42ea102c000f441a403d2440800881007598403030005454000c00d074404000030300c2a64895254400702070002da02e92484c04801c1c0302d88070b104034035103082401444e0003514603419101641c4070000c2c001030011940d03035865621601c2c4940013480341d900c0d01d200b2500303009800c400000b1990b01a4018101d400c01054100c001c210034441070308039400412031305511990200e0700d8408840000c100000145650300e04003170038041660f460720703840c840c80e10082 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 156512320 1250 156511070 156511093
    0x70f0609080408151618170705150705071e050901060c11010c08030c0703140705070312020c0108130501180c0512150c090a080a0b1012050606120f15090708 69
    0x7102403845400500d003040b0006c118002032201c0f01210b400000110410f01102e1621140000c0c10805032a0103c98502e450741d0306102c0b6511910502800500c190032812003007004001102c0b01c0c40910001c3da01904016456402041002c5002d900441c000780c0041c0901c424803603071484018600c5001c0c0380c281e0b82c20106898510140c4000342c004106420000b8840d01818031400002c0048180484110354400f1541000e690720b1115000584d00c4c6200400c18840d13090001416a411010684400405683d42008503640e090b401100b13492039500c0d40a040b0301202e80884400406214034042d404144c113207424841c0000f80088581d01c154055500f0091a881d04051540d00021020b50b0036920040d07600400d1120310140d2016003140f00b40004074082041154001c0c0c0305030b0343d8088140240307a03185044490b807a00090007810640140012030020700703024030b03c864020b0388a421180c20744020740703505140103480f220840d044480c06060158450090040b40002e2480d0001805161100d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 156513570 1250 156512320 156512341
    0x6040605010e15010e18040c1a2b020904090c03110102010618050618010801020d050709050112050c04120b060906010c12031e110a02070f1802070f060908040815 71
    0x10f507900c00f4184101002c030201640d8035140300d58449030742005c5c041362904151500c101ca40d05103010310001210030001510003080c1e03101c1a2804400751058205034801002c1d40c2c0400b003d076501c00b00032015002c100d80c0d0b590303403a076010b400c1c07005119049202040f0318505100741c41e61340121003d8116410b08400b00009075003d07000900c3c00351816000615074503140b00041c01070000841d512980c400c80c1000092006065000d40342d94103250b03405005603503650390201d90071005030082c2c90101d000c00c07118041c41c4445600055201c40710390240c6191948a001c44540003e48100c01c803000c00307011041010328200010b02d107030403500030700b8011a65402a6900340403442e0344000d80040550310508260f084a401160340340084003801300b0022140c0d04071900d15641c0c05645400058820040c1c00a02080110b8040048500125581800301c400100031006903000060507115000c01030040e00200c0c0310703889034901c02c078402c1c45119911031030300d4403650400705c2030b00804114125081c03c004280342c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 156514820 1250 156513570 156513601
    0xc010306080303060f0f04141305060702060403050307080910050907050102010609050105220b04020d0905010b1002030f0d0b120c090703020f0406050904090f1202100e03040b030405030c0a0506040605010e 90
    0x80c21691821b10004c00e20100b0001c002c9125030100740042c40b0700740301c0b220207018104400c0078010030940d50700b0760f0340d03000c16a03036a001941d00a000500070000256000c0c803c50341c6540058a40060303c401e010342ca1310f464103540c0151107480d155040000100029a0240f0a03440180300c2c510381800250324003c0021100c0a228080c030414070781c1c090030141c854040341c1c0030108519005000710340b07403800041000020f007181c0074115660b40c43e20001240d140b41001c0c4119108410307500643c0751225074503108160b034010014004c1010348581e8074880715540c2009030700c0030581c03140080040b184074000700a03203e6005401d0340c05141c41000100c50100b00c840803a07090340c00509082d6503401046000c1401881c1031400903001f1800ca41071402000340002840e00d40d0750320b5500700d03030466401c50104403c0304e00442c00389500e0703801004101300b80a142d002a652050041060300e0416103044644d031304180102c4001c680340e0b0000340400040065511a803405000d00041d004c1c3e0a20384018891303581d41 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 156516070 1250 156514820 156514849
    0x360e0c0405061c0f1407170703020c011104031b0f03080711010905130f0f11030109090f050a060e010c050a1211040b070309090506060c150703020d06080c01030608030306 75
    0x5000084040c40d0f83c08020500311a582011810065071031012a04c000401c9003007056001c09801c000826449445009441020075050100f1680c41c0c41e5001d00307800962002c03801c00181d54035800c0c3c50f038032101307100003171b0000703500071001d07a681a490707280c907101a03901c250400310203650003040a101240704403003a14103d643c03107e203242c11450b40c840140d495102c2a40901d5012503c0f14412010000b030b034001106c001c0310104140000d81d85400f210094074520500c2a003c450306000402c600a0b054010032501c0e406505280341c40f440540303505040c54003488040c0d840d00e803100104e0072170364030034403444412120074030705030b81446110040100a0b070b0b800d00156038003544500070520b850300040121001060f95650080e0b880440b07140c064000c024511030820707114600000030310141401801c840f403000080c000b82080c0f012026002c501e4080251401e01050303400d2040a1040d0b00300e204002c05029084010815504600c00040c00d030f4495812050302604280103100943d11000400025803 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 156517320 1250 156516070 156516079
    0x30c060f02090402040303030212060a140409020d020d080a090e0606040b18060a0306060e040911011b0203070e04050f071404020c03130608010f080a0507030b07360e0c0405 76
    0x10410101560041c2c06050360881d07009100040000c10160036070700a013503034020045022003c0d5598010451801360900c40c1100e00d240c2d0380300f816060318140c0c0c4203602042c4014851080420305401161803841000011900c00c000065203403501a041104c800003402980b108406501d03100d03002c201180900e20414210801c080380c4958001035040d808000010041c02168540c0301c0e014004011385050f1040f44c000c500e1502d40d2961505150003007294558001030751035110744c09880110303008004080d0013030202401041000c010317035060100350000c00344090452a1424603040c0941003c00d00c03980d203a0395034860034040140c401e110400c420456011680161520741c6106654114031446925840211103000c020450a801402c1c1c0e17030680c1c0141d813070400080e444103440369454414980107002644001010000110790407001d550015113450b10701103c1c404080d40c042035035643c1807001d521b078040350042000042c07802c0103500140640101000c0c203041920703104076203201d2401014081c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 156518570 1250 156517320 156517331
    0x30601050711120f0120090d0807020102030409050f0a0b06070302070302090601090504020c06070305092b05091f0e01260c121602010b1f0c020f060d0b0306090a030c06 74
    0x120382c0c50079000c607120440401950603091408400900800c03186007088036410f2000c010621b015006429601019005003904016110644a02c0300542252400724114401040045500c442600405019110071040303030699003030904410040d1551619028001c000620410700401c0d4006a0241141e0f0143c03180701e071903180c1e000121160103043d0440c580090002460080700000042d026100d89255076080005880700c0000c0d6071644011158030741c00c00d0311172680203112240d4222000340740086013071952410418401044052641400d04422001260b00784114650428074403450103c0c246045806c1d0742000022140c801098150600700d00c44200000301c44c1c020200131280c1d1001c8144a000701d23454881e041e40748441102400c14010b50030a010421705080410380561400c030119642c62140207088401c0f18400703070514003643c1c0401000c0d4a19002d0311444018800808081c401050000440381030514042000e44140b840c0d80c4614512004264049009640198401c1c000305a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 156519820 1250 156518570 156518603
    0x110405070504080f060915040201050a0f031b02011b0801050604030f0f06021201180c0801150306030605011d060307030c03020936010c0f0906050a09080706081801020306010507 78
    0x449014507008104644a584c1c0c407030300c4c0703403400259041c8a8110b0408650040c030001c54215040101620003c4c08200140001d03072015000b2001e0084083c100c1c6000103200700c0f0a404007450212903000c1c100940d54034081e82c482100049000d41301c03050070b410703e05400c1d458072020691600c907500c806840002e8400000003044944100049541d07040301c3d0654540a03061034240e040704085c03042d50640a4400040c1281c2c103264004c500e07003a6443c0d120030303402d40e19010074248100301c1c1100d15010150b8951000c40018598411107000e480740d05400034a00102c140500303181040900810301c41c0e0310000702000010309901c03011f81601d5059032202c2079a1905c0d030541540004050080442e0032902c8020b03550542d001e00380b00c1d42408490004e0201e1000004140c410900c10540c200000d110064180104c0340a9002003013060075911380513001c1581d03500c4103401c00f03846403ca000015500018032040420b071581d81403600c55610021444e40c00d080001a00d10f109561004013044c815443c540c5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 156521070 1250 156519820 156519827
    0xc0103090303110d05010e0a1109040e03220602010b030a05070501030914010e0303060108060904031d060d0e07061808030a0c080702040515040e01060b0912011811040f020711040507 80
    0x1c1588000c410312038a400d0704040843c0941024003031080c03001f5081d0006503c001d95406030709150819200a0743c58440d011061101426145106001c0e0f40b00401682c00f40003480c03da000340d409901c0e02404501424040000d00b5101409146882648184900750106001107001302c02c441c400d0800254a0f082d42c502007a994040c3c08080310107528090404051450100007181702d66026601d81110356a91700c100312015000ba00c000e00080c1940a100b8490488103800c00a22032008007084c0c01e2410750140c000990b140105c1500907038112800401c144c07034000d00301d0019158041d0142d80000c0c10219401e03502d00948002d0020010055055014880c01a0403a402c26030040c10900103440d20420781803101c0c2c0d040c151a4045d925290b48801200010b20070303e0159280f0041440c608031604042016030101c071030100115540c4e860200c2100c22206070b502400a20031b06218401c4828001080b00b00d8000921324200640104088800144021803501354110121000a11501d902c0d9088 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 156522320 1250 156521070 156521081
    0x201060f0e04021c0b06010309030e061602130c0503070c0303020405120303150f060a08090c030a030221090a0512070b03010906030506060a08031209010b06040f0e0a0e0c0103090303 80
    0x2492001000c8402240040c0e00000d840d100d50300a0f10074026203190150740c030741420300290b80684040c0c0040049401076220f9013007504c1087c028505510f00300d42e00c400040d890703030101c1c2c450315031424403042400440c02e03c0c000603912810500020085140c052030054001c0c44000d00030400c1140c0c45182303904060083d8191800b502015140c1e06004000551f0765503a40c1c000c1c1e690400c0c101d25000300d501c041c80c01c40a0001006000b40401d410315403403034810358254202400040030b6010388000b180f038640b420490003190a00070f034000d102444d0716070310060310b1904c450001265188104207144541e00d810040d0781c1120b0b010703995004801058141c45050103000d800c52a080d1000100000b400d285036040641680e02440590b0b441e600c0311070402c07001ca0401e105414940c0c00c00d116500072181c0242d00d0036071240024001040c2c46a195001480d9a1300c1030f0064450a002c1440510101c650f02c80a2079001341c0b094800c1042c080000ba42981c3c0f07a002d00d81c01810035880c1c2d80c01404252080e0003c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 156523570 1250 156522320 156522329
    0x9010503310c08010f0e070605090a090504050106260606010f02010e15090705010503010e0402060309071a1c15030212070503060406020901020c180a0b0f060c061f030302030d0c020106 81
    0x20250544800d140c071200801c280c0c403840740d03d5030800c0040c00e0804102e00c10204000d556000419002d4a003482c283d40b182c11000400e581f111981e440040e1076041401030602c1644140b000107483ca0900c411403c503404003224115150441d48144041c8402c00280307d6001142401c09003950252000100e0141201e20fa0601940c0202d21701010003a00300810319004011660a80d000f007030304c07840115040e010900c101c00c90341590740302081c09030424000075908030500c0e000b540d44560b15641c1d28201103050214504040780d000440040202c40c000b9000c84110070b105007444841005841d01c2c00040841c017004c0e02c54038800c030703c81d05200410031045c2c0c01018081d090711003034546801c100000f504a11a0a40903010f82c046142e031514002a4242110b1058480e80e04140c1f26000040c004000803040c42e40c001300440503590382035079130070302030042c011242c1c0040aa80c501040e00b581140211101044e2a01f418001400020380100075219918035000300040c00540d4808101c1c0500f09a174803 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 156524820 1250 156523570 156523651
    0x803041707030c020a080a080f090406081b040b0a0518061f02032802072306040b030402040b0a050607020f0415290403030c0219090f0204090e0309010503 68
    0x801c1c100305508604941078181c000c60701c0ea07000030359407050182c542e511032100510754070040104409103204107000e80b13046480a400040c419841b54a6903192030f20382040c0800002c440075006444c0d00c0c250140345c4441c030f003e50704428134600c1d02022801082c24000b12004d04504100021190744a01c020a241103880220000c05403400d200c01039140d5000c83d0ba403505001085001e00c1d450405080c4c070200c1841c8d154000c00d21107281c030003800c011081c40c404402c038140078442d1158040c0d8402c40508060043c2e960f4895076414544100300803112103000b51400f0300b595201c100240c1d9120400d850102e07405540c0040130642500000d002000b802d1800d14805d100c516000c02c40903881207940e08140c03e5030b20300341c1c0c116403a0060a0180d004030712008000945481d41c00c0b0060401d10112401101041030003c540c58031210300b001a20401c05a0b130022560104e0200030b10907190040094011003400603519201c0c0701400244944401000c00310016025445101c402c42403c00c4001d44550a00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 156526070 1250 156524820 156524827
    0x80702220c0903050118050c0603040c080102191b0201020d0c020607060504080306011106060a0504020c0102090a06210b06071403070f0503270a030b221101171308030417 75
    0x40a8002c19480c00305441941c40c0603d0700240384041820421510b400000400030b401840c4100641540b004008440baa074410f2000030710322100340060007031a103814507948100b20f14100c004181d1106110211a10559543e5000150360046441c0200286500e00200b1f111000d0000c40c00d1441900b070700030290340c5000c00704003e0001c013401460041c9400d80e1400a02c041000d1040c0c0d64042c2a660f0540c025200e5804204c146019401490f03500d40d8180050705101d01a40005ca9099280d441540481e4940100c0704019031140e0500380013a000600400c4000d50031b10204500c1c0c051a5030041c1f01c6580d104c05080242010001d44181c00d903c10941d01c010702c014940305460703401c13032960007180340b0a600d604506686280e10843e14680302400380b04100e4919103900d070b0058006800000c0e52140d40225104400b607450895410b0ba000b4050140c00140c510700040c01400e1030380c1c43e01d80211a1205010b000342301034110400d01c0382c025414580b0380d115410702e81c50004201e03003e0502006e000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 156527320 1250 156526070 156526091
    0x102150408030a0b150a03052e030506010f0602060612030c10150603050f0f070908070906080d030b010212071b17060f10030f05100c1707050708070222 67
    0x51000314071400c110141848011305141c10720a00303820707031090075586660500c04100c01c41d109620090703210742c2c0308001040d04220359103c41d4120883c44010355140301600f03000e0003401010491030340103004006003003d5840c50071000a480c0d510180c1401d21642820720f40c5e010f101d0080042d50b81c0741400d1001e1310030800c2c0b40074214008241442d0410b0034030030b11a01c0041c07110b0282c0300e1640304012018548035140da0b5043c2542040c1c00003408070b001c0c00320002011a01c100d080009030040c040c0000001012070800042c2403901c01a841070004150815035128480c0c1d82c00304888600e403175a07503010b0340c4401740740c81c0043c0c01401140f00001000e205800000e0b405496003960f000c003c4507039050b40d0881e107e90340c002040d0310048030411102d804013101080003071584900d0541290081007580e00c1d05000d07442d058141d44448440d1800148251010704815500046c10b80e004441410310741e02e002758a5541202c1c0c0d005514000e4810306a020456810000395601c1a6400200c00f03401c200740504d6 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 156528570 1250 156527320 156527333
    0x60624040e0709091a1e0307030816021206040f02060f04050402030c071407050f10030209090406090506090f060a0b0f13020a09050901030b0a0b0d06020a0807110d09060e01021504 79
    0x18032500c1e8203a82400c41c5c2c880c180e44500f02c0d4900384c0c0b02c040c01074586002000d051103185e01224a80603050712a8410000200700b1120161a40d05901180c98491a040e80100055048290320450320380d0448410f0100051620076510034a99040d01c00540720101403581c3e090758060395000341d070094000010840311001e07000051194901c0349035000c41c0f40b120708049690f158094050b2581000b88103200d1749003847d01030300300c40c0d4045840c034015140012310b0001c00c0502c1410303030301140c04540f03a8403002c003004010f00c401175105080030001c00c00d8800030103038039540d08006099403040c0d5a84905119031600c59007001148024050312841c2c0d00d61040035010300a5122644810002d400500b000ca0301d881c00c803c280f07040b0380d00002141410346803c840c110080040082c0ca40e402034a141c0e11740001440750001e424854032a488070706561400142c00382c0a913482c0691020030390008103241c0c43d25604a4034910503101580341c8685282006c10040c1d01e07105a5650b0102d60340d29010401082052 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 156529820 1250 156528570 156528587
    0x31506030f0601030803070801171f060801060902070512030403080601050706180f12020123090c0a150813082704020c011a0a03020109092c0a030e03060624040e07 72
    0x165652340d6041d43ea175103170320352103108215030300070010b4001c0c1e007542e1034019400403600700200d003560300000c07180d40d58001c3c02d0845409600c04151150049030017020f00406103e07008009011071886460b51415640003041c40c5801400c041c1442800728084050156562021a0540404241d1701031400340d0700b000000c00d1002101203030303034907080000f03203c2c600d1042c0682e00c51401620000702c045d07225021014103140005141e034a0511403034a00e244555240011400108100042c020801c0e117118002000684000e0503034020b11000040e035400250207908a611002d040b01901d1070041410101e104910143c07440c113a8401e0001c00e850004460660009004120394010030a41d41850024000384582621002e4084ac500c050200b020304501c0d0050081311400c402941003855102503146444400c84002103015802902e50200309504440d8200c5d2899080380142960b207019170010b9900e004d001d040161001c40955802c103144004010345009c1c0600005100c1c4030b2501200c010314810 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 156531070 1250 156529820 156529831
    0x406031e05241602070602070306021b070303050d0b10140d0f15060206011502030a050307180303030e150105030714040225150905070b0304030509090702010b040e0c031506030f0601030803 83
    0x1c3c1400700082010740001059021980c243d00540145407550712a10001c0d0003011180341c040450031aa11113240c8144610400340d8482e48841d40c0381c04204120008450881d40914010f103080d4034200e00d1076400820084da0701c0344050318140d8605400c00d1010180902c1c480e070380902410301c182d01c08416850700c00f140645040d41e080b10800d82c1c0e20200c01485000c01340d66080943c10402920f0245445000110b520403c54104107510f250080c154036861034266005a00280d81c4003042c4407010000c0c4140b004100601c00000c50a504207000203440e45402d00c00c000340aa14988140895103494040d1144071a4110400030300020304503030b100600c0185030049400111030040c14840003550310490800340d03081001807a9240c2400030185d0381d5400500306405010b818042054640d84201d02580310751035960004c107011075070f4014001a034661003501481600500200d0138952070008148490b04104100c0e50300640f070b44400319050408210312a00980241800072051002000c010360103103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 156532320 1250 156531070 156531091
    0x3609061a0f01083105030a0203041d060a060809010b0616050d0804030903120c0b04060c0306060e031f182105030105030a02010e032404020a050406031e0524 69
    0x200070140044800510403a404072902c00e80b0040300304c40d0568a079a101d6400c0d0038501040340440241c5441d4911f400000d4080016071000800740040f0f41c2c540100603c118600d18504002e0502c140001d12019650080204105150b0001050705100b500315684118002e003019503a504031940c0b0300e00d40c00c0e603040203603030703520a40c0b24000c0c0b010b124001e400d01c5a50180d80d6000814215911101035494840c000b04c100002c500107800894403e41c0401d00584c419000061045007400e4058251074841c2e00400a2010540d0724501c1a2004903c002c001041002c41c0c0c041c0d0710f549150b940c0240301912840c607081001c42140400c01886a2503050301c840b150140059201d200c520032140f07417000740a0950590004103041c00154090700c03803040003000c000c1c10f171004850006207200b40c80c1010100b20344c01d110703000107000c10b41c1070009018014080c01e58050280604580b501031207000341980752541234400030145010b210040c404940703c1d070096400d8002c0b00c2c05003541481c1c0c8410507a4498181c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 156533570 1250 156532320 156532339
    0x90e0f010509061b0d0f0c0201050f390d02040b1c0b06090409050f010c1d060a1403071116060315050a0501030b010302040e0c03103609061a 62
    0x908100040f841d2040840c0c2001e41a0041001c1c01580680c01443d4046003d0341c4404659000301342c1c42c010401070400d20360000505e40b519400f009012312001d0410580f01e002081c00c0040c9041800c0f0340b16428071810400c2c0355135006d510107150342c0d2080c2c0b560444400d00c003050104500c10440300510000c0c041d580a114180ba409040d00211380b404130540f07500000400c2010b205040a41140142034002e506a0f8070800034140c1290a43c1c4110680000003081d1804590207a41d940303880018000b001d4440b07a0601d440300340c01800e01c003002c1a2402107001e022002658842c0706000700c043d0055145c058558980c80e428820380d4984036401103c1c046814030ac121154240c0b0074075031404031500203003010456407070000190028a00c1c24110703810190200404100a01038000303c1d03019910700e040f25a60f918004600152040480d00200c40200e001160b0140c14042407071310b62040e02000c1c0c81603540f0320102d485200104801a00140420304110307081c201d1000e80001c9000500702642d0b003626 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 156534820 1250 156533570 156533581
    0x30804061d01200313030605010501030e03120a0506030307140106050111010c1202180909070608090a05060115030f0c080610030606050d02090a080a05060a06050a050603060415090e0f0105 83
    0x890000c0301003041c0c0010044203880701e405049031880f2041d50403e030241ea01c0e0081003408100581403542080e00d0071610392004000f80e503414481e50b000c2204e040040d50030519020b0a1003210100509803161192b15a0080380070341d076003401161031a59100c44040c042d4641d9502aa01038041071103401d000c651420811a04c002040c00749542c4e40700e0ba5074401d544e9045041304400250055255985540791100407581261030b40302c022402504114000d082041c078105005080e03d00080403582d90b90031a42848001a40c00504103064039800038010101c15494001240101030040000420350300300307807c2c4500140c000c403615008031402e8400701480441018160250780e03842c410000060400c1010380030140b0b81d0b60280441043c024409a4650b0381ca400d81c1785481c061107000d4a00b42c00090502c0f5406006100d440300400b01910358000743d601c2d000014045d4080100684e000c0ca840d040d80703002e41c2e035400340010090020740908203e070788455066555100140c216148813586424080755 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 156536070 1250 156534820 156534857
    0x31204060b0609010c140c030f0a05061f060c051603060903080601050a05040603020c070f080d11010b090a0905010605100f0215011401181d0a0b090f2e03080406 71
    0x504a002c181c6505c0c82c60511039943e40401c1c40c0303800c001e43c2c0d61301401400381403550b02404020700041c0035900a04910945080c01d60620101820303986035000062002d91210208101d00411500181804000219682803041c10000e149500400307400b000700c004810402c0540c800c0c4402c5010740c0c2c07202d80c03d0b5101401543c007071007000c2103480841c1d400d0104100281c4241c0050108c0341012050b5801c003561014565000d0703000380c0018941d60018040c100519a000b8410b81e0300c2c01d0500002d110b070508090100e030b5610005440e40100035143c0c0150814400b007500700d2070080401410307060110508000050800c240900c2a070018094120101c140f02410005175060320341d1180b000b54092003200040d603c03001d0002020003810081407000a85c0e103d00043d00740500003400361407a952401c040041c2c1120304038600e1520a000440510001281419459501100040c01d03080130b2001c10b0a01045000301101c90000e0001c81000841040b1800c0050400c40b00700ea00c99840c1351807d1500b10 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 156537320 1250 156536070 156536077
    0x80c0606010f090519050603010305010b100201020a0503071b0b0c09010e010206010e010521070602030301091113050415050301060b0702040b030607050a14160c1e12020d05030c031204060b06 84
    0x40b0000f40342540c2400a481c0441031103500703841c0c9625070340340c4583d81c102190b00364109034810b5a07941d55038106a41282414a441100312001c1e200031071034400100000381131800060030704070410442c03d000c0020310055144080c0c0d0340303070044e81c120600d181402c20308585910aa02d01800555000d100c01d64135400000c7d800e0690725202c0440d00c0b00ea09003400c2c014800000c0500504c0d40825091440c403814040c03001c80d0182055034044d565170b6041c40814415074040782c3c002c00450100b00040503110314115082001d44008450101d0801c3c20541101241c001e1500301c15855440c141300065000407160080003000e1080e43c0910a5801090405803a0036080700c02c07901040c010001c0681142c880d00f80c1503c8040580d900780e0070042c40241080c4020b0418108440300003a40d4400d1082d0b0310760485480c20251407510880030141820001d80c0101400c0314001c0c000c41c403551500341009000c0c000d036030911114400b00c0392900c054070f2282c1c0c000b1000361020744480e45040340c07141c6542000e4045 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 156538570 1250 156537320 156537347
    0x40305070306020c0307020d0b010e060904260d0e01020d060b070b040813030b2a03090a020d0c09050f04060c0203071106030703060807120b090610030215090d080c060601 75
    0x20304003052854071504041e41c05802103c000707010130044400181c0e50780028613007507030044041004540c1404208402d40102624040c850340d0081c0030440003034420030002c0540d00c00300803035030450243c00c0c0c0b10100d1406100314101c9601d0a10542c0c0302e4440055001c1c0424a60156091180076582c1007051030320310442e000038004445034400240803895400090401c050754047c102101c40d90f03915600203034175040c1c0d6001c0d0304c0c004405044092004401c01040c0c0d405203548218603508000e81c07850354034001a1802405000d14140c03120a1018020480f0003e001c8040309100318540404c0845220204807022100c43c0d00d8080084040c42c0700100b62a515035000840d41800000001044000c0d04001d0210b01015110360011a800d03e0078440c0400405504030300c202c3d015642d1a101d540060005c08064041d4020f0007008034020400101c5400c80388c0507034800c0c140f03a0030440d01050324411504800e4008061001c00c0c004c10005100410130040c030702c01a11117a80b03c1800444550900101 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 156539820 1250 156538570 156538573
    0x61b0e0f060a050a090306060b03090c0901080619090611071202061509130203010e100f0b030a14030c061e010608040b010e0604290a08060103150b01110a0606030611040305 76
    0x14942c25405100100350004203402c03d0341c54a0350b2585d8402c19036102d0740001d21142c801100b400f5030701d401080038900e6a0422a00640780e5810002043d54907035001b41494200072440c034540011010719400070510680208040c00a142c02001c50750950b8800c4204542d072554640c0100450b03440070441600401041c0b8002e424102110b0030404415000f40c00d500c454020103200100503a030920400d52151000d10107030018040c1048090111000c1c0c044c1070303082ea4100070300311a6980e80410040407042c3d00050714900d03036035a200a185135000d090428a441d10440c0188401060f2681030810b2010000b40e00f16103587c1c035500c086a03032103c140c90007400000c0c0d0a0052108140300000306501400240001481c10240d848000b020841c261500030140c940729901601c1c0d00b0705072217900141101c94000c00441d45555206e95900003203400c0f1800481c3c1c1e904c040e07d40ca80c810440505084006002c03903456405904241008290302d1104030b500707514100c2c0310400503400304180c5044941000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 156541070 1250 156539820 156539827
    0xf08030301150e060d050f010b0c151f030803101d04020f01030b060a08090d030b0112020706060302061b070609060f080c121008010b040203160318061b0e0f06 70
    0x15901840003165000d02420300c00f030300c0a14401512404081c00100e642d008011031b0341e040c1207070b0f8100e50b443c06800c11000036904110b21103c1c00000503082d40040301c3c007a84050745a407910842440b1801c034403281105480c6015001040c042010084c0d400b994a00d00c1c0e035101d403640c5200011604442c002c0c02d000c2c40d45000300103000341c9020007141c2480501030601044900745500000d40350b81c44103100300e000c218140c00344000000104589030304104541070800c0300714041e4001030302c0101e040b00e5209150750001001c1c020040140c0040c002903038050030315a150b0413801c9232b400d50324207218a01c04117845184030008142e8450302980044503584e807180e084100714200c0888101c20f00811810071400700304a031005100e07165054500c070311420040008202d0074070321011300355502441d603a032040e80140144880e50188144d0307600621042e003000109440208940025100b0103400684081d00d4005c10082e220400d040080302c1007590350b03030800e407840300700c0c20440c2c44440ca000031604100b01b071 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 156542320 1250 156541070 156541079
    0x603030c02010c0c0b19030b03030c0c150c0304060e010831050102040503070306090b09010c0e0607030e03060405010b190e0a0509160f03170c1002091302070501060e010f08030301 79
    0x40081c983c0c030341c1c0900f81d013010607a1a40040b042591011422421541210407070300030142d418441c1d4003440004401651504070340c03d0666940d200d13803049a40c412001c401141442450310002c44100740d80201c1503903281d030740d00c0301c001d0880380000203d01d0100e02520300003030711160000c40c2d03403000c61420310409006461305500140071315401e030000c640c559030811001c13844c1da0742080907500440c07007581d000c180340c1c94919110684649c0130301410060780c141420041d015400000000c0201e100b5250309440e209141005c03100706002440d096014000c4006110074000190040289040c080d00c00081c04144032403a00e008114030b00c1340b105a00040c2d4041007400c039041e004681c000b081d0108031105041c0d8081c5617a203a003842c0d480225082e40500c001c100300700c0f10700c031401400703200824030b00d00b0407030740410b4140c03122a004d21202d607495001480c04080d0b07880d00703031000701c0d110b8450b0115100c00c081e2a0040c000d000b64043d138000d0440b007c0c000504070340810106001c0c1c86603400514210b9290 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 156543570 1250 156542320 156542327
    0xa0605010e130b0a06050a08030306120f0a080d1e0501080d050403050a020f0a15050304031404030515040c09090614090c1e060403021003050a0b24030606070203010501180506040603030c0201 84
    0x4d080c10041c80d4503103d0000300340c6d8840d004c80d0040d04056002d50780e0390400304c0800518002010051800780c0002e600b840182001141154400c1c0c0c120902d25521000540503800a02420039101f15442440c1805200540650b20041c160b42002d000c031800c03140284400ea515000c0c070711006141d40d02c4220008014240280c80040007a0080c00c10045980ca0f080003c001d030044802140000320b000c0104070074103620a088400c040f568440781c900c2c150440d22042d4443c11000341c98600c0803840da012901300100c0d46450700c001d01000c2c0d42004040c03c9031030850003600300075640074040f071603220100f01c0d20b88001c9459200454018049911039001070f25809a0098003101705604c000203010000143e02c07092044420020941d41c0044c042c0b400110301d504441129810318010340f1040d15401204040350300035140d48046402c465100c1c4e545200291030343c401d000d0001d4040d421f0800018042c0007903c00300801101006050240b036942c401401b00b258854800a80007800042019000d03501 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 156544820 1250 156543570 156543593
    0x1180c11280b01081609060b0f0304050c03010204091401050a050f09040302030910030b01170103030503191e0506090a090f0b0a0b1914011403010501050c030d0e0a0605010e13 77
    0x80c80003032015058141c807480502d100990160045070460000e080b46083e00d91550340c081d00010504010860074042098002c1c0120784980c071003108000041803c2c010100001c1e01c460500500035552642c507080c0403c003400340c80e00d021103250070100000c10585070090310503080d01c1c0003900041034481000200148600003038415400d50004120001d482d4481548180d40900140c80205052000038001031a0746000400002c0100c150707001440001e038042c007200c1d0000803401c984841240940c2c0044002e155610104003005e9090301924419460f40c0c00c440d209081c2100e02601e5590f031005403005803800c8000003003c040e06407040780c0004001880c0e4540102c8141d200055481a62020a42c045c4800460b1400c0610100c1d0400499600e0003410031400404c1c80c0c0346144000c00101e2000c1d9000601a85050240100352810741c0642002a03400824805209000b1034085559190300c0d683d42e10010b03203800f0b080c80008100d03141111880ca004808550901c80d000d0320f142c4883d43d4141d03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 156546070 1250 156544820 156544873
    0x603120f04080a0804031202010e1002030702070b07050105010806010b1e0d0f09050a060501081f0504111809160b0a0804150c050c15090a0f0203010207060501180c11 73
    0x801e20012411040c00c00041254a1141500d550742c1c2c0d0075410003180030710024140408582c10709001d400309402c04900c20300e4400c5946405a240c2c0c6585030b0690a140c5203800521700c40d00c0204600d0280041500524121603031a01520340b5a40c0f6180704080740e10801e4202c0c40035240c5509074035002e060160003445024005040050510141c50802050f80c02d0701505513a80d074441005c4c0700c1848010301c544d6006100c204010b005a12050b20102c0e0356290945540da446940d86000400340b25802034540c0d14081d00501c2e40c444214120b2901c940d02809440200c0c19114040501a501040c0300d080c0303059404018060b414082c2101c3d00710340c41540100219051401305080384142d000500905030003055a4480503201c1d081d07000603c1c940600040700b4082c0c41d440d034061100800e00812228103440c2c000241989200481c000301c1e0280c4075203d00113001501d030000000d50072454400304c01001c03034951814441d10f241c8200480340003203445080700190b082080041811000c1034032811080b0f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 156547320 1250 156546070 156546097
    0x61a011407150504080c060c03150603100314030301030605060904170d09080a031406060909043c0b0901050c0301120f020a15090b0a020d051b0a0c0501020d08060312 73
    0x800c1c10548401c1950f509440407100a0004596001e8051040c010a94003003043e0400303074103600d40f00e0640d90780101601c0d8250300800c00000422807540b4401400005141c0211000403601c01203461030b9681d500900c0300b178406074076001c04105140f51005c4883d02a40e0080c9640c5050242c2000001c0250b12408160701d820396920049000180c100b4058580030006403030000d01c3c5800100d0b4241049ea00428207032043c5002c02034001a981c905201e40c2d04282c10000d44079200940c0401c0000c1411083c500042c16820800040c800419500f0004200c922521000b40b00c0d8645019080c01c3c3e9a0540d0704291284040c00140400c0b03140336800c101c018001d0f0703600c4103aa403142d0045050030000d50003401038040504c10303018170984c0210042d07005048003840c0600e0040130310b01c0207403504030304104c10b800c01100003401c4002040d4000035685504456064604840152810041c042c1451140d10701500481c000c130300c1e209018200152160304050302408440029503802e2807590b000407040c2616 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 156548570 1250 156547320 156547343
    0x231b06060607080c150c030108010b01091a0f070803010b0415020d0c140c0901090608160b0d020307030b040525030e0604140a0515090111090f1e03030a020a061a011407 74
    0x202c0700e04100c060003841b40101d026529414000c100d800e6401444800d414407821040411040500e060710103407900c1400c0096071100344690204005109003980900090000b0001184000220780100111850300800e84480e060b55102a80c40302c54100507400030984a0803103a000c101c00c01c0d0340c5050000180f003036403900115840041d640303520a0300b145881d03c0d52400f00340321041040007400c61000384101400801841c200f102e460314424080d42c0310a080e008030200d108075009070030108100d00300510600151130562075107910804140c68030101008811040440e41d03001c3c0c41005400101d90001d01030f00d41c1e03907445264284044ca0480f03021480345220400120300c00b805001388105900c0082d2030541007001c500f40c2174400b004400004240c04000e440d2050f80c640c0d9105450503002e8551036580307031010a044803800c011124039078141c0000101000c0f4035602180b10030380584540c100300021310b017000003c00d181c801c2d10a401e0103e80c4200454a03002d0080c3e01806089102c2e04c2503040 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 156549820 1250 156548570 156548593
    0x80c0906190510021f2a0905031f0605010513061805130207030e0a15030207080c07120c060206010f050d02030a02040216031107050109030b04151803030c1103030601050a231b06060607080c 83
    0x14ac1102400030404c40d980003003205041d80351502404009100920780541011810300c4a586203040c01d00c180c10910244000d10741200902d09140002850020a41c03010080162400d0010b944021022000220364180050991030401601d40036102c4107d40031a080920f84030030340007540441400d690320981800b40081010f010040c50000d40401c0b80c0c0c1a0304c0c441c0030714241c1e114403000c2d0030800654000c0c0d40144807441000e0303042c0003220350450340d90014204074004642407030090080a50008d00000340b1090f10f4090300c501a5405d07101c3e07519029500d451004940d1604041d0150310700060b05101c04101089009807140e8205000e05d100d5014000c1e182592000c99240029810032030302c0b03000c650814075801d0311542d40055218281404d4150900c681a5185e21005084505004000c280959064414142c0320400c3c480c1018907991201502d00f17502103500500076683c000c3c04a2110a40007842c08261030303016003405000c550034084035965240103a000114640303024800e0304020780 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 156551070 1250 156549820 156549823
    0x1902010c060e03210402010e100c061505130b100311040902040e071b0210050c03070501150f050a0305060a1e050a0b0307080c0906190510021f2a090503 67
    0x20020003082c000350b580310801d41512000074101c0b2101e4100c0c483c40d008010150340c00020150000d80f08990390400e080b2182804c0d100e03021030540140c600b40c50448900c2e414441c101d8008191f0b04120303401803803040707000c080790b00303a0b8160000190003000907117010410074040d80101c04114a28941641040e448249480482e00290700c090713812408a000c0c02000c5030841071040012007660310075080500c03103801103103002d999840a03c0802100145c80805c1d82030500a842c02594002c0c02072011210500400204144902800000d001c0000c80090146000808030341126801000361003c3c0d603440c00d80304018580d22030b8541c2c2100038100322111200c003a115541c46140c02e090000b480c1d01003281894607099080d0000c10039980a40540001640c601007403541c007003001c0b1990034807606c11140141c8440000c7d408260040b418110117281d00f6004200c5803001d15030a000c501e404112040700c201652950380703050034144989036405d0301e080c22028850140c07141a041541e0541e60300e4021a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 156552320 1250 156551070 156551081
    0x30f1810050405040b010503011401081b0c0f0f01020403120e0a0e04030807110601050f090a06030b0705030a27060c02010908130504060f060f0809010908030c0c15010303021902010c06 81
    0x4a00140700002d080c0b04901d80f0744246482c8171003c3c40d00a0a66050104030b000385819205a00c1c14010382000040d58038928003400384000c1d10003a4a25103030241c00c201182c1d00c02941d40d11081c2405140c0809940080501c04d80d011213801c80340c29940400030641c01d0f0b580d4139000c0d4400ba040903021502150404641c06d4441c00760380300355110843c038540a07034002c01d0310012426000e0303136820100040040b039072035842d00901c00c50115450303500e9882d1100c0f04070003010f4aa0000700320701141810441002d03044005540708213903c0390207010302e0030010701c01894401a0b00610300130f14000784000300424640d610800d030314400d60000150064207034896209a800441c046883c0116003113007071015003043c0c01200300400d15884810038641c02c05002411307100b000309036881045420000201d140c1025008990440d07000036815540e800d00c16101c00c1190f1080000c81514403035510580150f103810300d13043c2d0403031350951301400140c5800040ca2182c18183c4005a0400c159498188080340d02031040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 156553570 1250 156552320 156552349
    0x81b030d1b051c0201050721020d020c0f1c05030403090e0612071806080307110f0303211e090604020108070203090303030901091103070317090d051b0102011b02030f18 74
    0x6000043c00c640030003403c3d03c80c018404020030401184041e0300c040c80340c0082060492044000d601c91100e1104d0b04001c1c0105d040d180014810304200005640e00414248139030812000c5c42030754102d00b41000d84040c441568010001480404104680c4544960316030b04150028140c1140f2414440094640200c1703800050700c030310b00c21042d140005860310801006004000c069030400c03c0946134615088a0341e52075071301400c000180d00c1d0699070144101d0b40c809980010104101d02c10301d40013450500c0c1100d4a100c40141a0820100d0040c841d000030711070b60042000b45903550303ea900440d43c8010203041402944004d001c2c8044d59942400070314030503c0002c000090004c0c2c141055445007403c1c1d58030030301a4000801c18070101c1c0c215445843c041203c000040d07514032000c0085049034006402c05461409a442c03140703904600c41e10702100c0d2143c02d0b4024801403541c0e641c15510701c5c03801c0b041a00940d00400c41e0340c81c03c502d458040c0c001140840084103c42900c80003042c18850b400b0407 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 156554820 1250 156553570 156553603
    0x1005030f0f06130207060b1002011a04020f0403080301061d040b10030c05160308061509011209051009060207020a0b03060f010e04140c0d14150f0d021207081b030d1b05 74
    0x40721f00c600b405a0305030028040d070301c02407080d0303200c403400310706a42c50340020140100c0e00080d011b030861149038200c078021907010000b1540c039030307442a0041521704078101f2041a1031040140e070000c0e107012b00800c880034a0040c50640010f138000005d07030081c01c403054100f051000030b01c03544460800c5400c10000550003515051070a19040041004500341000034044112080c840480c00781d034000e010007040150700e00300155050060420f47e1400006030022812242028144e01c10841d098011b4184a8801d650000756552a64004d40c1c40c3d000455525030498420b80c070600d034540c4600c010003a0348901800000d140c06200a0100044800301c414062456000840203440e60242c840d80d803ca15a4880346462400c100b8100c9c80030002c07c2c04164800c026030000c40c81c0c00d03a641d454074103c4035401400143d0034400c145035107440f107040380305e0f04402d40a000d42a0001e05855062225104e42c000d019043d06285104181d90080c42c00b03802019041800301303c3d4002902c10800301c24818203c01 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 156556070 1250 156554820 156554831
    0x60d0c0914060910061809060f03030f020a080a0e1906171003050c0909010f0f0b01091a040b0310090c050310060c0c0b090409201005030f0f0613020706 67
    0x40035000900d4002d405580140701c01810840d120484030200c40544d4094a854140d10980d100e00184214040e003103045c0c07180ca03094000404c0440c00c07032008216486a100c004207055400d406a1300c8070400c4102501c2c0030000c01c641840755100703540245172a04c0090030942e030b9940c07190070313121051400e07000000401e88140d074442c030040350840816885000e0303080040d00c8038190b03561280c4901d6030301490780c02000c2910100d03134400802c1d0032210514003190000c1000c00c65016111025040010300280415000840071898428440f842c1001c0c4104501c50707490685800c00900c02580024840306008141c1507000ca8186004d000308903501d401c60b940d0507161f041c40c92540711072441a901c0300060052080654000544002010007200d802c42a12600c0b86500804070b0040c20340040e00401c514010019200b04c0e641801c5141504041038446401d546104503040d51548410380f1062154407106002443d0b40404050740ca900c1b800c080c203244003010a50003a042a1b8101403002c840007030711403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 156557320 1250 156556070 156556091
    0x60c030712140705030f0306062205040c02070807031128051f080a090c1e0e0702060c0f09040209180601110d0c0215160b010f08010c090608060d0c09 66
    0x1c0d45030114202c0c080c5681ca460101d0752607994078401c504030000030040c0440050540e03074800041d952403c000001c0074040800c620100919900e07076024007445145000c50008040f480040d6440503289104d004003910703800c640b2801000300e8200f900d140d000c40c4940d0041c0003070b407048400856924150814058042c18041081070204580c400881b00c0c81000135600710080d405003003244c010350800c40000e0b0004060400c02445d94054004000d03008121080e4046580010084801c5503244d00106542d501d800d074040781c40380310980e2145800d60090140e039021001c03440040c8031105000300010300c1c040701c00d00422820080a119402201080d07801c02c40e1558104020048046501c0080d21080c003141c1c90182c90001203800c0070303004425807944049040c510404460b030101300780714000e40900340f0b071500150b54202402660800814071400040000c41401002000c02464646901d9603081400c1220390342e4004101c5548083e003840c0300d01c081121500c08d54003428140707030f010505c810032 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 156558570 1250 156557320 156557327
    0x40b031006140a0c020f060315040b100e130b040f020711091009180b040f030207080d080a0b040b0d0c050a170304090209031c0206100504050709060e060c030712 71
    0x1254803203030900c14500a50342c0c00074510401c0b01e40784072840c208a103134201240042143c0078a108815a08641c0c00400d0000c00d44003040c00c032083c1da508807400d008520010080c404140000c2d2503107408507034040200381d014030b00704090380d514a03010200001c5260714000003500f5100b01807400700749650300080907014801d540c440d0f034071b400700151500c4080d03050180d804041102148101050642e0b2488200040361910a11483c85600300c001d001c41c900b0b103070a01180c1c90307200043c2203001d48901030000420b010042805441d04549841d03440c07150303980c2440c40000c0c20030301d04150b500680e54840f0315442d039039211103803500602400007400d1090030720003400030301110b541121800c0580c0a48000f8104000011513099980d2407501503120210100464039002100d1102c42d2146c0c041c2c00d51007902c5900081c1c59104440140070300701413030340c2c03502800201c5905441c60000141040c409011050041c40715036014a4094040c4d40341440041c4808e0035500140c41c21204a04a650140d201c07590 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 156559820 1250 156558570 156558601
    0xf0c0607090501031a210316081201050a0308030403051312060504030201110408070302240d090204060b0702030a060c020f0a0c2402100903030b04060b09090f01060906080a0908040b03 81
    0x10b120f440c0955044180003540c03039261046c500702c1d1038000c0718a0701182c92041c000c0d20300600801102110084103442c6c41402ca800103056424090203010000a03281f070803002210880390404002803441e00c0d9914221681d45c00154a01200c0708000400101a0307100c25000c00e9041c015200040d041c1080d180007420b4500d0f4080e02c01d00510300b84010b0203261004035400c012242e046800e48041e030b5100703019902039070000c0c000295600003c2002e5008020581009018900c2141c08106090300d420f80d8201d54000d185010f5010303400f81554800140c01540203510900141c0115407503001420f91040c80c04d61a80c10840700d07181007560401506109014068841061407686540040d500c01d0095079500d01640703224006449420400900d80030340d100d0810004080c0c810700940d40c0307030006100b40f0b40c00080c04500545850700003130b44003032458a5090503100e660307952194040c90924225503000340078000403449952660301100280e81c100060001300800d2300d40d1a00c030f1400014450f480354 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 156561070 1250 156559820 156559841
    0x19030e0c010e010504062a080406030c02070b0f03040c03021c03031a030303071d030d0f081506031911070b0610020d021f1b02030301380f0c060709050103 68
    0x55a81c0c0c01206a84e008419181542c01a00e8404242150300e0b0307400718000300b401001d02c0c00c0b08581c0c60342014055102c00410646515032401e00c01c402c1104d808076a02d5185101d034840461701441880e5885003800025508180182c2091101e41e44030780004078840300a0307401d80a40540351000e6003c06270103004d03c982c980e1400162420211207040400c0e200e201c02040711040207806401d42c2828841000388075941c0703c0107400c54104c0c0e0401c450181440801e03042d00c0b008100d81c200001c0c03040d1302c0b101000340b0181c4d010305030900310b440b0a103042070781143c15074500200c1b41d02d600d0909070b40e1402801800c582800303400110344a0412806002052a000500d1011500061010001c080d000120840e2410301aa2000002d0301c43e402002c0090020b5034008030800008140e00c40215030000180d8140c440f005940d003000c43d800641c0c11040c92890405a609030010b248e070075080b01c0d201c00a041c80030343c00d401242c47c00c103648404605201044524402140714010103200c80e5915105040806 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 156562320 1250 156561070 156561077
    0x6060908010f1b0509030715030204210f02100309060e060402090c0708071e02041b0306081b04090305040e010b0a03050c0702091f08101a040603020109030807050319030e0c01 77
    0x100341483d81c0b184540001c03008014041d00080098264404000e407070000c11546035620b0381807140c010010043c1d0300510a0070150010000d1220b141641c1c0310350102e180b039010105110008056081c018a00008590201810f58a40d02c141c0401d84c0c40c001d521a06082c440a4221403400e4810418501005002400780510500158000032610021520300c16081200c41415900c00d11514041e0030010000941050402e110501e07000e414480a06020706244c4060141e9501d464845030749030040e4414054030b0381c17500e81228041c14140d000112003070003480c0c090714182d250110a02c41071020390045842c40000580100c882c0c0d414401e654218aa00c41994584400380d00002e400c004080d22752940120500f80505914911170f20078002071007984140c403100a20ba40c0c2c2c0000625840c40704010043d010000080c141c90244100c00650358140c60760903802c0d045842c5d15605401140c0115540d110030800c6401d00a015041c0e841c2d4002e05a07008030b220007810005070b027064001003000b07061 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 156563570 1250 156562320 156562331
    0x110403021309060b2101110a0504030303050a0608010e0a06050708040809010f110601170f0d08010b070804050a032d12030e03040306050708061002060609070c0f0606060908010f 78
    0x5a50321805507162801040010440720540d0a020000b0424000c02c00c1d48076000d001c80d022600d451400e4040503030b00c180020408907078801058940e51150500050016808100c1400000d00a60056810940101001842c40d44070104542100d0f03c071700a003145544900b1300d400402441d4081c107a4004418500400399003415a80c150707003402290413650501101008003001580320b01c2000c44016a504101c40c0d40d941c0d1511070049244400d0140e407604e000340e066907090780a000a080213446041e9960f481c4907860f100c103981c0f451308050812a54240108000203d035600c041c5800e01840c0503555020084a002900881d0640c2001305c1c00c00c0b021520f407a0201117000c014640803034821508001c105070000311102c90541c892138000420f86d520f0300d000c2c0140d150707002081c51f01c600c1c0c06030740050000c0c0d91080140d039a80811241c190744002c1e0394000485152040c04910440c62054412541d4a2000d40d1450300b1b80352540c004d140004c1c5003182c02c1103000c1e001d024400c00c2c0c0b442d40004006 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 156564820 1250 156563570 156563573
    0x19030b0901081e12190e09010b0c07090504080702010f0512070e0901060c02030604110a0b0711040c08011a13080607080a06151205090f030d05060906120a060c0e1210110403 76
    0x4c84e02800c281400d6807400035442d001c50501400d807030400b07640c0080203100c01d0b603100c1002c0500340c3c00001c0044240d00c41c600d0042000030700b0b480303468002c2d6041000300e030074103510380d004644800350498100c003008810300c00c0d00d86454804a0650088201d0f40300d06a610700841e081c81301130b80050b0701c81010042120b1201025890204000f60032a40100000308040c8084010545102003640110713803441c030000b01c0c6002e00201564641d018081103505200b80b0a0030303c022144001c1c2030140d900703d21410a0500741d018082d00007414010710a5888508644e07550404a041c81d60440340031010840701300c10824058980d104030700c050000c0511681c0e9402c07042400401e18008180042c005640e12004038044072004c02810130710b01141c4003180e60f1014040203141c05060141c034194000c004d00d2000c01d0170b0746841c88001002d0541400280140f1046031140c4018140d019002001d01015104854041c1c5580c0c4d001070300b80c1c0200c0024003071001040111011962009000140765005200500 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 156566070 1250 156564820 156564853
    0x2030c100c030e1c0602030105030717150405010f02031810061508090a050105070c1104020a08160306030212030702030f010c02062a04030f110102010b030319030b0901081e 76
    0x104031070b01883d0160009420101040020f600c2000c4000d814078010b84050400041c2c0d0011410780d1001e505540c00c00e640c82c1c41d0400807d181c104060141e8000180e0090035101992080c3d0740319003d40d002003034428440b102481264002d0b0b8a1031000c07580c034003030101081020025080001051442000700d2460302e20303044507101c1085c142100f0880079002081d481542004010001070308403008200300d05103980041c0168000803421030710038842c0b00d0b96103503e203428400c0d2400000e441c0c407480d070240d0390482d5880607081403c1a102c241740c0d550742c0200143e25803052541c1612980ca005540e20303159401094076102480a40b42d90680c10640030703208450703000c56000d0300400d41b0681480c030503003040c00001c0407402c400451000c0c40320102d400000c1c0016078410b104071902a480751201030000e040124262401154500d4140e481080300714440036000e80c1d071229021981c0307400070302180180001080c09200307a2003911a64050840a6000356051885200180c0703928010321004800c2c16094 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 156567320 1250 156566070 156566087
    0x90603010e1806061e2107240c0809060c0717011401031a090a12020601050a0e040c171f02030a0e28080d0906200405010806060c120d050402030c10 65
    0x8034826820040311034000d880d0a444001107100518400c2e40c2050111181640c1f0156031003403402031491156650701d0440c54101e220360482d41aa198034180e0200e44400c8603507442000310a400100402500301c602c0d006000710409485028a8812200c40b001c10150948418010340c04000d2085001000042c0030b401500c1c00e0380b916034080440650380c4c00f050070304005100d200036000000107680d0580055010800394142d850854041c002261203542e070840c07808044400410703041d1915018050b0740c1001100ca1811034001045644030704001c94402050118a0300d44bc0d0800c0d00401400302100d524000e01c14141c02c80d400600e0002e1065000c10300c100d180c05441d0b0321040c44441d402e42840f000070102c401c8080303a00c0c0c042c00442000d242078001001d038864070382e0000c42d023510079005440c800011241264070594803841e0684602c1c1c1002581d50000034000c1c19071240c0a185104c0c1d002d844041d208003000101c00003400c0c500750050500b0714021000d402c0c42117428001c004401500b11100e07 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 156568570 1250 156567320 156567349
    0x170307170c15061f050931090b0109090b040f0c0504050f040b0109020c07181413170a080a02030709080601090e010b0d0201051608090603010e180606 66
    0x10440005800c03402000510072040054460302580c280408124070511100e809004180c03525440c194079241140c0d0310f99100041400050001c001040304c0780f07400108800030503401801008001c221041c4288911031107030741b42800903240c0c40107400b8414401d0040c0d0050006110500100d507140c0d451507404080100010094840810200305100109050801604026100300f05a003040301841540c004111000c4441d96060400460380b0740450080e036080b9054003000381805400c201481050050f180c00040d0215590305490080015811046004041c015003462803c1014186401c0300441c0d801c2c10200500c0420141d130075517500c425410703800710300c0e000b0058a0351190754084a203900594804179551003080008545841c00342c1c0130700b0401034214000c100c400a40420b0025009814001a000c200140502800d41206541c4014254400d900c00c034034020b800c000103003182e0000e03048a50088c0c0c0500070008407034507150704002c00341e4150008000a103400030001b03022117001000b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 156569820 1250 156568570 156568583
    0x5010f030b2701051519080c01120207053909010e090102070204050705090a080c03060105240a05071a040b01090c050c010504120905010c080a03110705030a0f0207170307 75
    0x40c0e10358126482949000910b0100000740194140040c68004176490608618410b8035240086032a020840d0003c1044864290140c41103140c0132006662640c4600758101c0c8058007041550b002402c01e00136540085604514100050501020840a14480c60105200708850301294040e41e83d2107201904542001c110038996946800301c15000e40501d1400030341007410113041c4110590040050280000241c604640c1c03640d4810f0080c1d61040c4140c00720350150003240042c020f40c00d050460b80d1540c85050a5081d840300341c2004080541d006555010028101003058400c00051081401c1e03400b40b2141d002d49142420340b280d00358240184507920300c596440e00c0310314440c0d00031000e0b01c48018407003000700801d20741400c040200724954140301c80001d01858011803075601801000c5003aa40003200d0300c2c104040440140c000b40707020014074100076410310101000030001c100510303084240d41e68100011401e9140646000180c4e0000045e500c81d514405910950000a43d07490301c2d003111 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 156571070 1250 156569820 156569851
    0x30b0603041a06120c370303120213090203221a0106050325140d09060605030d05030c030403020703080408010e07230d0c17030a02120304030503010306150e01140405010f030b 77
    0x55010781425218081d408180800206c103031604240303000c10046038065203031f00c98004600d01240c000c0b0b1003903454084151928903024000c4c801142e0141d64410950200c040300a98240c81d0018560460703501210b055031480c41049280e580900c00a0041c1000c1c1022411801c3c00001070044154040c050310204401041803c41d00340f00c2c2d041243d20100c2217001581c3d65011041660103415140005d452030341c01c01000140e18103002a20075403422440e0384082c03c542b02c031810021298006802a01180701700740c00400484c0e10380c00103100802240000140811304100600d04214045e401101c0380051007030960b40d021400c0e94061038250044402a00c4140146080001c52010f5042442c20a002e08004601104004000d100382003154085851003034001c041000c0c0745c0b02c2120028001503042c070041000031102d40020110700c01008501480780c2d1075003448003c0c440243d1002880340c103505204040740c141480b070039000d02280b040c40c1c00c9443c1982c840b4021914080c10021001c4400c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 156572320 1250 156571070 156571099
    0xa12091a07120507020a030e030604260c01110d0b0103050411060c030c0715021213090f09120302040f06140a0e0a090615030606051603080601030b0603041a06120c 72
    0x6002c811200380e00560208240d0402d00c038001d6681005101c11400304072800302a4001e480c0009545101d5035100702064091030314030300302c2c4082500c004c90700c0c6550481400b140c0d0700c1f54804e000c1c1c110100d4180c00c0c0c480d20b176942c8102810a0326402c0b000a41030610340b40c240310210300030004851000c20241e607a1584c80c900c4000d580e1451007059000800750142c0200860004040000d4030b031580c0041c2d0031180103480150101300c0900c2000c02e40090100c0e20b0104121766060b98224100c090718411001580352103580390744c4848006200300f0740000b5070025061000c401704131640b0004d0002c03441d05442d20f02e41200e00c034441e84a088034040502c007034840d405800e030703442c03e022801400603520180042580c03500e5080311a01a10111004a820f240001c02d9061140003552000d07210810314141c811542c2e00c091319101406006581099103800096065444840c001c0d0702480c414440311a480c02300c00130648181e54042c0400784211034140305440c0070039002031850044801280c40c2c54941401 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 156573570 1250 156572320 156572327
    0x510051503100e24180318040b0604150c050609011107140703080f07060518031803101104050901120b1807050a03061d0304080a0b0a020912030a12091a07 68
    0xc000900803040e035044800d6844c01c2040c043d001d005440c0031043c030800342c20001c5850340160000544000318440e4240700320302d450b401c550030b41100980907e140c02d4171441c1c441d07001c606803068840403076801d40da4082048420450740d54000700e00c070001c01400021092a451610415002521000e403600300d114007014180300a500441e40303c1e410b195200c20400ca52141500410401d43d03580703140200152200c03501c1c01401400d4820840910b20700717503199501c9000304400400300c580620410750b100d0400b02d031900c030740c100c854455000c0944441c98070040010900050700070b114450445038601c400a002118826080b6480100d0b00801041414449207801d40c1a0710580d408040e0800010502945500203800220030001230f05000e404007070080c2d501c1c0b05d18490358900354004804100404c61080d0320b103401c118250f80141c546000d882c001109251250480702181d040042c02d056580d80020200e080c2d0942d821040c40b4a1a00d5250600441702c01281e00480c400c91000240c003030f510 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 156574820 1250 156573570 156573583
    0x504110f0f040521010c0e1302030403020c0907030614030d05070b0712021801020114010302090c0f0912011e0504121202090a03050f0d03020c1009021c0510051503100e 74
    0x10040d0413050704050b8406809443e075804110071016511741090030141078814504c1c40e04240300070300880c64200100c1ca14000962005205070218020200c040c0d02c50b40d00c1c1d00520380155035a6030007040403414135a8030021a0f082c41c4809229501080b0106501070700701e07040d215080d8000c450000a80e40300081a030b844c1c9643e60701c1c01c1d80030f8400510000d8642c04140780d540c1d126004c1c1d0080158184800c0041030f101400c1c01b0103035002071848006041710010304001d100c40502d0b4903d01e0f05184030a4003180304044907450704051651120702ca40200d01c0e075111224500084004240704504182d1501160442480441400c000c00f41c4514001d001e6541c04444000b1009080f00c017007103559080c4540c030b0704440e000c103e1980c0902907818065910034000eaa80390300348400607003014045c07031000382c0040681060072a00080300107540440d890010229968450140c0d02600c121030106107204101d400041c034444900085c0982241a510001120092005961000180002c040301081e10b88030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 156576070 1250 156574820 156574829
    0x50f16080907140d050a21030905120c0a0203070e01090522020402211f080d080a0902010908150702010c11060f0414190204051003050d0c06060317130504110f0f04 72
    0x6c101c52400741040342c2c2c4005500e01ea0500005084c00c00c0c080c86041301a0b50020034003600315805402200c0e813001e104001010a03902c1c00085580c050b84517402f003810aa01640034030070040d6181d0040003009842c0c09101d03803011610442c843c070140d0240000900309014100a03000d50b0380440d180ba10003120055445009054014403030139441c100e44504a80350030061082c0d0210741c0d96000250003000014000849040c3d034075400c010369100d805c1c220003484000070130b90421040b81e41c0082c1f80e007400e0100041041200e514801a8540558041e080d90068500c02c8108149000d4480e0084000f042c103d42185000c2c034912400c0e01c0310700f0004407000445100c09600c0c0501004020100000e400d0b00c290305100ba50144000c1c1e40b00d060f0060b030000c6610003d88235800890400d6890341c800e0b19020300032485044002040b6480740c40b5600525943e00214216000c006009030402148068010041000b00d6051000b807032084032810041c09200342d8480c03c02e5010821108a04d80e0a050301c0180 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 156577320 1250 156576070 156576073
    0x60c0a0503151e120105061e040b091e01060c0c030b090f03130e0f09060601050d0e0d0305041a1b07050304150512010905060616060906050f16080907140d05 69
    0x60200b074104610324142c8084c880e54054000605940060090900c50440248201c000f0314480076402d981c0f0600c0500240d000741d1f21282c2c41e40a56521803450b0040014005101c5600d80001d006100c13181c068021005201103000240c00140c4409003003000d403035001c101200e040d140d800c05140340161440f25500c0300c2c00040f03071080c0c280d289041c030103080321191464580542c54061000a8041084c0c69100c0290000e070b0002e9899405140185107405803010005400100e2805403407c20b50000180070000e48c6407400d101c1407001101300c0040546036507120741510700b019081014582103040900340380c54800305a0300c0500809005503401003005a01d9860381c10410100100b80f540410806d035a2082601d00120f0713518528841d1610500020301a03914046400c0b00c21980c070401d8000403a00c01d40c460303d407100012228040c09005100c1c4030038501c900e0416419100f01c520b0b03885580d6003080f03405002c00c0203015001510200300c900c440d452850000c1003201003071403103a10302c1d801307082c9 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 156578570 1250 156577320 156577339
    0x60d02040b0a150905060309070603050606121303091401080105240f13060203131a04091a030d0e091303021e0a20220b030d0305040c0602060c0a050315 67
    0x2e0b600b001d01000b041401c0d65130280d600f03032100c4c1048543e02080d569180260b00940081c01407a020340e200c640c001c40020000303401d040c8540c4911002e00011640382252080815406041542084104000d4050b004401c829008907000003000020144a05403266104283c40032030342d030b080b014400f0400b81d01c905841d51400c824681232180e911401000707500700800307075000035a02d101100361007070006811411204246480881c4c608113103c25500c29107040200000114041d480c410900040217028850f109803015500b090305001c0c1c401618800e1110295800085698000400341c2c001c0c81a0340c2041300c0311540c2001c0345400d01820313100e4850b50b040410000a401e001400005892107401c5505595043d05c1402940380e22800c1c5c15038000040404289210f1206415044041e4007550001a460380500c0064031301081c00180c000070990720014001808154070207000a888180010596410603030080f07013092146140346010005c020011585d40500d4030b054448014005120054 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 156579820 1250 156578570 156578579
    0x190e100804050c030a020306010e2203120b061309090501020c010203070207140a0b090402030711011802010e1023070c0b0418050105010219020a0302030321130506060d02040b0a 78
    0x340c00181c805407000d1149501c4054540b9002070342400180c0c2c081e000c1c152036440d058a0403004c02740038202c4d27006c82144404040c1240b4401250080ba00c1c060350310101d1544c0180c07401411941a02449800340f80d0400151040c0891022241d046605140c40040d1240e130ba400c100d8024007860380c04e0313421540004140b09600d0781c001072800948012002d2400c0c04000c820411486410701d10405160000501c01600701e45002e5000d1640003503030381400b0b008540c41c021403501310364044c90100c080d4426240f1240541d42c1c000c010b483e10400c240d0f40003c0b183c0600c1c5020b23004a000010814600034181141400c4400e03d205450005a10100502e03885032903a492007090b0f0800c1c0a000200c910301d1001c002c05022600925040b0b0300c068001c0d1070725a2680c40e000c0388912031840242e80107210000b000005840410003000e10009640d80c1c080c016041f0a40a440e0f840c0182c9011550030b807011800b800f050000c01e040f0b03040b520454016003120094030114005d003a031503031156806035a0200011307 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 156581070 1250 156579820 156579827
    0x423070303200a02210f0114010e06010c060504030807030c0504030b2e0801050103021c0b040206130b0313140622060902090a09060507030e03030c030702010b0a03030e040501090b06190e10 83
    0x70349808071500b030366034646c0c9030145a401c03182a45c00180030881040010083d240c441110300b60044410300d407440d4005c0d0591130b498182e4105880c1100011025410001d00c40e600d1b20800150707010030300e021490180b41d0340303070850b0002c405043d803400c01003011380020050100751301c1208070100d5581c6a1001960b10f00b00c042c001c200900c010303800780c0d00041e15100c04505501c05406456406203840105450701d0302880110380156850550b064080f51000c03c11242e0040514895400160a20343d449414a0007850416622100b5400c41d13001d1b000f4481c2c3c2120404420b03402c0c041d00f02c2134216109840c1412006042105000b80d0060503035003d200641e48150420031541d8010f200920458840620450442d02e44450840071a0810b00101741319000341c00083d0313000503c0e41700104812044400050040e4043c0d481200410001c0b04204680d08040c02828010610034404000288040d408600e551103204102c22000b00c094890210917070085140e03480f5450082d00c0d042120080246c040d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 156582320 1250 156581070 156581119
    0x90302120109030e060705030304240f1509110d0506150a030c23040302010c02030109230607050405060901030915060b1210060e010c03170423070303200a02 69
    0x25000a81424041036990810b50115074030590310000849c6190ba850325805074240744142107560010030481c0a2000b8601d601034010704a8021000003203000852100240e8442d940d804812001d003400243d405858055060300c280351482d2001044690345c040010b42c1c06000c0036200e20445c200412034039501981523000342071641c441e4807030100010356010502c01030012103540b440814400c000600055114480d03900c0345604c09000810407080399600e4018081e0422501c18800c1002105581008401c10849030007032100c2c2411803800b0306200200d0840e104544040e07060585940e60501040180b00445602d0001000d080100a440d006820029440b4082c01c042210054000c134605114400200044400c65200d4044400c1603400540d000340703025070180c05007c0340000340250b0f02000c0c04281d10880c41003810801c0340c440d20305046100a003a0070401e00d560701003103052002076040784d0131032261806403c00342e501182a00b19507181600b040d00094000d40415803da0070303c1b010074000c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 156583570 1250 156582320 156582323
    0x170f0301060f1115070f0903060203090a020310140f360d0810060309051608030918070c08030a290a0806040c180902032a010e03100c090302120109 65
    0x40b0200030415007803a964880c5400350200d03200d1000c1002c54100350061b0030300c4a2406081c2440c03007602d50340351141c2013203810803149010641c2164200c00304600e0140400c1110004548081000c0885400c501c0054007009004200c00000000460101c0721150048000241845c00c0c0400810704010400a800000724030040c4d80d00c285d41541e00411b016a4480d88101c407018081d08e681490040203e0240100d4035045d1598000c0c681c460190f443c11114100141078010b00660340d649091082c4540c1c9404400d0180980c1110414012180e48c0081010070707440d0410350842d26600c51419000040000d003401c41014610110012110788880f18000001c060851320f80e07400d01d50341c4076059240c040845008080c80340c402c10500410050550460002d61000d40c0050009141c0d40820324110048042055803c06551891414451912140f503540000c0c41e20341d005010301e5002c40d5941e03141c007442400759901c600301460000d110b007200f10001d41d00180801410404211824004c1c200b8120 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 156584820 1250 156583570 156583577
    0x30d0306050108010b251b03030206010e0a1b03090201050910110d021c0315120305030604050702030c0a030e04090807140601050a0303051c0605270a0b01050304170f0301060f 77
    0x41740c0101e8010f40c1c40c0c0e086028445001208016100b18074030307003034440484081000407004880701c1500d45c1d0080103903220b0b03002403285504004c0315400710000202030500940c10011052800300ba0f50031181e00c2d035a818140444e0421071803005807403501402620641055001400f074010b194460382c1d40d83c1445040e0141d03808409050b17422a00c4444068000014802002d42e00d44510304c694403651070602c02d840d2019001e030301ea14160142000131103043d00050804002c2c442c0b00d19180c401c072030704101680000c0d0324000304500115203400c2402c8014083c4065454080c40a803140c2d04109541d0b83d10084040c5e542c0c8061074000424070249400006030300c504030012030141401000303402500e80548910342885403511124004a000c0b41e030100e903441e15980002078903140c1079403d04404d00f010b8407103000c0359003400308102031400c0148030352180f0b0304007400c0032043e90300142141d40040d0007400c200303c1c1d054455041c0a50381325110f4034803d0071400100000311160700c500034800010140d81d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 156586070 1250 156584820 156584837
    0x30a0201140604090f0f0807080d020702030d18090b03030c06181c02070b030a021315021002270a120b01140f030d080603010e01060923040507050f040902030d03060501 74
    0x140004ca58082ca001001030b07849080c41400700f44c80381301200d4414440c0741260710300159595111800e400c203030002001030760003003510002c41c0f80c144000c0031410200e142c8003030544a0604600b18080091069100e6169a03200100041e20140100c03210300340d18000720303851401c08070000410001d50b089885000c0c000d54405052003c00103008504400d8a0f50041c051981031102050342503101501c1005801e13420440c8252601d20400710340020001c046c034050200b000308401070f0408450302990076840340704106c0781c18445680c0b192203044031108078102c1c00000580d0080340b0450716903004500c010100c040250100180a40704505071000072092180019001003030002200342c45084961542040e91f180401c41d20640380f6aa200e0001000800d81071607441341c40e401c41e1180d402500340c1d140c6850118088003030702010100c44030389514a10720285016201c40381c80c0d81d8940240b920a08020400000c41d80d9140c1003198040d0b001000d4800e003460f1990040c00400d40c0c0d21845010a2030203 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 156587320 1250 156586070 156586081
    0x11802190b040605031312020d0305011502120c28110105042106060b0703090f1410080408040308190210231009240b07020a061d03030a020114 63
    0x380c020040755240040a410035041050603201a000104441c10310105200c109002c103c04038483c1700c04100c190054400c240e03403040020b040e10f005802c00c0d0440e8980c10802020507070b00040c0c5458040300d1001c07054603506610703641410240c41940445c620308803900401c0111902d43c4011034080c0c4180071600c403444002c0b00560381c9002d60b02c01c0170010503103041d900114640e01e20740140200d201b1303880050b0a07134444c401c80a09800200c03041c0c00091b140403007845215450b09020000e440c1704c021102501d098403000501506204491034104014100410104860103060328003441d801900075880d160440000100368180307602c80c0005105d800075104241c1c1da01d102c1c0110700004007024100c903141e90290103c0c25030014003900200f52850300e0014142c03400b44501c42d07100c807503061003095500002c2c0e01c90920f040d20303410a00100d0000c00c840320040e61064091022908141042d110b2110041208241243c180d8116a01808001481106e265065104202c0e2034048070140e806a00d42 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 156588570 1250 156587320 156587359
    0x319020106050a03020906040203090a05030307021e0a0f030c0305130308090316060e0d050a05060903040e0f0702070e090a02040606030f0f0608070506090d060f091208040317100503011802 83
    0x511011b500f080500000c100c0c242040c0c0c005503400b203008002c640c41805165281847c50340102c43c2d141c010b81003103e0002042a458419074420040000245908481501d172031455901c03a190040c00d000c0c1c1c2482c0d040c1094005c00c16034000d007200c500260710055803800d1031211940140d00880c42030050f8280c680c0100c02c0868240169880707642c0b441294000f04080c0018220b13081d5082da0366124052000001a40c1000722621840c07459010303540361454528103009814001e0b2401c940781c081c407070411034100c0d800240d01d011102e400742e5071002911180c400b203007465080100a904181003010100d2540d0300340e00a00288110700b40d0410a80c02c0d140c03002411a0800c0c01055116000034208225910f8440003a10b41d003d401000041c11100c5c50781e0348400c0760080c1c500c5844568680c1100f00921502d0380241003019090f0401c594145001da4004003802003003c000915449844007040056141d0b0410760003178030001c0c00801c00ba44003200c20b18912149420100d114140c0e15076007400b40c851 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 156589820 1250 156588570 156588589
    0x50c060103080c01090519050606100e100903141c0507021c030e0d06061a030c0a080405070807080115091803030902040b0d0f0311070602210408031902010605 70
    0x5110014001990840d0380e1025954443c1c0e491a00075034130380e1002c80100d03e06101200903e003111700c0c460a0010783e0329010b03060001c0148590700c0341d0040342c26901e6040c2c2048842840150448105031804032906003900c0e4a80d0300c0d0405040d44941d0511031894281c0090720045021011070540c0c0b0002c5600000c4945102e0240001d4011171500c040c058004180d032182d00183c3d00c0303400c045000f103150101051203580c100c0c01c261105502c9900c100401c0e40c5805207120098521542c0038a586841c00ba0482d0074400c000c0d0000c108103582e0000b034140582803100801610049040c0c8001c02c0d0b8500c0500d000e440e9440714614265007100d0002004007d034894403504000c45552100e00e1062174070150010194420281c8c1c01c26120348001041d40d590302c0b56008030340c1c403900c003096071b8034010b050003001d901e5043c003181607603840035801740700396900000c1981d210803441000315041410481540703602d000d190300c03080d603511010a0200c0340d404000c0b9404070083c090780c000c00c0010750715810800c8048 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 156591070 1250 156589820 156589837
    0x70b060406120303050c040e0403020304030c0e0c031503010e120a1106010302011707140f1804110d0218030307060903110105041511120106081005040e030f2a0706090605 75
    0x404070540b02002038040d4225a6001e402170902508295843c0c0511488460881c1e0881c0160000141401008052091400541100c460b178525504e0b01c0506c0c00c05620000d0440c45400408a0548120750b6094010340040d401c2d501c10b80318080d034284010070490f0410b0340300300b0118108984113200c0400018141d4120780c1c05a444058103518004222030140010b00041c0030402d0050070b91081c15000740082c040d1192012401d0355a4000841800413449003010f1688503608022410740c2101090f82a80e001010403040141c0ea01c84c07806208110030614100690940000f03d0550709010032036104145090291b124401000042e0012030b003210411078000304410440c40c01c400006c869540040920310700748190b9890500e009403408810340b026808000042e010904210061001c440c5a10007000305550502c0380e084240310301d0740c6902402414044040c03002c0344030001c00e45d070b800f04485c040c106d2020700c0041e5603400e184c440d107590b024007500c800306401800c0007a00b5032050f002c503031800 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 156592320 1250 156591070 156591089
    0x50d1806031a040b011b030c03030506031b01050d02070609060608010506060a1e050c011401051516020f0a0e10030611090306041106130e04020f03030c030a050306031002070602070b060406 83
    0x1040000c003040010088a113100e4100584404a030310a20000d441d14001c060090711201c2841546140003029540300500250294111f10741d039120080115100b013129001c02d0a1494460380030040d180000c2c080c801028210500700703051030081c03205590199043d50b5000000f40819a03448040c00450b02c2800710060002d00d4101c5d080b180300043d02003543c0d4441072880c0441c42c0c88804d19006094944248507601c0c90f600c00c50040042c0c0c40c0c1085001900358414611504003400310140026048010302c0183c0901c42e240c10080040d500d541a0201801411074030322080d0402450f40c0107100d2a90004450340391401d03195241511904c01501e42155004000384500e40d141e0f41d80c1c1c00f80c1e00340d003010140c11020601226102c080b42e152040b000d03102514103800c0c1d0b40b5040c01003200c1e0030b808149080c02070f003040240b1a40d101001c1b0440d41150840e0500a940b900c610020a00d010100040e50901d50320205e144000c000c0706800400c1e1035401040090481c2d1510400c01085072004d10664280 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 156593570 1250 156592320 156592361
    0x170d020706080a05130b0a02030718270f06061805010302090f0120010f270506070804080d020a09140906061c06050a060e2b030c050307050d180603 65
    0x28801c954000580c01200341040354000c00b450b0740e52200e074040c00e41f048082d031074000c410400303c294840001c2100e580c0c1900030000c074600c1c003c0d540440c4065029544004c007500d01c02004a041c046c0c000e941ca4226880341001141d5846a0090400d0100f0f01c1141802d00c07041400205c1e50702c40d00035100700140081031080d4001034007005440c0700480000c1455a05111209445009020b1240f000c920855010102d001c1100060219483d10440100450718642c4400d82d004100d0018955030b1065a81c1016a92504c2d20f01b0140400d000d0580c0c10480a030000401800080e400030b82103040701c451720f4bc0070541d02c940404001a00c44101c6000d6000341007800042d01025400c62b40503e00300d840d4200050050700d4070042283d1507400d40001020030504041020b8604100c680c180a2201c0750500348980101031660080b0a003000201604101d040c6503a4400d0000900c200c400095110044402c030024207003001d0000740c0c000e00c00c01081080b0700000100700d40203008011601c00344030140c201 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 156594820 1250 156593570 156593581
    0xb070e0f060c10110301060f0c050703030822030e0406140904061a0405151804030e010c0623070905030109020607170702030639032e170d02070608 65
    0x15a030b0030010100350507120b83c0450041c410014450089030801d01054169a0340c1440c0c00601542202c3c92070a040280417882140400d00106982d02583c0e07252070110751079111000b08107101a1010f42040d0308d0b07010300749007004254000c2c0311204181d4090b2402c5c0034050707603000b0310031002e06008142074111414800107000595203901c030448450440d018002610310200106045841c00c990b81489039280c000402c03600c3ca441e018050f076065203c4050105450590790080018203c1c6006906014402070000c042010540007500501900041ca04500c041d100310340145a00030743e078a801090222030049454241030150f03120301c0d81c0141c4407034039006040e5100e140b05a04580c1c4880c61038020300c070710001a0b400340b0415000390354400007070f0b444040ca181d50252000d02d4080d40070f50000c84010240500500c881a254007041b20b001c000c9010640356804540b4800c0340001c1725203085d61b00c1c004036a0f901d0468a5508000080b81110380c0c285030848243d0b5200d07014016003011840b8600000d1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 156596070 1250 156594820 156594829
    0x180303040311010f06030305040f0f0308070b0c0904020304050604020114031b0304060e0a0b010303080114100f030603050f0a05071a0301120c0305062d06010806240304050a0b070e0f 80
    0x705041e0030b0000100c160003400305400701d4000e904210001500000c041040c03034603c000e004080e01c404040444401e256660700c0c0030610422800030041c412001c00180151078000c10380e14a00e002074001e41d500d01e090310b0b1942e11000211001c901003a281c0001104003c001004c0d640316908072a4001a08000c1c1d0000c3c1020fa000140104c4600b40c40e000c2d0351054240910000340e10611424050311294107500e8080c000f5001600031002d098452103114000d55140041d09440c5002400d0807800c5560120f411070203000150000340041c0300c1c003078050f00c41050014000c04181d0003182a1202d007502d40700000e00030304e4042e65024000d00b040c8014451044c030010b070308034403502c40c09160105d250399036112820f120741101d160106404002a81200c003110500c1c0c10f000d051a0306046105281040000e002c0310806807142d8003c0c154603490350701c80d40c1048200b1081c031f02c032820166181d28061411036030341e285502d03080710f8400711070002c9004c250064103100d4088a009080c108000c40c54010f20 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 156597320 1250 156596070 156596087
    0xd0c03051b030702060c030901110a120503040204021303050c010e090603070314151f0602030909010e090a0503160204060503060f01090f0609020c0706030614011403091e0709051803030403 83
    0x2461400300f000040016900c03840205610405140519114001000054010110030101700da558110b021002c2c0014002c204d5051402c0140c00c0080c1c8a40312400400c00a001c1c100541040160321580171040c130000241c040400b00013642d58400c403a80502c10f2180400054800345d404d507024003001c0c00090345440e0b00c0406200d21a0171039001b0307124101e0355003c1220a81d00c2e035800c04d007405548d213200c80b105042c600142c0030300d00095141c00141004100c1c4641e052182941c081c40d241c0208007001e009112402c80c1981090449880e601090a407030703070b40c0c0743c000b1302280b2451420a0000e02030074081796084c46000381c80c0c02061030360310f85040c010107000541210000ba030354542000c18600403600c040e040d56284100101042410321401400b250764a8200e050120204401c1c81c3c0280e90210440d48840902d04045441ea11100405845c0156030304024024401c1800c600510f00310001e0b00c0740484801420501168607000310100d0074405171080e14000e5001080050f01003801040300 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 156598570 1250 156597320 156597367
    0x7050111031005090112031d060f12060f041416030f050408070203060106050c070506131208030901060905040b180726010b04020406020304180204030218090d0c0305 73
    0x100d034440c0340c52081841a84111800c481d814100070052125080c4960980d001d0181081c44400041898074007610701800c2881031103900e6803444600285881e0242590384807010b0030451511010210381e2916600310032100b0602580c02107002012601d81401914240901190101d0761340d00e80c02030f01c100f02e8043c42900000e041d240d05541d1031114013480303040d01c00c5003d101705e5522881c0620406d070806c0c0c1c041e8041002c226040c84910007502000ca0381604860044494030b55620400e45d0f20b100150b070540c40151030445c0400d41c03038280185940290310a14203900200a01070300c1c0c10f14502100e03c00d035005016803101c2c1001510485280146004a100f002d04850046551b2504003030712103600420940000c1000010b0488101d0901903d0b4030743c8021a8154142810110700950320700640c414a084e102c82c111b550304000e03025074122005960080c1a03100740c086071400c105061001580ea104017440740806c007022861061042ca1200c5a0507507a16282c004500e0002c5143c05040c1d10 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 156599820 1250 156598570 156598573
    0x152110020f250f0309152a0f08040e011a03090a0b0405011401030501150f080d051b10091a07120b010203040918030801080601080a0b070e18010503010b12060c0705 72
    0x18020a42c01c01400c20300921a0742e0309103075a4100100d105040603c1401b60342440401d0203103a0025800001c00c82c0644094807040302528039900303141c4103032421520060100d0304005004590f400340c00a00e01c0c180d0300030805880c2c09110b44100361445200464060f80d194014842002c000340c0204100d80d0081e0140c4008922240f4080181c0e1a14000381d2023240c1d242c1d5100b1400400401901d0144024941c4440f10409a840c00c100315488001d865805000c11000084030f1501413107400c01103d620342101d040b0380c001c07201800050002c1c45e804405132243c00d4110f404425512000840c1c0744914002c0d81e800703010034654980000508010342c001030550005000c081030020b440d00c0303108450178040994507084507903410f02800e40b20040c0c001805a4000d08014421150000f07450242168000400d0b032140e910fa1204a8030803e064028039441121319078241102c104418000c3c0c1038038821002001a1000c0c6030801044a0241c071503203405030042c8000614a00407603018184d010700400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 156601070 1250 156599820 156599887
    0x27050402030c1c0b0f030304140405040303021306020309041a030a03031a13090b06060f070312060b03010b07060b0a260c0414040501060815010e152110020f 69
    0x2c00c511140f20740c02c582d00703591a80e98600611030715040500800a6405402175843d00e07061010b0110b00e46c1c0d407102c0d0140100d444001060402d4400d50440f01d00380c100c1c20340035083d81d80303d00303000b5100d42c03020580078441c5040840816a05401100319405682c00800510702b002e590345e410344c0604000e8202c1924000704030f450705280c0d200c0100485401c86000000a0322101600c1c000303541402c0a00154080c0205019124030000c400e0f0444440f02d4040c1042c4c400c4000d40b159160151405030004107407440c001c0b0000076407210300c801800300988542e4050101b000c590060020b142c4270b034804c240c0c00895a205000b41e40c09a072050544400401c0e0540e2907882c226000300381a03401c048074661201c45014204414050700388112005045188050300c3d000041c0c500030700b6014018040c01d070441c003604020498130b03c00c0000741c0c004400301038158244519540c480801c50208401045214010030401034003460561084038542c1c04a50209400c0c1044030380d40d4211503d07049007145a00b43c641 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 156602320 1250 156601070 156601087
    0x102040e0103031809060b04051c02090420130c030c1e21050709032609130905060f060301060b07050318030f0f1f090209010612090803040b0727050402030c 69
    0x80c040c0f140a84806c0b040c05640700d241032706014070340000441a800401c1015100e200583d221551160896004154501c44100f0900c940f0b4402100226180e4000c4503040b5840220549401200401e10151410080da1001031815554a000d541d140c400040f110040548070300c0c0203205480742c151ba100303003900c240380345102c19004840e0b0545042011450209080040100c59140c0c101135802900d2030050303e10000030400c50030f0288083c0e00e485610210301403a41250300c2d50200f103106400c0b404807030b9603060141924900c00400e5032020701039400c1060204040c0500011100f13103a521800540c54000f54044410191003161130b5981e0600844101002c0c2000801100341c00d074094002400100394891502000040d544094200c440c2c00c2040c408007603a5032242c23841c1190707100d0801292129801d2a4038006140c0014010003401d804402e1000f80221110700074820384035611307001c0c0720a000c00c68040ca04c1c259a04119510800041c060081d41001d4000e507402100d828102030400040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 156603570 1250 156602320 156602339
    0x102031b0a05070605100312090b0403030f0509030a030801170d05030a0209120604030302030a050105040501050609010324140f06090a090b030307080d020a020c0609010909023106030e0102040e01030318 89
    0xd1700c049070740c2c0070301b01c10a20a012404c02070560006440c24898552881d14040d907007103000794031010f820320040e00400d204c418050001c42c2e4140b980241070704d9910702e080ca0050468502800b614030391420360441e45003a0000080d40710310040b00c0361103090035070399500700000103580701070001c41c1c00035504603001070742d0081001040d004a2007514056140c0c0b800c0f20700e02c1c0442c1e00c16406180304509001c01044591580d0341140c5d40c504082c030340803070140b51043c2d002104211b602d0b542103a007014070100192032404030503c01d40004c401c60704130b03c1005001c810000c290081c501c00c0c580c0014043c04c10083c142895011001120019081d01d0901c2450f41742c454030303500304410011550b83c000030064480741c2d05209288440c041110640d00700348118000900300c000c64020300c103400e5800101041c544648584a04070381c02d1a00c1d00c0c85015044440440710312880d84250804a4101421801c0012060083e03d065461042c10b000150703185440c11601c0c142c0941240084400700100071404007007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 156604820 1250 156603570 156603581
    0xe040f02100503041a0f0606210108010c0e040506090121060c0f0206101a09031f02091306080a02010f110d200105091509100207050615030102031b0a050706 69
    0x20581c945644915080c2040038640c8085e80050b103454188804224001102943d0541c000909461141e141c2c814a951044440d0a504802d030b0400c951400024080d10150014a541080395440310744800d00d810a0009883c000d0b07916a034040318590048c010304035808500141c040c0d4880c0020303032855441d2200c0040301d05600144001560441903850f500d901003014a404c00c0e0918090103403c0e2800640b09040310b607401071410607c3c80044c1c40c0c041c0d5602002614500d03d084a02d01d15001c1c030fa40c0d03121000358003010000c5e000e0788801ca1350000001d218444e44003200d001c0000383c1100001e603401112441288907001c07051140f001500945000200540207034440680c4814100f0350700100019902d00c5540712980c2540c1c102020400c4a05022a81c0700b00d00030b0040d08080c5544503900380c0b5050078a807400906002d40301140c080240000029402d00400d83c1c1510006c6180030801070500740e100855811001e00c0c020b01100180715071140003440060410314195043c00215501c0c801a6070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 156606070 1250 156604820 156604849
    0xf041116060207170c0c06090d1703180601031101051c090c03062415110607020607090501030c0c02010804020105160c03150204030f0b1009050117010f0507090e040f02 74
    0x950109120081200414481c1813904944040d5402d0940070b01421baa120303203100e41c00e4042e480c00b080114094403408000c20581e54002003501d003406210241400942040321420040000d80c1640300c0505c00101d034560580743c014480d0400380e9503190054549500c9080c4128034404041c1040d9500c000c20710400d440c0310301c50700006500b580345082070350685607164042240341680309909802450400491001c8540e80b200344010002d0b840015615514501c080628034005d40d810010f070260301042680c86109992206a81c954851004408461f104124140400c05501903100558000d01420340e01605c149401860180e91541d050401c0d000c1c11002c490000680c1c0341802080700c5103c0c2503001c0041c100085041c20b1440d2100c0780400c0320150094124a010408107544508014440307001c1c024114043c070941d6954801ca001030758280046039020752800c110701900e403840b405018000e26860b6545100c0d54204134903995a00030203481118140c802500120050311000145000d40 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 156607320 1250 156606070 156606083
    0x31202030d02190921110a080d050a02010615050304060b0a03080c0a0201020105060402070c0b0c0a0c06110c09091c0306120305220e04060914070b0309010e03090f041116 75
    0x1240002000b401c40011504a0501003207009200e400c886005016240c1c8031b42c0040c440880308406c5070100e200711f881d54001d00c607940100490901c0482d00039004100d5410b0650007000b030641d984140c8100310008000701000100200042404100c0301d07000b503603c100004211605c000d541c1e680f01141c60340b020040c02c826412030003400e81550380a105084d03200e802900c081d0300c2c1900590312440f00d02c0480c013808982980c049040c2d40741c580100042d8000540c07120440d0991074031481c001c2c124100080c2401c1c0d10744544003240000e03050a510b035500500c40700d030040440740360302d10010f907106031440c9152040507035492001a40c0c034070f50b0086220a900a4545a80d81c0c40700035800c1500418006036104c58000200d0100440c04c806043e95501c10781000380041c01812a1824094900780d202c00c6021a2181850118480d08110b0045000b00c03001d0f1f00822844019186007505c070700800d22010760209401c05903d546051603003080903017050b03601e0346a1600444080c030306419601001e041d00d61 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 156608570 1250 156607320 156607357
    0x70f030b0a0314070b16030c0302070b1804050105010e1e011205011502070501111c05040314100c020a02150d0603080d0911010804020306060411040f0b030906011509031202030d02 79
    0x10150140803490150540d00d0303005103400b86e0315000e826840b480f04401410001052044001e0620900c0410054110058000c1e40c40302c030310340c044015411841410384201e103800300014031503015244000420001a04900720404456608a142c03514001098184001200b000e01100c100e4801e0358003911440c22042c0401c898003a00030b29105882c1c0245043c0300a032600500c140c0d900050003070780e483c4007400300361403040c0c0c0083c215928041c9900007040060100e800c0303000c5180114044020802c040d1341000030904034081207903210404e40000c2e4010301100c001c2c2c5082ea9542004100007402803a0120b541e640c0ca0380d84000e00e510680c4140f0b0080d40c1e81840310200a212000080206400d02e05503c540c20107800280d160362014003030512441d1b4511414124071441002c0d24020321420400c806100e5441c3d0482c03410354411542c040440c014800085003100e20940d003624440f13015030341c0042c118199503c8500704040e02241e1025807005020062030403000307000400c00c00c100707558440780 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 156609820 1250 156608570 156608603
    0x4050105010807060c06050c071707060b0402130605030408090904030c030206070305010e0c030402030a0804231002030a200109080a1d100318060f0b2106070f030b0a03 74
    0x854906030030a00480d0403c003010000a94458618020a074100720001101d44034201008040c1c480e0001c000c2414080e0745040c5501c0d0316590140070301500400003844801c2e5003004101c1213100702503000340400000c6800f8002e070b40c4100d02039540a445442d00c0751400d50108005840c908046400f100002c01d0b0042410405505109198001006013000d206d1541090200810f40d0001404805c02c481c0100008041d03540800c40f281c80d25400002855483e41c0340c003480e99854080340750080c030b400390a42000c615400c2216410b40b4002960340910300300301840b0811580e92202c81401c00b10080310a0709445403207401e2117540c100c58415601c050303842120510142c8450111400508507050300182c46015444280302007803200c55030301c0c00040302c0e0100c1601c4550f140c0da406010b4122841c2101144c100700b83e40c1c1c440e016401c4125007403c0541c5c40041032241c03800c0045000403190300180b0114914600800084007003041508000c65032041e840080399010480e640306441240d02cac15618034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 156611070 1250 156609820 156609823
    0x1218040e071d0402060909060102190308180c0603010b0a05040305070f05040c020610210503160302120c030403060506180a050f1005030a2307030303020c0c09060d0204110d0c080405 80
    0x2010b0010030254028030f29250f000241c00c0e000e84c000a43c002c40e41d50340090301503882845807050075130300011381d241045c0390ba080050201e0030031144451a11865030104c000c0d400e00207503001c50781c0d40c0144928550b0382404601003283d0020303545401800010302c408400100203102d040e0140125040c80c05000d03280004000c00d84008000f9a81550003a20900102400c00502c2d40c3c00d640c052903c440781c2da030740301c445001c1c0d50403c000c000c0d00d9400085901c2c10401c6099848055290203070342200c1c003541d80304075003c203c1d1250102c0c07640694801c02040002540c5900402d070302c003400604043ca0301640a00340c211010301100cbe9050155500c4c0c0401540030b070f102c60501e400c00c041c0c02e00c80210700d043c00003007a910f1250700c00107061100c01401e2042040d15083c0c0c0081c4105898007510341260340c038039000d40079400c04c00012819018048000e802414107101181c4520401420500060403d40070712004207261940c0000b45801003191100c600d000d80a00040e2400c0c95650504030300d424140503 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 156612320 1250 156611070 156611099
    0x4020307090506030307030f18141206070206130c05040f0b0405010b03060d0b1503010c020618060c0f160203031309060b040803070803070c02090a0f0e010b031218040e07 75
    0xc244291400043c0000c0c0e450001c00c0c0c03050306505080c681121505c50706c0a1f506414801011040c00141c0c03500841d81b034410980800390907409a0f0168120903100003c15142e5000302e5580c40144d108400103546d9000309a81200d006000d0300c0e0200100307031600f0115041c0c2e8881401c544d40181c844a200110781014441c0030f0040c04080c11640c02d50a000e0000740705455100400380330402da40010500c010027000034409202c00040007080480710040e00a0b44030a4204ea280c05042c5401410704058500440c0d8a0710811014016a10701518401e00c0f020982008051151301104e4050420068030300300020000580c9100403200054600708807001502d8194000d40c00002c001c0c442000b0758035000094804040d4440d20b10b82d02ca594001007250390140a00003e540044400140460400f0315404070402c100703200da00340089840d8000721401e0712210400b90303400d076000381d2400c04501c00807805401e1115000c0c180c50424950704002a058074032194800485c2d82006d0300400a180c00903030386 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 156613570 1250 156612320 156612329
    0xa091a0a0612110d05130b09070303080c07140106060809190b060402070f0606091b030c0c020103200c0106090b01020d05091318031701120807150b0604060804020307 73
    0x20103201410890000c0c1491001e405903960280c940900d1040d800010040e0f41c00980d082c80c0422030703031400c000350072401c940b0504c06540541c48080414104030002c9403c0c4156074042e181c0d04540c1e22290060600d03948203050070744070b041c1c010300c255580d1402030003180010001552a180242000c1851900300305400c1d01000f40351401c03018120014007904060399000c0e00860300180c942300305040c0039040f00c2020344001c083d0b0349004404030340401240d01084808402c2000e0398042c545201c82982103410361516a004900291030900040d80300340c010540c010301240001d8500060b5034000503407038200a140300c004d41d4450b581403118010500c51094418000d00c000e00917051000e502400c9031003a540c00303a014013000c0150183c1d03031920b5084816440504500104000d50b0307820010700a00320800e19404003c00c080000881c0b0302401505054660458031182ca001501d90354950f418158401e920401d0303490f41c400200b9655181d002d0f0004002075103070b5070134502d031500c100740c01d29205802c03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 156614820 1250 156613570 156613579
    0x110a0501020d1b17040621020a021903030f090f061103010e011203050f0f07060b030601061d1216030309061b0809220c0201050c09010221090a091a 65
    0xa65012a4802c2c011403000d140400c03803500f024031038104507441003911119003101d004001400103020781e000c5181c00410f01220103884c07036094070354550070a03446240340740c01c01a031125184148000f103003114600c3c0244a0b040c0044c41503107a441d507000340c4044110941d14030601e01105030600559000b4072940380d81c00d130703581c17841c0d0344c18448045100030060155103c04c04001039200f0406015400300d4444031802c445940d2166101507000085a21600c011651075013400300c0a070442c00d0000c2c146060310019140d81403041505100700030704000032031505511098a015005000c0800d00c44103422030082144098140d0271420050700a8180d0740c00301d8204603035000c4100791a0b21446c00c00e14070690100c410390340c4000b00c5001401c8121054510000710041100070036005005a00408200c0d4860f00240015a01d0700540501070280001060260700141c8101c5240f05012078000b0341c080001460307900b00f00480c3e021400884060304941c6003140e8841401c1801100004900310804042720f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 156616070 1250 156614820 156614833
    0x4051018020901080a0c02120f0f0301182405060f0f120708100b0703200105190605010c2a0b16020a080c01021216140303010906120b0c0702120a110a050102 69
    0x800035910945042600000c410100f008240600305404031112b190b0044045500c80d610340e420220704240d0701d40d4881f0b1982c604446104050350b030929130701940c40f2529441c03410034130745401e1002a0340101c1c0e07500080c02c420808014400400000340c00460320300f003004002460030000c0502460170191103503002a07031482003008202c403d03208444243c0e0f454076204017040318a11610760b81c00340107000d201c099400d003400c01600940407440784443e01c500300340c00d00a00d96900019102c6080c142009020040401c01c0401d8808010008100007107200400e0841190b80b01001c0d07034190090006401076004c2142c07204298178100b42c002c8040c00301c1320701034600e00d40d504001039903070080011400c3c031405000c540c149002050000c0165856044000d2004682c5070003840c5450b640240110f41d81145000400b00d2250740800455a915a0118070044c2c66111607040c040e031600840b40c100c0e8006400c40c0c426021070400d210300500b0504c640040710021749100e04001c1500940d030401c604550241 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 156617320 1250 156616070 156616091
    0x60304120c02040608060f041209061d0d08070c1802030610030504140304060207090e030307020307031413030b04050d03020903030405151911010510030b040204051018020901080a 79
    0x404010400e50a03003020300404103144085005800c03e680148668016a410085010b842d060028480c502c0b5070303036130038200c0c0b5980c4095407040242d008000c0091042c003030345d000340c20801041c0084504000e20031030080b065540c0d00c802c651720190084490b0807812904100745d02c40900d84040700908014203508502d800c5c000304d0145e01203100c0f51800c044d1100049814060109142c4c0322500c1d08006a035a25a21100065503c07410b520420726446d11300181d100c070341a0044242e070b005d601a6030146103448070035102111940c868984aa10105081091032841000c05820100440c41600001e4151805040a40c03c017045070201708145801041016841e81e004001c031000c0d1342040b5100c4424182c003c2c000b0303a8600413030b80c541c4148442e10303982070130040c0c200c03020000c400701c03081c02801a507848070307019094144181b00040c4018160008100149416000300e9806003c4412844d605d540d190341d49024005203540d0b0003070a1ba400120308500d940e0180c000f035403025940100784a4580b62 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 156618570 1250 156617320 156617333
    0xc26070813020f03060a09030e0d0c060c0503091306080f010507051e040914041e05070b18030a03030e070b030603060109200301082b090603020f1e03060f060304 71
    0x60100751209410714940c0119910001d11010019000e0119107540c40c1c003849480007001d040c10194003080d101a0188200d140003003140075955408001c91549502e00f0318103030780d0303544021400c8425000074010104240c07aa65a40d180c1828201c1012072100e10340740e102401c2c4141c01c1f10401250341044d04000c052a041001ca0b01042c101c030300c510130108540b000384071941c0100c0c1c0221315180e0609543c9903240d1100c0c42024003c030b004065000080780795114403201a01001c00c0240141c00c00b12080011050040192040b14000511584200c040400182c2495014402100801c0d503410070105010700401515001c0c040c400041803841c01d18400080e6544414441c400352640c8440501ca92601c0b080c1102d81140c1d451220980c0305d5031107481260b182d60071810f10b91100083c025000a403240c80030520024540710b512000e6034181024400c60207544902c50a0029107000c2110840702120341025454552219801c036840303040c54401c015500d0300500d84117108620500c144004a500c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 156619820 1250 156618570 156618587
    0xe130b0a020a0f11030f130510021506010c0201090803131e0302061b01060b04030b0a0c030b210f1f0609020a050301120303060312020606030d020f0c21010c2607 71
    0x18513050810303800c10300401c04d074a0b601c201280f028006801151003209040f18203080401c1d20421121181040b0400d50700300da4450780c0002001e400148040404e085500400501c00c1e040e0040c9001d02500b83c03550704a034a154049a110321601400540c10000492454034041025020a08201d0003915640020b0310310b0080c1001e07104c07101c6452f004103070114800d6201c80b00900c0003e50a584803071780d85c180801121001c17105070f031000e400d080c9072482080c03280c8104c4c034040d41700401c03040480e4401603120400e01c080c5441c00310745114010185000600810981c514031800b64020484807428400c1b1078245e513607a50140303c040d401030141d03a121582107401c0d030381918001f0711644442d40712030074210098060303a40003408041a01041c0080290701040c0c00d4441c1c0e00030341c101c07030105400d60004c0343d03601001001c104884d0003440803160286480b902500d01c08a0700c1004011800c4a0105507007114855240e02c4089110013041c0c00704130800321603020302c152020810001524001c14043c14128 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 156621070 1250 156619820 156619847
    0x602060603030a050d0b03010504120305151f030e03030a021e03011d070c17070b1b19030b03030d090b1303050a030c050d0e071802161b0e130b0a020a 66
    0x1002c500318a0901240d0b009480b18070009000b030241c0e02b86410040c00c8100103d425000090500002402c08031912103d441c0d51030016111104207480103819891142d0341c0503c00003010f0f251502c118000da01000958001c03404c6840040c0d032941210741d015400c403024505050341000500040042c003280c1104521740c80b0030088803d82c40c4c1e48040f400c84007640007407001001014140700040410b448000030f03280c264840c10100e031958641d40140c90700e1455405100c05c4011003044103102d618284099560440321909000c5000c0d05404002815a04800c02c007162642d5144104414440780180068010740004035500b00160103031030003010707031261420410a250f11001080344503171145084a00c000c604c81c0c400c000211035a02d07800c0e103402aa206002c0030304900c010080c0088a50f10840d40307014035406040746107041c00d54801c074212100800d003802c0c2c082401e0f40000c034a2121003070303244101e0601415040030100c0e450300229992005e05031859981c814000c580b44e40d5000308010300020b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 156622320 1250 156621070 156621077
    0x2309030d05071b0b040b0c0c100c050d020c031819090c050403080c010608010c0905010210050a0605030f0109023f070807080109020a210f050309090405060702070602060603030a 78
    0x142e80b05070b425103030085201031181290f02d0924081c01801510090103018900c03600400c50383d516071030707504001c3d40101d8106a1161300000ea41d82d04100455000250820890501e5400e01c0340c4c02d2003800c104d8020307a1113110700b50800071381641c14029025400d60507007403c44880c5000302e101011240da458050140d2011143da4110780395005000f08141d400840d0b001d02216500d4140d07541c10f034041e19251007114900d60070420340000407402185410160f44040c4d00401080c80422045070140101900c1004000d5036070402003020340b414845056040390352000400d10384041e1040c0215030000185001000c03100310306c02400a599182242e50041c00312001a000d49084507c041c00c0071402d51018240f031068031400104c40d40d040d000401c01300d0085440b000394a540b0304211324641d80041d95402c248115500718800030369581030301d50ba054001c004032030500c00100c01180410b00151410784050f0321540c100101280c1c10007500018240390b102920f0142040c1c00480e940380039410618007070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 156623570 1250 156622320 156622331
    0x1005041a0606040b03070f020d0908151f061115010f0e070201110c0c0312030c0a050d06080106030b06040f0605060301050d060e07061707050c10020f0712032309030d 73
    0xa640c401043c3c502424101c02e180d5964244194007424030415103103000c001d402141c15241d8464001c8803640d04940d00207024103080710315500300fa00c1400c402084180c00e000100000000d41c521180c3d00000340249032122050301c00702c2c600740381c82e101c98005601d1450340d0a50050004204008105080f40c09071881082c3c6070725802c1050b030140086004190b413003007002c0345403100c8680c005102181e6203025010340d60740340b18103400a000d6200c202d4210040007810010404101d114030020141402c400300d002440940300e490030303800c0d103606a1013514440c1845050183c01d1520348a10030b184512141304111991600b400304940d404144102882041e40000900a004480d0807005c0c803500400d05988290b40c035184098040300c1552924011000008001015580200100e504800d0b40e40010006a80058902c00195006619096210b0003c4c407a28000803960b1400c6052201140c50102e2030070170a0384100129001c0070741e0400c80090a0091000d000801300450758070200450b8080360 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 156624820 1250 156623570 156623581
    0xc0a03060b030c0d0b0105040c0305040b010e1e0c0306040506040911060307051e07120908060408030601031b030603060e03071106030a0605060f03040c2403270309081005041a 77
    0x81c440d2840f0034a0700302145149400400c141107132140d041c0c03030080f501084040c6084104804660003250b00410003030001c4010322121100c0e1014943c0080c005401c00e46101008400341541c100640d80f840444002009120540c90a4055250701810980b02045544010b80b00c090000035020225806401d001010031100c03880349040351410121200e00740d054802a4441046550042c4802c0d140c0010123005280c400b07214104003002c0b90100d500801d403580311b50311555407542c4080d011506056031401000301058111075401103102c0d19440c0080d040f4610b042001c1a22540b0106130055001080204006105400205c4015000f9030311141c680d0346840400004007035641020385c0c40580030a20081c070807009401548224030440c80c0340d1840c1d50300c0070380c0740c0a0655003c03d494000203800c0061045403007580000f072201402001201080e160043c005500c6941140940001c0e400d06418018040b08020b04076550011500030070403442c054507045007204085400b424034500a002246 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 156626070 1250 156624820 156624823
    0x10c121202040e0603011406060d050c0d06080c030f06010b1204050c030304080619060f05010c0c05041b0801080712020d210e03100509030906090a03080304030201020a0207080c0a03060b03 83
    0x550300560000855695888001c545401d00c8112080e605c6076090442080e03c00051006082c080c00010b031a403424081d61090042c040d000c01828001814000e000c5a2060b20060081c1c000402d00701c400f6002980544042c142414860416406c55511000040090043c00c60444207003c07401d42102126803110314141d400c10b455034030b000b030b410304c0003250200e500480031580303c1c082d008a00c00090813184888261083d241a4403a8960781141c040c810002035000b000c03e25000c17442200903082d2191590001400c0380d0744018901d210201a1240b03014041e00881140d016182180040c0020b500e0300e84500300380d10b03025074020b02035481c0786580010000d16048031003480c00c040300381402105000718001e040c0c6100c161401d100c1d10810000148610080c81401e001d00e2100018501c1c03c18860203010003035210000c2e02d42c01003222500000130a50388000355020360b101c0d07800941d445807101c1c0002c0c607100300341c3c21410ba960402d905a0744250348176552107007200c1d84100301040b004101c10010307 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 156627320 1250 156626070 156626087
    0x11190c03050d03020426030901080a0f0e010c021b090408130906060e01170402130b0a05040e031809070801030605181c02070603090b0c03090f030f0a021506010c12 72
    0x6055202c0ca8601100294044e00a041a602c546c8001800b01c80c0c1d421b6404043d0b48061030217940d6801c20072826940c0c3d482580070b5540a0341d00304001c0f80ca140d902e0a60000c4610300301d83c1e4a1240d5450b020440d05560512114159141540c0c016200320100e4002621640026100603c0c0e0040010420032151480700008000d01c680d9100300580740c1e540b41c020b0171030310714580b0040c0000c68052100100b10300200c4d200e03000d00d4025000801c0c1c80155021034005001004101d5803001c400040041c403603079203000b461403030380b4214041c6403500b20040800d40800c082c0040e40d440b40414004003c409640b084189044035041600410309490780c030050024550800c0b9640d4140c004d8080304074000900c018a100b60b0700c03480e42142c0385507650b620201c0464140803030050100f41c003080031420b201282d8000e0754020780e21100b03480440340291a41807440d4000410648050000300742100b440d44c051140c0380f20340244c070326101e829141210000f0320303c0070403070001000c418480c809161050f100d0f0300340 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 156628570 1250 156627320 156627323
    0x2010b090108161d240a0f170606011d040213030807020117010602071404020c01060e090d05041d07030e070609080c031b0909011512060c11190c03 65
    0xd032000d5859814035a150603440d000d212010300f40350030001d01e912130011115001003000d0300044964407402c0345800418010054202100d0740d016401e00140d032542d00b002d004221490309100b00600c0c00303061000340490028100c216402c090100003072a40c0201204c01c00304034248231110400500c034002002401154400b00c6c035400c01c4500481001807010042c00800c2c001d0300c406844c0c84840b0842c1c072540009000c1e020040e00515010400c4903096030709441264001080507052602443d00242101d00580c40703d81c044215405200c5101c405020000e03013a03000f864102c0c030303150804840c040112810145c0040003041200000c4c0020300c03d070301810f40704044100303803020145d0f00d950007800f00343d490180d0043c80c06075002c07a1046280000741203a0300340c0c000c3c100c0c03a81900d41500300080c481d0000c2c545034280d52a1000e241030200304140340d83c041d24806168624011441c14450300310b420b5104078100b84200085030103540240041c0d042c1d041c0c0c283c200b640041701000d103845000d90449600 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 156629820 1250 156628570 156628579
    0x1121502040312110a05120a0309150507110703050d110a020904140706030b09130c0b03090102040303080c0909010302120102071e0302010b030a080403120c02030f0606150913090302010b 82
    0x10702004000c1143c0c0181c0101c3c00540d42d4070489040b50802c203803118450b940c010580e80c094045c40e604254000e000c4c252200b210b0800150108040c5c81c5d425000c43e214100c4042166a05d0801c40519080b109124000c0c078508001c0040b5415070f80c1c0c25a458403060007150a00046c0504855402d50030400e5418042d409000341001d130406261010100521104640503030042c0d1502040f4580320344240f800382e420041166400b0748881c03218140e40c001401c8140d85000007818003141d041000c0e0002c6004251600c00140d40d01d1460070014048000a000b00d1181413080000d90555610740d003076181525011501d030201c078030158070600c1c0240320b040340c0280340c0c0007800c80502d0f00a0000e00030f20076003030098009214034410388040540329187e40400400001c003c0c003043c00030a06001d9100504e5443d0709203a1120310054001924000b61040b12a9286d881001040040e0900c055401007054058081c2414812100001043d00340c4c01d500100540780da54284038107151007500b0035191541c0142 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 156631070 1250 156629820 156629827
    0x902040b041b0816141b06090f010c050c1b1906050c06010603022106041103040f05161a0304050307060501121a07090501030903090509271501121502 66
    0x14061040301049600100104045400081d6225401c00344040e40301380c103985407a02d410f4140004142d5800079819048007070901e01da41c0c07a00c21070401400c0e025180b69001013444003520020a801d407a83c2e40405000c0203810310910800280010b40f0255031150041c02d950759840200c0400c0c14481d0740940715010400303000000418a8000303005208800c075400a4801a0303072901403d5090380b1600f00c0b2064907113809524006001002070100340c01840050012495401c0f1030040c00c9190800d94050716500c00c5a40c00ca81001010410000084e565040c003904141ca0b080c401c00042d8100d400d941c070f40300000000034080000034800c0303c11941c2d103c1d0702004156101d030104450000139540c220381c80d480148400070030844011011740700344590b980e0003c0c030904240044020f00051079088041c00200c0b040441d542c0d44041d02c0300d2040140c040c00703540742c5c0308104019400008107901404503401140310f40f0001500c80400505442c0349804c0124464003624003411034001605400506a1010 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 156632320 1250 156631070 156631091
    0x20414130e0322050406050d0b04050102040f090e010e010c021c140c0a020a0e0402062b050f06040c081b0a0207121203110309060610030b041b09150e01030902040b04 73
    0xc8543c0d8039407181e0004901080ba03e82007400200c400c0360254561140d250803030600003800000c6540d52040c8100300140c241640c5800142817030015030000c400060300c440c0c001c401e540c024814098a81c02c1000240600c0c130a020b80a515448034650500c000440300750000718042c0250042c0c03658509605440c1d82d5041c030070410644078400641e08078400c290b0243c0009402184102e0580501d070000d0006180040001101400c003101f01c42000c0682ca070443c0c001c00019262281c184142540c0d0380482c2c0034078166007000300701c030302c4a00c00317405009600b4240036078075280c940b0600904020280d400d07035568001c2030680c50010143d0000f0950300e8a9a441c504202c1d1040c0c0114280b0010344045c004586070021100d1280800c44515185921040020703c0518005500c1008080b0354200013484003044008a025541303a0840c0c7c005c0d0700c2140c04a0580c20742d000006400400956000048444200600808412250388024100b5444207080c0b401d540c1c56a101502c5a0b4009000b045032813601d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 156633570 1250 156632320 156632347
    0xe0a06030212030a0801080f030a05071415060a06030207080315010e09070903030912080d0f021605070509010501020604031209170408100c030c020a03030f06081204090b0103020414130e03 83
    0x130100400000f41d0300400002c141c000003c012030110345002c0034500b8807002020440d42500406030958801d6800c1f15a0200b07100c0c140408078cd58820912607410601d02a01407100041c0035511983c10144100410030209031074074103480d04001041c43e580f0144810300d00407594a417600d40410f501c01c4110003801201d03508442e01d001107a1003901c2d0004103955901680d100c5c000e400790040c0004900b000010043c40d241c5d4007452010010800040c24040186140f480002502c4030846155016082c240114070380310342d80758010003091000b0840f0b032078203640c0244050590807070786640e41d442d14422020072860f0b117003070703010a44592136039500c82c0e0303035910007581d41e4104c940034048035458120008030080c800c3c012464074081d00c3d0024000840165012070040a0414604101c1e40e5a03210104280d20140030003030108094131505900c440c00c150152044a50791340003103050601c100010410480c400f071140b0703824541194552039165041c1c07040310140008a68108003400009030a1741030440 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 156634820 1250 156633570 156633577
    0x5030d120e010e0f0f011406060a140408070906080d0c0b13020306040f1b081b060d0204030f020118080d05090118090c022a060a05070b0703052e0e0a0603021203 71
    0x50100300e0b04c212205d61030381403ca6810941346124a640000028000d007005402049980701700d18055240c1c3c0c1d403003611a00c01c0e03005904800340307079084407008216108090145401800041025000011035400080d011440b241c40040c61038030500c4c00500381801c42012506002d4014050350114901460080941807041d0800c65002941104030202481508044025140940000c1958006c8a90321217101c110302c0101e20b030720920400c00043c042209002810085104078600c0034018554800945489000d110440400a46d100d04003c90f45000815102021003401c0041e500e0441c0e1004807081c0380022008144228502c600080e07036075030780e401003c01419980c00e656010114007001480460306a40091442e880c0745d902d881d180c40c1074001480d5000043c00d00b54981f400030360b40d581d02000d00325100d01c0070035034813010860341c2841200381c3d06c0c13a129607843e907000b00400c002c07950400603c0c074010241c10740d43e80c07030004500074010392054010715002450810384a91400860303a40f9803 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 156636070 1250 156634820 156634843
    0x50d0510090e1504031b0512041703031005060307120203040507030201030b0316030b150d03021501060e0105030f0c160606030218060d080309120a03050a110405030d120e010e 77
    0x502d4034104400e48400031a4a0202c010400020003440e191500c0445074225442583c07004043c1d8184a600007440800101003c04010080161110b02c0d00f03054500611400d0b111003180e40080040201031850b0b60720f880d050314000c0b00c41c82e4032611180011190034405c0548810300510000902c0203001c1b000030407008681c402d80e810f02110b4814003c0c184c41c0c01c020344042c0144100701c0800d10000c3c80213283c00d40d02c04660f400700783c50681c1c400005008400000400d40141e0000849582481c3c1101d5900707015001904001d00c06504000c0003c0c643d100c020309240301005044c0118003054905c40444466034510900309403500300905140d00103040e544012803003030605198034107481011a40c3c040c8521001004001d800213251985180c0d548000e2264046004004446030b0a0a0001c0900000c1541750350000340e52400188040440b0030411a03548034040502c030405c080ea5000944203403580c01450311105141210040c10054000c550400c5695420806d0003081038200003070701070101 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 156637320 1250 156636070 156636089
    0xb0d03030e0c0103150b0c0c060a090e0112170904060306020c0c0406090612020904080c070f0513050c0f0a031103070e0a0b070812090f0114070f08160f050d0510 71
    0x1c502d407001941100c2c09500015004e045100301044141c950700007812110141b002a00c618003401000070312103500080240f00440d4203220103004081442d60840e000d23010101c5030042d14402a00d03029548078006299226841c4005000720f010749032600180021540b084c0155100d08170005070315201c0070b0230712149004d0707407030004002584174442c01240220f85079078640200444a9800380718240600800c00c0da2515010890180508010000c0c4001040300030400d0310818200820081c03c61103045c500100281013000744003030a8045e404950741d022405600300e5561001801c25800303480443c254180c161800310412400c160041c0403039040050445980a03001e40344c0b040b9502600400c9409001d840c0140b1150001003030f1a02c80c0e6401450041c02c946609030380ca004075007910700d0080861098000c84043c001200e8000c0c0d940c0240803c903042c988294503001610320034206104001504014810843d02c00c1c850040040340c590b40000d0800780103614211100c1941c4418900c03450559 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 156638570 1250 156637320 156637333
    0xe0d02030409151a0c121602010e041b0305130203011118120309010c0c09090f020306130b040f0602040b0d0c0f110c040506060409090f0506010f0509070f030b0d03030e 74
    0x940c00303008203802901d0003009650b00307201e50001c40503a250800e005d1070145204905400c0c40c8140310300c4c00740c21030444200a000325a5801e10005240c4801d450b02e090241c0e080c01000c1c0b00801c00180e04070050050781c5800100d6a480c90800040f00800c0c46e00a9051f51030445080400d10f10000200f01a5040d07065030708024201c6403d0002040d071100005032560414829281039610881064207042e006514040007203884103001000c46041c2ca9044402c07200c590790120440c01c0c00d010107a40040102a40d00241c082c0751112001058003d00c0100302c4201e00c0000000c0104581c1698094100014901d4a8144d0f000d0310a0040c00746140a0f40400c6144103c40b5003144111200e158a5040c02d000d803034a20030240602c0040c140c0501a298004814040441c1d188094418407589030300560005100d00c0711424141d040c2030040c0c00804402c81c3c03802084c04a0348401c841c89410203c1c40c0303468401c80401c18400c40c01010700400c417550004c1c40e0541803091590580180e00b4402008041c0e440 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 156639820 1250 156638570 156638591
    0x912011e050420030a080d0204182003010f090b030a050105130b280203040201020f060916090e0d050a02010605100f020d0e09060f01030905012d06050f04020d0e0d02030409 76
    0x1441e80c0518283d81c1c584e001038400030000b0851400b610b48141103038005402c0a807500b40b4a90440040c00c0d001156a80e20840601c000c0001010148900311900916207103504141040c00b0940081c0114242d03035031076003a250740310b807010090031103802d41140081119040c448a109140404054281d6000301c1c0c41c00400d03001110620700b94035603501d001c65034071404006103824029410040083e810b42c010400b00e040d118000b4440544a0610040078155002e00b000000728041c500340c1040350842d00d003210314944010300040c059080710050410548a03000394804a0141c0304682110341c03c90380d60352100c20800d402c00103807502e0710260f8007038400c280c3c40c03c501210000140340100740c0c40200346c07020901c5818551804d080c2c00906140100b5122402c3d180c00d400d5584114050074001c3c44500c005005001c1d801200840c0003100f40300b0301c203491400c2c0000340d10501c400060f0b44500d50000e8503101d08034903584403450170b1107800d094868008031880060340320b810500ca503000040c2070408402c3e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 156641070 1250 156639820 156639863
    0x3060b0102070608160806030a0210020c040c0302040302032107050a03120c0c02100f090e0c130b0309060609060a080d030504020f220207030215010b0c010b06030c0912011e0504 78
    0x38405c1160150ba9011802c80600c11a041c0d0720142400760180200d411080c0585c41e2054500310f40c03c01034004054465400b801e10045808000303414003014410b00040c401690003103090100c0c12496451005000808030b401c021074422140300404a00c907680c998030030150028441c00c5004c040d02e80400660039410416140035a4402000758000079151061039554010071201c00c85003040d281038030700c00d900c0d40750180e003144055488200a0a002c81c100a0781a09060710001614801400a003103081103013110f580d4640140c81e40d44070382d2000f00000e07600c1c0c40344100d81e80207048070b000729401090780000182c01002e0948041e401042c100c240b016007420039414808405041001c04002074141c00d01e000300039007141800b20304601920142404090006050a0180280c0d41000b40d6481c46040c6481c00c40342d1a042840c010403003842001601d42a0505a44072514103940601403a0844040580113295040b649001e02500d045800740e46d03a01940010300c59881600400700510500f42d525 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 156642320 1250 156641070 156641087
    0x714040f020c030d1e09050109020916021b030111031504050c0a050d0203180a0c06020f150106030902030f0105011d06030c0f1215042001030908250c03060b01020706 73
    0x2810b4a80c42003051600b50180b80d4401c102d03043c0075034400b144903c80c03034200340c0540d00b04440540d07040e91a03c2800c81580f419030280c0d90800e4003c184020a41d42003240a9110312424102e054544841111b400341900c0079002108800c50811080f940c0f860520100e0298244144c0100d01a51614000a4408000303404840ca01c0701d09032a01414010450503420180d4002410a00e020307140c4054841d0302d445c100908a00184641d0489500d107081c010000d2a15021501c40b000950020700c1c0210340341031400190b415102d072450041945009400442e161550028408903203610340700c00003607a2452003000d14202d000545015950303071503403400c01d070383d40c0c060001c829440320013a00e440e1850b242805e2858841c1d69220143e52800c1003552601c50681800c07141600d501c0701d2420300c03c8100c17980b190340050265003401c0070070201c14903803205003260181e030b01101030180700b078007004502500c41e45611241540c4208000461600d03454113802a01e078100a10b4054481c02c3c3d000b14002d4003c403c00c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 156643570 1250 156642320 156642337
    0x20724030e0d1b031103071227210b01080105090c01020f0606010c0f1e02090f1006080901020f130302010f0f05071502270a06020f100f0209030714040f02 68
    0x1618404026028400960343c20341400b2414043e140f1040c0c0040307039040c00581803850140f80301032210b9402483c00340400602803841c0004503c0148002d503400038000103030007910040019041c81c0310b4030072404819a0381091001d049254030307a0000811201c1500118802c2c20303d507081d2641840060b0042e603030703849140d14082003034001d10006606548141c43d4408018060101000c3d40480c0d512240c0301411107100c8030012242d002102000d6082103d07125411000314001d0310f581e4541520741340280741690192000304160200070030080c890035010754860350640a90b1076614a032182c584000f03c2c5248c4400ca0100c0c2100f4000003449001d001c044000c00960380b102d610b8440b89503510080150071403e24900181d00b0300510041c901d5880c4801c0c0c50410080b2403400030004c0c078003008544801940084115444800c3c441c07034404012483c1c00d040c40c041200821400340c102011006405000c029942510402c1c02c0001d0404117880d80801c502002c0c1c07810040d203c0c1c031880d004142d22900c030302c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 156644820 1250 156643570 156643577
    0x20307060f09090c140309010510140303030406111902100c0503090a03180902030c0d05010f060f1805060304050303041101180308030403030605150d14040507050907020724030e0d 79
    0x410403c040f5290803414141c41607140404003c0180145490b280c0c0040d245040300c2c0c0c0d907030350400000182c00c25074100507020180e904036400c010f00001a0b42c9100082c401090309880311054400d0f0140f03c0d0503554154845d90a030608010807075030095440444000c0142d078103091291102081b4014400ca90140a404020307000040383d40d10180c50980550089c103052150501001604c03c94910295000e0480c492080c0e949040d401d40003015543c042c0c0180b180f040e400320301000010f80000817880e81c0d40090901c200d094031000b40e00d40c8040e015502042c1c01060010410040050100c01141318501c07800c80c0503013441c480c100446160394503030101340003251515018004500b41e134016550142c820316001c2802911100490309440c002490031500c03000c04a6583e164001034000c0400c4022101c3c00e080c1c041c909034880d0f641d07c0a152043c240075500d20320100e40902d1091150801400f01c2c2c0081c00d001141881c00502401c0d200c66400c2c0c0001c0c41d1040358a502080824442c56208003942c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 156646070 1250 156644820 156644837
    0x501180215070305130e01050f030d0f23040b12130b0109050405010e0708030a020111070209270d0c11010203130b0901050c0703080306011403040c060c0602070816020307060f 77
    0xd89410441d808210b0981c2480000c0c8801010b0440c2d90406502410f291807140005514280c2407103203d80c05008c86600c65001000070300082d03540417080e00c072509000c0c81c0194107441c0304c4054107144000d8100030780d001030700000c001c181c1000a1001702031a20310403c1c0381c10706903190301301589103080781c0800511401d08840100103035212074001d581c0041c01003000045070082c1e03031029464211079074070100b195000070429400d09034080c841c415094005007010743c0781510036400241210360081c0901841e40054000540c108200084065003450460031030311300c1c80d89490040d2039280d85242c1100d482005441d8100035501c08426074100c24440b108401e2900c1c10301c0402040c41d0440b000072410420b0920041c420140c1c1004468010b40c06820400c6c0d907424043c000405010482c1c90381000418200103100008007103508002c03c40b009850301c1c4200d20301a18051000e4414600040d244000100d020f480482038400b010201c10301c2113040380c5055950302001e60309041c0d050700c04008642c810 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 156647320 1250 156646070 156646099
    0xe0616060905160f030b1603270606060e0906130b1c061d0c0f010224040506010f050109030b040309050d060c0908240c04030605010303050d0c030b0a03110a03050d020a05011802 78
    0x3e4030742c200c600400e05009ca0500900e030380c1103881034030b01d54804141c1390001d0508030a01005e4801e8101030441e504d445000c03078100c500819424035010f0000c5006490001240e12041c800b9031000d801c03d04010214040b00d262002c004181c0900d440040d40e50714500120440c09209001d1420b002482c02000f1f0090800020100000140c0002105055004008514107e07201c40244101c2c840400350000ea007900341420650303d0070070160040c240f544803140b000d0055a8100e0f0805007180c2c3d0091520f4650b0341c071481c0842e5522140e6014581194000711014100901500000050191503a540c50150790b14500d2641d00c00480030007a00071003410300906250a01e01410f1940848807030004c51a0030755903034030102165402d80c41503000030740101e8000c240c030031180103030071000c40986420b02c0056443c80004880b070b2954400100307075889a4031451903603124101354030b0045070018240d605003000d0705c50194991152840841301546400817549089041c0c030035800900350054030104012004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 156648570 1250 156647320 156647341
    0x40509040b09010902100210050901060e040813090c0c050c0f0112020904240807060503040803010b03280e070906030809010503130507060e090703020a0e0616060905160f030b 77
    0x192464560f5500c03a1326060150312407040e91240004298014660801c072030220300308039280a01680140d1341020350803c2140c0803070080380c0c0c000c1e4014041c903a4921925030b19640c04000c5611074200e85080121454015400030707000542a800b4006036881401c1000c200320303031b00903541102c1d40864208000c11000040d207a020344913554002d07000003000705503205081c601c51a030440621283c1810300f001c2c0810341040c418040102006e00300b007819401c0940c0c80040b030340014000c03102c05501c0030001942030740d0b26800040c41c40c03200c41d5071810845c08201406016124002840e400d030711401800040074495481030504598012203458145070728103004450341d034805400150140c10304a9041c001c17500a00900d4001d0545449012121408009000b81588001e000380280341c0f041c00b0a010090300070002540c081d104480d200d13a078048103036840030204800300004c0d040c10314111041040020028548003001d80040d285040b01d9603424140381c540c1c1c140c1c040108040b0b00c580110340030001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 156649820 1250 156648570 156648593
    0xf02121b1510080f120304030e1801140607030905040e0c0a0b090a05060711091b04060e030f120a03150504020a030912020d1b020607060e07150504050904 68
    0x40586902084900200019141007284901401540181c0040c0032551400e0000303000209160400380140d0b048007540e1507120661660740a019020010014040605c02c04584010040c003e20f0385c1c508040014240c1d103580400d016401110342840030f482d1f0385180c40c50998040070781c559109500e1509001c00e20005d090f000c440d9200310b00c100000502195582d110311809071402440d100e46481d140d80030070081682a03407215005600400c840300106803801c10a02c0c001e803042d90310b0300c280d0b11800d11000c0041e00c1011540e030400d80216010031503540c0a1040b09901c60b08608075064082d01c0c40d14140c403455a25001e140046c001c00800c1e9005009401800c580b4058415113088a5a42c0010400382e81c45600340d0000660740d4410303041000b5840100c0c0380300013002d200400b00800360503000303005c080100000149440300d410000c02159108003c07140030aa000e48244021803126820340c1d91000c942c011401c82c01c1c2c280411141d80c41c0701c3c8040d2422103100a04800050700c1396100e580c01c024 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 156651070 1250 156649820 156649837
    0xe09060d08071103010c020f071508180f030a0207030303050f01080303042406030b0109050a0501030b0601050f07060c0807111f0903020c0d0c0501120504080304060b060c0a050c010f0f0212 83
    0x880105048181c4c0d402c3c45640d03500c4006070041c04004910074035150510180c0e0700000c070000c0c07261481c401c51a03840b102581e4069040c0000207410542182080d1030105c3d0400c048141d0321002440140040d804901101103c1c440c0d10180102e4039000741e00c0d06242c609014030b00b1160300620024010800d03505680c80703d28038034060f10307a1550009801c0400e643e021780054034010808401044078040344d104243c0c0c04002c800e420030040d415560307501002c090244c1001d04100021030440a11190340c421941c040303610030010090142102d9000e0001740302100c44401040c20201450710402c004268000e0809946500070a48052038007110001d00b00100d051302107101e41d030100340f0b00b034940a5000b40c2981c0107420007403840385041d000402a0400d80492400c3c141420140800140034405582d005540000c000c10f2083d400d101250031030040d407407000c12030310410007000c1c01d018001c1148603200c8030aa0754005500b901082c00d44410710444d00d501d0040c0c0c0403c6c140524422610060165132 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 156652320 1250 156651070 156651083
    0x1503020a09081005150405060f04050603010b0a03050601090b010c0506040314040b030a1506110309060d0207020907030e06060402090108180313080f0f0c0904110a0b04090c0e09060d0807 82
    0x21074681e16028030f0442007044801c0501e90762000d00400c540001e129201c0000100d90500c00d62410703101142091400c5800780340a56102c10202e441680c0c00c0d0059100700501910a203005076480c180196200000e214149245c0d01c0c040301c2600c25441049907010303441e040401001151030f0340d81c08581032200d14203192038020080c4800303d1a032846100550040102c3d207004602c8070707480594001040c200743c1c8103d00b4042032000705d0800f8030010040e148800e1084034000e8590180c405180040c1c80b80110080d4000350041c2009540c0b0b8266004004902541040b5003040c0d0307440d01840200c5c4655869540030030668400560714101c0342c40300031804981030042c5c9050090b43c000e0303e03459540e250014170564010350010341d4401d208002052500000000814000310103201280040b6000b5001070032a0306840c15542913501c403481c80400804182c1d40c40303030307503580d42c0c503210320041880c226a0360010b007244180010f039152201e10340e8010030004000c0da5040940d641c0e92001c0342d2140b00100c814 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 156653570 1250 156652320 156652337
    0x11a0702040207050a03020705030f2d1e1b09010e090c04050720070621060806070e12060f0121061104030c09060e0a0f020717040504060501030203011503020a 70
    0x5840d10b00150414030700c10b4005040c440c1840c0381c06401c0042c10f800080c040c0d8440d02482119890004184000d40d46c0b40e180100b8401c5e01c0300160440308015a8014402c1c0701d1000072841807961010006c83ca421035505a0300c035064400494880c52040b41c400c40d40c4580d43ca0010301500b103140e8a6039070407500020880d101c003080c043c0071070152042180c080020506a41c2485000d010008400195001c1c2001801c601403c241c4054a51441a10f801030344202c10803000c00c804181d030348084064411001140e10354500007000074540c88022107207500501c55400817000d441c80000b1481e000d14030903940142540e0034040040b05045100800c0003100117000201e6022441d54883c1000414069004d02d650f03500b1420440d805202c6c030342c06070040074034200d4104013104090000981003c1c40c5900454614420361f0440d01a000310075028041040c03002c84541d408546800502c1110002e860501495656030015403c80c08241308007031011341c142d0710904005220380e0082540601d28280320b0031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 156654676 1106 156653570 156653573
    0x61a03010b041509090f06091b08161a04030804030b040317040323040e090d120603020307031104020f030c030919052505100c0204050109060b03011a07 67
    0x24416910105c102c01c20400c03c0c200c143d581e8003c0e0f4280b001e0180c80c1008603003070118a4500d81002080c00b07000844020119180464104821040e2600751906c441c0404802c004507002c2074400081001000143d03500c00a400a54001c1401039a685040e19025100a00e590080c04609459408005c00a0340c8544074482c3e095041591001c80c07046911032048038085ca4218000101c0e0650400c040b03c0400a40d055109a45503070f54440c44d105000614104c80b010301010f9056040101c0900101703815000503145450040d000500d802c001c05203a10058209640d060301c0280d001061040d5070104100a10003060b950070b03004001e43c580d5440c80d56031340c5c40ca00a41c2d80384200b0540c4d140c044840c2c1d43d1000003070001804a510814142c08001c01c80000740004a100742d1411001103180340940c0302c0c450a803807855016525590a100c03040c00c50185554000d45086000c101d54070 = true := by decide +kernel

theorem cover : BRFrame.Cov 156474820 156654676 := by
  have h0 := BRFrame.cov_init 156474820
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 156474820 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 156474820 ≤ n) (h2 : n < 156654676) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
