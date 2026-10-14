-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1930
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:11:31.398785+00:00
-- url     : https://prove2.me/submissions/57c1a722-1a90-4b34-b7ab-2ff3b41dcb9b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 346942446 ≤ n < 347122302 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 346943696 1250 346942446 346942459
    0x60109030201052d0c070305060708040f08300907061106060d0813060e040c1d09071206080a0204051003080d050a1811030f0a1a0703090507081b 64
    0x10000750340c02500311400c242c483c2001c01c040a069a1500a80b039001080c0410040c0b03001521400319480400c5540940b07105000b0b80310191070b0300c3c008483d03200d03060302c02401e855024481c51001520641c01864034800d42e04101180040040c0e5140103012104804036074110420208402c02005000c901c001d01001d0605c10200c0340c0c2e1085455840e48000c003001d0203031410821071810301800f00c00380d071200300d0b00f007090200309525140018001c0c2c0c0f0743d805e554000e500341080800e04601070003a14170b0101c0302000566803846058100b150702c0001a001d0014010070050342c040304160ba000d000040c0038201300514039035080b03105120480c4c000800c040400c0c10402001d01c00520300400f01e40c2c0d481d2614502207070a44403020034200030700500d02c232455005841103041e0104580420842d901910807402d4a074450242c0c00b4039070700c0b070010110080c400904089084500c0700000d80c1942c10181614000444e605031ba80d80e5490007130103810583c907907401502558030071103a005481d901500280d030075 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 346944946 1250 346943696 346943699
    0x13061112071209110f0604033801150f050408010608070e0c041511101d0c1e061806040e0108190816110a09020903010e0102070203060f091204090501050405060109 72
    0x7000100142c13000624451425038030445410340d2403005680145401803200c641c440511051598401d0212412606c42112003224542c03010344107580e507049501d1900d0041c030741c6032400780032038286181a00010a11405001c00710300b8440920560707000d485200c0062060b1420034030082007400c402011010100c000b0441840078044000085d005416142410780034222403950080c01c0c40d000c0c000c0415180c1c5804812425400b01c0003403003407480340c2082a2040c968008090010710865406609000001c1072810030503401c0c0800200300c00440d4440440c00e044070075001901c00e61150b4001c401c091200710040c81000024815043c19000d000840c105020742945c422025000c4e040313480c0f400645003540d000074415001003d60465400038082a412601c0d0030506000350820b0b600c0c036000e98a002d41000391124144200d82440703130010002d00d030580d00c0d00411035070740310000d101c1481c46c09411071408400840e5400340001e801c055001190380d40c104014001102d600030f10890400030141c40 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 346946196 1250 346944946 346944953
    0x103150f05010804030c05150a0c0e060313060e060108061909150905010b030d030218010813110a12060203041406100312050721200613061112071209 66
    0x442004640c1d003030070720803070301e5a40e0b060039141d440742c01d000a0054007030110003400b40d0155001482c40340c90640340c104442810850200d52080c4220795460308400c040002c28004c100b00301d84401040e108000c04110310032034020450900c8005e901c90b0505900110a11a501a81c071740ca942c0c1200d452001000340e0705154440a010785009461041f1140e520102d5605000d803e42005004e420007608a98840000c254018020340c04841e07071440d41c0740700c040c3e039000301e610a40c80b8900030300021a5100007001c0f1500c4000c11440030f0340825500008582002941c01088500004800c0c0181001a00d920f098141154aa600411072101c41e4200d0410003a8600d8905440c070305482d04880008011303000108141c8079885159030150042d14503034111050440608041c0c1800001955818030520320300c1000384558040d5800c405d9030740c00820000b080d080f091800c1c0411103014820116040142020019031944a40709102d2014400e00800200e1904440110071140014000300828101ca4a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 346947446 1250 346946196 346946219
    0x131a0d0b060105030408070b07120509010b060318150103062403080a0804030905030a0b15040b060706050a0f02030114040507050901020a0201081003060608030c0c060403031d0121020405010315 85
    0x8288070b062000110100301400303224802e03200d01076030011010341a030070700030000b80280c1c084200455071142040002101040306028003a05034402408090458031007400a00403082660220b00e064070550a43c003103070b411002406402140200d1001030714413400d02d900b28034a26484141d0710008035101d001c00008164a080300c1410b1628580007031b158071585004c50310a98150700095240c8070701c210981c00c0c040c2c0341040c01e008240e519220080354110500344020380340245981c40e8482003d00c011030101c0c005401c0070394005c0c0044d8002960018500c5132070100c0e0400c3c1c001030b01102e00c6049030385040c1014418a5000368460030254201219603000030369a41c0010802030421141e240490030742d00b001c1e038102002c3d44c0e12500c1440030300c1c1c8070b440c0b0710351f603420041c4800c080344541040f07840641407440403141541d4155940c041c051203810681c90320403c6075102c0e1030400c03141118500e55a981e1100e08010a0428900969070310f00d0f000005080d0380380004406074640840700100580171204 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 346948696 1250 346947446 346947451
    0x302130303050304020a03081c0e0a0314030a0f0507110607032a02030d0207060b0102120901020703030522030c05010e09061c051216021003090c170c131a0d0b 70
    0x51828a503a99205c1c404912460110f41c0300903c0c0d07001c080f030310780d00c14582080d41003561a40b00c0e508200e28400201000d0307694110880140100310a680d4a030403c10994004660000f80740710702190310f10100060700104c0d0800c5030210000303010514401035120382070084580041c020720f814007050150b8088150a1050320a03224841c2911100703442041e4000c3c020707030784d00c01e0030108211344502040c10b142c0040c020205100b801801043d20b502e0310600d0000a5940064042c4d0040c1340b01400d41c2d805403031941c40f14070a1600383c40c0c110326011004080d4480c0310003861003407070b844280c40e10704800503000c030380c002d4022480b038124030701086225107841c02c005150000035140155424080c0c10421305160541d1034010313a645000405600c1456002c20011074140b0917a0715140716546508114215030300c0240040010b82c20b04002c2044007400c6440b039a4200000003030f00c042d100f1742030014001401188075009d02c1c6494040c41a0003a900000d000054402524599610340240e5a1806401c3c0300 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 346949946 1250 346948696 346948703
    0xa2f010e041d0304030c05030c0901080319200d0e060406020a020402030c09180105090c0309060a0b030c03010c030608060109020909042009151e0d11130c12060603021303 75
    0x850507402c0c107040080c80b2040207038000c40250303a9a0b9480303082550340711041f80109806482146182605400e1000d01a0304950346240a141425005008502540008803403031040000c085105102c48003540c04e0b5112400c1c0309402043c0c0d014143c607026044074842c00c801c40c8a000d0034401004240d0b00440e80c100305649c100c90043c1c0e41d644081c0120024000c05c8034464011111702e061003281181d03466814143e03181110b6201d059500c1e5000300000f0702c0103d4090002d40c000d4004203410805035049041d400200070165a03031091030501080c2140c0407840307178100198503400d04000c41c2d4000d0040a024001103241546030018441c003160003d500948000c00a40359507c0d044620081000c8034142c0700c4000300300c8107160a0416481c0181d4412504080c0300e2080781003010080000e50003003c12000014150000b000e40d175849059521440e5900107411231000542d905514030140b0074490301c81141e448400400940312048800c0b6500c3d50081000e142c81002059103480c410b08084d401c8950 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 346951196 1250 346949946 346949951
    0xc050a0c080d0e0d110712080c01090204050c12010f061403070201090f060b0315010510030c050913061a0307050f03040305090909030301170c0906210a2f010e04 71
    0x100340c64080c0c1107100e103401d4908071514091602042c80307004980c1c1d0381e446040e82d0703030700309400c0300ea030346040e103815880c41030901c00c41100040c0400074800e40043d03c0701510200000401e0166a004a0705031b41c0d04940100050400107605100344485100c00c0340075020345d801391300c10b2a040c1b501c043d01740000348968034440c0d02d020000540040c401d401c041000c1d076124074401090b50f0300e454900c01030490010342502c24003070301d180d403c03101c642c52071042e04840008150740c88409100c2e100798014104035041c80e040010401001c04180c484401242400a00950020380350780b8050120200d285e5a20709607406041c1001480f80203580101581c0f0b088000043c03865582d03d0b02d18090310103106004150380c00521030302c1004880c40000c07014604803051000c8a91904a455121907111441074541980c40018840460713282d08005284074004541c0c10201541210103400441ca4050b140c00c1c111000c05081e08454255403051030b65001402540c149103c0442107100042c2901c1d8010305098015039 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 346952446 1250 346951196 346951217
    0x80d0302250302011505012f03070b0906010e070224130221010b0301020c1b0105090603090102042301020c0d1b0609030507270b060403060e1f0c050a 66
    0x103881c0ca10862850300004000d092581551a000c0e010704a034481c6000e454440d800c0014031035025001c0450300035100805846524100035441da801418503015103100d01c8180003000c0090303034010442d07014200d440000d1007a589000d042240b6002c4c004d00c001c0071508071802d5260040c0d8001d6045081d48601100301249550380032110504202c1041c0203540721040d00180140c507016100c5411075101640000d1010b044488181406e0344102d401100303590780520b052000508603501207401c00e050515003d46482c03400c41c0080c02603002560b0880c3d080c1d6002600308003070603800c4042030304c011b1364500000d440002e480010b92511480d00d0b6903400703007030031740c00c0d0320200410960103c00e244902c985440d540c81e10f80c04010403038140f44c0400c8440f03201d11040030414800d20401c18105040c3c1114142000010b2441000030340030031a40981c2042d814023012000035403d0017071460407642a001000040300e050003800020403c14031210140b0324240500b62095031110443d1402c0445040202c102c1c5e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 346953696 1250 346952446 346952467
    0x510050108210c0a0807150c0e010c0803100504060303050a0f030b090a02160204020c0c0a05030a080306061318020a081b04120804031712010609060507140c0d060506030115080d0302 80
    0x15540801001c519001801008008200807c07400c903042c10202080b41d1284510140e550021703004000d4082074103140602e00003200c210040da8042d90341c41038076081c3c40d9108007007002e8131203940007100850400301d60002541d0b403240a0082c441541c1c901804007602107000311348a1480a011240550340020710741d6443c0c4010a42c00c05c0c65035001e13004551b01c516002c81c06849400f0000c003a0310400104100003402d10700050341050064101d500e141c0746864810812449030b0100000c0407080c0e401c00c600250405502d030b8076a959183d40700d8096520f005800b0000d00080c00104160000140245041178004441082e101900c09011030000c5a0800b41440640e0303004a0b440149400d40c6060100490030011000d4250b03406156035410300c2c0c0c6d072105c0007039603c51482d00521001450030300200c00030500d43d65480c1c4845102400340d0b401408c090021803040b064007042502d0040d1a2420f010705030409103d14000030a04c05d0807000c009003080729041d19100c4003042141019004524001c04 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 346954946 1250 346953696 346953703
    0x60e0f03010b1201060510020a210c05150f06040c02060a02030c120c0c0c0d0f110406150804050f07050d1511030a150906080c010f0302160510050108210c 68
    0x324100600d201d903d15000b0101a02a10305405284d016801d04000241800c0c0001031445220340e00070007080c126503104c01c00d90703c60040c03007400b841004038022101011402c113114011940c01070194043c040e00d890851040c2d049000741150307010703c0c9030442d1450b11aa0201d40f00e600182d208a000d031b501c7e1544881140b140c0909e0540524486000003444240c44110700213100c8554204103a406030440003003040988050030704098100120022024006100182404801c600003400010741544802500700e11004d00c5500c000400c80e042d05000c14050104003140c0c803450403030024003041d420034021032100311900100401c240d01000f0164013100341d58001210790845024425160300e41011000040c12581108128100d544080443d21449900880c4182c070b880300c1c002d04d1074540040044403c020301d015010100341d401d200c103001c2d10f0f018956040cad17098042c0004000400301045200201c40c8181d0111040754022689101c400f0303228648400b82131103c1180e59156540d44d56900c0c02d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 346956196 1250 346954946 346954961
    0x90b1209100e0304030203100203010f090905030f0a112b030e010e03130303090806280608120d11130302010f020f0732032802060d09051204060e0f0301 67
    0x100700e00340811240e40d0400000035004481c0224111040c2c03540d110044d004920080c06403881644010700d090004a02ca60400da00702031203081100e1500000c2c1c1c0d5070b001e4640160600d10002000a8003c5009100401280320b000e2501c000d403440302c00034807014450080101c3c40c4031041c503403102e0318070303074140000c0d13000c03a00b100013035003d40703580e411003918101050074580404c901241344200c012840503000110f462055288090b04203800179444400c0b1140030f0710f402c40d16100c540b075690210345c0000c1444030102d42d0180c3c6030030544030000c5002d85410750300100d0b005140d080050003640c2d200c1e01d0342d01c1004116602801c0500002c0f440050403800c003c02c078000a1760707a00c2091400101d210000100354440b0148017400714016094120b150340880c080c200840e0b040d44050741c1e031006100c103200400e00340c0d0340038181c1c1c6009003000e07408035401c0d03009464500303840c3d83c0d918000000c2c40b00c10b212440c0030100d0f07070300384600d0141009000380940200341c1c9085e00030702c01e8040014080d28258000d04 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 346957446 1250 346956196 346956223
    0x140714070209010303050406090906120803060d170307140336011505132d0207050105090309030d0f080703050403031d0106050f0307180b240a0f090b1209 68
    0xc2503131a41800ba000784d010380300e500005208401d0000b404c0b8464402c0c02c040e1261550049603000329501c1c0d2200c0c1d900040d107ca5802400c140c181d50004803581c0c4d040d40003042d03030100c0d00c1e1645420740c0e01821402e20300d58503140441040041005c603400c0e00c691600203a80ea2003090f59802111044641c0224014007840310540c0392540b06000300513813500d00c4044a0701101c10034800c40d080a501d005803456450300940300e0260b11024154507058002e040c07a4900488401400e00e00c0c40c1e1209425108241d82c0041ba541001404241600742481310820540c018100266000c81c0c1280c02061814000d201104042d07a90001c1001c240c441d8202030340320a4240b1485092149241e0240e00800d000e11405100d800d584400e500d540c2800700b450300488c0e02c85400249860520219075002d403c54403c610784c0800c002e0321a10b48140012003003400722146020743d54032002420400b51003292003032202400c3c40100d04041000709002002c070f4214141d0900c000b94191074409203d41740611207403209 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 346958696 1250 346957446 346957459
    0x4050310050a02461e030f06090204030b01050a080a0f021c030f1205100302040b041103180c0105040e15181608060405101710060321031407140702 65
    0xc102d0311042d544041c203030607007480d50703800d80d4140d0b081d13443c1e011410022040c021454040380c5807540810b030b082c0d04401d0708980c1004249081c1c00300c0c5080c101e540d2a003104041c0ea50209041c41841625a04079002d0032040e50181c089a003480100d5540f0854018010540420142c42c03c7c2191900084a02c443c0429040030002c441c0300e00c1d014000c10340c04000d01c1e00044400f12140c0318003c1e00d010f0180110b40d0f00c00b181c20201c3c259000d01016108004426420a4603a1401741100980000552160001034004444030005050fa0f03428055000b854904200c8140014414810700d0000c1d41d8010101444030124040c1280101d542030388200030076030080101800700404824401c00190141d80c5590ba10085560b40104100403201b080c0c90503034803003d20100a100c02e0991404c042070b40d481d0701c4101c5040e0400c030080d1f14103031110f98200312851380d410703a0204028000e15800030904a201e0070700340561001c0b2030311a0314a02000b09000c040101d6044200d1001041c0c03021101c040303401a03c1e4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 346959946 1250 346958696 346958737
    0xf0f0c0b0705010f05060f120a0812060a08030301050a181401080d0201060f0f030f052802010305010510080c0f0f030f01030c080a03140a03020c0109050c030c0604050310050a02 78
    0xc16aa40140800b60384a50900001001d02c41440c400c0f07900c5104018141c0344248014000c3c8400010503403100d43e0540300e110089800b1a611001402200380380305016012440c14205108510001e503020207500c0c0c1c410702c01404203541d0b00c50000266030459000d8040703030491500c0701c8094110621304c4400448883c0000c40e03071000c0803521f101554455002809110b58581080009030100e01c10100d6002100c48140001283c000240d00480c0c0514110f40c05501c0f0070a5121942807803c1e0292a900d42c1708040c0011540c05008050041804030703104602c103040340d000545032803401000b24240000000324109464001001c0c1d403403041400901d191285000d690a02403400280000e076400d45000c0340005041c54009035050103c0d40c95690011103542000c01c6801c5604000010410325070244400342034500244102d1102c24080c6006091501403242414200b4607540702d424041c000400081c016030301d0003e5a0403000062000006480da22408450002d0203050348402e20400791929 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 346961196 1250 346959946 346959959
    0x16080d020315040b0609010c14070e01060207091103150d03090b040e04020a08030a0c0807030e06280930022e020a020907081008030d1d0304050603040f0f0c 69
    0x101500d10301003d03541000001c1e0700340100001800350710a900d0010b0360707400d484400244264541c00108901030101c607403ca496030410070240304260007441c0180e1281c80100281c910f2030141004ea02c0b04048454510b0504e000c0208113817100c42d080358082d07500c00c0c0d042c00400d4410f9072100c0003400116040d075144d07610f441c1500b900f80303019a01a4842e034040080464500d42c00320865410030744c2ea481e4040d100010303980e2520560440e1500b90f0604c01040f5034503149803240402000303a80588120310f0070840880c0b1095034562030014440040250210050000307401030304812283c2c581815074030000a2411401c0c13048003015460080d0800034506d00c1c00d00008004411004d072480010111041c24400c040c02c90740d440320010060740c031401020104086134040d500c0305030000d1015156a0b00030343c903211007900e15030054030400d0400d9603403511384820500d000c030b40040024401c0080e51a0034980700002d40390340809000075000d400d08904180800c03115002030b140301356210316100703070440e035442 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 346962446 1250 346961196 346961221
    0x120609020a1d0901030312150608090f06011a0d061e0f0911030a0b01021504050601050f01110304270f0b040f0e0601090f021c0b0109080601080316080d0203 69
    0x5001e4000c6080380701c0c40d400030812442c6104180c81e0180c4480220781c03071601e003102d640701c80804030019640d0381d004007003820710008469805840d290301d1700d41660600d004000d1078000c00960700c510725040f840041c030a00c49072407805240b201d80950416159511322408034000c04003036000c00040010314417441400f8001e003400e04c1c103c803402000c90071541e039102080420364000b2012800b440c00704200086480116510a90015406104907480040e201035140180b6205950503a29a4400e100403c0141342c124107154841c0800e10b040d024052001980ca03540e0f0003503000e9035004040703015071a2002082070048100c201c6200f2018441d00340840c03a020003c10b1026846802681003400c1002034800c58001c12911ba00c14900800241e0700c1c0500c00d000070003001511040756a003c1024a0350f42c030701c080120541740210000000c88503058000988503003aa07511801d241d410140041090160200640d101c0c0e1820040301c05801c00c007441c00280d00c0c428280104200d51011062212401014 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 346963696 1250 346962446 346962457
    0xb06010305010807080a12030b0910230f042d0f0515030d1107120c180e0a0b04030c022e030b0307090b0d0f0b090c01030b100e0112060902 61
    0x2a2010041a601c032800140c50300040d004101003a030050395020300240e251110170348005140c8c41c0015140140f1400110000c00948080750001c060b550180000100f00e9000d035610312001c044140440c0800e00070030604a0300e6401d2a101d60f598085075003108c0e03014528a130f4080401440700d620110310b81c60a400510900a11045031480e0200160704011030760303800c2d2003001d0020010200f07921b64001c110f41e8641d620000810b28090302c9000503400c0c0c1610340e140c2c181c500c2075140104403414484452690a00c498648a88504000c2d04000042c1d0124010f00c00319040079080c00075503103900301564028030345c0d0750080d004031180203000b101120901081d010410200009070f04c0b40c110004c100c1c1650744c0364042c035070b064102220420210b00640e0080c02c820402524400000d01a51643c1c034190649110642d161400c0600304402610140305078196404242801c1080c4603921001c180100500c00c0140203110514035085041d81c000c0a03484241c1c0801401800050f44642000c400f94018 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 346964946 1250 346963696 346963699
    0x1180f030e1806040504060f0608210915030405010618020307080709030206040b16020d08071e0f020904020f03010f0c0f030501030b06041e02040b09090610081506090301090b06 78
    0x440300c42040c140b80440a511442050064100441d10707510104001010003910444035159160400d544003a041e01440300180791040292810703104503049001d60407226051100810801c02c62460280e0b0342c4000c00c460200848402034030303035640c0e1a081d40105856003207a20044c5510441c0c100da14419001544074203081e98402041d511129016100d421407400000c0d40004148018046100488082e00f0309900078504102d0000c1c0380d4000c201d51808041c4165000c400018880d03003030001c030110824100d0760003010b54214500c10b49803c1188002500b00078815401080800d0956880200504848a0040c0200b20f2112170704244402170809801000c08501111004000103009210703050480303801c501440c007655624400c000c000c00000c01142c000820a10004550070100c0c8041c0015005004405a96a50000401048610042006205100802000c0a4541c2c40840740d500050307002103800016429500281d11402400c5840350158a444000018000b0310005113008030340 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 346966196 1250 346964946 346964957
    0x1403030c0a1b05100f080a0b09180601062a0f060213030501050105061c180804030308071b031d010e030a0f12030209030a0b0415050106230a09090e01180f03 69
    0x241c031400e002c8811400c0044a02003502c02c040c540704180508a2191f100748140c400040c0001007100042000d48140c80d09244190078000038001c3c14810007032030740034000c103080c1000076881000e1064200c0c2410003100302984104000c6504220000050181d640e03400300c411341d280c00c40b10000c60304071681480182c3d42ca41c2001c0001074581400380c00c4070a031645000c0d00b10300120441d43c241025010038400881150804526900482c1c00c500203403011b94800c1d503601c1440c0c00c254a0040c01d1640d5040154140c0750084c0802d00040c6d00f0040c090803403801803405a14001895006840c65842500069058080c4048400810042100c6640c4c410705c24194040c41d106140011022400358a0402d0307059407000d41c2450204140c45410341e802403140c2c88104001002d56014410b45100b03902400c08145c400041d0039506c070116172040704023007070624030508102c4500401015001248a641d41c80f980d202c41c03d0111110a4120b40c480300034010102c0c5101c9200c0c608400040e0715450161300054 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 346967446 1250 346966196 346966199
    0x4060203070314030613180503190f1715031c0203070b0109050c1204060b1801080c030604050d030f110315120f0a08030601020307020306180708161403030c0a1b 71
    0x9810f01903d00030503010740442ca000c1554414503006001e000c91010f612501c00610b000000e83c100010419012018620304603143c1c141c1c0040d0401c0391202c42071090019001100019903c45101c4503402030b400819110b20402c0140400e091901040020111100791020661082d40000040030028800c80200c811a0b0342d40405104407101a58011039001d01001080c245405100506802c00e008100020b00c1c5007100300080c4400b07050222114008070940f004109414091090006000054000d4444c2d49020740d103050702d9440f02c009040030300d96a0400c00c2c4416a05034046071490040c1c074007895503424000e040262000c80d1001c40e9100d160480140440300c0d00115010800031206002014186040e0744e0302e90003600000d00d00742c114401401082d0140c0e80821085000c1c4800c0b03500130000841038540076090807107070b80106410764003101c00341c0e90b8404011381c4101258907602d96079400c0309030000020309501c01ca006008861059441c50001d0000106170441c8001007000070707000c0c45 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 346968696 1250 346967446 346967477
    0x1060212070f0212030f03010f030b07030c0207060f050405030a0605101e0603020f0c150601020d0201020c0c0925020d09060f050304020409240b0a09050c0406050d060506040602030703 81
    0x610604034010003580c10b0302804001428140a40c120102c0c50078240c900307056911200540c680c00981c803480220403511410800d1003504070807944c00044038581403104030015040a0b41d0342410f8411042080034a00048155502c80c4c41610040c04004068810040041c00d2907070141000381c83c501881403840c0e00000e5011100401818805001004241807501d4480150b0003034105050240b9901c20030001d40f10f001e10140b05050780c0b9072070b8a1100d0041d0800400083c030b4906122221825a84100902ca01090340001d014042072400c8800c00c00c01e6031a4046100c3c4107a040320740340480206074421030079041e00440d50480110030350780d96030549541c07004104c1e01820b00b03035452801304004002040250070039400960210b80a0120b9007855100318074507a020700306c030790304a060a964580301c0c0c0e026480d18104441c001c0c01d846205000d507040102c1e4140301803046115102c180034000031020006011134103d4001050005c19540d165959014040d4a983c03248004a000400f82881400503 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 346969946 1250 346968696 346968733
    0x18060f050c0304020d03030b1c0b0f060901050d0204050402122b0810140d0c1203030b0906011e0915050a030e0f0d05071401050103061b020a020102030d0b190b03010602 74
    0x260f50028545d16482c0c0d13903a00d05070000e00310020300c2038100700801d0050090a056400c40020a40310324548509441c005c682114400e002902881c800c0c4050001040305030b996609484000350110340c0040d86494610018a0341f62800961518038003801c0081d4410480d922041c1c0c4512444c80c101b5061108210400c035998401120f004102520002c030034815070ba485075105901c02d1014001600c61000303619007203040d01e035960190014401904060b8101541805601c1103500b00783e031552940c2c03c14000107420040c1c003121410090140104c0341480520800300d01c8010480820080791aa00d28640100640e03c900710300c102280c1840c040c180a1800000c40004102c14003019101014000700c0131a41079200c03010a8401003205e80c55440e101c50280710303160085125600c00107406590880c600e0141007504107910540d00065200300c0581d80110440c0c2e4100b581c9800001d07619407400010b40e040c0380f10446210041406103002c51010400f4000318103913940c0f6002c959400b4070101d10b1194 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 346971196 1250 346969946 346969951
    0x151903020a171c05030a2c030408010609021611150c060105040516020d1101060b1303060b0306011508061203070501050a15120219210339050118060f050c03 69
    0x100d0410004261b1445c5a00c0188154074942d0304658400348088180420007014610070313070540002070104100c3d10309108030001408210419401c1504036030b90f0b40c509292280c070290101840340301c1c1000a07601c0c1046580d22480e40b102c415243c3d41e41990050742c610302401030501070382c5000c010a581e42c5012802401346001a40240345908c04c5d02c1d42102d4200361070f400b01b100d640d00c8080114102c4c00d58009032100030000c2008030040b510b14201a02541c1c124406076020760071940c0140a4140646807041c4c1c514150b042c036203115103c1401180c3301050102090b00b441c00045156410440c0c19003101e030050007581402e00c6500c03c0e540f0036002013040c0e445415440c0140c0000300c070060400d0010b050000c80201130380e9080ca42d03911001600d40725800703034454020f03544601c441d00f01500403080c403001214410221404c644600100803145582034400c04070004c0c0e80800b101013182c25000004402090b11030b403403140e007071440c6c29009080b11620105825003010002a0425003c1059a1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 346972446 1250 346971196 346971253
    0x1020403030f050f180f0a03141002070803010b1309181407050604030f0f0605070908010c09182f09130216020904050705030303010e04050606030105151903020a17 72
    0xa2411741610b4101ca1001c28000c29240c201442d440c078440726658107a5203400031802400d071309140000c1041024101101000344002c075900c14002c8038080384019054a05460780303107495640d910810100340101c24183d9100340a03450405590150004908030a01c010f03a01c03890401c8006820148590f844040314092290850700500082002c2440c80313003080c451074041d21401d05000d040d0f40352082501c41c102c40f403c0100d010031100304058402441480790305402c81c502081d40034188064081c501d06881040c0c101d80781c464802103a50714040840c1d0a240402840800000e800580c2c0b1203180d4106501d507602c0341c204101400c0e10400c040c021691010f2410303140f0080d04040d60f00700484003d0280c0251401c1c41011001302d40c940342040254003922805030482554a030505d040b514223900100001d000b82d041400780030320b50030309048860309018200c41803002035503005030304030346191a60700180d4056804100091089520124034105c80110b40a8400e11114003011900c6c001c102000038 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 346973696 1250 346972446 346972477
    0xf0e09010e120d0b10030c0f0f08010501121401091d0604020d030302030903040e01031a13020a060f1205040609050106080307030c0f0305091e190b1215030f01020403030f05 76
    0x14500700e50038006240800c10060009040340940c1c02084517080c2d243d2064020994030300102400540015854560128900d4119110b80380340c03030000c03d04030041c0b0519043c80300342c0960310003008245d082010340c40c6d91100c40102640c1d517064008080e100c030201800750605c0c00f0b0081c805032640030800d10f10507070300a885a40000c150795800c070025440140703100c62500040c800441d0208110042900075400303054040c461a503941c029540036580503203c007107080e02c0d8404600042e103554160300c00301e80450606c81e482c611401c105840c001004941050081c0c03800d0100b004105196100c2081540500300801c1019215064550350b403144d41c10190200314060003280010300403801d1700c143e451003490060b042a801c800030449800f0401c01014000d0305502c1d20f60000e046c00540c103e48504440c0117079a106203022045c81c45440707824492100c0b00c10b098002054142265503800c1000f0028085640d20f05200070881c4c000e4209000850000b08680010024507110318140c80500b0441240e0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 346974946 1250 346973696 346973713
    0x40201080109061d06060405090703060315020304021f1b0b01080607030b0d06090201050904290105030c0a1209050316050c0105030105060409180b090a0b01300507030605010f0e09010e 81
    0x44c0c3c0301d14100030401a4081c42c20040455591a4011981d01600c0b039a04c0c040380141c154580603403104001105101d82d1403043c030803c00035a40e03110811184c240b81e2481c44e501c00080242c11a40c60144100750329113083d4050020081140d11140035040b01c804a0035140c9507143c600c4101c0a86c0ca2003030125500c240d0207000c040c003003910740e400b801246105040080c40e00e5001d40110781030b5110500880d20950a1004550400c1552840380d003040800746401480c520b840e650240c40ea000300e6046004015180818150f2601e442d800402e0341130f04107040745e4403a0304140c480c400304040360200700c943e4040e451411b00254003510542e8180c1d1801804103082a0500002c8002000c50840d0190b46140e040416000326523107109040c090031840010340814600e504040c2014034040e40480d0852103000751250b0f010341c1c901c0c4420300c1c014580811242842d418140315183c16519000680040d02d040300000e44c80415a52150031142a0b8071000081d98502c001c0c07078221101920b240206400c42c114 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 346976196 1250 346974946 346974989
    0x20d020307170f0a0308060907110610031103010b0901181808070c060c030807082a130e040f140a080c070f0509090a0809010c0602120601030617032704050a0504020108010906 77
    0xc0d0960109c41860f0400554051000040c0f07024019101e104500c03004100174018007250740c495a141d000c00350020300201018402162400905226860208401440070b48102829410620b900c168403030a2415000b40b604008a042d4448a030403580c0c1070101400041060250704c80c0c0da035040e0580c49003000b681e42e8400a0342c0b81c49000b0030001c3c051401c041c2001484441000c100b100f94800d030071990321074140480491750710343c1c00d0300110b003c41c80003001c0100103204036030002c00b02940002e0b0f0290008580c4640c9141000c46000205054000b0505071104400020a03600712004500820025135590040c000540000e03141c02c051500503203050408500898000d20000c9018905403400071859100d020480e00000001901d0113904400e1081d07540c0d25005180250051101c030814010607030700069644c2c8600140c8009000300c03055001d02c0c50b145540c200c000c0307150181c403c0c410740c5842c02c001d500402c4100c03022400716030f02400200d0110141d05c0b5540548503806401e8404080e40e18 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 346977446 1250 346976196 346976209
    0xe010305061311100e0112060e0a020a0203040f0905100b0f0a03150f090f0b09070f0f1206091d0d021e0c0d05030a030608030a0813020d020307170f0a030806 69
    0x40080d2516001a000300c1c0c495184c00c8048054002c25940350380451260030001001010018000340e841400c1c041d090101106c40c0d510650411005200145e03584800c450580c01c41c0280e0b4402600700000038070000300082140c00180c890031046003081007154958400c1480c0d409210624040640144400f0010a000342c0c40303008604a407400010180d0740d00d40040400400640042c910542c56448541c4021500c1c021001035400484801032245001c10004101c1c44101d550340d010010030402c004983e5005103008400bc0500030404e01c441d5440d000904080d11141413103007031580603170040d184101004544a0081a02e6501130072151882ea054480c51980140812006008010301100a56900404411000d200340f02858803980c1c0e140016003214405e034414500fa4000b040560000c0d07a1050040d0740c8002c403500d55031303110040c0e4008030300e9060b42180002c0d01845640c1010610744280d9680000c246000003c0b2081c22000400041c1c40300d002550040c041485100898114504034 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 346978696 1250 346977446 346977481
    0x9080a05090d051b0f0301050702210d05070c411509060105150306060f03190e06150414060103020702151908090307051c0e03030c070f0e01030506 65
    0x8180e88000300e06612101d0074005203600d030280000150740620700c00d080040b00300800e42c42c204c0c000c005509d001600a92108480e940380d20008601d00c040128840103001a01c00c440500070341000b00d07181045006d40300440015043e661690b80c071840c0f4203150640c02020109011031901c120008582e100686088644003801c1c1841c1e00440c25081c040743d2240911602c80c0f0891002001c40307500d07000522264444c820410022000d080041204e00e031114000c54800358100c0c07070f0707043c1d5982d52441c000000b000c80c0200543e40c14100250700c44003c0b000a9602e018003024090603500500038020002180e9444141807500c02c0c4040020304107600030b0b0701405800b40060710f0014400000072094080d0760015400d10f24214141c403641000e00e512030074456200c1030b01401540340031015203402d230356002c4011800402900102d01c10400c2807003454007410510029049a48075110001c44d00d85a03c041c0c0512a652103280313900064100c1e140349032504a0341c210010780f400382c490302544103512071324 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 346979946 1250 346978696 346978699
    0x103021608070c0f0b0708161410050103030e0303040f092309030a02010b120604110102033907050d0f020103020f0315040510081b030a0503030712060909080a0509 72
    0x2034451408500680700400750548142403410480d8180700c1811424070341c80d040102680b909010500000c1d82a02c00c5034440031072254149100882843d0803a6000c01d035207142c03c0a40100e8148041c1c180103500002d068901c00c0c4c803940032128800003456964000c0f4402d518562000103005c0046c014a98804903010b00006c140d0124100c1c2c1c1d00740c0c510100310a58862169074400103540d2131450b030a100e40a9440340c00c41d4041411840c03d1031696680c58060400703816103a4072a031001040e0b008100302c45255040d05917484182c4010368104800803034114642c40702002d81d500d0360400000200e00342c070545000500a00c01d0202c9034540c20300c000b0324641c0890503d9800c0205201c1446998080c0d03102e00d107420b007002180007214050005580011b07200403001800441f040c08902408501d01441c200c501c07209140c900c0342c45c800a4584254010060038901002003030003422a4486006205c01000580c1805030a641d002d503103007290031499003e40508000e010b140e1242d440390700182000e020 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 346981196 1250 346979946 346979977
    0xc100203070609080d1509050604050c031504060801051e09120f0a0507080d0507020d03051524040e0106080c2818060509040b0f090106050c0f0d1701140f010302 71
    0x8448401c1044a103181046c01c0111801102000a5503c0b8022941c1c040410f0340c061046040c402c0611240c0c0c0030181801803180090704900101381c4441d4000e10050100300000c3c4400e05041002011605c10440040b845174890000102103c3c8000b881140b00001c400c0c0d01840d2000a0140003850f80001c04100200401081182d0108101c1005444d022200c04800202810b041d50301074949440021280c041c1401c081c10041502141c00d404100d045054400000d0400303401040c011488010643c01d1580ba004100400d064480d640080c0c1a2880c07a22086810386410051503a20301a400e409024106100d02030740c1302c105c0d850f010903115107950800150303902e03020070012001c0ea4190020400504081800901c6103481d004025130414240c030625540710002010500b01c1e14140a1001404000241c1296080e400c0040c0941c0b800c0c03100a840b000c1f040e03110024104c071540301c0147d110034200b000206641703042e5100d031a10348a000300009110080400154082d4008440041e06c144 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 346982446 1250 346981196 346981207
    0x10806120a03050a1d01021506010c020402040806161425020301020307020f010b0d0507051507080c0c040c030204061704020103021e1c0501030f151e0e0c10020307060908 75
    0x19010000803020342d109883e160b4862066410051070440d441c103802655000b08078601001da46c02152906048450380f6244650340d42700030060700e041c180c1140c001d40051000400080b900310204419000308110702003080c542d480340000f01c6060700c1c81c14040d002400100001c82035044000700b50750520368010800a0166000d400080c00c98008480607c096042b9001600b000042032085440300b10303084490761042001911880e030b0f988054000d160103810780090306118100788009591409521060300d9130344881490807240c491842c40340c03881c0035034204140d0400300d9001e4000c0d1429100300741c0c0c52601120392428010511680a0001d0f414581c0c00c000c0484d0000800b6806600c52071884c1160341d855015a0100c2c2e03500103021159116146005d0040c0002501c0000700707803200790080c040039031258a80008900810304001c002c0589507000c2e69428040c405c03600025800c404140585003480e82041c28008039882e002101801a00200014000240310741e00900c5668042c944007400e01 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 346983696 1250 346982446 346982479
    0x8070608190b040911090108030a0f0503092107030f2a1a0106020703051606020c01080406021204030905120d051e0403050d02060126031c090b07230304020d02010806 73
    0x12640030809035a0710b20703100300c900e40700e040c46c8074010700502045000b0b515000701c0c02001006145803003011010401c002000c00c9000000f0016128035195860985001d0720b0031600342005548841411400f02e07a036021220a0b00b8010f204c098031580f00300e444580c41200180000c41e9601808408450001005041c00b04003090724034030b10702802c200d4000300071650071800d01030710780f091208040d142c1d8100b0380400c1c000c0701c0c0c0c00300d06890b00f84800e007022059526940386c000040d004941d00c0d09003c015040030002815407003031620f01191003e452400e00e480c40048020f4a54400c550020042442084120f95041105845c10a01110403003020b04290b207aa40c1d95007441d076824482801648081d005001c0a034103100b6001c40d0150009003c080c46410202c000e880b406003a07860702c040d901c2c40e0906c021140030394010450082c0d212414160a00e00031801030000000081861518101040c000116584081c100da01880e0014a181d1444120754011142040002c103d6500300024280c010f065 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 346984946 1250 346983696 346983701
    0x60903120501151202090609010e060f1206011101020c0a032102071119060f0c0c031208090c1918150b0a02060f0402060901032d09050708070608190b04 67
    0xa0110701100c0480c401c1101001130040d212800c10700742e40e520420580d0000c1d5a500225140d043e801e0810101d03070f0400c0c0001603014040c42d0824400c29a000411f2281c40d0207911000c0d210345004d0325401c0350b059040440d14203e00448140301d6030b962192140a001c03a02562a52840ba000400080702c1b200d409035400040e81c02c507000807502e0095aa4454100c5c2c0b60110a8a40d51114030030794201d4240303003c0ac001d01400c280f104690a01041b0641c0c01d0034021002a660061500210300c8090a4032903003000705460310407100c48015009070700100083c2d141071480303840100d4107007485000b138a00345607040b6141c01e00e0401100c20b441d580d5008000c203880141e21000180921542951100d8840c00080d052139170003042a10701040c002b04100c0180d645400707541d003d950a107400203408080c40000d810410783c1040b5400082103402840641c0c01190300a0801c4500c200295400c1541d12064140c0d980300c140110300105a50200050656407860011846a06891404110340000c403011408 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 346986196 1250 346984946 346984949
    0x90f03040303030501091d0d0c0302010912020f16080d11102405030102070c09180230070e0c0703050d06030309090b0d0206190c0206040b0301030c08010902030a060903120501 77
    0x20a03207071401002100a544151047e1506100540301c5954a000a4945481c49446000103105002004002b81803003544603d01c480e41c00200b00c201c440ca0b00001a40e1514801e601c040a03100381d8a04a600031a40480c0710201c0da42c9000900c00d40042c04002d952505c091086c0540b280700780c0880c040f166409000f460424184005000d0030071180180c03000c80e0503400c0d04802e00982c0100a51000602c055040030200d414001c0700050009159007103052000d0803120181d4401c00c0b044242c0c01680c900d03032007490a11410a560700c040c641e1202c1e0a0380310912885034030105192880090401c4400c1da0082a00364420f00d0406c2c942000c01f42031104a4580b9042503002400e066401e004841d2544150007440400310740010380720100d1b0340054910f200c0d504140c1131640100c3e021000c19805081c50011103507000700700030b8a5540b6240711802a4200f4402a6640c800c24000000c28203018426107000c0f9401034080c0030f40f16590f0321100c01404802c0021000c00035038150091049000307105003030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 346987446 1250 346986196 346986203
    0x3040602130609031a04030c0b0f09010b1c020108040206220512030310170c090109090b071803060203100e04030f12021201090b0406080312071b02030a0308090f030403 74
    0x584403400040e03040d1484440303400c04014400c6041042c404104000c807004800207010172004425662890103e5206241c0940148100604014403041041004519201c0c00d18030008102e541803410402090401c2c4c80300c40500c60302d1048584025501c01c092070f03907001e800544014a0103455070040914a00c0c44686141d07040c2c80040144110f00d000719885074046a04801582541881c81e081d81801c61284950094419170f139210700c4c0010800c0c0050686010014a0300801c3e40c0e4660b1000c0141000300f40c110344201c0705000251115002d089440c00c84400c517842030b0300803070443d5280f000030f51000d04416042c031078001d80011184200440c25108510075920030707003203400072000a450b0072201c0f02584103850050244255000440520604403064124082601905e04001c1744c001c081c1030f00108001d000c00900a400081000030f00c500580707491359141308450071880d0751108200507100082d4103410044110700420300c503000441d08109141e007500c210400ca40c3c001352969000350b0048 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 346988696 1250 346987446 346987451
    0x1305060a0902010f0305090d120e03040801060906050301090305031506040504111306020c06090418020424050a051509041116150203150d3f020a03121d03030406 71
    0x1e0741156848040c041c1300c03110f907060a20413400c01c1006a501c0304003a50240741003201c0610f480e0700f080318036001a1400610841540d9569480e0850b05002e040d041c01207880f902c3c1810000502e0741014801d44815a81580c0c4142c21500c5808880102190001d480d60340a5014000412700d9179030f42c4104149101000006640d500301c02040e4141c0b414980e0002003076421507c00c0008035100d42d412519006811200026100d1b00c18404180003284118081d422514002c030000303040d0380d01e04d41558500c0d80e42c024600e071a80d0380d0080282d0220180101900030b4440064500c054217204090304280707400400200d818000640422183d0b0400c0d07210a6505961010300801c0c00091107009e103080980701025880c6151030040c44001141c220b90441c06900901d0300201070000b030004600c59940030540301490040c822494800c140c40e800420002d0840c44220b1000440c000a16070020540c180c480007401ca540050000081c44001c0c3c0b820400c03600fa40c00549a894148011480713144241c200 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 346989946 1250 346988696 346988711
    0x905010c0309020102190b150109091103010f0902040b09060f190519020105040b16090f0914150a0b0f0d020c06010317031009020d020409140a05060d0b06091305060a 73
    0x2843c0c40ea5000c0c040707922201d91b000003008a17403103003103440e4400301081000086c410100d004035026400344d4040d02c0c1072032419825a8104440d82d00a49c122078003072030400d09058541d00da40b0202d00c44c0d032150401c030403400c01190ba103500380074019101400c8111b07109030030052095101e001c4051081201070002c2c50010340b2552800300084080c040308030300c0c80200600c1c541075076044d43c03540c00603191001e18000c1d02c140c504005d1180c480003010303014003213500d02d0079551446504050194240c04040641c5004e002496510100c080c09040f40002020502100d1421103800060741c440507480304442000c128001c04440180010f009200b6101c00070105507155042540300c0000c06840340001078800c0040c00f55040c80d018521042da05072078401a5030701c0c441c106c040003c0c411a4407a0a0040c102180384000001c6098614031800c08000140000e940d68020007400801a0030000d0600c0030400100d6044d05104440c00da1101d0700d0501c0c1d618000c0f50f07840b010300c1d0200c1101c050030040d8480b0607 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 346991196 1250 346989946 346989949
    0x905070306090f1116060b122d0d0f03020906220504060302010f1b02120a0312050c070f080417100e0a0b1f0506030702070f08150403050d0905010c030902 68
    0x540c0403600300b066010007011000300303540c00503440f50301d24100041545c6091901484510b03881000c5c0341d24010300000c009510460500e0f181c1d83c840c04040d0140655000c0c401190050605607500d0340581c101078403105028000a44074500720380e100ca01015070a100c603040c02c1c1c40380c2c40180380342105d614030112403140480e000c80c3c1c2450190801070003281425010001030360020070403090380c200c9081030a801c141d0458450b0941901071000b95002c4480a2a51502c00022900950450281d55080314007000032a0038801d540050b10394110840c0c08001007404244001c4c0440300062003140010303e010390321021300c1102e20b45c612001402c0d0700001c44c2030410715014442c42c0c5100d0780d04c3d00900360106803070304d500c2c815841c01070400c0302d000442003c103084005229041000713000010a019201e0400707501c02581c1d20418090345008030990107010500710030000d4136854082176102c00d002c03596559901110f0981010550343c91181c0c840c140748000074403e008080d10420705540001d103882c40d500 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 346992446 1250 346991196 346991201
    0x60b0c070f0815090a20040b010e01050306011101020c030406090f0e0f0406090f05120d0c090308040312050706061e050103140f090309090405071511060f0c04090507030609 76
    0x10301405441800303000030030810b1004140030001d4480c654030160281c1d1036103001420100300c0704008121070a050303440d0020f40d00600800d2690901500e0800ca8004014010b480d20310350007589501061041c40094030541c481c3c4d4400c0306480c2c2843c005030070104000e1540e4a960020340100c030104280903814440f0300101500180281800001402c06050096203c1c2d00710318054000f602454030b980103001032020304020184040d40c000111400c1010440f9070344000c0d004900c018102c0360804001111603445a8400e4056941000d20b0750300c1d01d480e654404a022000080c140c4c01c0c0001440140e011450902c40c030801401c0b0300510a4402d101243c7e20320030103280740c2001d41410701c2d120041c00100880b009107548012942030002d0b00b80c403514459440c6016040000ea4400da01604000400c03074046542c1003214001304c0b0b100d50640502c00c06076000301d200b00010b105da9008400048030300700306288041c1c0040c00d02089a140640302c2c89204291542110000c0202c1d0320307400d08211460491 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 346993696 1250 346992446 346992449
    0xb01080d050a0e06160807031706040b0102060604050717040f15110706150b040314061b19230c0f010e03070809120105160215070e1012060b0c07 64
    0x286049032070919074102c0942144255803c060140303c010a1304403100d42e8141c040d03900303650400803079078407600f4174900101400d1400811405465802002c59a00e041501507006480c40503005031000d50f481c142448002c2100070030140411403a1041d4203c651124492207001c0c1d0b02070f5010f0300010340307107023403070550210b5501e1807021003032504100010b1041028152001164025408146401e00301d103410701c14545a04800e8025800040000811036940200102c20b002082170b1031050380c5014840016403803540d980040502c00304075030b0b480c01074240380c0c0400240d81c41c01d0a18651001c160800000c1c900c05030780d60f007040c40001d01c102504604009690700813800a009110840001410076140d00031810b00812524010449008036610380c010307400d8000548008004030b240014120851034803900081b0003500544143d0034150282c5400c0134072070746243e207840c116003120380280420848041c144200f005849140102c094030300b80a5040201280300800303840d071a8010360705003420394a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 346994946 1250 346993696 346993723
    0xc09061b0708150103030f0e1003060e010905010501050708030901060e0a0605010e0307180c0201090f0308040b131115090a03050d020d0513060305090703050604080a170601080105120a0605040b0108 87
    0x3016003000720301c0f10000254192a814170b002c50042136183c2c4140d490fa03a5010a0703503800424004007540c80340d0b2590210003122605110a100359984803884412101c0c02c0c0038850029030b04200c0d400c00300b48464021034110030010f0002520a98070b00c9a0000280103a500480d0b02c0e031a050304109560340200d002014500841c0904840da1a02c0a251a00f5041c00701e95a0402c0c0c07034500500656000307606c1401141c0d0015040701c100e06051500070b00a0404075801c482100d001c00100c1c0303000d5907003030007143d00e140c2c00340040400c2c0708458108000f080c5100140c2c0d4802008000c02e101c1c9403200a25000218420402807240031000c1d45d01a0400317501a90000c00c002081c0000032507100d4040000003110543d0070000340c182c8805805d50305190b11b40e0400307401482018180010022003000400c00b01c4805d90342c084141d2020303d01140801c0e401d4440381d000a03c00001808146404170001c0381c1c0c290300030700b11307403044081d070b5a641c090b20030450b0241d401d40074550040080b07080c14401c42825100 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 346996196 1250 346994946 346994953
    0x1005160f03060806130812070819053c0c0c1c020d0e06070f1209060203090319020114040605040e0109020a0e1005160308090f0102090d030809150a09020f010f05070b0c09061b0708 79
    0x401681c0e0854a058034400c011403a8146150b28685003101004440c2c024042050310714549070507200b23112903500100b43d080640c1304000790b10080d080c0c03f0b01c1407000030342a603000e81030710701c400582100c4a9006280182d4003000410281c000a410381e0308103000144100f0410b0f5105107090310251601910751300810035074100b00440780c101d1381e020502260444884400e5101e200c95400101c3d88076581e00e2040c80b040c5030018000c203450b034015000e8012212500f170032031556a218041002a40a0f800104000c201101010701c0c0ca480e0a101c550a800b2a51500c1402c009080003885a4020144800d8012441d04002e0060550301400070100000064000f907142880740c001040c030f0b0300a100303c06010848040003181501009011500000d000424928420b007002401c000007050205000c9203e02810151030609501840c1d41d05150003c64560b1070410441d6240d04500d110003c1c5010341d40d200811180d0b0302551800701400e08101510007007150300d400740011a240110301d400003a056070 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 346997446 1250 346996196 346996201
    0x506040506010c06150306090f0c050d020d031b060c030e06100503120c010e010507080915250513140a0801051003020d02031005160f0306080613081207081905 70
    0xd0b00240f1070b00005900402c0060080c0003000d502c070080c2c1d20740d080140903a080008036024008410480c0d4441802100088021076958040004071900800c00a410240491141d000700e8051f80802070f441d1800099401e14080a0b0f03500d1080302c513400030322808699110326004004d80b04000c072681c04802061070790b06260624000a80d0340d001d212038060784500010b41c850540000f900507d0811070300500902c218144500041c0c50104200e8021200d0b1003240840c18540c494a003445004001c80c00841400b03a81c64441c000d442080105410240181000356102086a400c02c00c0c00070040410300c5a00501d0210030010640142e510101e1181c0c18039007448031210880c404e00341201c0e070403151075a0f2103140b440403038280301c2e5850440e0b240510b000d0800c100c2204c80d9209401102c05592000e805012085c41901120400d000740d80d0705a000301c000409070b480d600a5010140e0150f00da8500b080c50401c804007040c5411141000000d50180c01c0c8072100c08800e4120080040790b45040c44a80f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 346998696 1250 346997446 346997449
    0x102060105210307080c06010504050903030610031a06040f08010b030d05040504090c080102030a0b1f0c0b06030a0b070e04110301050d02210f0a0b01060305090a0b040302031306020c03010506040506 87
    0x308000742a42c45010318200407000601003c00849003c140d0000e446502c40741501071254942c10244a014000d50601d000200c5a0101004883c46158001c0c10340e0001f9aaa0100703c000307000c072001c2100f41e85107241e0541c0e4256141400361005111104e154952903080803803450a4540008000303010b644010355498a4903003001c113841c103548003a075001555014038142150704882c00c3c1d00c003000552000041c004141c209400041c00d0303142c1a1003051142c000000d508110722103441236200001d11004005000400d1054819008240182140c0314462240c550809000701521014041440c0414214050a090003158080102141d0050966143c080840c1c2e20500c4240000d1207031015205040c406c48403040c0040003d0064421114040040d240442e07035600071501c06d88683d10500300000310b05110b8051380d441030f10200e000d4202072400d991080503454002c0c00490550106001e000415581c0182600c001c0c0050303802000114090414542151809044107003ea4200360800665 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 346999946 1250 346998696 346998709
    0x4020f0f011403060a030c03060c020d1d04051506030f1006020105041a07090f12030305060f03031b07030614040317151023030417070f0809040e060414010b0102060105 74
    0x1a10b440400341c3d0f030f07559850003e841c10304190001020a181d6003408030031300c049544490150034203a001c81d0202d103a512002c2d81c144402c41041011200449843c10060500b0340110b90005120301036500441005c00000d80d503031b00102c072140c010702c41c04810400c2c1c0c03075020050b0313800801c0140003c0049003026200e01e005880002134146981001d40c000c07480703052280c1c112100038403800c2140e8100c2e035261840969026070701035054000905203004514217261003581100032050040045251030301c1c80e25850180310003030300728400c030f80100c44000010034410700401d141d820299408180c1c5103400c5c03502070690910503a0f0000c41030140010009000014048560042011560300315458000c580459480c00c00380129072501c2083c41d80c0301c10804003d40510300484c40784a0810040e007414031752500c18040c4240c00f81880c010b044118012840000c020614150042c0001c00e44030041d01989180001c0ad4070f00710f6450100c10303640c0c000d1103420300c504441c11000340f000c3c1c500365162030b001914 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 347001196 1250 346999946 346999967
    0x507050304151209050d030e07231c030305040311010207020102070e0a0e03160212060403080604050c0903250510050418060806010b0c0d05031e0601141204020f0f01 73
    0x2118030000104010060140f02000e000810820080c00f00d036560b460070940303d038003151022021030300700114011826008204c41c415540392001068034000d1017000c0d50400d00c0b07003240c0380e43c202a104007801c0c000b0443c80d07840690b850013601d0200e400c0c01e00e0f00d030080403040c00e102d0102d500d07441403115600603a804034803101140c44250f00030030603440d07500d0b040004108641050b8103600c03001030b04280300c0030049503880e100340c001c564040301c00e400f0408440d00c0b1142107400a0000310000300080c50340c80d0a80c01160040034541d1264100a919400b203481c2031891080e42084d26003c0d0f000c1c090540a410a000207414191a1a4000d8070100c80103019030042d401903407101e01030103c660b200c040321a40480e00074400307042100e0155a54141c01c1c600c5602029122a680c000d40c45109041801401101d00601e000041c00c8601c0107450300e4040400c4010342a581000010301000065507981c030040e0041031003403844500c46003010710400170700c141e0525045019a07001030f64011a80c4e007001e540d01c0d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 347002446 1250 347001196 347001209
    0x1514030a050c090d0c1401080709181b020604060f02160305092701080d031e1d1b0915010e06070303090c090e0c041e0b0102010b040906020c0d0507050304 68
    0x1401c0d44440318504564025600c55070b810030480302401c0c003800202d0031600200e48050215040201e039640044410a504807406000304d42c19000c02c12411102e420980c91a0081050000300c010860024182401007a40c064006074031600a11061040e103105e860603201d41c0480451601c00ca07080400001000100003505108000c02d809031a51210a403072a078102c04003c0804901c400510b0a2040c0c210038020070310a403003995000a0014000d00c205050341c039844419408912010003c0400b030040996440e00044585030480b2590400b040320000d4400a02202d03000164143d040c0081403c0c010704407698600c01b807105940c540d820006d02150741806907105544c0344580d040c103070041c0000010040100303c140c0c00020f40f5010991142080c071240a041da00341a03005410801602c2220390340c0c1014151400b00c02c0c03c07060082c0d0203944c0d144810300000c03501002c450001030072519a4801070701d803960005070440c0c81e0348080c4030309501c0d00c1d92414028248800d80d00e07410b07a00d001e42d0107000e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 347003696 1250 347002446 347002451
    0x92102091501030b0a060302030714030105300f060105150708030a0203041b1401080a1b03050a18050319080106081f0314070905070507051c05160c1514030a 69
    0x941c0c103030b44240c00c5007034801c2003d48240b840c1c550300c28000b1b000b07510807503400001425030b180e91000c08000c501124100d410040c104d00b50b428090716011020514a02150341503030f00010b1064110209122110014407075001034480780d8500814003010340721000002d100008100014000a159103090b01d400040d16000103850303075114580209070501030a845503110241e200000b0b4024080e40d01001030030800e98035160f86441d280b5540c01940c140882e41d0390307103181070803020081070312a80c4140c0d40080f0018011448902c000220541c00c10324070025165038000003042400d1418507680780559400341d01e8089150f614048000b0b00038fd50182000c0130030002e01c0c460340001d541030f01342e040245800c02c0d00700b44031400b411070655641200340f24124101e0306080008100c14000e4003500c0646030854090903600194641510074020300804000500109010050b0038035402c0c081c502c45984945543d030030140c10042140c22044440301890200003940c0e1070b103002d07180a4000c1d240c100b030464101 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 347004946 1250 347003696 347003731
    0x9080f07030201020c070f090605041112101203020307060c0807080103030e0301291509030c01030b030f070308071b14041e020c150a020705030a080916030309210209 73
    0x483c0a440707041c404140ca0702c901c14002c115280854502c0e02250303212003081081d00d56a60600040d1032000d0302042ca134100a104000410020611aa0340041305201c0091007a0314ac81071104007520f0140d0a40046c0d00210701d6800f00700c15071040302041940b03400c20110b64900820020111101400300600b0058480002c0c6c040d900c0c00d40080e1413860081d0b103d43c29101c600040c7c6c034120309013501c0b60fa00c94400d5000c9400240101403c4400551000e400341c030481480000540c058408550b04607090703c6542982c40c50703c501400040d011358070880116a0311389580c2018264103401400e440074900c00100104a0040200c003420001c0b03c0555000c208090742c078036004007400c080c9819101c0301c0c0c00004c00c10f10b820390200e1000c815880716881001180c4400360311000701d01400b940140345500c02c12805041c50b0203082c040394400240c50484007030a02041c6090125400c5034000c501140d0000320a020001020300780782d0030442c031108030343e1000886400080703002c0760207416401e051100908 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 347006196 1250 347004946 347004953
    0x911190c0807060507050a0e1f180918030801090501080a03030f15030c0501020106121707080d0911150705150a02090301020f03090d080103170a0c050114010501021009080f07 77
    0x54070b00d99500044100498a0710041c013a106030b0020418100048400000044500d02080c1e4401d032104c40742003078007801020a10541d801019020b8102040f0300c011400151901940504100c8000702600c0c600014000d1901400071141a00044c0d0004d04003401071080c1a00090740b41c880701d400d440c0c046800c03680d060f99840104092001c0c1024004060004014007150581d814103c0d002a4003c006031540c61005c0c250040c102d41c40202002500b030951200d02c842600504078242c02001290301c3c02c0c115580140031134035980350442e140c00c0e0f0340740910180d2410307810416201c4a801741403450a0340560f40c0544902620007008204a010404a50110358690658030001000b800031541c42c02011030852594200329189005440780c410030741c840c0c600c5109654100c90b849100080c0070360314103807580480d07000070700540101b00501028502050b000d0240044d640150500000c00e54101030009003050940b1300c41600503070629440200040708a0121000030284440302a1650ce10b0314 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 347007446 1250 347006196 347006213
    0xf20030417070f050f0d05040f140102120d0b040b040c0507120e060f031005030f150c120c03040b09010203150906060f07051005150d03030b0a08010f02040911190c 72
    0x30018181c2000003d006081040014910b6039043c90b0004554418000c0a0211845d100f1406118204070400d4400c00010034800c3c1c1c1003c0785881401690b0841900c3c07000714034190007010703441c40741c203481722000729003400c00d403041c0300312110181c1d07040c4003007100701c00c029002d44185000242402510894800d2280c4540d08034940c264000304542c0c3d903010003201035113268000340c5800300400d01c1c031000005d1500d40001d1503001e400441d0054403092503100b04002d01903030300810100410100700004d03804011000c3c0d07441e108a42610010341c036420b290500380301c40c600081030003400c0d030700c1002031155908002c905a4180d14048070f08021796511100810040d0243e2520504041c00125842c0700300701d0081114540c1414441003040a0364903c0d4400b583d100c0b03100c01c4142c01c40e07042c06030300000c40d200350400c0101e1000038010340d007900d559510180c210740400340c4030020250f000c20248000b03121405442d00d4080c01c000d0710340c144070108421800e80d440c8540e201041c00104845601081401c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 347008696 1250 347007446 347007457
    0x2071d04030905060331140105010509061009080a08071401140121050105090c3105130c090b1e03030901031d0610030b0106031a04050703020f0d0f20030417 69
    0x80113101d40e1035806c1c4c2c0741000340d80403d4000c50307001c010010100c07501881446198100c44c00140310541d1070300c46c0402d100c0b00724a825100360170440f0f55480414401010854507456a00c100845035442c0034504105100710302d4004260000d905144903000e07135503c02034427581510080142040780d19a106401c801d812100712005042d035003001c081041c074203070100d01d03280c2650041d1203505a03070000000d03000c400e203901d203480c80e00d1405000341c810f83c00d280c507880786612009503008100e2003a42d030b45444040340006e80c007860304652900b0030601ca5091440305141000c440d039000007904504040000c1e01c9000f00c02d1403504141d0f55540c405030286d0924640800203a126041c1c1e10b642c1010024a00e9800031804203541c0410441d00000e1042c0c840d00c1124610b070903d4461b00e1328901c2d03410070800035000c058170700400c050b0240840044040a0307001815a0320002d400001c070000d8000b08941503800b11212200f032034000041c415008100901103a0b48190f100318480ba21806910000c5101d0245 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 347009946 1250 347008696 347008741
    0x140904090b0c130e0124110a0b040606050103110d091113062c07110f160905010b0a020304090213090c0c02010e0613050f03030d0c02071d040309050603 67
    0x1a0420b0201444001c0b00501e00840d81100718003145450754120703c524038083c0701d071501030039180010000808011407000e10000c00c51030081b040e0203440601e24580100a041941c814454100b4401044141e1143c40300074003003802c00340700c040c88807a40c04009004d10415135085540b10380d800b80800c41140c0ca24502804000c001308038504040901c13000419130303070144030751443c81c1c6580401ca11041440c8201c40c400090321003840f60360340040441728442c9420b2030390304a02c10b075103200441102c01e00062810382240d00c820f98455143c01c0c00c404c103036101030703010717120b001004c000c2018421b5021081724162483c0381805070740d501c0600c1c0400704036407490707012440345850800805981a4400e54505446000342e03110b418022122041218522078000822002000110304000da8141050200b030301250040549007000800d0148106464011102600580140b401445041040e14100004100b0201c6012003440c15580c06000061507000e102e00c1340300048001061280141002c8074003140 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 347011196 1250 347009946 347009963
    0x2904090e0304031a01030b1305071701150b040b121008010207030c1104050c04231905012007090905031308031e0313060c0908070b091503060114090409 67
    0x451032640c4a4129000480341d10040011880011080c408402d0603203030005980f101d00c0d05e41005420a2001148007100d4600440d90b0008001c08000410b03019880d05c01d00100b44d180d800041c1541d8103805412842c1c0d000b1050006021400082003070768150f40e0720510700d85c21910340f0400b000300e03040103522551303042d800018810700f016408280c6c1e845c045c1c07040f418030041100b50020042a83d90440d030310340038510241b00401c1360031141c1241945400d28560064951150302011400000c040c5400c01c1c1000123040d0308004a5074020340d012a0080ca00c035102401c04040740c10389031141d02a00c00e4401c62512640700406020041c011500b0002c000041320100c10f40d00d030a05512030701720180108d50140340034021419590980e0440303105108200303800004140541c0d903a40204442d0b10310000708030031810f012070341c490108a410003031b0202e0300003261101214000c10000d0ba01821051140f906c085c42440307942d0f604a03500f031441c0c0303103240360058031200030714080b400820054038060111071 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 347012446 1250 347011196 347011211
    0x507150e28030905030f0c040b0112091406060d080301030605150d0507080d020a172107030e010b0d0b04030c0620041403010905072c0403020610050a290409 69
    0x5810407148801c5512075101c0d405443d07542d1307082644030103010b2000707082500007100b104024a4581c0c000d407071303141c0141448403401d0078900c0b142d02112502c2c0b004940700c405194002030916020408217a1081080710011401040351340c8201c5503000603c0018650b0744c454011072303000b40114001c502d415801401c12090400c09060282c0c1c0c4d52038511414006024103c540d000183c400310f0300307113003080d00001c1c055000340814052030650307070011f8820003040c030b034010301b50b07110700500300f03680e0702805841e60081a03524580c5540f40c21100c080344100e02c2104503400300800506050740095110307826080200f000511801c4c25400380800500f01010400343d40011175100c0c0010002d0010346141100c42c0c00d104440c0018103088a5216402030680e03030010600700002642d16401e802848070301400d0072070640d0386490b81003810505840880c00b5030031001c1084100040e0304415030040c0400c5810944c41031610b41030004190002250002d405d001c81003981040d181c18045900500c1d00f404200a6403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 347013696 1250 347012446 347012503
    0x1804020123120c09010c1b05040e030a030b0105070c0302010f0e06160b010509040c0b0307090b0d0605040e06011a130807080706021e0c0607020d1b090c0507150e 71
    0x7944180d500801c44600740010030f144243c890140c1c2d00401043c0c480906142035520f030019410020510f00080742c0e50304a000c115500c40d8003d1508020704800215292002084042c0950705036102c03050400009210f01e40200c0c40411354074003220380a0803e4040725403a2102103d0700715801441d241c000d00006285200c03c4107291100c00f05c14010409226107907200c1040010300c00c030a03140500003104000040c00803240c1413008540040c103508006001d2507554041910981009505d04400c583e900b2007004a030409000d908500c0c0f1120021b04003130b40c14a48000c421014400d5160b414907400f080c50800e450100c00b9110107402080100c0e045555079105c40355945846001c0e01c0018041c512034101d40a041c808920700901c02c1401600d03a4400c130b4018085142c11040003a0ba000d86420300c808041742e0719144c0c503e81c2d5403513400100320140c1402410390a40f80120300c84002c0210801030032021607820706000c056503c0649000c950001c01a803c01c0c0307045144150f0a00e001202d0f00600c214 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 347014946 1250 347013696 347013767
    0x5071701170717030702090601090f0303021605010e030a03030c1407062a0816170a051807050109090b04140112030905040501150309030908011d060a0b18040201 71
    0x10109000110b46005031111145a0580d101031410784440c0d2040c410702d801460802d003e243c1c40b40c810f00d05213400750780d1010740040e41b82095000340c0150b08140c51550082c0004c04c9440040d040a00b81120710780320039004650703649604c00015040559a02244030350034031030154600103030114a4580c1e25034205091070002054503a0300030304c80a0460a494a2030484441c1e02c103000e414a4540f42055600c400418119030400c580080402c00c113100109406103009a11501668116500280318609460f80c90441001c0c00c0c80080e81d54003a1004000c1aa841108041a1044024080344030000b43d000302e8040c02c40646040802843caa002082d503010008841c60b00302c3c0a1b6903802c81c5207039a032080c042122030a000c1c503c001402c2104441c5a24026041101554407900d812010a5500e485481c00c450300606c50000c08040e16034107100c90309041210a402214a40040001c0c00c22000051640c0c000c00489882d043c40000c001400e580c060b170700c0b9965920322000038000c0a414458000701 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 347016196 1250 347014946 347014979
    0xd030e0c1008061305040c03061e020a03140718060e0d06050106020d230d0911030708030909160804140f060c04080f1f020c07030812090f0c031005071701 68
    0x1140750a001c4c0066010038020140190342124984000900315268040980f914008031107007840c400000078041c1e80c8920052108518540d00001c0c0080410f04a001c0e1504c058400c03002c0140c0743d880d24041028610007803046400d00d00304034a050501c4808919110100040a01028030300000011603a4020940030408000741c2d60fa00100c00806c41030f01036942401c1890310000005006984803c010742d44142182c60241013002074002150000074981000354220f13920a400200b503001c03a504005116a0f040158884030000080d1b042500130548407005001810500040c18000040031044c06075000800c5040306607450703403074510b2113200c50798060b1061031510300c13403d0f000541c11503012901d0707400d95081c44603200c80c40e07001c5a02040a07400c0b00420304090b0003072010002c001130740c460051041401c00040b03009140742c80f0321540c0c146000d12000072500c2d0050290070b212543c002c0f80005c00c41c4400e600001b02038841e02800c4810300c05440907565400131102c000300e401d181c0d00068a0303 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 347017446 1250 347016196 347016199
    0x20f04060f170406182117010e041b08010608010c090b16020118090219170903040b1e0a030f2304060b060702061804050112050d030e0c100806 63
    0x5032403400c0e24001c8804809500a07aa121002c58001c2400120907800a0200320001e07580d0f580101038a40307500c8101c104182c81e005000e90034110f007030b400e5908085002841118144d44203c42d6162001561000800034001440e144c1c114050090070500509075602070011a0004c105880e1500302407402400010b03101c4010030610b10300040e01211182c100c0d51880301c51908a440905580d0040d41c085854401d00810112a03c0d0003040046562001d010509400f5403001c810203413070300c0060301010150340640d0710341c80003d041190030000002110300301c0d240f000501c0e6907014009140c55200a1001d0011004031002460300ba241e941900800c1310b41c0d00c040801c204e5814086000b142d035542c0d44007500442c0345c40c2c500080124030789510901141c58003411503880c0c100c00c0c1d0300040d0503600524a0000c2740b070707040c924412642460300c115409001084000382c1440364603103c0341d40d18507001d6140001c158035003503d110342c0042807107103c00940c130140102900d60301d8514080e101800446880707 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 347018696 1250 347017446 347017457
    0x9011b0c0c050d050d1809090506010509090601030b0106120204031e12050901021e0c090c03011505040b030c0306030a05030a02010c17010b0919120c090b010305092d01020f0406 78
    0x114040c5420340940d43c00b00d0703020740145080d080403402500d2202c40f90000401e9a0000c4000140e451018081c8518851040307010302030340d60515040081d0b060012304182242e5211000510004240c40c903035506413129803c001b85482c141c4644038001c0d1003030b80c00c010302075000251381d11160448000c031a66207910609100810805082c0700300d50303a000c0c03694201d0040c0c2c4074541d00c1402e5041c0c1e14908500c08802c0e82920a44a000c00c04a04c203031605581c004464940080108641402094061a0b5160340d251051400380362131400707001800058105103030444008045180382d9002c102d0030b449039601031b00b40d07501c0e19a02c2002074000c1441c0c21400c1b0110703901c0c0003010410b03444041418141c84000c485541480141810b21040006561751180025204403010500b100000215a00300b4815900c078040c00d810300180e00182c51030403510506040c00d00051103264003000c54542c403040800d0b03480da040a101040c85044000150b00002d01d10351000a00744580310a000c01002650550b8445 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 347019946 1250 347018696 347018699
    0x3021e030f210c01060305030f070c060503010b07030e040b220c180303050307051303060b0a0503011a060307020304320901060f0e0604090e0105070806011103030f09011b0c0c 77
    0x280c2c0314091552680403100d030b0080d0b61140500203101421110000b01d000080c4180c81381e075060310303681c0300800d80800424040b0b05070040000c4001c004015101920340141154500648803d030341c00341c00d400400748910103811010a44456002030840d040040071441220300104101c10940155071601e0041810640e0201c4060f010341100350b12029403402c160030503407031901e0407a041d400282c00300c0c0c00c00000304001001c461055a22202440c0582c90016104406404001c10100c40b948000c2c040d90401c20301d000c3d10000b55180041561040da1102c0e500e56503000114c0c00c510540d0006a50810316403001d240b01c509185585802091010401c843d4038a00000c000c070042c0c0905c598000030385001c011840303851254010102c01c2c0070142401d414140c0314501102910740b941701c0c1031190383d500c400f041842588120900d401480a0825404540c1c0c0b41c00c0080d2203200050140c403064821001090a02200750300550408103131400c94600c4201440c0024205416070205855079040140c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 347021196 1250 347019946 347019973
    0x60a09032003190807051c030f0501081f06090609021308060405060a0216080d1b080114120a02120f1b090f090a051209150a140f0403021e03 62
    0x2156a44004014020030854800520000d001c4503c80b604a51403641400032000103401001011156800340301c40ea03541200032600102220b56158405c620181480010008006c0219656000310720075103044610303503c0e03482401d0107000302d0f50002c0c0d851031400d8000509441c195000d0006034030300201e1848290754540c0003a6850760243c5004d040da41040b00070815105040c2e00401030750034000c24144035403480361580380c000d4100125203001c031034541b641210f100391112820041c507043d5081443d82e55041000351100580c956030510301490040c5401104e1140c200b000740c00066006101c00305130300207600b0944d128081d050381540c182c4544000694907032801c041c1c00c031a042c000342c40c80080790b640c0d480780282100054580c0c0b9140c01000415000b00e0028011301c224044a011a80e90380c0c40c80800b401a00004002140c00c0e540007171000e181c41a621841c407180d0203600c1019103440e016800c40c001c1c00c83c483d551000754048085a0384c11f91036100101d140ea9042402c0b419258002480e01c07 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 347022446 1250 347021196 347021243
    0xe0106030b1f080612070312050a0206100e06040c050c0105101805060d020402070609150501140a0807060302030601050d091b0b0304051c0c050f06060906060c1f0b060a0903 76
    0x801c40404500c00c00009084c03170414002410580c400c0104480b0b401d6600e4603000000700010191500041000440c0340d04da680401085420441c0c3d205201566442c00e40e280b0b0020340003038180c40c0300310740b81c0300d001d01158171410998182c1360aa030020845400c2ca140300880880041c842c0310054104000088018a168030074603110700070280c070f031150a0607140d00700700007940010011600542e4030381da10004640c0f079051070007403504407000019040d41001036034235183c1202d2401600c10002c15038240891100450400106c0f030450a02586989403440161150b003d1034015090051030501c0038002d225620440340e42c1c04489000e00307100700751030300240f0040d031008a401528592140343d5000001c001e0344446841c00107645091403510f249540c2e03070b070f0410700d003c001c1c540164010400c0c00b400c0e151032210903810420440c1c480d031805000c004550740b2050150b15813103020a540740c0a500d1760380fa0750000c10702540010031155444400359809012030040f400203448002c07266081050115410 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 347023696 1250 347022446 347022499
    0x402120115091a0301060e0127031e0f06180b0a140c040503030720060d02030405010606080601120902150714010501091116060608030c0307050105061c020111070e0106030b 76
    0xe0300f949181e0800009440d0010800340303c0e0b040000070091a03214843c40710004030030f030424812141300c940c51410259410041389800050340c000514040300001c8514510a4a00f6845600440c00d0f44051403410b03480d0310480303000f9001001e6042008031449895111550001040703030360711f00c240c50f080c9405199004501800b074256004200d4140400c220b00d004a00c011112615540318842d1180410000d410513102d40120a07004410700081007020b0040102810307240c540f901c180c4c5000c800003001036090951520100340d5401214040d0341f0384002c140b241000e1031076602c1e610161403078500b41403c00e1340d141c804254a001c002191404e030500803115501c00c405000c0e0f0619120012101c00d20710003003070440b2029915180014480c0048c4003801020200b040915195201400d1050035503500408151140e242c1041111801d1500b8000c1d4205580a19002d03030302c0201c01c4100c03850600c868001c4103542007800b0000460b103505401031801380d1010f4540c6841501800b01d0180f001100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 347024946 1250 347023696 347023739
    0x4030801050618061801120c08011211041407020f0607080711163c06030c020c1809070801050f010512032514030319020306040212011509 61
    0x10600400c01442d006001d42a1070b078003d04005002c4901c0800101550701543c03200c0210900ca07121034000b9030700801582c40c400d1a00d0402e008041159400500d4080140510420440c0e441807040c18001040502c8003464405003040103064030111108415000c102d80000052013481601d000b51400455203074043d0465489131100b68036030500c207852006102d441d401c1203104008480ba4101c50b40c01040d00103018503031a040704500458010b9452003024140040410000c48599480400c080741e00011520580b5000404004405081b4240700802c260030340e00c0704081c590351030741d0354000044034021200f0300d00312566150b41c1c400705803d81b00308648031400d58444200401030b40c240f02c90340b0702c0c40d0070b100d0090740c1c94000f00799062113030030500e600c805141c8140300b042e110401102c0b004241c1920500301c01103007075250070011900c54840102c0f00c00c039000d40100110340e0540310b913010ba8081694020750800e0741d42c2c41e01c070000f02001081e1103141c0050350031000001c884a80e2600c0c1e0410109 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 347026196 1250 347024946 347024957
    0xb0412170f070e180717010f0302040203061305090d0201060510021005070c080703021c1103180a1502060a15030c14031204090b15090a1707030b0405060a0e01050403 73
    0x480c07100441100500a1421080c030255075112000c030f035900c1c0742c400d800c1d5a000715265160305003075000420b500030b202584600000100014801c50690392514000c8950469000da942c0c0d4581d0041106a40400d02d45640107080038140601420042034040b040c000c00d03802009101c0d516410050440b24822140303002d6001461401c10646058100ba6400802820311514503045d035030b03c1d0f202c164400f207010f90040e0000746c1c0d0b11801007803e80d404101101c45140c40c1c03641c0d10507912920344030b202b01441c62405039070001140601c0e8803480300c00c00003050b55110700b003101c5080b40c40c060b45491049030b40d81203262804424000c075241081100040d0b0f60010714881000c0d04185205000c9240300ea00c0f40e91511441c600d000380d03c458400200080c203103440002c2030088a01e01401a0f100000b681c21814a20074021100140c407000480c004581e034580301205240302c0321030590b062250540001d400784400804000900034005451402507007007150810a1201040e402c2d4200d4800740d900600051 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 347027446 1250 347026196 347026201
    0x60c08061903023f1510140103061503150504110a050a0c0b010303091503060311010507081c020304021503010305070509070e040504030e030f030906030c1c090b041217 74
    0x404007003c81e2409807400210904d0031201c0034006401801801c0d1100060441403002d403180c0b424400b07290f40c1000071030401c03028104000002084455809984480c031201104442168400c0e0030080080c80e1a6030410b41d07100d00c0c0c1030020050080660045406568514001403504152295402c020740b4207160b5030030b1042901041320154030641c02001000300c50080040400c00341041e20303000f18480e48443c514240303404411150b8094070038554040c0f52401c42d00b0400f050250440190500c42441c010355218054601200706000755503241c484140f0502d0000103c0320389a000714010f50003202c2044c1e520015013610707442440240402001904203010411644c20301c0194103801040c0c80c04d00ca80c110700d50902140894108a03019070008004038414020390505000c09119105401c0203103203810344020101e0740a100250002c440000700040300d0110a04104801c00807000d0018144800c54584c200b02c220900f042e1800d54203402c4210181c40c89500541040d8995495800851900c2d0b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 347028696 1250 347027446 347027449
    0x1051b070c05010f090b04090212070503090a061127010306080a050c0423090a1203021602091e0f06100c02030a02010c1704090207061a0105070b22060c0806190302 72
    0x90302c0e002010405d000103524081090135000c0040c1000d81002c1100680710560061070920f204030203490642400000c2084c405150004143c0700182a040b440115807240c401250450740c0c49000307007a0301140c50400d920b011564030900e07580042ca0f4260707010300007281c9410b000d41d1680001c03507000705298000d030a100c13504d0616401211480d00032070313241e07440075041c001161010b0004a58040c0c160b0003c04c1d003407040040c1101c80721460085c83c84c00314207102e40300c048a040400d03024806071280c21000000303289101e94400074541c2d4070030b2018601040c20100f20b0352011030340c02e481051044500d60100305000d48079248002246400070010314090740c00da001940d103461000d01c01c1c0da420040544040c54030359140010401000310341401a507941581c24600225007500d0091110740041c03110143c80d983e8814103030f4a40d00c2e0072501c1081580c49075100c206002540400d0022a14580307240001417221a901c1030340e1090303483c0c4030200030350b54800405c80c4408a0748180c0362014802c84052001d03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 347029946 1250 347028696 347028707
    0x12c0406050910020d02070b010b1801030504020d0507121403030f0c090f06180405011202010e12011410031505070f03090f0203030f030103150204030b06010f170901051b070c0501 79
    0x1161010060f0789801e81a0078a14059a01c5844401500c58001998100700400b209070387e80100000e8428900b00740c038903841e1501010102c2581410141c84001003415907075030520001b07007164420122010565201b594494140e10070106441420780c01211401a06020044038420780c0c1c01e400b0f00d0000d98510000076520b070050800190403803415000c4118584030f10b00248a484130100001d20082c14800820090f00c034140c100c0b0700500b150410200050340c100c4d0307220310f40350720403035540c5840040c140589004090391050448a103070b1003011300504000100381d0b034003902e005500c2a101d0f007480d2086007099a80c141c444000103071903070b0045092280710f80e01001685100b0304040c81309504940019156801100d00126a004000010010481c210f44514140f602a5100b5410989103807102440e104006114130f042c41540903506004503c00c508401220448070003081e4070381040d103803d500030201220300307030007120704103140d291303040c080e00c06443c641c075840102d074807199081c82d004541 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 347031196 1250 347029946 347029951
    0x20603010e1504051504060501030902060f07031b0339141f0605040e0604030207051903050303040f0302010c0e06190512070f03060b16060e030c010212012c040605 72
    0x2c040c91040300b09000c0b5900d0703001c0c050083c590300e4a803050440300f4108101c102c40c40c0750300240c145032a00044034010386984090745c80b141c0380142c82d0380d283d01083c1019500c84841c0b000c130f0702c544e03924002c40404158020708004030505c0450030802036800d00c440f40c1d003558140000c3e01920952031401410010b05103e105600040daa0004d03102c518001210400c03110740303040c0048200c1c0b174a40c1d2062003942014032403061340c00c55180c020401c508094402a40380c5116024150049150094081706c140c2e04400d800c0082d0340c4078048990307030310301b90400d0780e400550f08100310f0042d400c1c0030755030012a100d90081403485000810f40c1d460f12124000c0c2d003800c2d00d0401880e0061001c20700902c016014400c0050b4481c2c245911900c1034403086c10700040403149141c02c1407084007001d011060215124082000325658020400180c0b0301a40c190749185000310928410503600005e400445200d41400003412660312903010780f40c0c9114072401b200d0720a400c8030489109400d0350700144c0805d0591300040c0c1c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 347032446 1250 347031196 347031211
    0x10f05011d150118091b0f091401020712030807110102041a030402120d230310060c0c050402040611010509030405010c03120902092401020f19030203041827020603010e 74
    0x401c00030b0604c1044a0000380d0310141049943d140c08280d0510680400c090503582440d000c1e8558010b8503000d400507125014080c7c40c13155010011180d03034020807807440038010004070003007150603528006050703280841304000029540003021596901c140252816603501c07070000b00407480c5898040e845038000030300a03a880340404d425680c8800051141d070120305140c0da1448100c40c0781e0708850701c2a24041000d20381d5034408008100101c061a01c0c0102175924030310f001c00904410341051407200100340c00817035015100180020b515900440000e083c0550f600017403090f03a4400495039100d0140d84600341c046107070f9002100000e4401d050060301c08111030030011f0811665004107101c508202d80e4a40200202450380c540d0280d40c240424482030244005c01d07051003075810036510b4480c40d110482841c035616107140c04041c000c0c02910050014507031400c280c4800d0148030704c09000400444100004a503014004064a040180c0c2ca5070360042c0c1510b00c0d5918114a140b441c000090010703 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 347033696 1250 347032446 347032457
    0x302120d14040b0105091006090302210f0606010210050f0a021c090f140a0309171005090d03050615030630010501060e010f0903060510080d02010f05011d1501 70
    0x70484088009000340c020360003801240140d605000910104c01e0001e40b44004500e4040300401105a00818a0051307030b9042c4c810048a181c5004407120707101001c50102801d0003544903030040c907040003c246119600036401c540140405440b501d00319281500c042c112904207500044814240d034004015584a0300300c0254103030354450862046421000c0c0072110501e0780030010040c040d00400155210424201400281180340d4007d0601486403045003000709031907541040000007848401c10494140038144604c1c075054080c00d880300c2800c401e25020920300800b1442d40e0408e00412640d60004410307940c519100d2604000c0094080c5494004a0012a405020803079090000704032008225001142e29410100041c05113a902102541008083d80243e030fa00c5620407a240d046a421602c002582e488003000300703030040749a40041c0340600c146080c113030b000c030350540c4034864140300740c07504000513600c1d07010114454107280350303c3c02001d030100042508615050f54804640005040c00b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 347034946 1250 347033696 347033711
    0x7080c011e0e1b01180905041b08031e0423040608060112080f0409061710020c030714010e07030f030201050c1305010e030a0204180c0519060f12020d050603190302120d 74
    0x145c01c0000309400c94000c07036480b24140000c014980d00c0c001c0c4400101402c440d6414140301c1c00b650359006a10030b490300d60400700005800c030508034084030094104c0c030810085003107044c0300d01501f04040129503409286800f50008500d040416014140d0f40041c20200c401069500e510a15422400344062610410000001c00c90914850040180b800300262101c1c0a50244241d0405000c1e000b52441640100004902c60101004980340c195114440282810071100070a0050001c00c0c0100383d00c1c4519240402400301605586c0d0b101d9101340d0080c002c2c0e0b070713424800d9410750203400c0c03072044c0c03a0400490510807507021b80560210407801034111666901d40c0c5d000101078448908184110042403003e1005000d80070608070050801541d0034640c0301c4900a40d402e1500291017654104000d00d542811024403484049090518401e000d64071082941c0c0c1100040009850301c2c0d109200c0d6048480a1224544001c1c2c41c10b5015005000b09e6213040c2e240901c20ba10400c940864030f50340300399 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 347036196 1250 347034946 347034977
    0x41a010503190513121e0302070809090702061f030305270409080a0212030c03040b060d06090c062d1812050c0f061206010e010507080c011e0e1b01 65
    0x80903c01e41001300e058041602a0400076104010f070340c80d400403c0103d01c0b005807a4661200d900e0381001952500607660720329410641042e0142c1c1000f2035000c0240414880003980c00a03545000b41581e0713124125000c80d1000104086100c0c2c440100402ca0500c0f0203201c001d58100b48070300340000610720050000c6080d00150445446400445028002249802005074100040c0301c1a0b000701c00d406186003029000c007406400018802810069040001840da031249072902c0420742d4405014040004c0c9490820407168190180a0019400700744e030303688889403541900c5180e00100c80542220707802c0380c0d084500b078000e144501c9000c8858840041c040007414a01c001d4180a04064a1041400410028614085151640b180005000b942000e510031041c007504003000b400c0800c1071401440c0140c0c1c0074000c4440242480201240e802000342c01900601d8029100207045040700c040704980c001103070400356000da810303030001040c49072400c1d6100d51031040e1081410200c860820300c80 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 347037446 1250 347036196 347036201
    0xe0a081b01031b3f110715020306091015030e120c01050108010605100212071a04080a02100c0905040b060d0504030f0206100303140306041401080304080c041a01050319 74
    0x7a0300002404503d8400041513045035248400074510540c0d2100010361145421926074030141050250751001410303006034104007290021a4003507003100c04100c500480400039001107440c03d0144040310002554040340280007426500d901c0400380e15030002a030210b00800b11900700100034883d03410f40d1903080301404080c00b10102c0034030000c07903190704102c0f880d4251401980004d000b89240204140c0041d004100d00034a1400c40d20080e88426203418142076a000c680d0b0f40b01c1400011405100500441c44001c180ca4642034085030303100b03050600d400341101d102c28210750000d1040030051009240c0b54220828400d0b000748450305100f41038801c14219001a41c0850200c2e801d000c0002a07190144541d6502200418420360043d1841c0c4001c0e1001c00c802c207483c92481000030028641c2c0d901d65009810844260a848a071903031941b072a0765995004d400340d0308072032160000d0201d003440c00e03001d0502005095481d11010200751001500d5540000c1c211314210366600500500100291 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 347038696 1250 347037446 347037491
    0xc0807110901092a0e191e03050d08100911040902130305070608040b0f07020f0d031a09090a12110f0a021305100e090a06060e0103030e0a081b0103 65
    0x1048000380f00e52400c4594250394030324061080c0c4c0c0000b10201541d5050308020007800000f0255140c5811a076408140c4030b003c802500001c00360003240c40302c0c1c5410143d1318504801c0e07034403c1e02191446c100340762065030100e80c2264200b01100c1100750600541a460700000d81d0a100c0c413140718181038031805080180e0300220780078401d5440d402070800501c141000300800800c1b56003860030282c01c01c1e0312030040c03442d002441010500b1254000c200c1c118801c00605100da0306540503100300c4014220000c0150403000c2890b911110110141e9026203010800d240c001d80103100102040c00b02c2d80da841c40c0d4541c11205c030302e0500c0500d181d40a032240080c4003002c07500c1d0003107002c6c04241c0001d00c10459800304010403940014588006c00c800d80c248c140c81e0505480382c19850146a41c0c1e90452685800d04501004042c2402c0100001d40540c1420700c842c1681d22981b0307100e07842c485503000d20020850b03510840c84141d214008402d5210f8895003407051040040c900801d080324940c0003006502c441 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 347039946 1250 347038696 347038709
    0x370f03060923060d050604060510030203160e0c090604030f1e050105160302030403020a0b09120423030102130e0406020f0f0307030b0a140114040f060807030c02030403030c0807110901 81
    0x8070048520030b01c1c5071990940d0002044941c1188494507856499840354000c1000303003441c0d559000b155041c00d0300c40c0d0010040d6401011a290342011040821410720584104642078842c000814a07006041043d00c04481001d0070040c1050b00c2e544034003c40c684401026039540b01c1c2020300c50840a2104d00e0500c0070750013200041014109000301465545034000108105881030091000281d030101c0c15414181e003040d5100183c1d1618070540e4203044031103081c1c540d501d100190014842c0040700000300a60381000d41804403410390700a041c01c2c4e1107410b81c0009001d030191001d0043da504415000d030058000e040050524014150768590303940000c8800c0200d02c030220400c000c4c45e03418003a49142040503202000001e180402c445506050141450b0600c05296a000000100581a90010a41d5000441d50a9620701000c1c200d03000540c2d1101c00281404182841c540c000021a82126459a2010b40c00000b6845001c21504054000c40301b2000b94100d03c9000e5541e5032805002c4c01a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 347041196 1250 347039946 347039981
    0x11d13020412031d190e06120115030b0108060103260c0109081804091e03030b1008040506010b03010e060907210f0e0a050606060f04090c05370f030609 67
    0x481c1c0e41c8851030340c00589980c0b103901317281004001d110681001c3c40485a40080d00c010301c1c1c03241c80c00a8107c800307103d180c02507980b174a10b070443c0300f0110018074000c590041ca5222026620344001c6a21030b94240400b400054609601c0c01556440c00d0080b1040003080050b20700f0003180c2c0c1e103641e0032756040a0303003603900300c1c0045040c00b00101d001c2c030060b018071401c45042146030f00320745c1c0d01c4100d402400100149201a14070040516000385c1004d514102c0007400140301012000010300408010b440948441c8200030010500e03a613024100c0c0d05035100345e00605030a40d41e00042049240340205083c0404c04060003004105509542e031a4030846030707500200c0c51008010200c2c084549901c00c0700780350340c000050f110200c3c07404103100e50060030130307200180c0d60048201b1406181c850b82d4011b0b019685050300c1040f04551101c060903456450a001125025010804e418000c6130050320745a60308108803807086041c00b85101a040c40c0c1241408100541d5034480c00c0121414074403600c00b1100f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 347042446 1250 347041196 347041217
    0x5100f1e0c0605090d02121804050a0212220615270c0e0603150f0303030408030618011412071e05030f010c020a0b040819020c03060105011d1302041203 67
    0x801c9020f502c1d8440c140b1401010311201a00c00295034014440c443e40100900040d030902c03007070000d5102004201c0c00341061080c1d0810400c004000e5014242c0c0072401c2c405400843c42290b001c01700c10340703030752402650f00c04010b1181d180c01c40205048240c14518003050302002503410003110001601d1089490034240300c2843c41404000d440d8840e05c40390420071000c0641c4000d9455005403500200c6a0301c2c61081c40074800042400c49591710700444d45032101004010030010390b00d00651107403006880c0000c0112001c855036864003428001c1e00402900d60b2048040c43c21b01d074028142c0300701600d04840c2503d50741c044000c0c0108034480603c079107002048040c0040d050070420016070b8010f001c0200404000300c0c200a468070220007000302241c40110119081c00f06260a0b05c194000c0c00e0401400d4450011000c1c1d503e48401140a010b0700421000003078940c02404680c03120b840c0c115810f40b040c1c0e400800c025401e503820700f40d414115400d00020895a0700030124508041c800c0d201d091010 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 347043696 1250 347042446 347042453
    0x209090d0216051020070b03041217070302031506040f0806011703040501050307180f0501080906091207050a0b0108060f0a020a1b14060c1903050105100f1e0c 70
    0x2e15201aa407468594400080040b5180c04003801d094500c2c92038040c96284208418041e50341980755190501d201d80000401e0990200004500661007050045e14600341d0210036281e01020714030600c40c041c25070300003074480c5001750001c561110090b500886000b841030006a0690082d0b00f00b00600803101c241842031040401200c3d024100041400f013040304115142941d81c4a540101030400c1000b2010a4181b4090032450902c001d003040c2040070240c40d01047d4110350460f20507e4000744900c4045410b080c03011030b07503d002d03002c20005030500d48100c05080d5070036480703444200c82502c50b444104000ca20610f1000d0301806482011380f555081211111900035005016111450b204001c005031541d0002c80004640c6141c002010100342507041540c104c0c0c035401040b4001d40202400c001503007080c90024400d9010340c5507080300b00b0040307950884c1280c409019041e00b040a10400c40e0300a40125050b55100d00d6628026003920b01d071451000c4220218091500400d10001030f02040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 347044946 1250 347043696 347043703
    0x42907020c030102072310110909011e03060b06041703031b0301080601061b081206031b06221a070506011a03040311031b03041404110d0b0307030209090d02 69
    0x1c500c040b8000c2d4101003031603ca11080a00b01d01c0300c0d9140603040001c060740303074400b40303c1d400581d001c0e04810040303284402e4040e0781d5030340600c590390f210345a828008038046091041210340300c18400a000f4819043d541d44000a01c1c40c640c00030341c8a00d0500c030014400d0120703180c0c1d101c2003010202440c4c89050881d000081d1500401410845240c10700044c080164001040c604440c00c51411058480103004091124940710402070000400050f00c101c076900c0000000d806031900303404803002c883c0ca9007440c0040003e01410381303500c0141006050a0600f203104440400d10171a081c40e00b1050351541307082564005204006106a00480c110302844001c0c00072600510f10410194801c94120031000c490340300041004051040840090340c4d00042003050700c10801030110441800101c01c00030aa690b04203115141c3c0001c051a0300c1c20b4142040d0094000c07041500200c00d0a00b5407a410b4080941023059106415100b40a070000250f0366004070f403400b5051110113450900c00c0e00b04000e05 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 347046196 1250 347044946 347044963
    0xf0f06080708161a0a0302090d0506150301050108030f0334030b091504020a022e060b1312080f0a030e0c041a010c0218070906090603060b0d020304290702 68
    0x9001000358420010000102c0b04005101341492441d940c42c0d00c042002d070b009003c0e144040e90811034100140082110000e0140e00034581a4843c85690704c0c2c007401c150a83e42c00340111200c0c0d410600c407005081400f20051608400ca0480700390000050b80b01c08107811003641040c40503601c00c0341b00d0000c103030303090710840240000070360700418140340c40c025204408400302c580c03a0140e503001a071500d91034401c0c064034021604d500400d00c51a190000c0c2e01e841401040b00c9107200d2442c0c084009425407241044030700403014002c1100c00a8030306030040d800c00b003031050165041c0804001801c00780d460000103000b224401d4a00041d00d03c0b01e01e910034584440045c6e0300d4002ea01e045910740c81442d00807032801d8134400929005640c88010310101c1c08044201101620841a42c420f01200704d800c040d0510076220705039034a410300c65a50b071040b81507441511441c040c0540170000d03008403c92940040d03074407601428070303d84600000304503140c88120300c4503000010352581c0d0a001056905220118 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 347047446 1250 347046196 347046223
    0x923030913020c0c012f0615031605010e01120c030515100c0206030603010f05010b030f1e0115170a1d0102091e011b0302010b03010b0109030f060f0f06080708 70
    0x1410501101034041e030304d40c0d071169031906202e4032084c400201ea41c09034800c91029542916030750b1510103030512603a100b4040da400306e06890b4600d51200e44d81000a0401041c50003000c120030300710710301300054034003800c44007040d8100b000e003910400c2080c00d98011010300b40242e640018052402809044410205403407861103040d521b4401c14000c1d62003142d17240b416404440d95039403501c40000190041c01000c40d0844a01d05207800003402c00303205009107201d00b1b03402c00a02115960601c1c4145c00301d100c81e440e140003100d00390044c061b401d0100c0300c10b0080b01e644d003800031555192105244806504403682400b054584420156041800384d52140032403411000358103102c8004002a14108100c802e82070380c01d8007952461185c1e12502c1109210001003140c002300d11181d05009010b8180c82151901a6007401400d0006522440e080710480780c1010f86056018125a54a03020b80300415410f450036450310200070400c011485a03100801802c00200152894207a074542089456803111 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 347048696 1250 347047446 347047451
    0x3090302090f0906190605030f2d0d050a03090609080c1204150e030c04060b1207020312041202120406020102040f0506130b030405030409090602070605090d0504090923030913 77
    0x1c4401c0c072001900642042d21700c0403840c100f8400d1004003000780110ba000c1d960500c540580c3c96500030340801c5140f20496102480f00c0d41c21055600c1903040000c4080001080d407000c5010504548140d000c0c0c032480e002c81c50003154141c0c06840b0b0906407010540281d440d50800030f69034042800c10000111103114a00764142454134140c004030400303000c0b440300c00901c5400c1f000649180d805002c841c40742c110007001040959200d0300f00c2d41083d000130340154180e581d01004162a240004180d501c0741148080040b42076480f6542d00d1900e00b420b05540c02588210401c502d545030052000d400940010350006880d2440c089203110b41e81030652010340118402c000340d001e0714070a0441102500d444040d00c60780d81d00c0d980f03800307440e41c8170f5544400162881c0841c1001089019002000c0d898052070060210348c66046801e52508408107030032021400c1000f0812010b00540c01c5502c616008010043c0030072400242c0d10300c00003044032101401d030070010b01d01481c3d2400d0404000604034440c0704 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 347049946 1250 347048696 347048701
    0x50109022101051e12030c01020a0f0311030a180c06020c011b0b060d05120408011e1a04150504051f060c080403260d0e01230402100e0d03090302090f 66
    0x402c142c44d5145540070003c10000c044030841d500e54540744802d20303403000c1c03c903591100d44026842c000c3d005150342c800021031102800d103270310b48280201d214102101c254145075807103100a0400501c400c070003084407940c1c05107240001c111409500d80c010080c070340180ca03000b07020200041000164100015880b0240310030040031801c0303098070300d5012a0a40301c080180c1d849080c41490080e40590b4682e010000250101e051310040d044203051030295048e96400301c0410500c041500d1808660f25801c410341e00e5156802e18061b000a03440201c000394003007009440b0f13000704040c0d032011901201c80755a00e040d110264580c62050000a003014074240d10003120079906c2e46c0240c41548405810a0360010340c0c504195501704030704079402d40c00391030170342d440302903568000c003400e00b14243ea15554a07040a03040d01c1c0b0792944040703900100000c408c80c01c43d6155400c0240c40c0c000c40c0c810000f013180703a031044d0840c1e41340c0c1c0a0414856009468a4032110b107180f04129116600405442440b400c4009 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 347051196 1250 347049946 347049949
    0xe0a0603150c11070803040506070c150e0108070f051c060f14030601051f111f09050d11071703041e08120a0e0d14010203010b1b070b0405010f0905030105010902210105 74
    0x11f58040d20802c8441503980c3c00b003801c0c41c3d4041d4400340c004050410f5940d00200c44e0b01d4001c080d51601060a80b030380711043d56100c200381d41c041d0f00100c20a000c10400c11121082c07000300302c4400c4101098a2000902949601940091076129040701c24060003034035010401d840d040141c40e0040034100d41c1c4990b00845d60030304c140b60354102c48000060004c890b9001680020512400c0000700f1030050b61318100294001041c040c180540c403d0b0340600501c0c849400007403040c81c0a02500c100d0b40d004200d0503107800c04884030250502d203401980d02081c040881d11001005000c000030311010001148a4100301d030b42428651002026031107201c040010040d03103500400485107003041100e44000001e040d0421800d807036900f042981c7c1c154800000860800b801401810341c0c0d980c0c10044541b00b45d00c0403185a0340300365a01a03012102414402000315600c94400102102090307c1d01400c01036441c2d01280c00d449003a00721008050300400d56112540c0d41c0c03100d12441c62000100400350b03514000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 347052446 1250 347051196 347051203
    0x50c0c1203010b070312060302090411010f020d050a120b090109090b0a0b09150d06050f10060207080a23030f09041410230901030c0e010815010e0a0603150c110708 72
    0x240b005080c011b0b00701110243d00c500b03a10080003150041e19050300c41c07415142904c094001c4400c154041948410440821031000440c100f0070644c44d10b809142c9094100195a5800146031950086484e038207030748010b031987c01145000348000007001c034891303445241062000100a00d261006413030a4034006071581c0c0c3c000c40b41c1d0021020300c014100c2c204058085410f5426141d0b0181c002410f01090209051101e008148a01c0007150300103a09515000c04a03101d4403584142030701c90344441c4000003c9011842207500302e807038419444041d415020140c0f82150440d42c5081c10710074012a42006c241031178050409210b6204540541030300c0c209660b00e2000c038081c0030344840145040c66901078188c0302e0a0a01c0507100041000c00306696074030b00005901014000d102044000c1c50000408200000d903101c424450300440d42c403960300b450700d0b007510118001c0034441c40340e44440000001c502081141c014100c0d2808001c80c0500114070040c0440c00c031401001d12542c03050101b00f01c0500c3c0030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 347053696 1250 347052446 347052457
    0xf0507240207141215060f01020109050309040c0e0d0c080d03020a170417071b0b0c0a062301030b06040e030c12070206210f0a09021c060f050c0c1203010b 68
    0x1868200b456070074000403e80d83d040200c00c0c250603100b417807040e0544400e60b140103031052000715a00b8840e0040800128240d81210000401070f50003844101590300c1e041d040110400380e01c5c540200c4501072903000620311361180c43c3c20390300b494808105105c0d0020038003030141084003d00f81580b80800e5080001c10030318000c41c5100da210b204802050030000c0f40c503070748040400840c11003500d4212608011a0820149460056052603008005960404e0f8030540e03185602120250001d810745803103090280c52148000c0603e40c180f80503110440f6a20504d0701e02a601034650480185441c41c144011292000c61000050f4018004d03040d100c0d10004e04032072942c030701d50340058503000b861000c00c0c054000c82140980c2031010074241a050040001c046124102404030301070a900e40c0020101151050400650003100d1a8403003001b046a80c1c2850000b540300b8140084d0688080ca5a1800c442c02610001d19091000451240b00c12040051100f07590070306141602d103514042d00301466101fa03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 347054946 1250 347053696 347053709
    0x2a0f190515070e300f0c182d07050714060613110f0c06040b07050405090703020c0a060c021e070b04121e0507050a1d04060510030f0507240207 63
    0x10309094108130054040004214110f0841e0040b41038000051941c4420841c090022070b41300354143d1542610701540f0380020000b411100348010386a100049400d03103400d08400003100715620603803150080c1e034007445105804950310a40c480d0718034680088048502408841c03242d20410500070b01e0343d1104010100c0d0b4250410001d01e041011542d04258061483c6d1451001804181c02c20340340b0303002c5501c0b0301c158810020858150703200c590a43d05400386000d000d4000d921440024034050190b4010302c008800d0508848100b2210340c0c070b0105569840740c4407801038109802a6650040341004801c2406002000d014442d0400d40002e10500851094144266551020344240962014141582c0c02c070340c15183e00b01c02140c10210794070100380c40f419010b504452000214804034118881240204506d03500150b01c40e5124800034010142001c1451054100e00000207100c081c1c1c0504102c1c8940040c080f01c40c175100000584004080584044499542140c00e000d640880e0800c00e03180c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 347056196 1250 347054946 347054959
    0xd050f0a0b0f040e070503100e010b190608060a050405040606050a05030c01020a1b08030c011505011b0312110a08060f01020607090e07180e0612032a0f190515070e 72
    0x2184050075140170800d0b402590075000b014802030304242640c00c031141c038600d014001c0c0007807180401480051521000c00028402d08500148040d41c420310f01650020700c000c0c40085c10b60b03201c0c0b002508458003aa411a460350381c502d0708021508000300503000924003100038180e0040298000f030340701c460303100c0004c20300d09591590000c0c81007030005001c0608480021251120383c2145028020402c0800703145002081c1c40000030a5031050700c810b140001e00c80345800c90305606603000d80d4810030f407000442c4013036100d40003c0038000040001d401507800c145d8544001781480024401c4c0c2c40c1e80d503c6400d0464003c6010410203a821030b001e20202d03004907052030010764030b000b812a00400e0006611355841d081f544000b40e01c0c43d01d100e0003400384204a40303001c00380c98071050b080d5492140c1940c41c0341c4890244503440303000100526058003500c03048107550f2400110a40c603400c1c40040301c6c103610070024000c07402e400d0040c100302c104007405c28003000790a103040850f80900109250038a1501c21032 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 347057446 1250 347056196 347056211
    0x130204050a03020d0f08190801350705100c0209010f05310207140f07150f020f0303090d08010e060306060607030e041a010f090b070f0c0305030d050f0a0b0f04 70
    0x81c40307514040741ea030f42001b4459211004081030031800082811041c0014089000110b594900d5078070b2078a44c0140d00d41c102c0c0c46110342003208440ca0f01480b4001d042400707950800926501c810011100790800d076618205004081d104110590f8010303000007040403142c440500564985036128000c00504220f00d48031034184502c0c04190b142a8941100c0d150700201d0680100702403d000c0c4040f00000364240c03085468401700603542c8984030f02ca00c840365150007081c88070260107991050005101441a140c008824140c01451075109454807542c039400021515041c990010415014210140141038541000c90000759140000340032580b0070180050340b07804142c0190561140c001c0f014106102c80c16801d21468aa540e0203034180380400c1f183e07450040218800c016403401c1d10000c82115050070100e80722440140c03120482211010040000030012907001c01c080c140d44081c0744004203081c6031201d990020940c0140200045130b040440c04405036456903403003070780001d0942d00040c80300e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 347058696 1250 347057446 347057453
    0x2505010c052104030204060b19030b032b0e0105040e010504020a0c05010903030e0f03120f06030a0c0b0c0736060902070f0c060c03050f07030923130204050a03020d 72
    0x7000c50b01060007244408a2070320001c804080141c01101d00840b410000550f031000d0b071580f10700c0ba442c1140c2196004080c02c03207066019500070480b010001c2c0864a2071100c201c2170808081030503540b5080c0c0e900f0700c00301c04402a80b200b054103103007100b0b281a40c1030516240e00c0c4886500180501c6120756008100b0076907181c420703495842c296801c000240401ca1417418041d004081c0c068000d2124005c900410740c01450000448490700129400d8803042d82e80d141c01c4110303504029010590502410140802050402c668100603000c84042c0c1b030341d07071b0071003a0300c146c034100c1254000464003c0409100110003082d00092542c0d030f00a1014603540f60888004a000b840309411010190b4404580c01d002c0c021040c09420010348541d0005038030300d4844c5810399450001801c020b000807020030228440409002c058580c451003420710910880e103e54a85c41030048a801091800c0352901c1d50412510303048032603054800c8a26002c61030309040c42c0105400100c42e0002902569504131110100b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 347059946 1250 347058696 347058703
    0x144c02090d06060b070c090501050639070e01050108040c06030902030f010f060905060901050303030705070c03050a030c031d0901060c11030105010603021902120a0c061e0203092505010c05 83
    0xe902c84000c10000313031582c2c002c3d8802d03000b80c0403c0da0480301c018004038440380c2c5441040c2c1a0380707000b0480d500741070784a09000c0348901c1000c40030306051740310903c141e8890600c194214000000c4409440d451782484980c42c2d0b01c180580c031450401c14220140400702e82d080902109440d00303490081401201d90000c0b0745800084148081c040d0710307140906010044503846031081e41c43c004824072035615070340100240680d087c0241541034000b003020aa6840c080d0340100a0140325160390035101e9582d4540e00e007420030f4901e081c1e02241c0d000c4904c1c0100760344511410707180910075228604d00b811140c017052000605024260a01080d407211809228032180e004140080c000c000b0312040d0f8560b40010b000c0c0d00084808402a041d08881072865800810b4041803a4031a4501d203041c003c1032102100d4040707503802c007a0b03451a681e5417605103814440348400103a106084c400b507500e0801c1c40f00c840c90001c882c04000c42140d114000702180f483d604003a40e04560303091900300c01070352550400d030b0309 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 347061196 1250 347059946 347059969
    0x61b0b0a09020d0f200f09070807140a0207061b050a02010e0130060803030f271510060207030305030619051905010905040b011b144c0209 61
    0x60321218002c8002000b030604861170b80301180e100e0650950300c11005010860710b496001c070b0340c0030380d00300c0000c0d0145204005455011074a0302e0310810b0043e49590700c403c035600c150588030040e00030342014410150001c51507080d06840c00f02c110411a2a03468040c5c44104c8064000d0400401c14110401c0ba8495400e100b10700b50b9000c1c02c1c405ca640c17040205000002101d420342d4060381041c00008904801005482c41103868540000c020780d030310318845a54950382035940308404105250043d90309010026540081d042e91842c98041c200880c3c0c80700700b0306a82d440b05086511071041407001947c4201683c0d00b1800642d04440c407100030041c0203220450a0308002d402c0b40d8500c001c2070040107005040b404507030302a02c0340c4014a8075030090000361000545264041054420981c03e00007203450b0312500b9501603041540c0214004134900c0c00c0c201400e0703858240c4000c000c200d109503d1080ca4000300100203d6030071013820000c00c2c0ca0180c0811801d091101594045810802c07134960340e20301c0342c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 347062446 1250 347061196 347061203
    0x9090703150807030b060604080607080402240714060c18030f011b122705150c09090a0513080310150c060b0f010207051c150501061b0b0a09020d 64
    0x248210b44a0764041d03030b20b1035584403e41d11410841e0100d81d085c1810001c0303d05465909000e4520b6580e1104259002d0201a2040341c015460500b42d00e081ca41003001c0103110040c48861541d03c910307034200744420104000b10410243c01c06818440e0901c0007000b214102c505407007004100008810000c0c1c2090040d10160380e40394201003803846400005100ca200d01c00e500d466404840e6244d003054011100d561515850380c0d0074007564540c0c0610290100700900784150220743c18000105110325100c4411790704814000401705204040c0e1030500d01c0c0306e50251404c08100b10310310f002408440900340c01080906002c1002000c5442d603281810408003400000d603500040000140c4010400c1c80c803a030b0250344640c580322400790b045c034082200801e202c0050f80148501400d0508109121941c116490914800d96164000042003a0301c044045044c1d540d0000d0b8962400e4000b40005003a820741003182c00342034550000107680900080c0c1c2007013140900191140c014804038a88118954016 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 347063696 1250 347062446 347062481
    0x319090605091c0c0b01140d0c1530200304150b010201090b0406052809020f0a121502072102010b03152a0a0306091a0609090703 57
    0x1260b039140c0007030003000c05070311510b4039a50f650210350112400310040200410b004100401005211518a0745604118005162403000740250f40c6240c580f1078154420741211030030b1103100c2d1000d134004c0417222029040014aa9040090000c50706140d403e41e40c0c12130449940b441905520b000c40740c4022824201c0c0c0340200e03a6414a4100860841401000781d8000ca0508d96007000341c0d4418000c0c01c0300d40b6404011001d040d1225a103480180c80000e00d4207e1820008079880f01c0300812550854000d610200c002681e82d0b80781c0140100c0c4131205d000c41d8018010018200052400c048440030400d8004515451480c0ba5100e200301a1142e0840548020f00c0c1c2510304000313559481200e50018109c2e0005c2000d07041c0304040c1920740000380244041164803000141450914207104400000a0848124181d500e510110f0b015044503070f00c900003c0c5e07551020300104900c5e204150500c4444800d400c05400306100084040c4152200c113401400c0300000701c1c03100b0b4041d07000164140300310b0400 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 347064946 1250 347063696 347063701
    0x10051305100b09010f0302030a0609110d110a06080702030414010e0d06150906050f010c020f09160206011208041202042a02010f020f09190509151011030319090605 72
    0x40390040c00302da00c0342d5441601640d0000a642480084079800c882d40640503002411603501d03448010079505006580754640100c0c90b803804e644101d2075010051141c00000d148a50388014050808504c0e000703582805036850601a00c2500002910b049500b07490b07d40102000d00300040b0360319086525001e811040c6401c07600b0411801e40c0000741c101010344400c6c02c2841c1d641c102c0b50151540751140d603070040081e8401410551003240788185490024040340031f0b5600790070106403154822103009a40714415801040c81c558144111801400b80e600c0032084130f082d64036607800500c654420380c0c0c442c11135142908119104d54000140751060280144401d09400c60ba08891100000c0c41d03230015480c2c180d00600c901040d200f030300e100166160070795040921081c140104011800f031480c0380306141c480e00048035682c11050764420a000810f00418046840c140720719104a005079a00740302445851402c19100002030382d901000160301000307061f041e420604000c140240700a0a5281481e08 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 347066196 1250 347064946 347064973
    0x21060f1e0c040b042c070914120601030f0201170f0c0a02010f09121211070803040203120a090609051008041b03020d060b01020c06070b010902070812070903020a0b070510051305 78
    0x203501402c5441c0740312009000180d171302071600c2e03480203c50003c0894501c107000d2009160002104d100b0032005807030100c0d4100075407219880c1000990080381c620400000b20001c41d640645042a0380c40100060105407c01048407004090000c00075000243e002c43d0055105200350440c0c0c0c15100e4040003048440f1950600001010380d9080c0300d4049112603120b0301503541e40317202e45201c03407042c0c1550900300342081c1d440c2c0310716510142050382c0c14407a1200c840c98458110004010358112074a0304802689040380207484081d0a43c84288103085424212aa65400c0341001c1d6002c0c1d07020f68022203002c3d10b0f0414080541e21078202940002c2c0300c4010a082041035801000d00c034500341c085600d030746580c1080100d248075051004040d0740d03800d80100041760742c54003d803c203244141c1c2100d0500c54901d0340301d04052401c40d820000900312810400540c1482c23a5508054203c0e00b81c2d2a10340181d9450b003950307444400b5000ca4070151380d1800a002c0c0069072100e030701d56541c00010f44074024000b00c1d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 347067446 1250 347066196 347066219
    0xf0b090c04050903090609040e070b1c0c0302030108190615060804050105060f060d0903050409020c01090303060608100e0c1207050c07052e0c0221060f1e0c040b04 72
    0x3550a8040c51400300410381d4048000305681244070300920880c0341c4940307641030101a101182d8071780040d2003800d402240100e94200500076001010070326040041600811400350707001c25000000341481080140321040c00440d206008260000d058521000c25203003c60051040c0c504031600308980001c04280300c1e50202d60f203405140164003e025a4540300700b005034106e1020b4680d60b22480401641c2c4105a454200001180c002d060050500e03640307641c030034144d901c01c0000c07501503551003002c902010b40501c540c0014000754608407203507192524981d012100503009038482001840d00007551085460215103a03401c141300c8100c5181010764021703006030481000040140150314000c079050070320b84c4064461303c141900e4007200e044190074005011a03031898990801400300142409601da584445d141c40e2860f42002103800003659186050607000350074141c280c20f403c8244074403545006c0f800001c0742c007900307002810380c2c4079000041e14910865002c10710802c03011400060130308012 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 347068696 1250 347067446 347067463
    0x6030a0e0105090d05073f0809010507081f0503011104080d1806030506040b031507021612030e0102150103031e0201020c070902030a0605030304081024060c0f0b09 72
    0x380001d2050307407500c4491a840b007256100c8500012001e211440c085552040b00707812040000003841070060700b240390345018103210030000c0071141c0a9071003080780c00c3e8085100c9600070618030003045030341025500205041c00280000c071480d040210b203440c000044034071a03401414024000c00150001c03800103141900144600c0c800ca0189004590300c150082c0e003131000f000c00e142032036150541000829402040d024010941190b80c0c1c000704da6042c1c070100003800c825901c0301d210b01c0061601107002844c12076a6904400501c80b4082c0c100104d020842e10384108507818100526003940010040745000808140c5803841c0303282c0000002810341184143e03a000300c5622200031082da0491080c1c1c21703171103001642e82d450b510642e01000542015405980c200c060100007141140c1c0d41c80009140d0303089504018140d4110200c59001345085208070b10b0a0540c500454001c2068240d100c20306007028031400e003c1c40130001114003004416006940e50031303031000034a5458100010000c4c0d170380b04007 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 347069946 1250 347068696 347068721
    0x10903080d1404152a0302131806090c030b06071202031e040906060c0b0a1a0a0f0806090705010807050a0c061103040510200906120903180a0302060307051806030a 72
    0x500310442c0c038408040c5c01400101500191001c407480345104101c00030350283c00952101c04400c00081410b040301c0243c0f09440ca0081c6000c1045070a04c0205030480b003024500005242c98070505960070707168841510301036500300000070621030201000740e08600c43d103c10001003009905400c1e900e850103070050001c0d100144410490710f038441030300780c1c1d00c0b004a00c8041d00406802002070941c4d40b444e081030010f00c405111a21a40120030045000200a900b00d00e80c8002ca2410902030b03240100840c40e44035809400800140f807800300081d0200d0000340150040200001d040406603001b13002580c0c03c07903400441000103501d40409114540c20941d0201e4550180f04041c1c1019000c6004515111054400055180c1c2d1703412800180b6920521031641c200070240001e5000c50703607050100c0e10816003440510b40c0d40e0a5030540b01ea03400c503007505152003241380b00001c2c40562107510542c1d41c4556070703007849540d82841a039003030034601c810213040c0d034030540020802400c01c4003a0042e0910060 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 347071196 1250 347069946 347069951
    0x708070306200a02030415051c020309070302100207030605060306061f020102090a0308041415030601120f1805070b0c0309090612060403030c0e06030c030a02030606070c1d0114010903080d140415 86
    0x40c8498215009e11540309011410940d5028010444159034010364004000c881190342d40e90b901e030b02240d51031007024a40c4000d40c1010408005020311070203070701d0784141d00b20060480c42c9007840010350500010b204802c4050040008500030318001d60440e680014020b006501c0a0303901d280800199216014490301c80701c0c485010622030501481d542c40d46100c0c4d5007000e00b5660749500440e070000c86550341d003605c2c944510038080000400e1080e4a60310074003e030f4600181c1a40c1c242540340a0066002d2025800200000124404040149d40700c0c480101d4003040ca03074071880005401a03401041500c054040d240c2400109901548101a8403080b03441e014041e20b0003d040102034003084400780c00e100400c01c00684038442c039034015035000314000c00da0b50402c0d00e00e48031003c02d170000b508603035240c2001900c002e107a0414001c0d0240100f100c0500d007080c611502d0002010f1000c2440000d1880741e010640c15610041074104454000c6030400c0091a071401d410a1100c1c0304558118482031403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 347072446 1250 347071196 347071229
    0x50103060c050a092d03060b030609030f04061b051b0907090b1603180b0c06180a02150c0d03020415020d1b0f02040501150e030708070306200a020304 66
    0xb40620103941903103c10351200d101440c40e0a2261074040c1200790200304032241c00580802092845c0034041c09907004100009030b81c440b00701030520f008405040031070254024000966035400030021101a560203142c40c19800702044843c000e84201c049008245004500121284031090540d0f00d00441d0304650f0310140e510307070358800d4178008018062004c40d09004c01103001c1811039801d40c0c400300c43c07107807a20444010044500754800000c58000c2c44403068005404103099404014081e000640d8560132400040300b000d901d90b49416152000b8007039803150707076030f03803000e071000e2060b100e518000500ba902960346000008000303500c68068000c41007508152124811b10009080189030303a103485101e5a40800c00310100c031100c0310705080316840e081080c8000180c8580c01000e000380300081454262600201e03001d814030407101d2209020394000707981000441800280e00c811a42c100c00009a0210040340c8981240c01d035803070400e0340550000d2541040d60740080200112600c0e03030074042081 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 347073696 1250 347072446 347072471
    0x1090b07050f0a14040333050c160501090501060f1805161d030d080a1d0618030c010501030b040b0a0612060f020c0a0602040f0602030c1902120a0605010306 69
    0x74010703040c44012001d41841081c80039030107410b00f400000130a560789410f00f41d50f070703840d80403d5139126580c202d030141d81885811803031303100c420040c401070030360105100c94600004d0b88034075402148a550b0020021480b0f04040c0002035000989080d0000000e0141d142c8413100d03158001040d12a80c5010300030007043d101c1d0a186e610401d8060848503054604403400c802c1c007119041a81c005030b074002000c088000c009070b42c00700200003641e40d0075229080c00d840d01d0341e4414122074007005004106108240910410000420380c02e90042c400100e107060840d42c019160302e18054201003920b02d41c44c2a0000c0144182020b038548102d1050a00c0c01c51503031920f03010b005403100c0d885061201c2c0801e0b992040000c105401443c402c0c1c0300c00c41d005007054002806c1501e01030030302000751001d690000d8103100c050122000c05014200380d000075440d18500189032982c0345a001c40001440c1060b51000c1c0031503580c2151a2000d2030414200c803401d00e01c03420004e00a01007840212200d07403605100d041da0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 347074946 1250 347073696 347073707
    0xd1104200a0905010806132a0f030f09030e1302130f03020306060109080a02010e060c03030f04120513030f060605061b0601050d02060702010c03031107030203041505121302040609020c01090b07 85
    0x240c08060001688140c0c440141405000d44401007072103070642da11411100b5030020031070040c60512349d40d1030304886e4031318034007804854610045031440303801d119201010035000181d44c41620000d4418080711195000d41030300034010b444a4100241c1d003c0e100003050003043c03000009490007203040e251a611500015600c100f810310490007103401c1f40341c4a00242d0701859001410f804060081460142100082400d56004890790044000c406040c0030920042200c2d5003824020360074400e28110100075140450241c038800104021841d518102c01c101058022200401024107800d80720003149890309034070728180300c0c0b0309001d1013070000018192402501c0c103800590040c1801d49041080e40044030b62812586040d814161903690003040101d4034401800134034000c0d406107880d10b050003460002ca000751040401041800d10400464441c0f030000142c0000c81401400788032800c600c0410040d01155000520700c130720104002e000d188044d0002101d40b0302c2800801480e64990005844 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 347076196 1250 347074946 347074951
    0x6030105061801090207021c0609050c01080c120c09040e060106081b04030b060316140a09050c03012108070b06100c210905030d02031c0207020d1104200a09050108 72
    0xc1d03540b0748401000074600303590060280d03500181c210f4920b0400b0f01204040401e10f66012a580e81c0d88520302d4080c00030a10070785500c4002440e0190b01c07810f14401c610020301480ea42c0817150440400032542c1c1c40035680403070b140840e0207030050040c1524500c0058036800e00b48552400303e10142c0005112503c090304040e0301003181c000766402c0c6800d5456040701d540d40240034030f406120345007041c1c8040c00f034100c6c1d00006102204040211195000074802040e06a07440007107014100000d1000744a10f50f010340b030559911800f8140603408034540c407000d40c50031103400340c5000e10000c0c56105100075554060b00c0341c0400e65803009203425158003100c00320740b0010060086402000d0f29021f01c0328429002100b210280b40850409841d84c00081c141821880c40d000036034030000b00941021103510150b080016509411400c0c1901d98002c140c00c1041c0f500000e00140d03640d491210140c0c0d4540c4401c075044280203403d5640c5c89161b040c1049503008074250004200c1c1c0d035000040c01d40c8904620391 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 347077446 1250 347076196 347076229
    0xc1209030601030602070303020c0115080f1603030806030a0c0906060906082412120a0e0a03050c19080610050102071401170606160602031b0304031e05210603010506 73
    0x1110b0b030300e143c0310f40c0001d405c49031048040580800124a05441c24040c2c2c54078415150007100d00c040c0f511060754a071841d100140c800710b402601c1003062518010800c8400c50b505402c0c00070540d6078240009003420a0408000d0614585420104600c401c0d50b11250984000342c580d500c00320b460366010b590480782102c003a500008104003c0b1540103030701d042c01d006944003070002024a544005000d00308000038040b101c2401020600c40ca02c40d40c8800c000e00c010301c09680d03002003d030542c4c854a48840201c0140317401100036484c0b105030340a510807034200600c654000e8400b14100030010300130182080c8501070061040000204a04600d5400d10340146416143e1404c0c07440305660941c0e99510060a05500010900c110040341d20180112a4002d12503c0d0040c0e40b440c000540d2914000607204020365000148200800290810342200c4885c140e1600903c8000c00c03080d044480784a2880503004c480d010307151885200000484881c0a44c030b00324002d20481e6920002c2c480c05100c2c417032002 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 347078696 1250 347077446 347077453
    0x102131403100e1c140d021338070b01080618011509270c080f030a08040b150a091e0c0e010c0c0306020f0703030513120e0d060c050c120903 62
    0x324113051621040c01d118050a002080c000400c50101a40e0009003030003034820340025131051105199590322000e000702c9414080c90016104100c6140486200245185642204296010041b210030303141401d070f01c04110301040da1102d80d4a23458140590341c11101c228009018481101c060140c0c0f826100d071070740160549498039200310060a00700d849044184680600790742881011078000c10150300614401040350310b03048100f842c054400084d00303003c1d0800c0c4510f405040d441500240c0040d040281d101c1e00791100c0e01100c2070a002c01e90030643c001c1c41d00d100003442030a070780c101c1007608968200078003144021510240940c0c100303005c090001a010352456120350b01445038211b100303008140c1601016200d944080490348866102c520000b0003041d0300007050303498003c80c0e40c451b40e40d6490507c40350003503031118203010311080c8000510a1100e440c8030b80b0740f60300900c20b0500f5003086044c0403070b418201c00501258440718071020340f4090f04000010509950b0100d4240803400740c000d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 347079946 1250 347078696 347078713
    0x207240f05041212110c0102030403020f010204060e041d0f1b01020111030402040e15070903060e03070b0c0a030e16060f0801030b040809040b030d2f060a0506030102131403100e 78
    0x226145011000131444c060b40da81d5400d504000e2010142c0060503070903000580d282402d04000c0d1520f00714a0041c5e00d00e80c0108418040641e00403146146181d0130b8a002c908916403004512104001103c0c0312001d229031082d00c0e11102000801320300e08082c0c2c4100303e0b0094441c900480c241c0f00c8601004807100020004100181083d074020070080a004003070358440f03400c0c20f0406500f080150360903000150703504001d00611401e403181c0d4128210200c002c51400b031250f610400040401009000500c20225600006070b01a410641c02101c40000b500c20204d0110303c21131501000340560000603110102c082c01e518010316865040e2500725006503950b59460f030f902402c80e800303614540c4c0c105403104c0341860551010041342d880c6440540310841c182490700160204028042c540c00482040ca1a48280c4e4401c0491f001b904405125804621030740d820010030301a2160000703c8042c0c082e4804001082c092034005031260380401c034140c0f5000c46c4021085400c2d901c19421035030454100228 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 347081196 1250 347079946 347079983
    0x4092904091a0903120403050702090a0b030a031d04090f062d02130b0307020109050c1c0308060a0308280f0e0409050717010b090117060c0d0207240f0504 68
    0x444603841520350f82181e240c00325080440c0c1440740c040d00c0440128001040d103408614207010b80c2c60344000807035020004c00601c0c2c00020b0b59407440a00190502c0346d03c054070401c207070042d1245e600d1040050818071441d001480c00c0904064950000e4610615100e2025500860000c0d000b2200451072038041d1025141c0070002c0c005d6015a01155545003528030005459119601031031250885400004155045040c0142041215001684a45642801d80051100c200c110b484500e0b01841c1110080e40da400101c0e050034801d8101521032040800d24440840500c8520142115400061854102544010b0b95400400c80030740000c16aa0410305401f81400d0340711004942c010700445588036502c842000c904091000e03940c1b816511014520954104000010700402c410350007840e4402c244485982c1750080600709014403d000244505160420b80660b42420f800100f4110301d0b00483c51400c9103c0e40f908a500c0e180c85c201800000060342901c03425103da0b0b0030054202d0440d14039031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 347082446 1250 347081196 347081243
    0x204080a081b010603060f050709060819060803070f0507080c060304020904020105120a0e0d0e06040b03070c061107030e060702030a060c02010207050a050714030d02070513020409290409 82
    0x1101d2a000700303079006a814900e5000d02032a401103000d081c0011f01019401503100907110010080c4081c0030702c2001c00c000066010308103542c000405161180441050b480d02400780c503a0f544181420300c00458100144250058950500c910800451f001d480e6584683c80c0c40ba108031500c558412003d000040160601660380d551080c81450070320b00d0000006407056081a043da007640c14150364040318039071b407481049142200015410a070325080030f440e00141052140c0e0040030504d000200114030307041d010703440074150282d2040b4280580e413072030214026150040e0031700b500042c0c0d2018005107581400800c0316842c0d80c000d006800e842c040c0342c90342d401600c08890303a841103660805c286001315200f030103003011480c4502c000c0d0403d1803400540c3c2990b40007410941d80300c1c0d080b4001d2110741030b0b0001128412140241d8099100c01d1108900d44001e008550080c1c0c107080c180080e230b00d0500b01802c01c7c0d80901c2c488202c03100092840e00c0c2400119010080c00400c46013141c04000c0c1e5440080 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 347083696 1250 347082446 347082457
    0x608010f090b040b03100609110414120a0f1a16020a02042d05040501050601050c06130f02040203010b12100b0702010813060623011814010c0c1205100204080a08 71
    0x3d84080340c14094480032a01d4204194071035500c8560b15030080c0221800b0b405091084c0811001e0142440d0900304400c0c100c4019660b481d03c60f82031420350100f90038040c884c8541894001d6030460300c00c603450078140000d06143c1e120100c810700b50000210002803007900740c1002e0207558020710302640c0300e6007400001c00d1026481802041c21040b08041c910480c0b00a015010f10083c0120b001d0074140307081401d64102509042c1441000c4c4a20000c82100154013a8003e4410a00c024000501e042907018809044800f9400900000000c02c1c10b0790310b10002d1005149956207802650380d02c842c94400d2426501500c0d484580422083c0003640c41a41c1ca20b40110745001e10040c1c40082da6135200489900f07500941c4251002d2080106000c0e042c0d00c60807032400c0c2801c1601a004081c0c03200c1c0140034090081064044480c140301c00c080e403150901500c40d5a01c00b1088103990f8854000b0b03500e03007440c48421940b5100d4492007801c50038840c02030b1004c03145910002d00e240383d080c1e96440b8094120 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 347084946 1250 347083696 347083699
    0x3030c14030c07140604020603160e030607050901020615030723060d060609060e0d0b0c07020a03050708071a09040b01170712060e061513080109080c070608010f090b 73
    0xd00c9801501586030800460103507080b940075568402892400b11100e400d20003070300300a07400240800026894101c100c0741d2007802695280e010b01442201030325450405e0000303a8040c818070040003e516040740013409484801d800720341c00c42c1e90787c0003400880128038810741d400d504412001c100d90420701c0c0d00140d00e840e545111402690401000c2030b00b40d0003840c1d1010b4040c0d1118001c00103990000700d090003038402443e00b02c403000701c2100840d01c00140702c1c000810000b00c04000405086440042d01c0da010f81c018451103903d030740ea080c003036502c0495005080303490260450005206010509115100c080300841500b072a41d40300c1007000400c0d5504001d4188854206041803000020000c070b0710500c19501c460180c4c06d00c09402404540c3d00740c100e90031101643e000d20815649401411004e5594982d01503030b44c4110030300a450b4404240d100b20390b658240603240c0304101e4440c0207048400300d02003c803411142c0d15201100d0b544000e115124075082d81c107038203008001d41e82c1c0040d4a030100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 347086196 1250 347084946 347084957
    0x240626150609121f0b060313020108060d0b0916080102120f04031e02061605073c150c0203070321060b0a050309011104060e0d020418120f0f0c03030c 66
    0x10303412555402d10390600003401385104440c9002c2d41d00b0416118005a440c41a90242c0c00c518065948880c049901c500c06414072103c2000158035a607082203c060f1254021a5985242041400c5035502c0c00070400c1c080003036544610102d6084014825581d0030240081510030a8840300c10980c03600401410640030032080c2c00781441c00c40310500c4034001410044c0e000340302c0c501e006805184601104072201d0100031301080003101140074003e0b2070b10700c201e07442031210505544003c2200300780100c500f007001d090418070607113042c003003103128410500e5654041030044075840c40c0e04076100e11807590000e0114044903400c0b034288240d11058594410906400921152103a031510501d8001c00d1600000134400401c01c0f050321001e000308001c00f503190040ca4101420b1140c058242070001c51058003511800d40c0317030021b40d62a0380100c500e804009032610070003090303424080d03070b41c0d0070810708407020078002c3da008489644584109650030090743d9800e240008555000c0b009802010807070b004120 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 347087446 1250 347086196 347086219
    0x8010b031012060f0e06150303120c0307030e10020901080c070206070305480a05060a15030605010803040e09060702071802130611010f0204050307030204240626150609 74
    0x128280700d817140418083c4000d00c15441e08880c1707014800c021000b0079000340c00174494522043c030400c00c0d540d04101105145603c0e940c4040c4200c2c000c00030045124a18412044990304e9042a90b00415041c50280c5e581050740e076a102c007000c02441580360094110604215130720101c0d2103038010740364200d45171859900c0f0b0082081c2000209240400a132220b800d81d09401c0a103c051400c4403007000da10001820303070110544c4540e030311004000e01c003c0c8140d403184e006030009503103246c00ba000340d980400100701658494007560f5480c1c0182c019441462401004100343c2d84c00000c842e4840ca51300c0d40144481c03401c20604c650501c3d4600740b207000594082c440c1640d80d010311011800036002d1684c030030300c04603120350300c0c1420b484105c0c1d90040c60301e10400c0140703c0f0361404a07441d01a65016078001c075540380215004003005544803e07001030500101c0e000704035654081000d13040d5500d020940701041d51000088000008281d406200f0303006580d510010a042103406080080001000c5140c1079 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 347088696 1250 347087446 347087471
    0x20127122610080c030607030b220e0f03180d061404060506030d0c111002030415030c0201061a03070809072d0e100308070c0b180108010b03101206 65
    0x2601c048482030640380e24441080008489821214000d112001c000e110058180011039101c08000d00200c0416445140b0b000840d01c4900c001035180d07101428010700c920030020131030010b040d0000001003d020b824036072030303080200105680318014900071000619804008001c13100d000c02c0c60807510b4580340c08a80351845d00c804030541c40365014800100300d5107440f808140c240040001e500c41405103c0c0f00c060007046110384d2800d04014152000d0a03041c803440700036403541c091503200798030758007481024104041c3c0c0740e00500948132880d0003e0250a849464060030754410141020f07400c401400001c14441c03103141660740103107801050740e802c540c41e00303a004170036850036007641c0c0c0c084900321611400c21882c912000041c8034180d041030b00c505000d07000e40d803040110302c0003400d80d0b14007041410034801283c0600c002040c113001c03455030710700000c400510110071525456010501c0000000703660302940d0122031080380a403002c0362085003401c104a0810310740280540711540c0d5030b05080d020 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 347089946 1250 347088696 347088737
    0x40b03091f02030402010917030414040f0203180d080f0a0518010e070f0803030408030c0a182403060608010504020f0d050c070203071401021507020f060708010602012712 75
    0x568501c2080541c1d42e181c180005400a10386d6442201c0601801c480e1800c0031801000f07880c16601d9403002a0140c40f03e5200103800303060040faa02d6a80d92001003172210b5480f480c06100c48a08048081e51010b030f480810959071200200c8440440b00031f03210000e031051032590311281c1c0c08481101200301d6420150100c40c2103239880f240e01202c41d44040e40911080e2407002c0b03c0303030080c14084000c5185240c030342d50b1002c01d8040034116518903540070401c0f041e1a0302650003404002400c0c400c0c0e0216680d02c1c14103c1041721003c10b840c411582c400380390050b0710b100e40102402d0312180e4a0b003440c180d18282c1844000d60044043d046465810b00c00d40d4107000d00350103014018122084c909031a803000c1c2c01050f050500644c40074815041902c940103280e40c0105803502c801c00310341e0849070031b540d0b0060140e05000c0c40c00f00600c218003946081003006500407070000d05071200c6500800c0851004015401c00d40c0388c141c1162100d2900c12440d074001603408030110700b54002c92610414a01052244041 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 347091196 1250 347089946 347089993
    0x1202010f0311030112030216270603050d08101805060108151e24090301060806010f262a01090321020c0d0c05030115030b0402040e071703070b0c04050303040b0309 72
    0x80b8100304030311040012701072854000040c80c071031810820340c3d15541e00c0d565a500c09200510601084000040d00003140b600040000d204a68180b01c20a0840002500404080300d0741804501103030301140c0c040c11a21034140741c007200038040740c40c00070240400e003c00c0c01c01e14446a0b400b000012805102640710046080302c081082000703034440c44000201400d541c00ea4022058507030040300104185c49103400038100316258204200c095520640715a1070ba0f03032800d042280903101da036440c0070b2600504022440c0301c02410b00841c1c00d246078a001143c0c600c0b46d910014011011000c0b04402401e02901094a4400b041c0100d400b10200c2c3c902052390b1464201098030038100c80d0301c04011034102030254600056008650740d449500350360f036004103a100508040c0c0a00d664082c0c803a102c4030200840310180407003a200b4500301c7c142e13038030b5640d0b41e621103907080303a0b03040d00c45020032040501e0a05540941e08014040d5003010b007420324400540d0002030860f204d80c030450084d812156102c110150 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 347092446 1250 347091196 347091209
    0x40c110d14160f1401050f0a0b0f0904050303060901050a05010509010e0f0307080607020d08220321060518090316050c0d030f030e070f06030e010b06041202010f0311030112030216 79
    0x481c0d40d203a404c2858440e59040b54000d2941d04190800481c000980394066200304009000a852082e10010409096403d1f88c03d6400500110030702050140c0080a10305c200002c4400c0e4519a81341c0301800084904c61041e1400715000b4003102c0310300e42c000d4001400c02c08000c0d00b29854254400002071078110207501192554019100f0b004c29140e060160000808181c1491462030030100701941e030810300545018038030151580d1603c100742c4a018503003003d0480502001c5410801c00f240303002800b440c49105c0c450b401100c0c000070030920703c1c02514820b403a458082d500300a24049903100302a00d40c001180c0500910500481c41d0343c2c0e03a084221083d010380d5440c0038205c0c2019014007241c00e60144090b0503403140204108640e01b1010031400e40b02245404603e40b4140c250f000c1c0502442080c49501c6000864041009680b010306580c54038001d0761b58500c100c45455050701103840b14003032540040c2d82000103010440c500380b8628100c0340320b84101c0c5e642d80881e0000b101c550303a03a0740021 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 347093696 1250 347092446 347092463
    0x81906090221100b010906081e07051b070b070609020604030f0503091e030a03140f0403110301140106052a010e0c090114030318061e09040c110d1416 66
    0x1110584420418041c3c0c843c03601104104540320070300040c0880c54984943c00070400c605000540d8004100c11802c90154903000e00c400f1414000c401400540200075000164002142c0041404200107610700c1212003080c51035240500035110300001d0040c0303480c148c2e0840d40c1040000001040c000c100c41881d8040c130055901e0346030f00300420440607440700040800301c03c8010f038202155408100800d00d00e40c10304005480009454410031280600194407082c45404200001032240c0c14511240d440c80c120f000700705845d01000b08044003203081c010000001c8050200841d4801c103590715110040c0342001c042d10040c0107078692402c3d1289000100c5a46c1c208412170913540c204942c880b0f024040c1c8002c003081800d41e54020036581e0094800c842c640442d9451020055142d40e0121810241c0070105903061002061350b8103c6940700c00c854070300aa20b0f041a11203054450003500c6503480128020707100214310308a0840311000c21700708400381c12008200800c01d903038501050264151090255 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 347094946 1250 347093696 347093749
    0x7050705120721030516021f05030603100c0207150302090d03110c030d120f0b1f020c0d030e0603060312160c2c0c07020406030b060f0102070819060902 67
    0x30780c0403e14400180605921038406032000281d0000c05aa002421110103c948502140009030b8070301780ea66201d4085020300140c00460b1a8000029803043e01c0681c100c2d41c1204014261604444200500c400103820051080c0301d140000d14174802046080d240160030066a040018064044040114081000000d241003185d00610000690144c11000340c1010001000c01030b00070b1002c030a010100079903a04c04509440d4240d88814140b02000d003c0e48189442800329404200400c1c0078000035100d001e05445591506440014050380c0c10744d6164400011072040c0802900007034032859141c05040c0411504400e4900540f0410304040004105011350b0b0915640c4900d15400c0b02c40d40c4c0445543c08088038040340010040107142017540146503458600d000080d01540303000035446410400c001051040541813580100002c03261618141d08010040e65a00a58801c0d000140c10858038103035040b00d0301720711100d4140030310400704221000307a00050b00001030380415003051446240 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 347096196 1250 347094946 347094959
    0x3010b04150f02030a050c030c0109030512090604120f0e030a0516050901030215090612071d12061801020f0c07060e01300e1009050f1203010902070507051207 70
    0x84280441803814100182d608068009480c0c0c400e9984138418084005081108541c0400403034860440e070b000200300d1021603240c02055548140b03125040da01102c00864801000840c0503070217542e021203004040501554142c41101d124140c081c240086981041d00a442c103201202100d8414805054040c41600940321210015042180245101e0b0018001600c0328002030198a406e001030759200d079400c10000c0d1561213a8040d1038034446112003030008c0c180d0840026150814524a0000328910f02c0081c0200a0b0090072041030981c04100030800d980720300004114805c440c0c000140c41d00c100d42141950075070111070b941c0c0301036010040c00c02c60075a100701c9030003041d0400d00e00142003090b180c0c0611560740c4021040c3e81c0780c100a4403010381d44c20b01a44802001380c806000c1d2220388082e43c3c030000c000c106005c07060303990b4010441e400550400201d0081980d144a022090071a400c1c00c4000c8001d41144d00304891350b101e000b40100d015510429103641141c1070703100504d0031904000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 347097446 1250 347096196 347096219
    0xc0b1003061a030604020d0602040f030b0a0c0302090906280303050c06060405090d0e130513020f090c070f020f0a030c330804020f0406090207140f0601050d06020c010203010b04 78
    0x92900002c514285071480c140e60003080702904141c04a84001100c0114100003000b0320070781c0d0040800e4604100000108041c0c10006807007a80d48200030000301284160503416407080c020060750020710040055424038100e0200302c00c07440890088a140d03e00c2401d009100846608242c0200303001044a050340101007000c1c0c0d41c08502610140858100190b80c0b6642d0f40c0703404813541c00e119111207010a02c0d101c464501404011f0030000780414245400b40c1c0c4009100a07606a02801c69401d0b0380070541003a185c0c5034020341c06448410301c2d141c502d0700c030031151441401c02280d02c403448084160050343c4a0303180d18041c50050701200c1800c1c0c80c0890b0014040740d208a415071078003901d0004075031260b0701800401c20f032003a41000100d96031a8400039a95201003014680c1c032500d402c070b000c600341c88207501030108a0b04c02d8816000440001c0c030b00396920070020022518540c018001031285052100e18000f949100d508050700b0031502c1103405082e40c03c2601325040c21507011608201400d0fa030b2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 347098696 1250 347097446 347097461
    0x60f0e0402131103070c2109060503071803060f0e0606011d010c1a01210305040b090609100504060e0105031005040914010f0911060a090b1321061116020405070c0b100306 75
    0x1038513401007800e00b100e01030408e41141c070542c4280040030001490381c85c010f000c0030821200f180701d901d406548a2030b0000040140c4090017444034130b0f024070030000e01400500c1e00c0c06000e0584a1450070121100e04500350140301c081c682c100200d24240100165900003200d1020711030b00c00502e0a581011220109000074104a66103013040b4500400031940000c11682950740150b0865514030202020401c00c1c0b082c3c000c516003001c410100c51458560100281040d0344c910b545904464914100440d1503001c20307640700c041c45e0079100040203a49401d62003903081900c0ba28032403558191250701c284c2100c42c40903c0c10700349926901401d08000c5c0780124402c030420100c402c10f082240c00180207160070342c14024042080000101594958440702c081001410b0101600c1510610b2516540031a400c0e004200e030341c80c0c182069904021080c10954824011110b02d081c45002a0340800c0701610005c1c18001c248540100d0080104001080c00c5100744178150200000310300d035152507401c07611394 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 347099946 1250 347098696 347098733
    0x203060601230313050d0305011e050102030d05041112030d0b040903020d0309330501080d02030d090f08040603020307080c0301080c150c0102030906070201060f0e0402131103070c 79
    0x31240d10030004803000c0d40441200b00e15030a21610303581c4107482184002001207014006110b11b41d26129901e6258025605a9030b0300700548045601c20200c40c4002e9425000f200d015030030910070900da03007581d60711403135125014455043c54001c01c003000c50345032503409182c04800d40001a003d401d825070781c01000700d040b1050340c0802a45041da10300a46035210740c403000d400c05480f10410414800a09002c840307002003044c0003103100356a035001c08242080c110590700c61600740000001d8100c40412450306040f20f86c0c024510301404200c543c40142801c080c100d441188171070203040415403030801b80c030243c4501e440060340c80c180b14801070516030000f0010104400b0400042c06a4034020400d02455a82035031400c1c14140101440d504a000d1112010025071000c000c101080340f00040440c02110280c000b004ed254540c09141003840642c020304181c1c0e210380003c24018201540c0e03401c0001c603480302c0007590000ba9185881c035648103442404c0047c001000e403900b4000590340c000c0d0b00a0740d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 347101196 1250 347099946 347099957
    0xa020106050102150a1a100917060f07210912030f11040b21091c0c030813080d090503040f0905010312050a0c05010e1e03121501090306050a090203060601 68
    0x584c00702c20b09540801015120307083d45541d180f07120401c01e5407006118104c02405004000030803203006001c1c0d65688151204410001e8440e0202600030400707034050020044005c0780c0c4e81d40d0480c05d40f5022038180107105440040f0b140038610003100e11030f15a140788950150900d04080c180c00805841880d9a40d00e009413a1a0300040c03590a9001224111141c02003440d0721068140f4104042501d03102100128215440c00c2000c40800491031440c038080e0040d048a03400d41c1c52400715000c00c0c0f41310000740071907420030110302220f02c28030094495a03c80c5000c5440d083e04c80c0c5508c020f4414518046a0315440800c05001c0700501001120252411100030000f5615588030a0302005081c1c1120050181c0080c00c102003a2054041c960b296400c20000c3c040141c80002c15541c41e03010810761003108030302c032a5103091000e000c8101c1b60410511400c075940f40e2224194141d4400d20319489505101b9100f4000000400e40d0140300d2044150400004a1613060f0040c1030a113100185464100321 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 347102446 1250 347101196 347101213
    0x40f05102016031d190806090f030a0e0d08070308070f0e220b0a1202040b091e2d042d030503040f0b011401111f020c010f0c050a020106050102 63
    0x19030b01000e00d6030140c240c07514040301100070000da8035850a42d4002500700d52100c0220800801ea040a08100c0c1c5c03041d42100d0890780ca002c055900c4240c01c403075410050704100455264070384a11800c0c042d8a2005217a4442020155515403859001e002c00f2000302d02004100911280c0050071042001030b079043c40707054290803d002904040002265082d080d030f0400425001c0c0700c1942c801407500c0c2020b082c0c2d032089600c0c5c40c080d1000c0003c3c680201d108034140b0042c1020381c202106030501a00e000410460035940c00c1c002c40c94081c40043c070011083e40c4443e04140c103000c2c120110580444c2c40d1003050702600303041c140103510005138803002c0c0340700003801d0b1143c4040302c000000c03000d007640510b046520781d1218a05696a41500c0b4030113840420b00c14004a441404041d605070b85480907207a00764006146c0e890702e511342d0028084614010490f107180b84495480ba0000c1411459a200004002c401c02031000c0480b0742c0020100d00085011a4030000650244203820161009000505140 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 347103696 1250 347102446 347102467
    0x90f0503070e0a0605120a0501150f03020d140d2607050909071b0c05240307030b03070f0e07080f06030606041a150c070506040e040b040f051020 64
    0x4100500c1030000b581c15410006000050940c040800b902c00100300c4e540005003031101d42d80c1d5000216040e034030342d4178181b00400c01e0b200070003125003180c0705041005111455034080114010300803c0607a00c00c0040c0c1c1d402c0c0c010400511102c28000c00c2c0741c4070342c0000f5440300c0c00707025184905140c040402c0014001d001c0040c0e00441030f0381c500c03c000c84400980356201e000881c0d4514001b181c0368080c44095400504105017409031400380d440684016904820a5581c444060402e10194840c84030820118075840e00c1f07074102c203241d240c02500b00d0340007540c0e4119444000410740d12003508101c10301c3c24001d1980d4010300ca65007010b1480d4030016030381050800a901e6480190000344a6547c903c00902c0794400204103110008008105c03000b030036926898400a07501644000c0c8443c003a43d00c6c081490315003501940d043c0c4002d000b00d83d03400c0d9211f54490302c80c110098007d03584400540d00c0140001c0c0108000c1c00201e038400342c04200310005004100749540c00030456010301000f03000c4410361 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 347104946 1250 347103696 347103703
    0x8071e03110a1a030615070c0603151a0306100215012c0f0109060f06080c0903160306020909071e1409040903020a02090604020a0516021c030201050601090f0503 71
    0x103403600880358000304114800000e06159882d801901d265448814500b00300004002452040c0002e0300c41e102040c1c84004c0642052180c0c000040c00b0b103981d030354107101d07151007a441412850004410707600e6103903c2d0012001100b690903034505200d480041084414103102c1010341e201d40c55400280824800440c0e8449100310500030b088810750500f0205581d54404040728242a0010000c0e400b20300382881040b10441c42402803032107003428250300150046145c00580e04850250f80e83e0f51072500c1c0e0225020281d0301081e61280d0611800c038264a0068107026604021481070400503a545800814480041c800428031414461807481e0740e000d018247c149110980c0d6103160280740c0a900c9840d07030420780100c01c040e6421500d000740c0c2c2c00070981c00040365440e6030f00842e40f102055a82d401000141d100300c60540000510a10800800c5200c0d0341d80283c040303200502c81e010700400780c100644100240d5605400603911107003803110030750300140e0140182c502c2401050b10141480e020954 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 347106196 1250 347104946 347104949
    0x50609040312020d24062f030912030d06080105010b0414311a01020307080a05040b12060909010902031c02190c0609080604020f090702031c0608071e 66
    0x500c00c1c18141c0001c1c0c002983d04841500030180800c01160742004030511014000088001443c4001c4e000810750901607421042982108608640d40031015824007201c840f03c000d00300340c2c41c4018040d9080b10f079145d1b480d10344180048002140c42d603c24200c15425a4055404404c40c1d0f4134142c018417408000004941c1a603007442d507024500c49104001c0307980b5035813511884020010040002d8a4640b1600c2103903412005000b0520645401101001a200e8038607202c0d4003680c01003000d440051501d2000d4a1100303403c1c1062403c1a5841c40310242a0f80610f41c425083c0040314208001894228241a082103041c1e00801401c0c3d102c0d0b0100303a07030340b2100342422030b0707004410b0381161114420040b16148420020300c0c01140c100710b1030b10390841001c501400e40420420031001c01c2115000800710b03c00d680003001800095181c5c0240140f00d98082d0201c000c600003008211810310941010214000b442540042c1e0b00d460b2180c4a821710304032382c000030422980c0880c01070a2201c4401c0040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 347107446 1250 347106196 347106203
    0x50307060902060d0606050406030f050f0403081003122102070203210421020f0d08030c0322110f01050f090609010c0b0903031b0703050a110708030d06150305060904 73
    0x10007001d140006009800307002d01461465041075400705189074000068402c4681c2c948043c0403418012184500f519000c5851200c04903907600083c0c00305c1d1203840d120350058a20601e50540d40e8070794461507a0861441d80c01400708a00701c105603148000420010a055201035046050400b0b42d0300180c1c8074800c83c4a044003418000c0740d02e0325144c2100048400074042107210090701460340201105420300c000040e03120300c0444414001d5410070f0016191050350100e1400d1643e99140d0380744905400c0038001d11491008042c650920702d50040b130000500b8016100300b6007002c164003c12402503d01c4921504010b010b218800d8907403554010785a1000080b90703002d85415030007004868514501d80d015082000003c2400340c00381700400158000c080c0010f0f00000300c0101e201400c110b200d000b8005002540811011541a100e0b85010890040a43c240d0f40001e585071201c51940e00310141181d074203580c4810420243c00e941050103646481800c05022520344035001500701a00104046e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 347108696 1250 347107446 347107451
    0x105120718050d2019180f0b01051c02210f0a02041206180c03150509010902100e04200c0f0a030509010f1803061b020a110121020309010e060a0905030706 68
    0x80049949000c090150904484d054864446d40c405001050b00d1804049501c051f11740300e41e405200c20b1a01502022040c1a1685031070600446039080c5040e0b181301258000030760038850841140e001c8620000d403013036411141d006a0500726440326505401030013140f0040d104100405c40580e00141e0714405c0c0d9000000014216030101802e484400e04200091082c401c00d500071041121500400d1110481ca010811a950b40d0f0100c0b80d088840128010b5401508140c0c1142c2d1544a0000218102d40181004c00d03814000001245100b2109019500e5508003060b030340000e000400801c880e8003140c000411010750191400b070a648100800c00707040082d814031002050340680c40c5128011940000e600c9000d0350303030501c10001d007140c040400300f041c01d9450072000c25200050194001d500607042c0d441000500c0015600520032410034402e102904000355804116440618460300903c000441c014085144113824140028042c2012620301030801020920020079a00003a0384203400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 347109946 1250 347108696 347108753
    0xb071817030f0d02031806010602070e04050a232112040c170a0303050115080a0b0102070503100c02060708090a08030604020f0a030b0103050a06180b0105120718050d 73
    0x1041c114801c440441c0c41505001030310b510580e03100c1d40150311804092061103d04600c034010103858040c28442c401c01640100303c1480402071503101c1c1504507110703004844200c035407170380c451a40c0f00021106c52035680400644d4100e510060010084802c0b41c9503285000c5e6910550034001c034010aa003d101d48040400014200000d9400c50405410300031211205111001700c1259184194072044001905140001800c0802c1845040d40e540302510380c2d000c0da50322210220020f080e1026101c2c1184680d81002071151401c0c81002090b000c071000228144221000281c5007400c060005410083c040c010450400b4000c03d841c01c03803551001c00b07223641e0345820000902174020b0b40035990102000081282c1d1a03a0950700070b080101080c2c0b024040d035074400813150b01301d0744140308885441d0b400100180180500d0307440342070402d1050504d0ba080580b608880700755001c08559007000b040d11503402854000c00003000d8802442c0845591030410f18030303560400780ca81071502d541c0c56070300c00c00403 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 347111196 1250 347109946 347109989
    0xe09010207050a080d0f02030c03191e0b030607080c0f070201031d100c09210602041d0103110609061213051c030b03070602150a06030206160b0718 65
    0x100d81e803032500001180d09094540c10a2100c5138040c101c283c2c040707841c1010494180403240240c9104070321141c03950341140c3d43c2802c3d101c400d40400c1c0c0105200c581d140003041c1e800c5141000070010519003540020840c0c1258281850400094480e5060201e001e080081810441007240d8242001c0c405031600c410103840140c01400324080018140c040414024030341030400600e04070800702520060001c410382a006403842c0045010740b10101c030003081000d4445000629115030b240c0315442c01494a81c1d20180a1688243c0d0010303050340a103000c00401c01e1244c0d09030f106803a40c0c0225005407400c0d52250000345c85200b1500703162001e1100c18000f0360f103130000f2120481d0090b042401c2e1348808a400005408694050604801186c5803030a045054100011840140d0750799400030607290202d02c1418100c0070005100c000050384407038002c0011384070400503148081d9081402102c052107840c0000760510001c0550042009061254000c2d0b86a520400112a490103e032590b4200c4075a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 347112446 1250 347111196 347111201
    0xc010c11060403030f0206070c021c050c040911090c0f0405120307050d0513381e030f0c07050a060b0f06040f0501090609060206011a0c01140601180303090e0901 71
    0xe0580e901038000714000043c15045000e549440d201607003a10401d9503072100c140c85110391581c010750441d00020380c96a0180003040348252850155007242e034900d4500000070309880c9107540c115503984030000c40c60060f00b04540700f075030090041d1410608055800014200340e01035881003511403100a01c900003041802e02c201e030a0340c0e4003c400c1c0d660541010101030000d074030040c0e0040351350030071a400040d001440d0114007410080c46581d812121007210810b0400742d09040404800701c0c003000120f0342802103081b01308405000e0714006807a40f030071504011820600a100c80710160040103007100042010408610186d408400020600c0c001c4c03010511040001107500d4100c4800a808140c11003080c11160885000760b07a03600c181c9841e0502155011031900c0744402590004005000400c11480941e42c110705002e6001c2c181090059800c1c203445001c8201c103203060320f42c42805038950b071100c1119402c09000091146861039990001c011901031321550501543c4107011561750207003034 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 347113696 1250 347112446 347112473
    0x4060f0f051003020f0d0b15210f0d09031e05010204121b06020c0901030605060105070206040303030e0631140618010e0604020f3703060e0a050c010c 66
    0x640081115140c04010b58035200c1c2d0502040c0d116411200034240c0c51b1511540038481c46901c0018102da80c0c81752002e4003011803814040c0c950040d00b02c0c1c00c104400c005800600107404280c401406182c1d020552a810181d041d405841041511001030020a20070080c2281d072400240c0001d10611440c10454024060303070300201d400e841d60000c0d003824000d4484007808100800c207960b09001d0303503449060341c1d10401c02e0701280c0c020300450010400b040083d4044c1e5071080c4181003661400c0095030005e05158082d81044002ca644c1c1c0035030080c0103108001055010050100381180858100a07144161408041501b008904040042c081014003503500c503161001e43c00b2105a42000c1e07124510750b103c80912440c50750b103400348241c00c108000914601868018103044a0300340d40f94103103c1c3e040d0742c40275990b03108150640c05d0740a515810f20590f40c0f043d44000744814032401c610300755080e5030381480307500020f03407116444002150001c94140c4184409081060238540c842c40c00760174070001c0c0b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 347114946 1250 347113696 347113721
    0x109030b18011409071d2203170a0204091b0816020c0a030506240607080a26060f0406031e020d050307051b0d0b07080705040812130b040b0304060f 65
    0x311414403244c4000000c50300d0540d070702034130410100c1401c517204004551045501904040100881c001c101c48189401d00f4954068540703081070070303900411020000c0040c0c0740010115400101003005000c1071291705860310801c1c044d10000c1524400050500c9030181041d400004509504581c4a000300860404404080d015035000ca680b800c1030764071040c0840d0001d05600031a181c003e01515a08140e402e606801400c0500f8450300e0b455640b03094002001210911540c1c02130200109440711105804100c0307016850b406140123420300c0007990900348101e0003982000001d00020f40c0101525600d80d07403452045041c44603a0001519a1027805409400741c000007030307134500b440000700d01c0e0280746001e5544204041d48640c240b00030045600400382c804050756010400c894468400c00b0f422500c0c070320b0840d060030f4540013060b040c0406941c1800c9120400035444103070301c0d800700c4004000e0480000150519113080801d02c0d10f888001c3c001005155603c1140241912992100040a28 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 347116196 1250 347114946 347114981
    0x709050a0e040311121912050901151e0504200307050903281b0503031b15040b010e0712050108011a0405010510081b030f0709050109030b1801 63
    0x41d6564291049a42a10241c001480b6110140700104000449001054810500a140071100c5444103011424011aa820000018044651070002d4010980500c00f13400000034110428805510303410007990116826030420305040a2400c0a10b02c040200c900944000c58480e200c4141501000a84c0b210013210840c04818050816404005499200e405404a401d100d004a001c0c60704203882000d1140414094100320000990f980402e01c1d40043d07841f03259940d2a01c0308006421034202c0700700510b4044506484d441c1041c010070100d289801a11200044d50a1603200c812520005025810454041d400440e80491184440d488940700b081c0081249585481d02c0c0350203400c1c031400d05428013a41c4d141c680080c0ca840d1299034100c800081c6215170741508601d0655204000074580d05150f280c001c00c1065250741c071801184910282220941a46050a0301404544e0190402410415009030500c0000e09029503281c000c004850740c000d2410000e10381c140500001d40031680b0001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 347117446 1250 347116196 347116199
    0x2010b0109060e12070b0708030a0614150a02010617030904050a06080a231606020d020d09060f05040503060708180106050616060b190603060e06032808120109060e040510050709050a 80
    0x6200c0c8c1c0507500950180d6001d000e0542d5440100c00c0242c81410300503401401542146083c11409005104d10000b9000118071a60f40e11580100746507000854402c41c0c200003840c146030700d820700c11550300c200c91420400c407039410620721a5503070704a111300800f02c00542c550740c800c454101c0303c480040346201c8111141d111100940100d0100c4620606c0e0152283c0400c0780d00c0140085205100f40740e0070b0307451510091030101c04940c0e45048040c01e100b808410040405d040c1c5007444001c0c4152403580b50104641094200d8912403c00b600703059a1136450304105100544c1c40100700c072441083c4814194814403241002001020b001d0001070f0305c4500002100c00103844584510111509a2000c010150360358007030b030744445c00c2110240c0c0d154102040d01c90303003015815980c100311150f9a0381c600401d41156261911036028903107040d90004440010000c1607950300a00c800b41c018500940018181503550310342e01c5001c0c0254101d0b8a0b10f400000d009644100c46010040030001d1031151444d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 347118696 1250 347117446 347117453
    0x519060204030c080307050c21012a090b041e0504021303060b01030207050a02060706060e0f10140d020906031c052205010206011512020304050d02010b0109060e12070b07 75
    0xa5006110844a5070f118100005030100040140e80b07a580e04030003d0010400c100c002c11080364200c1c2c000203040400204108a41d07103092180c0b090116000b04100d440c00900c4404542041d9004180810004045810301c040204902030700c04540c070208846e501107501141c0c41c0244602500015086840890f03103180403080c01c80701e0b0b001c030303806032204004050352100118168400c0810242503507120000702d10050400c03000810310603004d07410008441d612040801c402403015924000701000041c2400804c5608540300030007001418803804040661401043c9030206000300a03108000150004405850620001048112021080380030a240d0307040901103410868800c9903100700e01c40b5a8400c00003000c9208207854058008120322380c070b0000160101c14403100b41d50100704a4418070000c0d540903001440c011791140740940059420290000e08445006003102e0404c19160380404c03002d90030082d00039483c903081e590051100055040ca9150400303a03071082003080d1000030401e051 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 347119946 1250 347118696 347118701
    0xf0f0712030b0a0614040302060705010e0d0c03080a09031d030f0708010c03050f071b031b080913050105010f0c0c081204030b0901050405190311060901020c010c081e04051906 77
    0x40b0040711045207581c1c582900701c0351404044103010546004000500141c90b104000c1c01c84144120004986000240141030038148400e0016003c070303030700242d00420036401a42c0c1c82e500c844440300400c00c10303005450081c05952550b04076400391030508021100381e2824403405040458560894034001d80d104c02d4a4005d196802c5903000003440d040114101038205905a8002c0c0055503d210b48408001e10701031f1450b22a0008605000001c4040d10321401c160503d084058028100a605d610160091002c1c0e240012008410145000010320450303810020845031034100c1d00e0658041005483c14400700e45054004101910860b0b405c02c0c1d2403c000ba0040c002d5a116025000c3d450301e85454050a07904240e41c020015007142c100e1180100c0c0d02e500520076140a4903044c00c400c036054000310304024098a0303500d0349035000601c003284c1d890240070300c4800858900e00b030030051a00058903203c014203600080d541c0380560001c00d0600001b0840300c0706080f0320420b90b43c444041352510900 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 347121196 1250 347119946 347119961
    0x105090907110a0c050f06040807050103051e13020112090b0f10030b15040e0a120507060209060a0206040308060d0206070f0c080d09030303061d0609040c2d0510050f0f071203 77
    0xc1401b201d102c800050500034152800c4851620080443c241490015406468020300288000e40c0e100725144140ca2600d2606008104902c0311003501491400018070050a0b103032010705050501e20044001906030701c5c080c0d4000e6113501c501185841784462500304800380e81c005402d49641c1000c0c05031030b41403007610a0020108071802c10040104280c10350302c030242c42c0d101502035048401e62404940c01000148101845007000606e8507015900040c00c503048200a000140d200f44104010190403001558000a040701e003003140c8141580011003511a540c1c0091140d0f9100c0e410800b004a54a101070180120005071004010420402002c9403a40d00c4143d00190404100040046090b19a940100051f622074442a904c42040c0401c841000c0e2040302d226491090021314012240c000340700c0040c0d00b0425a801c02d1702c0600c01070803404c168104a1084039582c05c2c404c0c003142c1041c00c544160446030005500c4042d402d03449100b5000d410000350190740b00701e9403914580c0d4554800300 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 347122302 1106 347121196 347121199
    0x30e010b041404020112110406030f020706060605190e01080a020a020c1518120c0d061b0305010801150303020c0613230109140105090907110a0c05 65
    0x14201c2d100501c1d2024044903003001e1004641c1d000380b40890740400c200090117041002d01c0038865a10840c480c5105042d03403070081510503606034050f80c540c250005401c105403030342d8000c042c045500000045218170107041b5080c00e11405241c980c0301605040e5202c1e2100c2d40c581800c0d0f40203501680a400541c411020300d00c2e501d41d2690261500742d44802e000c1c030740303400303034090f0110807140c01d208124800c842c1988024003035040001c01c601020402c5518502450303850600000034501900c1da030640c408440da080d542c6a4040c0c102e0750494070310300000c00080c84548882c00701c075070f06408000c4c0142c008800c030f00d4292809002802c085100e6004800d40365580c0c00c51070715040c0c2e01d079541c04c0079030050038143d019940e00148280001c0c03903500d03051502e05804500080c080e104424541c2d11032004400841c1e81d49110700b466503600110182103607005020b0b810000c0d03841040f449080d = true := by decide +kernel

theorem cover : BRFrame.Cov 346942446 347122302 := by
  have h0 := BRFrame.cov_init 346942446
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346942446 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 346942446 ≤ n) (h2 : n < 347122302) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
