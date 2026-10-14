-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3484
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:47:47.606412+00:00
-- url     : https://prove2.me/submissions/5cbd4149-4ce9-4028-9547-703f945d252b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 626438848 ≤ n < 626618705 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 626440098 1250 626438848 626438851
    0xf070302070321030e0d1e0e0a06030f0c17150112020c070f0e0103080307080a0b0a09060f08070f0e060d14060601031a0d06020d02070f06060f0f0b0a0807170f 70
    0x3a5030b01441101010340490703484544c2d440025022407c503103a01c89401303101c04201c441034103c901d8000400c0b102200021034403040d580c000004242c0c1e030340380c006219406005108086041c1c0c180140541e40d50300c4500b4038010018041e40c02d100b014400303034a16030307c6082c050310703986243e007029501d0740125482d4585940c018402d0140040c0000000200c900b842d00d00b15040b2600001d1050070750752000d0083d51142401050b24240d10381d101480130450761803400d40e074050400c6000c0011418180981c00005000c03d170440711003507001a104201c47d0300d10425001c240d452038403035001c1544681c5e003c156880030b40b0034002c2c9005040c0c0810b0403e940c000800510500b001d03602070190742440c0c00c0a00441c1052800560403801019011021801c1e54000b801250100900140b50090545078403030000d2001c40203c40103615180c003002801100003074000a068070140c3c45610b60b00d080003030003041c4078520078602417106c00400604803d000c2c041c6c1120300c5c0c0441004100742d29002c43c000c4000300c0c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 626441348 1250 626440098 626440163
    0x90e10050f010503010513080d1e020d1d070f03020607020411030109090b0c040302030a0f141b0316080d0e0a051c1a0c0a03020f04051909050108030f0f0703020703 72
    0xa028001840d1494595078047c1c002d40140150346007500e183d0040d00540302440c8070a4201ca207000d82e43d141d0203641e200400800000110000c0e1403441c040070441e5007544d04140d80c415501081050042000310352065040303a0b8100d64240e030b5411140702140107849c068a84021611000c400003c00201030313000072010354411000c0c0d84c09503480806c003d00c10700403030001075010340c8404007660001c0e80e03015590030724030b00841340700d00d45110420400307142c5103c01c180151544c0080c2c1c9410120f0808000403603601c5801c2240104c0c032030904107030950300e16800c0901d0081100b0000100c10036120a10440c3c0605005049090400042c0b280382ca1040000340e0101c03410300320b9040882d00c02e40108241401003691a0106217044101001100a90050840c844141c5010000000c1d180d840c0f000400070380d411100030401e0f83d803411000320111036050748150312a400c104907010310301c1c1c01c0d4012110003a0500699907269221801c3c228035164041e08003c01120b01540c509030f00300c4054500145081 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 626442598 1250 626441348 626441351
    0x50604030909060b040b09030109050f0a0b0612030915210f0f040b011e050306041a0f09031b0a02030a030305060316081506121504030e010e0a090e10050f01050301 72
    0x19035611244007111520b00c100c80c1031407810b004c2406007a01b10310007403e01440060003c10303103074129212141420364000c0407801584c4020310030800c0001d40084154800011900100348126109850380c41e845181c46051003080d1401003001c083d40700c0410b4504030b680d40740c0003901041c08820741001c2c1c2241660b46c034910180441c00540400c02c180445440b59a12020302031300740c1d1808407041190080a000e526544140d40c5010030507403000c1007070505c1103024140003442e40c1014952400314440280842c54525a00c1042000c07142000084a4458005810034110400350402c4181000c0500d0402941806408a41d40c103059068000701e01410b0110191544045545488006408140300d40c1ca541c0d00080d20703500601964811050b0b01c4103014020107010100c005149080c00022041d500b85000300c04140001d0640c080b038840c03424403007070038110030141c00c110008082d00d811740b00b064440c1c2d0721150045619a8140207541e00c0c0405510207100c1d5081c94000d114035104240180740c040d6 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 626443848 1250 626442598 626442617
    0xa080c070b010e250906080711060c220312080c0c03160204060b04050109030b09030c0a08071505070509040c051303050f1002040e04080702210102180307150806150705060403 77
    0x31400c5000c5008480c80740c0d15040b17051454290306031040c450007411882030054110b402d00d01d010080c003a40d8403c1600c10f0356603545031a003001201c1d28940d03246900d026905550020b00002d4030042a083c2182c40504140c102542c5039030313105113184500c2000c030340107010124401c1403422903001745600d01c6100700d50500010b41c441c2c080340000d02442c440c00e8005032a0030710070000708601c2040990400d085009032032410000210591419080c40403c071041d4400260300024800c8603c07106a9445c00785005020500b042d40700205240640c0308240d1050380d49030341a508150044080b600390903410710300c4406499490400b40c2e1504209142c015090041481d0b00014141c10710031201641da80300c0c032007505502c6a85880810f03400800d0220303013090404540200c5001041040d4000340346020026a03148041c1100b51102440450564042d5000f2201444000403003404034090312041c0c50503029a070341d404c0c0081c01d043c0b411340084442e07085c00aa0801800808641c0c9480b8038000d88420041 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 626445098 1250 626443848 626443891
    0x21c051b13051e04060b071a0412050903100614090a020c1905030f040909111f0c030903080a030c020d0503100e04030e090a062303030a080c070b010e 66
    0x500c255078420650205100d0300380141d140c000380b481041c8248a1040410f0081400070030100c0c1c2e0745401c00c1002000100c4c00204101c92080c5481c5906251032210000d801c107a80c8034180c880b0098848014800085072914250b21301300038505000c0c600d0340f001d00140341d032611400003a59900c00100d0045071268001a46030206000300c0d8416003108000b810020000c05803401e481c0030b00002150140010000401c0ca80f48040c00b420141c85071807000900c4c904580303040340c9091000071070b607070080040103a042c40800025055440000490600307002d0280146412140c1c121560802070840340040750003280b840e4181d00c0f501a0706207a03000c890081c6600001543c4901045400340a0307110300600a012241c200c0c04260f400c10b1107030904041100c0c030b0000103070310030008683d10006280d6034081004135413108120401440c0c805008803d070070201c071012940380d1042503e14824022007002046401050744100c4180b181c0089a0000300d5841b400202c0c0c0840c0141c4107180f0010300030107a80b10 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 626446348 1250 626445098 626445151
    0x3110f09160e130212010501111b190306180309051e040207110d0312110414100c080a09152c0a0807080303040b2215021c05 55
    0x141500880e803907540564403100702c48050000d11441d40100c2c14001041c03800e80f40e8006400c0a04115255070695814140018807280d40c0c40c10112681e4041502c4180c106941205644081c4060721160096401c0d02e890066038002a80010306a5240070390281000c100031440d07250f5648640da8441c6815610350421643c082c5018003940d00030b50019108540b440c00d54000c0000902ca0010f0f1072410544400060210000c800140c0104d00f1480211407c02c01e00d00c24600c62103088402181094104410442c44105100080d4000c25181000544c0c0718090002d14081592084450303903a040490702c02481d04405105030042c503001d6032001c110f00e901441707000030700d0040010b80c1c24412035801983c2802074040308841d6048001640b012880b0a17047c49a00d014124400003555079007404d03c1c2c15819918000c0c82c02481110041d80507030260002034544800c0e0350080c2410345640d001414800007840307544008900d0310b100100c0c50303038600029004688200950f45c0b22249815840070701c9035 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 626447598 1250 626446348 626446351
    0x20114010803040509132d0b07210b04090b0403091403030f0f0a110d02031b0c0d0311030f16060b09072003090a03050105010f1d01030b0c070b0103110f09 68
    0x29800406a0000392050300d4001040b4803040c0216060f600040d106080c0141087c503500e440c40002c000c1c420b100080c01580340740b00d42c00c54043e15141640e030400c9440110320751280303c4414012501c3d909202c2140d591604074004003508220440c04074200b134900a0a1141d0303e00c02c40450811600210103a4036010043e1608401c1c0d540301c05182051140c90040d075540841c03800c00c14019400c11241211000b004444081c60064000750350328032140f850040084c40c0c2c034615210305d0b40301c480b81100b5525500d40c66280d89030f0500340000b541c40c240348941e045001e0480b0010b80040007041c00990504120300130003186000d2035082020141080601c00a281e0440c2e0704008101400303a00004011045518102800d10106507803d24100300002101e207501d80d0300c00d0b91943c0d115070050006c000c020385c87c80d00504104055889060313026105402c90f07007051001501080d0071000041c0412034803c200d074074860340f0804843d055a124600044407001e010603560183c2e200c1d0080d602e4078240001c5c0b59 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 626448848 1250 626447598 626447609
    0x501090e061b0702040e03040b03071d1318150c09080a050709150b0c0703060509010209010e1e0909061605030f04120908011506031811120a140606010f050720061902011401080304 79
    0xdc050705603000101030301408000100f40d690380002085000230803040d00c6800180c1c0522000881c4400034034200401500b0203810020f041d400c6104c02c040001c400140200880b0403507000410286140d0700000a8548540e01c000c81c010b00029400c15405808074690080d2441814208445d80f2490380701d9080b0b006508106000c2191000410103614118082c00a00260b0381c42010a100c10b02d03022a00741003060320004075503070010341801140003401e940030004500519100e415454850006a8410f4024102600d0314000f03000d8540e00c01c0c407400480024100c410002c0c408003a501d08284406043c510402000034a0103910314117840d40c1540c0420920b40142c40c17180304003500410050078451042d0005168407480f0780c410002000c120b41b40216021250261174141780c80000509004101d80003101040342c100000f0002400082040141416860602c61850052404545984205051400d20283c20010b0861036581500243e40f42c0d440c150681d0410303642c815a090b901d020b140107d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 626450098 1250 626448848 626448859
    0x200c100809030d110d0915050f28110318120c070603020c15160f08040f060b0a080124050604030201020307080f0d0204090501090e061b0702040e03040b03071d 70
    0x2000350b0310f40035042403000c858044082480c2500c42d44444003264001c85048071020300e1840030381c40784000b034451940c0c082d40d80001c01c003407031030302c0054000c141a04040040400c4c594002d0a044861580d224040051802d0155682d90500316840071a4444040000c00a0301c6010f881c070511500f6603094881a05482c0000e01c90a41040030940282d0003000901019104081d011005260504c011602420f072446800b4006c04403c48000c150382c0d884080503061000324818000007898001c00038200d141c100c580091286018000913280c040941e003e04420341c00c7c00031b0032144010114003c042f10071041122519284c0c2c4030700f807142500a620010307016070004e0000c00c0203c1c0b100c200038100d00c0841c1180615288040c0030400498000343c00001d001c503075038001800048503510588407c0d00100c1d002306100d00d008503440c8184c0d902c644010154a8022510364110744071b82e008082c09000c15003d49407203d4686000041e260422104200010410303000901da801217440b179200c690502401 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 626451348 1250 626450098 626450107
    0x705060a0e0316150507030b09070e010c1e050627061003030f0c061802041d100b0103020d0203090c0a0f0305070b03070c050f01090c08011a040507200c10080903 71
    0x320031507403c518105841d442007190300113403910b03400d2144500c14242514005070481d482c0050001c3ca1400a10210620a20300303d240e030705a81100c003d054240e4800c815201107580b03000c849584a910b100e00030010711a000c1404001d05c8038115102007144000d6082e01c2650706810015500c1005807140c1d007410304149414404244240b0310386900d40414100b40041000a950b08000c0340c80c0154003058601c50580d6410441c50705d40904201074400813400e10b50130b540b1203000c640701c070306900c810307034005a1b1600380c0003035640a038040d6100440c0c806011512454904083c0344c0300c075000c842e2548202648200070414802291001c8241c0307801100601d50542407542c18001d950019100600b403149a041400010b041001405445102d11001044129041c507216400140c607411680e426410801100942c0000043d5082d210074210340200c3e00d500c9100050ba02d00140e44450070030354500300c0501c12660790008a10940e29015150203101080c062012607504200340d27042c4500390004c11 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 626452598 1250 626451348 626451367
    0x3030f200924071407060509060d0c0e0a0305010b1c150c02070302040203271c0c020406050d081206010806010801330f090902030105031f0e060a020705060a0e03 71
    0x81652080d1005035040350a01c0302800903007510742c0281e0412101a410407181104da94824407801e4003c1040341445030402d40817000083d40341c0580d480e6980d41c1940c071146480017601ca06654854004047c14100d09143c89003052170103403c000d04041e005101c80040b07261054210f03e004007036036410404900184a2580000300a04030003541501188560280480565150710040d40a128014880d0220907441c0c2e00c407110104d84c1c00c4280d110742e045400c0102a04941d0180403401c4180c038075240c0440d0003544001760042c8443c1d0045600b00f5494050304003000074440003800910ba4443c0340700d031a6540e01e0011140c26030200c0e000b90004603150010048a140680d41c442d880000140700001c01040380b1902601003070030301845c40013a0040a41e0701c1010f4000000c40040d10300000c0035861581050042179494100752040311030010041120303460408a1343c443c01507014070070700391903040c2081c0b0381d104003a401544094415002c1c03100031400e50041480b44a042d0211716014608040f04035 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 626453848 1250 626452598 626452609
    0x3020f0607031e080402100801083d0905060a0207021302030903190915020304080717070902040308030609150d060c02030409060308040e010611030304200d03030f2009 74
    0x4011001c0c031810f0420300110a2814408502042042d500e24011303283c14010001c4003084d00101d00140070480005114009010400e601c07030314282c0c02da00c1e51601c0400725200900c2d542442c0078401240d4402070030f0031801c0a4001010041c007d0701140c00d99256406a0f0080380720b110030003540005035040c5a43c20741155006168800904410307281030030300c118485804980c080d20300388000b484041041c072030303540380f0170000700b00400b688025428141007103006640c59820f801590349005500d081542c0d82c40003041100050417182806640b00c0307a41c0d1805a007283c01c00d913a0309106581200018130300840b9414503245214000346900341d9000e07251550802081c0310b0401200f1408200004901c505803806484007d600c20311003d0b542d82c0c40d041a0340c2c20880181c121500700261181c0b00c00f0a000300200341c81c0c000c0e800000c81d00c10150349840c1d5103d5012007540c10340d04001810f03842814180c240d4421061303100000c005002c03001c4040035000e0751030030040030010300c0072041c8000355490419 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 626455098 1250 626453848 626453857
    0x120f1e0a090b040b070f020a1e02030307151506030b091902220503190302070e070c060c0c05070501030203060a09020c01021b060a150302090a1a0a06030f060f03020f06 74
    0x1100005800ea182d0326808100703070301190203480030485501400291540b0040c03041c84603856201401d14410a50703a01c220fa240d20007128020441d240c0b504805550701031044481b07060b0301648802010966802c1100607088030320310090513140e41840018018001d005034003c0000c0206071403e10359880404400b080a1000b49039444d0350709005542c2c0c2c0c801441c0102e450b81c1103c903418015035145c42c0c01c051a0502c600c0526218040110049000940009160f01500c6a003481000155035a0004880b000c0060402428441c1407601e1141d22036000504003100c140905c0030745d0500c58461300190300381d00c000d8400361b400c2524580c0800001206a0142030303e654400005481d00722800403400308601500e60201e02d40c1c200f01d050080d030301c4407807049212816103018044142c034030b0343d00003c1c110380e0000d1003400c2044e00c603a180e15101c0212a041401400010030b6144629221800107000700306008400c02c03860314242010a20b10000041d441c101c80c2e0090080b11000e2141c818400541c12 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 626456348 1250 626455098 626455111
    0x6070f050403061d0102040618140a0303081503060117101406060901031506020d1205040b070305071106011502120c0a141009081207050306010c031d03070b120f1e 72
    0x40f010f41304107220740280010001090303240d4980c00700b800c00c928000d405034419031040f110944482958002c0f9180c0140800450f40c1604100c90a9500c90071407980340c2955207100c5a25015800020a00410014218841e02c610b942110004103071521000215003001c4511030700f400c44540001c80394500f11004010040041c540402d0700e44200302ca0b00c808400c80c0d0000405a00018078105106d40d001802240092080c0c0d01840542456152220050b102030421420951980001010340d8050001800118149805c90300c2641c1d4032000d652113281c041ea0102c00600401d504802c0482421041e02d1507440a8406490580384030b52703c060b00708122455481050017140d103070040e158840d00c80c04030024001c4692a0380c07454038580c0c000305010700810100a101041c0240b102d40d9030b10500c030002c400c0c0d05041c200007058018864088000001c00341c5545403184280101750010710501900c4e4844c440c590000641c0c9400a0301402004120746410705d501d0140341c010350642850661981008 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 626457598 1250 626456348 626456381
    0x180f0306180a1a07030b0d2a0b0a0e01080c070308060f03070f08030414041b030902030313090e1b1f120c020c120c06160507091d06070f05040306 64
    0x2d507590314128071040842d40d488080402100300710710b403901170007499070460b42200c6004800d299a640d0210b0114000b2507200b40303402050882d220315400e6243c240141501d141d02981707030407001c3c00007003403c64421075250000f404540414961058601a201c40b203038035480e903802d65a645e40034050007054074052990b00d841750f1000050b040c03a40c60b403600080c00348800903580e52400d0168041c03d48400000e0540254500700781002d041d600d440c0e0341d0030850841c5c83c0229040440e0b00000b86940142c072880a81003162000008103070007254452005141d281c01591098108030454818100d0307a85240341e00480781e10072405095941004807903148030a0b00340304520707408a80000040b180c00000c10f002680c80740309000c45926180301d90102002003100100a4482c040300400c5a038060a80c80216242d140c40408040110920042028241a490800c50001c21900d504400c4045101e10a060b0055a01181c26140701c0c0084800020407500c0d410f24051a680e2035100900c0c14404085661 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 626458848 1250 626457598 626457613
    0x50a080109030917030a03020f091206102301080405120c0312010503010203101e080105010311030616050f0c031606051b0c120706140f010816080a0201110709020708180f030618 78
    0x507542d20304074581c18000a4001d0190b4505042c04c1c0c206e00e4a550800d0b07a04007401c5142c1145406815100ec503070010031303c1c01d5109034640b840c045150030f03010400a1204000811030030209400003019105e04020b407010b03420103036a9101458200c0c0710030784403a56000c1e45030106004c0003040b00c83c1950382c000c940c02121200750351488500d0865070300b0382003180c2c884502c0c440a085440c2c2001802d401101c0041c1d40c2069030034180740680240300d00d5102200c51000400c0218900e01c0030710a0b00c00b50030503c00746040da0040c0d842e042004240c11038820001f803500c00b1414407000100703000d613107100b071045008061032800075414050940110302c08440ba01d0b100c644c140c80001680c0d03642030046002081403241941481c1c9510300707142c2e100010050646e803114080150380b00015414a14940a003402151210028000340c2004540d4000d0354030103000281280c2000021070051945003d8881c440c0c054100c03003000c000c500d01c01c000c50380703605038090000315100404140b90b01c50204207032011100c0340b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 626460098 1250 626458848 626458867
    0x9140c070c08070b09040c050909150102030705060109020c011506090e0402150a1e030c050904091a04080910090b1b10090302060a15030203030a030510050a080109030917030a03020f 80
    0x3c04000d0b802c903c26401c40880e124002e41860b02801c4200015400c00d42d0800c6202400b00780c0502000f803100d1603007a1040c24040c1c00764024811100c019410009072005580c40e007140101940c072441d1a69101c2d843d08140c1c010300c1d0f000c0f00c0408159180c41c0d42c0e40d000c0c1454507070200445e001c041c20981e03001d20001e40201406c503402000305204070103529841004c207019260300842010744c510100074941003103011420264000c00311000a01c00300e83c0000c08003040d081223200601108100201107a62205000034460b50f00301801913810100e41ca066000d01c1418200c84420044c402c40e900c014007800405141103410106042109440049a409030b03403075241001500c904450a901503088501446150103031805810b0f1424210a01e03c0a080e2440c0e0100303950f4812991141c04050f6147e0106240c0300310200344000916000300034244090302c0b20902070080042d2207007100400e44503440014001d0a0440501510350300c00702550404e4012403059010317600200304150b00102c01c0025410 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 626461348 1250 626460098 626460103
    0x41217070f0204060b0a17090c150c060108010213031202010f0c0e0414040305030f091929042406051302090a080a2d0f030305060a09140c070c08 64
    0x2841c02050740072168031603401800110740c4250003804036090108003102420340c0090700c002405510fa80904250b6a4480c40d5034142200990030590002c04485100b101140302d0340a02a806005c10560320a6640c0d004481d00300e01c43e846401c000911002e41c10001b00b03042404000c034460550001040300210111903070110340c0c0c4400940f0208080c924600c4450403c0d10841c80d079008102540c120030f0030b140c1c4002d402804010f05881001c0d140500041804000b071240c0011003074001e00c40075400e280c500d403081d84401c2049071590004811008101c07003d8215200714021780e000400440c22412500302074901d44942c1500c1b450781603d8002c006001c1c1c8646603d100071406181c00140c840c444401088200c015641c49080c090b4810290840811295001c0c4071480c0f0800301079440421142c00113514003030403902c0c050240010f0812810515425400251040d201201c11078442c6480e141d0560442d042c2482c0e28801118001c005002c424880004002140c001c1c1c04d0140c1059842c0c00e90344c03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 626462598 1250 626461348 626461357
    0x604050d08150f0d3801030c141f03050406180f020108180a0f110a0b040e060f040c020706030b0312031503030f0c070501020d140306130b03240714041217 68
    0x845c890484240e505070040d401292030003002c5868424030380d40756890714240c480843c001d110701c4210328094118103665000c1440c10300e002c0440d481a182c51040307406002020200c801362015402d02044d82465a41a80c0d0116165402030004960202c40c0c0c00446d5001c1004191094400c040c6e041103007500030803c0000030240c0304500d210320300c0000d031501e4250214841d44403030041408160900c201412175058400340d4602044091403561f03400c00003400d0101c03001229400601d001103c0c0c0c40542e010800741c0a6980540b001e001c1b0540c52000c5c10f940302140742040004900c14000300d081d1002a01d01507805110041c122424203180d1444a207a66025132501c9403142d0100000300415601844a000e14654904000e02c5060441d01110140e11000700110b01c5070807000440100d418081d4414544040058112128011114403459602d20340072001181c8618070b03000225030303c1c40360b20307652280740f40c14200f1410285003c44500500304180b400300e507014440103100d451001210080c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 626463848 1250 626462598 626462633
    0x503101512140708060c040b09040b06040308032a070201080a060e0108030c0d020601120b040201140c03070b01150c020d0f08030a0c03150b04050618040c020604050d08150f0d 77
    0x4034640c4002c1c103295242c0350144d40308900a800440400240311800010340d800c0715064029075076a6025000090020800300c40c8250b0310070307000700d004010700054a02031803140c031004524200030085d0008422000d841001c0030081028100550700043d44169101c507001802800080340c0c481d200c0001060b0280244c01c00002035101054001d080a0b0401000d070092005001070134007541404d003122820402c0c40e038060b00948840c000318045902c03031044d8407801004406420f0312103041a0b140c90f100e0307103c210180c840f0003101e400480c0b02d00c070300441e42c5034041864035400400b800c1d41d8280b1034000e503035990507640e852401042001213840503000307620644c1c90704000200700c400d4210250413100c2e100f0070b6007542ca000d007105100e4850384c0307000c4805030347d8100d135400c5e210f0b10175001c42c80944104219480c0c003d0f040400000d645a00090040e0040d840380c4140d8607003184040d42220074134021903c8550004480d0400b403003034108041e000c044004042c02c2140c0440d0180c40b924100b14910508 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 626465098 1250 626463848 626463863
    0x9080d0c080a0605101d09040606061103040e04060902031f0c0809060609190e07030506010e010b0705060402010507020f030f0a03120623060912071404060503101512 73
    0x4502281c0d40454640d910285001003000500d04000c042046481d101d41500107220706814003600f44840c0d50b03404582c0340c10003070000026241900d40400508000c4c4641c6000c1600c90200820505010040c0c0381500c159501d01d1034a941c590312100007610042809a80501562040b0007007000e000f041d40480c1103203224045015201c1c03041c002e00042009042400c0e42d00a401407185075500c10380d81a4011400c1c03070003940f20305085c407589002441c90b5a80070b4158803030703600000200200420413034100e0310740e00c3c582022070b079036541035940710311a9002c0281070380c0002e000640150300480c0541607042c00503142411000111010034605070022800c000e0079071180f2045410954080d4001e00d0270007101c00144041c0c0d2504580c0300041584d26441c0c4000c032034000100039151960000c0d91804240200380800e048140c0721040d4071400240114100b0340346204801c0094245405244110703040607005042000d00d1604590041074066002e417942c007820f00000030300041039008456018000c103035 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 626466348 1250 626465098 626465111
    0x60c03010e010504050610081503030c06150f0105040303050a090b0409050a06050102160905130813140301020f030a021614011e0e0703080a0203270f090603100f09080d 74
    0x81080e00ca0380c0581c0710603c00c505010400c001c64503004203011005003282808c41c1c49450320f6000c040f540355800b40d100c5d018071012844104500b0000742071070040c0c00050b0800002a0424140403009001c0078259021400822040000038420300c0100545a85464941442c40d120001c9004583c051b0340109002074a860500c651486c1c0c0d4420031005000900040c0344000388481c05456000042c030910040741d070745800041d482d10070050f40036000c0741e03c0949280d1740c0e40041041000948076000d01c0d90f140c1c80384d41c000111030505100302c3d03041c84d0000751180d00315954583c06c0e5029610400301110070400840003000061801e01894001401400001c10702da01e0060a040d242d1b43c03440f004010240c101700c10126903500224028042d641c2002e04c0513030310400d24500b80d20b14480e101d2480c0e1018403030507107a080301c0c00103007441404202c1207810201e004160010041e8651055401580c03503080306141c001c000c051644407001c00c031001e01c00840c03524050341701e40c0f0300c0ea00116802e06506480740c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 626467598 1250 626466348 626466359
    0x304090906020c0f011a0609060f0d090308010f2601090f03020601090c140306061e070c0614130b0c01090506010e060a0f0e06060904020d05070c032006060607030908060c0301 77
    0x105600f01c4521130f0008204600302a6203030400c00c400151042e0058100103150460380d104c3c1c004850600c000d5296190756130101800540c001c04140030198001030000c000411700e4164002c8042c11102c0c40d20b000301c00926031403c003402c0110b8803c661a010365a4a0380b05001440b8000701e803040b18003075005410315615100365401591030000d001801c01180c0300e5a1001c10440e081034a810450603241c6540328020702483e8100b84088141c6007801d16030105503d0308000703a074000312064401c10b5483c140c2c00b03058102d0044040c02042d003092081d80001c0814065108010060821030380c00e14000300e071500c4662552424080d007a0041a65103031418204040b90500c11003140040580004007000701d032801e441555043d0b409440c0c40c0c800d260025480b5116a1140c05448200070001410041420140005000e030f5400034030440110b031480d001050320360b80c07040c42d1a00b03960031040a4030199030389208205040d84804001c42c18803c0e0017201041c1c06004000051041c0040111344c0d03520b50600 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 626468848 1250 626467598 626467603
    0x50114030109080f070507180603060f02090607020f13060b09100c03020601140f0a0806180304060e090a060306150306180c0905180d120b04060f0509090304090906020c 74
    0x2a060640681c1c14a440840010f64400c100d5501458030254035464501c3c603d03009041c01c05681c84001d6640c1e18400040c4c1d146000e5000c43e045074401c0c901040403043c10100d186c1603010b842611a40301000380121805030500500724a030910b8000c02c0c45400812070401a01299055005030500000205003171200d810080b40a0210001d28100028001d0055030002d5232034605010380045060704600c45103540e2142d030380b4000302d00340041021805c01d0701d4400c49652404100c0f0151107540312207860303070000c0c4008407c9038140d807420f0359500002c0c460602440207841002c1c24038440b5654401002000c2841d510a6407002d18100c440c440001c1e1a5040840984100d45010b281d0150b43c0148030f0001440b0385c418000316205005c0c0032030199213240924184000003e0300d0112805061003650b603580d409080c035002d1601c80c00b81042040d42c0712003400200c0703004d401920190710058006011071310b0022116640825000c0c1101d16068486c48458140c49054034122180c0f038001c00c9008468006 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 626470098 1250 626468848 626468879
    0x60507021b0d0521040909030507110904121b08220b0a050a210e0102041809050307141c0f26010302040c03060f0b0d0501080f0a30030501 61
    0x4482801c02e10280d0f0300da0507120802c280700043c12001e5105241d4a001c0c40c40c0664005200701d0718200710a40d0341c1d05001d842c0da8416401214010000d1000c40c070b003450310b0000a40541d0308102c4080894000e09815189840c801d0f2100d4610604134003030000048a420003045540503245804043c8418554407202421060704031040704403042c44200a1701e50700c4001d80c0e2540643e403504a9a03c030513501d4041c40c045680702021104e0303013810030700c0f40c80c040150018000c880c4440b20742c90210740ca00b0b107918200d030300d04940200543c00c104002004585500142070320703209818103030303241c6500c0c0c00003807da140a20400500866145a18100c14503044a0740040b04800855448010b82800312601009101400f000384101e5444030400c280340d1080d40b003c00940b02d6041800c05c00358445151000d0f0b50040300406804605107000400c1c00400032a8401d810506040140340c4056182c0d0f0f05124021440765203802c02002c1809000c01c800380e250051030b94022600d000407154181208600b54440c0f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 626471348 1250 626470098 626470153
    0xa120c140102030705030a260a05150a03020105040306050703060b030109061e0e0f04061b08090c01030606051804020702041d0d02011802010c170705030d0c0f1d010c06050702 77
    0x4d02092000c02c2c0040100d9218281c145060a01105a803020b00100122260055098000d5000b0855410303400d80c40385000704d074001c0c0100301460b9800d0800c42411040d000090010768240401c10002d0084d80025400c21a03e080100e02a92110792911450300268001c9590580380d04042224031100300040810070282c009900da85401d04440f00c00030f000240c10044240703c600c00040c28000c9551141040c00e065000c0c0910010380c3c14002081c101c0295403e07849806420000300c00380d8024802c4608075a241d84802d401c0038044c8940108410300c40041e9500903808111950060752244941d042e0118620404a000d104020740b103454040e00b800342c41c0c203580c50041200c24480b42c00000f0f0309170399070910301103400e45503c1c070304440c103003800030840c426404020804038100440403000d008441c1580d4020408a070718420121003200002405402190594000e40c52003003c031406a0514001030400032408200f075a0344100701d82007241d03040c0060300144406d411000c1142403001d0ba200c03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 626472598 1250 626471348 626471353
    0x60d0e0d17060603041214040611100509120f0d1b18061d01051e12090c01120b12060114030c041a0607380901020c07050603060a120c140102 62
    0x506070010403e00c3c8030140019085a2062800e491094450819030b94028403036002507071100d55440021340700d4501c0000361859030091203681400d144851041a00c2114420010b00002c528103400074004e80c0000100d4000507000c0101040030301541c050350300040c030840d142c0342000d042c017074008180a144500c040b00c01e40c0d80c0c1404000c0729500c1302100c0a1440b01071900c280f21001480140d4007840346505030201d042c0c0c4080c1c0c01c0040b404100142586000d00c180c8503030503695285a0359143d0300c0301049940880c0004034060898403060340b000300fa4500140148803000c1074138655510b0050260b00c880314411400044200341d040a0007402d00d07020090b6428015191700d024004141810303402094002c07807000c1803810900000c3c60034402000402c3e0030100704c51403c61044d0824202d08034101e141c00000b680801e007000d10500c210f6031848501c1c0c01420000341010101320003580082c1000368442d00319000030520b1134421682c0c081c0984074040c4d00200da8076007031f008400241d80482080c10354 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 626473848 1250 626472598 626472601
    0x50d0f0c02010e0906010908070305071505040f06050a271a091c0804030f0b07030501060f020303040f03050d021c0b06040302011b021f030b0102120c07060806060d0e0d17 75
    0x140d8000586140f40c03401102c100c1c01607917800004803100b0616901c68101407103208800000d02030081280d034107480c4501e413118071a119040301965a0311603486504100d42c1c1401d1704210301071154000e030a41013030601d048032414401460310b01002400064000d146524541c0400c18900c1481c51a0b40051528100c0ca042406000c0000d880c111460403a51821040c540c451080003c004100c60165911031a440c009048900b84020080c20403501140030034501400801c0b03040c010b00e000940f03071030300354021481c640c0d4503a9070101b0700d01a0b08080703040c0602800600c540741c0281c0050308000502008900c851442d24018000340d6038811080c5007c0c600c200710a20160768000e480407041b0310701e12440312940c510340c8041040418824040c026058404400a184550640100104050903401c46541069032603403e42030344181507400302c80d54401d000820100b401582565842500100b0650910906001040a4980c21084044603801800c140c0c0300e401e4000d0700500104610f2a000d0805 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 626475098 1250 626473848 626473853
    0x20a080c060f1f060503181501031103030403020a0311131a0301051014010f0c0f06090b07090b16020a0b030a051b0c0c0402030901090c08070812090a0311030f010603050d0f0c 77
    0xc03141c502415013009000000030310407007d44500140e113a420a000c64030b144800812840f0924001c0c041102c05035000400b44156190000035203060b290020320300c500e403524680c0c8048a044200040c150840403090301c00002c48c003548600340c3d140300e400b80f010303030201d604c00300305400c40b54001e24000c0e13015114041408500325402c12144209400e0030040c40e03607074018000313035480d0010003401008000b42c900a20100402a007100b4007061103000d4000d00c2e44c0722500242c4054115004081d01c01c8418400052181d04036003480c4082d6002030542d5036004d03280c4ca003500c82540308450b11492a83c54000f48210307032044600d9501222202805e003410700e41d90a003205c0c0c40e500074108480c405ca401101260200400791b000001c2c495020500c810303107070340e21100262036000510030813102d07000e404c03265900118410111142c0901c000c210b40d00c45401e556407001c006000480e102d0f05031150118641801d4001d1203401c0146004100070000301c080144010a81301c0305002c40802c0182c1541d03410300 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 626476348 1250 626475098 626475151
    0x504150e0313050f1207290a020d08061503180607210f18030c0201030b03030702060d021305130603020312071a0606090a0603090c0506070b070f020a080c060f 70
    0x10b942080320a100300f085044009038081c0d208504107840380c0650100007400c28034152081e00030442d800c00c0c1c80f130084000710030a25680500103184001d4ac0110845104040c8034118903680700200502c891001480c001c0c00180f160812201400c2c22065224104c3c4510380422460303901a801c0d29142e40b9028000800942e00300c0000e480c1035640d61940300d62880d9a4154010311103031a0203044075400340f0507a040040009500320300907408240350403c4001c140c1004003c81d4240c0390050b000c04d01d070004001c1110020741c0314100d241c2800b608020041826a141e0600c04030760b0514020101f1550700b03500415003860b2414078180340300f030300401c130140006032460341210700148102c0031203045580b5a40400d01c43d1107079030601a4004003044c1c1c0400c0d416015030000a04601414142c20199290b00508c41c80d44504000078210000c0403002441e0b10348a400b01c80740840d43c1c0d10580e0f00c41011a580c880b2560081304140030702e40c003d582041440300703069509541c40709201e01d0403003110030f501e4a1144c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 626477598 1250 626476348 626476387
    0x90309090f02161101090918022d0f0a0816150c030e190305030c0709050603060106020a1b030b040f11040902060a11030408030d1409011109220504150e03 68
    0x42260011300440d1303c0580c01001c4a1004000e000d6040c401c440841da50174041008490381280f15050aa5500d100c03181e80e02000140d00102211513064122044100600f00100381d082a500c0000140003050124091010802c544007541c0c00c3c1000606140701d10b40c40702078a00810b0100302d030400072500401e030300099200001078143c80003400340d074910307007410b5285510f40c1010303100d444002a21081400c00141d0502110360009080040b80c50b07410030140c89e43da0030320503400141d025801e110301007075864110401d140d500344003036589180e0369541e048000c0002c9405441c3c61034404c840d5024400318404030141c29100300e40403c000d05896001513100d00403a00d1840412030f400c82040c400b41c00400403071780500f103404202c94440c65141c580001a0541c00299404103c02d000170a4644005000d00e0250404100d00b03581440107420034009204685007101e03441029054071000e017000c8612400b0f020310b001d24140701000b0100310a550681d4102840c181541c2d00411500c10f2a412050800 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 626478848 1250 626477598 626477603
    0x109140a180902100210060801090b0a020a0203040e10030201032301140f0402070803041b081507050d0e0705031b06090915061b0d0c05190312090309090f0216 70
    0xc081070105546680300402d141031000f504081402c08600403690002084d030144003203081e00340610342d00d90402d142600d0701c05030f00401001e0003c0110300000156000351080c8940382c81100e040503075440c034540204070140c450020030076240c0014415035038540a45001289102010059155419911003100005105101d603446000840c6415595980811808008000c0055450360000d09003501154401d503012a4240304210498903004c400e452203004650030742d40541004140b03031a1415400d1801401a0100902001424030000ca1481200100110803004220060919050620788074075000c6034801000349243c0400240c5e1140b0841d0100d84040d00e880109844180f101100085404880c580c0210003289000f0040500701800400340c0101c0220760b152a41d03404203a072041c8003200050420b0300001c4c960f011440010070740c1c1249510034900b4a012401c850004002c85024140460000303c0c0440c08111a140c5406101c18440807000114603251694890046403202030000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 626480098 1250 626478848 626478869
    0x80309040f0e01020f0903010605031f2c0d030f0204050a030f080909091f050c041707030503040f050406050a06051903110d0c0f0206070e01110f0f0703020109140a 72
    0x200c41c410140c9400a1100c101150001e54561564550060094100005c0035009620b0000c00046502e0002160303c082c00d01c0c144040340300c600401032240038000c0382c3c0d900c0e00c0c025603c02c0d80d01c2c4441c2039403516007055103044c0c000e002280001a401010f4502c000620382001c0e00500082c4501d41c0c0b01090f203c1100d5006491680d444600d1071700050038000c2c054a0b0350b200100f0340070841c1210003c2401c0000349480c101c11064000d150841c00120b5074152203400190340188002d2140f01d9807040388540615105c4200c17000c503641d03603036210326540c8070703400143d0b000391211010030103401d09025500c080c00d0121141172090341400f1000307006000705446d400798100c50310741c41074010780039a00401001040030651643ca4005100b0500900300141d4010000b8502d00d05100e2810b10204407680105281c1d981c0118200b02c1400444400c0078400c5690348900075600100d031098003c218a600951100e000341c16402c0c80d500003d4402604d0354044c89800c1c00c24006804165280d644103000c4d103048600 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 626481348 1250 626480098 626480111
    0x260d180b0a030f02030c130b030403090b0a20010b0109120213021303170403110103050906010e1803180a0807080c13020913060e1b0301050d030c0209071e030608030904 74
    0xc80140c01900f002c000c500344004184030460f10300e43d004011061800a1408006980b503d82c1d40075407200325030117800562890000c3c444501c103c0700a0105404c0e42c50301902c1012101028400011101403602c0960755400c101c2207296040400d00004060a1501044010340358010440803280003110301a415800241c4030030310b17042640080040d68009066480c036000390003552489078014041581e1900040303101214640c4a8090a40b00340c400f0f030064002c9900e00a01c210040304054003581d28102c04809090151604002606441e5807245080ca40c581003401480354444d0240c00c020087d8005c00005d00640800182780384180505441244000d100c1111344002806001003e03035104408500d0107020160507007115007507480340340500c481c41e1201001d002403080504403030315140038144010092460035480500f540340c041c1c00c000d0300c0d48c80390b540003c0040e0800c4641002280506a1210441034103041d03140c0003c21600b0100011350400105c00c0c0d881c020405014800c0f900c40a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 626482598 1250 626481348 626481367
    0x203011a221803020d031401060f0f030b0d080d060b0a02070e100e07170916210209040317060d021f030e0609010b030f0105060609120106260d180b 65
    0x90081c00c940c60b45900040c0003030307401d15009403500329881d80d41000a0804c03010300202840b0103a264102c6081c1e84031350303444c5441e09c02d05032840c0c000c100512046c1561000d082e45a17841d2401d210305618810210103985500344129201129019040140024020700c81d580200b43c0004070142541c0252140b49060369810700e01f60039401d4030780c0050403a0f950460603c09000c1c0c0210a2803a004910107600c1000d95614200c00c1d0b0fa140868800c0c0119480c021040068038018095030203888511444144603c03c1034020500d004e40550b003c41c0003540d40d451180e0b0046a0310078858001c5c0c400c0b1170300941c03410a60006406c80c1200d000c3c244070407020b40c3e410900240240d00124000140740161021441c1c56500c260003481002105806800341c644640180741040c0f0603c3d110380c030000c02d460b080c140400140241c80300041c401002c00e66a0320004203910580c091038a00c0040c036456131440202c40303d5002c3d400d02300c1707030304400342400000180c9407004002012040300762043c81c0c16040e10ba000c2e4a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 626483848 1250 626482598 626482601
    0x1517071a0d060305010c08160e060418200405032e051306050420030f0303010e180709060906050303091003050a02041a130602060907050f010509030313030203011a22 73
    0x1030f48000c00c1c640ca090070070220341d03411040c1c0a1040c03090340e030b08440e289134848054401d420400025940000100000e0000310110b20000e60b01010706000002c0600300c481d50804082180e166684050b400403c0400051a0404c0040840000d48010008680c01044951880071a4404150509460b4400108443c0b14402680c01294104c00144621300b414248607070b40d41c0d14030640103103900c18054010064200090007100c2109940000c500e16840c1801804d90004050010100720203076190303a030442a000c0001d0350161800500c0021075501c3c0500250072284650301c054002d400c01d10050343c507503031000082485100a8200071030380b550b40175100c0000340b2603908040340702c0211a62903201b41e45030310041e02c08480307035514590b80261204c105a070780768411208000c0a5215403000d120030b0620750120048d200303041c18485e0400182800007802d507040a01d508800ca001c0d06810015483e09000b41e400c400e40d10102c90907920200345c04120500c107072007c0c100d00240501610100d51419 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 626485098 1250 626483848 626483861
    0x114090d03211e0b01091203090b03010b0409150803120415090b04020f03060603060411180a0e071a0d02070f121e0e010807030c121517071a0d 63
    0x1c8240c818100602000408001c103000549001c3c0384500705080707110342400788500c0400200c16101c003921070385400001401c10b420030f1f070101e08100c4c6514001482e030744c901002d18042d1150750001502e481c00c01c0641c1040b50806a080c03203841e018104d08000c19080813049803c01e03043d150310801507a4403400c228020440c15150301e42c9003440c0400316400d002b00a100c1034012842100d0520703508580c0000c050341c070351040c1d86003689600b050000c50300084210010311f19841c80907040700c0d078050703d0b100001c60040d02101c05480d0700d038030345180065080b024481800904003c0d00c0032410070b40e260354000301d540141003000c6d2010340d0008491043c0040085026016035121034421483c515a44004002c030304480c41c0c03011449a036040c401d86071400b58075018a0b050043c0d403081210341c2d07840000c07005044101ca005c0309100c1c0c0c0321050214100355000310001360507803c401403041d901d0603001d034921035030030001500b16804c410814803181354003100d0320240388007610442e604c1711001106d8400414070b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 626486348 1250 626485098 626485127
    0x60c010609110705281103210c010b0d02101b05011b02060a0618020906040503070602010207140a2105220512030f073305150f03060403080702070e040b150114090d03 73
    0x230304c82c00d41045030010500500c0c00c6458840280401041a42400003154001000035889040c801002202c80c0c030440880384141e074031848040720882203031034190868044d0190703080840103a6104900315034040000d1a001545000e04010035840c10700c19100007031303903403072010200d83c3c00040c805519a502e00030f44010b000000e054544840c0d54800c00b074002c0d440f224007185d5491108405001480c4041240044250003001c40d900d903800303030301809880e000d09201c4002804030030308c04400001003403000c1151401c0d5008212000c01e00308820450311101c41010b00086a00c01c0192114990043c3c0580d582c0b00d52064100c0710f01915000d00f02440800d001001d0364500d004000041203509640041d4003802d56400c1122403151103405001e22420303401140c3d80c0590008001c5030009118008a40e4880340e036106480c10746c3d8603144007200d80e1800341d4041da00c1d0310b20b41e401e000c122040c910038941c440000b400d114030203402c2c440001142c1c0c092900164881c0500c030644005150140619216508 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 626487598 1250 626486348 626486383
    0x70f120203160806100903031b1e0b090f07140103110f0a181202012703050312060306010e07080a060506160309061d060c010609110705281103 63
    0x90116802000740200d84042d800145000e400300f505414003800214240c20315507513201200c1e045440549494072070144040f0f081460340310b0700e40071402c511044685007904a40b0b6040484850800b0f00721803001510340c00c080e4000c903c091140c1039001412204907020030401441c0004c5860045e00242a000b400d02c00700b41d0001480c080d0100c000e0001c20302213040341c031400c003040303100c8606100d005294040d039000c4134100301004015601620004110460300c1b8940a000c402c807041e1348901c05040d40c0121815880420400e00b0303100042904e541c03000c003e80c014142503140280c444002403000d0400390074003449070042170840009411490107018090310316030745c41214540a91100c040040d050b4001901c2d054045400c9100315000c00541c0e5540c2c0c00d003d0650300120800120782e200c000240410f40d41c6038000106190b43c1e00594001260004d0940d494140e0790801f1410900c0c9580700641c00040411100900950308080301155900465000b02c08050030010903d49200200a0030581e03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 626488848 1250 626487598 626487601
    0x120105010e01080d02060c0f0c100c0504090609091e0c053606010503011503090f030804050706050301030b0f062403160203040510081314060a0e03070209070f120203 73
    0x2102055607182c1225024011540d104000700c00c202c3c1c480409580390450b03180204002c040a4a441c4043c040d0900e010080d075500c43d03a40300f201012a640300c10707190041040032504000d2040503120f2507009052000041c00928600d90320761054080281d030002c609404d040c1c05105103c202d803013180c0a0311010f06904c03585440840c22a035122403c0720400d2070946d1441b1101c02040290200c00e004a4040e1906030840e4203098808001e0540c030050442059a034a038a00b02261100c240b880c0b800740640c80c1d104041c2090700703219013060416003180082c418100010400600c6005805900045404004007203450f03907c005020420b80306200a20003103196174648024a5420007140240303d00f88401100d04600038090b40c8078080c0748182d503800314855200321583c0d8001c5802c0341d402408249408448036040c2c1d1454503100ca54440401c465206a0170000303070601034800d0312109148038004508011059002a081c044010124020801d1030601c46502e140220440c119a044580065443c2e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 626490098 1250 626488848 626488859
    0x1602012d03090204050601020102070f1118010902040f1502060a05040212010c0e0424031b0b0a020c03070504050f0a1d120712080403050403060e0309060a022a0f010e12010501 77
    0x707810042d0080c1d2040c1d2429001c60304d95801442141c0c1401d034000c2c003a01130320000c1c1e21031600214000b0001394102d0a00008511544585252203028002800b00142c807141041e5028a400d4401c1d00021034400c082551100c007181c00040860f48180c0002c00410701d85d4641c4003003920100003106403c11582004003072000342d608010200c0782d054040c4d50401c02142d004a4042c02c901c030f1644111380004500000f40081441c041c10700b420102a50f0038141801e07520114a849035000c0034101005801c1901d500140749014061500180300c1100c09101170b00b02146207103403150b400b420361900195600c28810b07607150a80500e243c00b101ca01d06854440083c0035440c0d45950042c401100d82c0f500d040c04100459010382e01040c010364155844070b003401d0455480200424902c6c032502442d200501085c000c40c4d03645001011102102c0d8050714046c1c0b4581c08046810295154601e560404125020103540704c000c01c600c5d4158007464441000b0507800b001c9807001410281070040ca508180001c2136 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 626491348 1250 626490098 626490101
    0x9020d0b041b1d1c023709050606090d050a02131d010204120210030b060d090302150c0d0915020403050c030601080d0206131a01030b01140103021602012d03 69
    0x2420400c42c0c50306004140344a00340c1c911812034101c0b0540c451500ca011041400c82c8104e20011988080d1001300c0d074015280c800700d040d598017840d00c940e8004031600d100f1440e03900040c50001b8080a00d05000904044000803454021a040c29001b058201d40c0c034030034402e0401a1100494015040d9240c540d041e65090010300b9000f003080b403140070b4915103030103202c0051081310b00300c403e1346d140d61006101c0c9030300704509001102e41031800c16480d9020076441340d5074036005050040880348002803e000e14507002c0d04002c8c03c3c41d05410010f4403102000007282c0000101c1e180c401d94070340001100c14961414030b11108204041d1484a84081008410050001403952039850100c0444e00544e9982851640c1c82281400607401a085000401d101c03440a10144100b41d114501c8110780185103407526802c090700b40c0c030545011140c08010024190007015064031100d0030300e000d6160042c809080d104018003804000e040100042e5811001064840e042c0340c000041c25005198241c00703c001130 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 626492598 1250 626491348 626491391
    0xe04030509030a0b0f0907120b010911130e0609090a05070603021c090501020909010e0c0f070c0806040b0105120c220605030a0308060f091909030e0a06021b03030c060109020d0b04 79
    0x1406c3c0c80380031800b10b080308aa206880300b09038812221000c5038282100c030300242503410340d041011001030162500840b807000942c000f401003a01c0464541ca405010405240c8001e402040c0a800400c20301d0042003001c1004001c3d2807040c28050303030b02d40d00c00300c18445200e11071460029651400c00f1000070003038190000c07e00042c00725044c9103142d0b210304a0507890340c800d9604210200c401c0040d10404003010015014090054000009960b82d444255043c2030301220116001c0807504010b0045103401210003040d9901c00d001001841c05c0303c2c0100300700110544040929000d4142c0f01410040190040401303414081e050b504841c045240103429290191451840364a02981424142c104a030599200d5890900d46484503580c0c1c1944200170000c4034070035000c003c00f06c103200e8001d0301c4009154004191540c0104080e0074060105603008c0580c1c42070520a030010007405892490000d09141541c903100c40c0142ea5110000c103c03401440c041d10b003107401505000c60b0223011a44241c016 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 626493848 1250 626492598 626492611
    0x60b12150907170604140307080a0e0a0f06050a031a0303130603060b0715090302340e040803040b07111204081624091a21010e04030509030a0b0f 64
    0x141c1090382c031889203040400c40304500003d0fa0340002d00150100e80c00020078500850040c0036240f4100c0a41c8035581c803584071902c03490104242e040341913514144045c0b000300520b0006004081d59080c41001042442000c2e81081056100c01c0c107410940617070700ca500881107008007180e03a46c0250444c031214014140c450310020900c1d00c80c0000364569200129110150300c00c0c10040103d0405001c1e0000f441d03842c0d415001c51160b00c5e145035403c1e0010180c1864a6a1284101d613024007402d4034403036003040381d048112140321100501000840e14130549801c00c0d4003040340002c603500e4941c100d80c81c1246604e1030000788201c2002510360410b0000030800d54a401041ea115208083c400d5000a03c00f03200358841c0710900130320002c125220809a900740398542c134100c100d25594a2801051100e150785003a0082c0e4001900c004100780700c0240065440d04c03003941007507580b4110001c4080d4400600240912400240042903581c090159820855002850710b04504105e807511040d0641203500 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 626495098 1250 626493848 626493853
    0x30a031e09050906060a0318110a050103020f1b030c01050f010609050d150f09020a0f090c1107030b040f08070c0f09110904110408101e0513060b121509 67
    0x10388031803485100d0351026100e0181c4034101e941c440f81c0500185a200c00e0b41c6004142c0d0714502d541d2440c11000700318003558052400312114106100401203985125401581450f104001042c81d00b0003600690300d00103212a00d000594000c000e2442c254481d1211051a552901081002204602586074182c4089640340302c0c44031707224400c0c030480400304074019040b000c035528036080890880d045540c600030244404104480140c0c04916074400a404c51018400912070034041d075040e074031908000c003e00d4507054805140403080c190316003000380000b0744036140c440d00041c10300c04010454a94070350300288603030ba98130f46410b02100c60710090040c8481c5000301c410000308aa001d01441d01d6000005024502d03040c43e20041000905500103210b0006030207000020b5030800601249890a000e0400401e080d5041090000a408080e40384810f580c40d0400340f01e01e00f09a000040c403071942c0004000350044010700040c1c52417104043d0311840c0d20508000101038040e0524031401101c01008 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 626496348 1250 626495098 626495147
    0xe06040b0102060609040c120605010e070f0914060f0706050f0711250302040618050c0f0d0519020f120a091101080a110406050a0e0a03110f0609030a03 67
    0x1040256000200181e0050f8011004250f443c82c0c210032083d04140f1605161290640d01c070078001858007062420795030310703070740d00d00401050f04140e40d1a5403100861400c00d40b2035a00c29005401072801e13000d10545c01d4140c9003078007440c1d103802e400c80312142a0740455503140d401e40e01e0b20340c0291004482e00300303d03c0c0b0b003d00172980c41800f4006113204880c00c080541401c02c9040f038038004e2002030152407070410000304d1001001d620b851050802401d8441c2d0b544400c0f50b4445007242c250340003d403030b128001104101504404036008251450980381d0180851180c6400702c0d031003407040660000504603403000078801c1c14412104010b101025103210031340c03030740d81c0c52030145000c0b140301c850040d000941d50a003415056114503101503202540b124009420180241c403116a07411680200012410008043e00e4181c2c0104010041d988200c071348040c110b0a55482c900f00701e00303da0700c25018270702007542c0340004e03990300083e41c0b0b650a0240840e000124030f410300509100080d280300e18a804041c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 626497598 1250 626496348 626496361
    0x902040b18090c040909030917060709120c090b270a0b0607110904022706010801170c01110f03030f0103170703050406050a05071a0901050a02040609030206220f0e 72
    0x2104180315210000b40f00c0d05040c5003c03403200103400f03000012400c201065202041c2c03214450400d40801040030001e000e18a004000070b46a003020390801d20011000710703070390300c005200303443d040f001d40d002e0140125400d0682000300710212414020102e0f6066001c012503840840d88180a00c80d4100020500048100c40180141442445000340c411b801d00b4414020318145503010640107031020b1701e0761003070520440b4807450030ba25060f1000c00400141c0c09210556030f000200c680907000c021440f40081d200700c010280d48181e50000f050500104400c9180500c00030710850b44030b50600c1c42900d9481c40c10a0050a48620901084508158400304c1c10202003021055a2060344e041d00c40b10b103403605062080e01d1a4003c2150802081810885030740000d080c00c8281407481c9045103000d2140c108036100a0968000514000301980305120401a850348800c1001c02c40350103403002c40d50764044c207907409408000c5400d941403c002c402400100b880b0010f0600341100d407280040b514039150030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 626498848 1250 626497598 626497609
    0x5030a0c030f2102031f0902040305010b090f0604050c041707080d11030307081317070215090d02011404080f0a0516060909051003021201090303060515041703040902040b18 76
    0x42c907045143d42c1c0180340d00c1501c1c4845034015500000501c0c1160500069a4420f511241340e907044000001d402240800400609004520320550f04460007003062501310089a05080000c0100b03101d9502c40c0082088900407104842c0a4030381780051000d10070407444190740d9890340b4421210184039804600d884613100d01c03140f44407204104003075495500e074100101e410f50b40c0035114000510b001000d01c800681c87d041c0060b16000d0301c0380314503100c4003e8010002000703103484090700642400c01c4018a1581e5148000c0e0070180d09003002c40d00a21001403241150082d0b0300031344014420480c5032202c1600015225410902c40c05c121107203010301003403c40c0e496611384142000300e6400c1c00c051002e00d01c5504201c2c1d00414000341c030000d0503500c0e0006400c03694030201013100b41e50360740350080500d82d041c000d2901030442030b104060a40107480b0060814400c0744188a283c42a80100300d00200c0700384102c90080103401010b64442d078485c038002c9550b0b8400c03070501d117500900801c00c5006003440f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 626500098 1250 626498848 626498867
    0x4180209010f081c0e030109210c02030d03091b030f050f1f0b1305040c1e050904020405090304091a10181502031314120f060610030905030a0c030f 65
    0x4210281444d258803c0a440c1c89600c481c040c8810300c0900303000c40340562424032800e0314140c0a4442d85040440b0454003403189092164410304100d018601107000d40c4000800c245117252074030340040e02c800c4034241043c400c00c40745c40c140c9201d10360200000500001c007404c030303080902460907184c2c40c52085611642d0345880c1441680710b1107005003004081402a4081422030002604074602100300c2c800c00000c44004a40440d004000c040381882850080380b503c40b81598000000042c01741403100180824400070f02c024800e6440c1d00003e4081d410a00c01c1d10002d014804040c0f1403038185064000d0602c4074040e080b23004440000c0c0c0329005902c03413100640c012082a02204055007002c5003448100c412000c000d06600c0100401110600d0f03041d2032800400d505075035040f02c9000c10342000001e0010226051082e0300840304d15903090350100b400e0380c100e10100c90b0007254031006030f070030380103803201c2d0340d014100e40400310301145401d82220b034083c074051013683c1d080e64681945500f6541c1162 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 626501348 1250 626500098 626500109
    0x2090a06050907051201060309150e0706080c130b1b070e1b120412091508090c030f070608100506030115090f1a071e050d1205060d020f04060504180209010f 69
    0x1c0141c01040614001c1e401011041d01500cac442903103d50040152042d280e901100d050b0541c00b4a10420403103a000c80c0c0c0e680c0040b0015807a61174074241c0d41040b042c030340460050342d042c020b001580311800000148111110300088042d01c00c2e440d91245a266440011144c48488144202143d9612458241117902940f040004408103440315122450392001e81c0003600103001803541c010803c288401d4055111041598504115150481015007080d10788410907020341d0041c411001054808111041582d80c10700e07241d165680c1d400c59400c000009540141d801410000c004900416542c84404070b403603040d124609a1030b0b581400180d01d80c102e00c200c0c1180603075110340404001412008002003030050079000e28209120181003001c001c801c1c2e08aa0a038030042c40714548603005941030180121a583c2009245450340100d01e00e88071110340248102c0b154000000070303548a901c00c40140c00043c104000c00c040c007159980582c44c0115090380b2403034925000041080070303000380d00c06031031 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 626502598 1250 626501348 626501377
    0xb1215010f050d030c170c011a0901031109150603010b180904030509190305011b1d03030a050f0d05010b030a39090e0a020406090602010b0f0f01090302090a0605090705 74
    0x10b106850845c2d0030b880061080302c1d0940b0740044480c2001c0c06a000d400181d00c44000003c2980300000d0103504005050103150080c0140d030300400200340b00130ba002040c034109a230b84a106664107002c0242c2c00c490200000d5202c4008000401e40c00100d1010700751f980b041d0402c1d280c1c0001d1070000c00074415011900100090801c0250140c1414481d58819102100302c3d1400102a12941c07880d0a40e1085454042e0100c1e01600704520b01e03a210b442c0c40440c1407891032001c0304400d03500c08a0744a00c6100502002e0082c0041d013000c81c42070f103004891b80446107000402855840d21111552036006450800d411810300084000d099442415610840d0400320b07104400114101542d440300c000c856000f05012125600107900c20104000c0317031045500e9140180d840341088406001850345030400011a0f1401c1c8540c00caa40f9075200b1041d81d04000c64180307100000040040f04c1d20b06903508002d400c0010b910500208600c80d420410a50b0341c100c850b12015036070504200d0343e034011075440300f6804 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 626503848 1250 626502598 626502619
    0xf0c09100f0306180209030c1e0105030423070312020106081e1603061e110a080a11040902180411190201090b190506010e03031b010b1215010f05 64
    0x340915250742006440e400d0110b039090b900d80a400039030f0f01051080c07110a8000800020502e814044404982e00c100e0700790b101c10268103920400103882001c02c031f050040000105081c0a09100402c05007d040c0050b81d029450a945240c0c4480c200c0c481201c1405041c507440c01605e0040c0181c1d0195031640000f000060342101141c07110105610050b82d842c000c1e03103000340c55260540c4801700034600460b0080b0b240c482e840002200003c0280c2101c2a040c5082c1c0305420010001e01140d91081700c9241c40b084e02c0c1c80710b803c042c1c02400303a02880503c00300002400240108a6005001040385104032200100c0d562070600080d105005000802e00e030040141c11107030300391202e0824602e10984000902d1410ba580e0b009600e00302620311203101c0c0c59015002c0003034206070150301c2e400802841c0440387e5031000f501080c0c0c3d9008031920007004041000814422170001d620900d10080b000300f0101030300d40803019031074491400405080800200320000b14902c0d20402c00b03a003c035074014101c0b071040b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 626505098 1250 626503848 626503879
    0x1050106120911030102070506150a030f0b0702070e070e03010608010e0604030c050a050d0905120d0e21160617060d0201080c0d050c03012102030d0819090602030f0c09 74
    0x2404a414200c424200e0f070290115240c03001d1000c0d110035480b800c000c008906001c0214650700003448104ca128024040301480061032006049090b9075010680040648826030217a00b801540d82051038032110310000c102100b6442820300152420590003004000d4442e5520750aa4003c0c40c001d0741c441d400314010800003441a400f0381046400b92003070303569104e641e0355800e090009102c0d8000c009030f0030070000d0081d0315000d00f81425540180b40104007483c02d03000050518440800d18500c2005074031300c04225011510007200701c0c000480300740c50456102d0a0300420270303030407405481c0008001c03a0b4402001b52084400d940583c100070840e0304002140d5004442071400204401d0201d2010b021300c10708401103019450140809c440034079100e6040504038000030007031785c80000c02403007c07880c0c0e040542c030041001c8198901518011405950310f6954941c04003039200c0008400b441c000740081408030a5003d540a030220303685054064031805140300d894040d0580b1551721801e91104080c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 626506348 1250 626505098 626505101
    0x7140d05070522060602010f0c050c0c010e0307090f0c030c02070b030f0411040903030e160e010e09030f0304050f011505090f06240409050a02070804090f090c260105010612 76
    0xd50300c0c88019492142d0803010b045002d5400700c5d8001400360f91220711148105c081030141e5a00e43c2114903102d07080003002d0b803610381e650140714075244c1880041c240602482c0c8060100c10081c00b9032130014400146000985c03001440701c210804e000078502048220304901c045006411107020088903800c548552040d4001d00e50090821950466140c060f03400d41c3c0c40d0740c0204460745000c2d0310001542501c8268160600039203441000f00034142510500041c10307403150240c103440d20440d8100e09a900c04d5443d07440e510520051000348580401080204000000d000d0301c2d00390078400a100c15030741c40070329002264142c003406511200c17450000e184070a182182541c0070900401d402d241060b0000c00c5200440b040c1100301d501180014180520302c00e5000d007540100811808615100d43ea0300c4104880c001c3d401200405900e0b4100c40e00c40380220382145010907001158240a9503a4151441400017031041d00b540c20083c04500d880150750610441e03040b501203880d0701560b012142240c00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 626507598 1250 626506348 626506369
    0xf0f010903120327150203070f1d04110c1005070f3f0b0f0a05060706060e010f05120a02030c01110f060114090a060b090402030c07120207140d050705 66
    0x420540d551040030b01c00007045004c84003100c84207022240110450420403038420f80080c0ca034140f103004005000107140e04c0602c4080041e0381d840c0a481140e5107146071800b440115540562060902c40201c8283d0394400c020509141d00c0001c07a0703a44105c00c03407203000b9540101c40301c5d40410303000004c4480300d07401003001c9006070324141a01c1510050a80c030100010000c1c3c404030300348500d4441d0610300c0340c000b48240ca0142034100ea15404540580c800901c1211080c003c89000d0b080114014041004540210b030250400901001082d0b03100d50300220a07409620a551145001c500c05505009001c80c41c000040e4000c2e02030140c0e612103000540380c0c0400354401c0d881510801c080355640d14002d00c403803030103000c000d0101404a54200308010206602411882090785495030801000003440100c400344801030314056100e079210312031718035540100c400142c0011200b520030601d5650100d4101c09491100c0c10001c00c9012002c1482880525604018115445000b0500151a000c1e00c0b90 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 626508848 1250 626507598 626507633
    0x601060f0e040f140a0605010e06030a0e10020c0a0b010b072001170a021b12030a05070302041e05010f17010b0d0207050a0f1707030f0e040b1c020f0f010903 69
    0x115110001c0d004081c103c50810205603c11500c8801780302d608007240c014140101401d181c59401610210005645888054240e2900d41c0e602c80c01561400c0041c44504444000c8000031500e0b07030541c0c402c05072a281240c9003160350402e00e400125880c00000155000180c02140309426000ae141d1298040c038040c580c07040c1031284102088180c50442111180310305540c00015071140f0089800d400c0700090300c00c880d003598015011504040500505817a0310031004000824180c9030404103400034804c3d50005211000c441e06032031060800000c440c81159401e03a0f681201c003441d040202c40d404040d0f40c08030340039040c03a001081000102e901a12550610000041c0740c07142555801e0f00c1c1441880e400c03125203803441c102c0000c1c0a00c03005003070a54400283c2141c508541a5030052100c60001c1902c0e040c0b09030031800105640310340e400080200c1c00680840e94111071803a0030441a00c0c1104100d00c900c4045813a043c0c00d0401c2c0840f83d12521041e103a03c0034070b41c11039461181120104062 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 626510098 1250 626508848 626508851
    0xa06080d0f030e07030606031104050f2212021501060801050d0f05070b0309060a1b08040219031407080106150503010b0a0c06060b04030b0601020a0b0c0f130b03180601060f0e04 78
    0x43e0080722a05002003c0154400c80f4001100e034610314001022401114201d84104c0c90300d8100080c44554401141d40410081d040015503028082218030608400401500c007019a031901da003c0c580000d1064031445602a4641d0340ba80d03107010448640e5000d0180079008010454a440020b856901804215104600317880446032142600602070b0011204518a50700c03010521a01c1c142c02c0c850600341d0810066040c081ca180d4031405001100090402801091a150800800c0b92404214000381d9444010303d440391038004006641d0340404d005800107075281510010b01e200306400819185411602c03214196031078070290b6601a00b000e1140001d20081000020015000b4420b10018000a00126850340e00714109840e0601c40107107280d0542d80700d1003209003c42c040b0b4248c1d5030b2000740481042c2e41c90b401c09180c8040c80c0110003046080a80c48040032400b903900d40e020b507104070015035009030700300c9110030016a0b03082e0a110355004648a551000c1030240704240803202000080c00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 626511348 1250 626510098 626510111
    0x70806041122050d111912120c0f060c171009021b10051009091709030c1c021923041107110f0a030b0c210705120a06080d0f03 56
    0x491803c1d2020013044400c00c00c3c10420705003078540b880a0014042041c542405140c0c00c1c80e00f03440340c00b043c15001401c011304007041d240c11984501c032480901680300704030307440c0c0354070a240481c0a0210310034481d010030340245044c2c4002c00100c102c00e20030404d001e503000343e4500e080d400100960182001c0c8255250380055101803070000c01001c0d40011b801080000c407450070222442c00f540f002d4000015407804d1035001030204d8107409480c107090701440c800d01d507141c91000c0020325080c00d0220700c2d90020140c010000c01e581a4420704001c0034000e49682c0c0320080103c0e8400d40030340442c010005012611581c0c1080580190401c2500c298064000500944588014040e07900070060403502d400c50400c0702d07482c6040c07001e40c140910100361803074840c540c10350b039805800315070082141c0710810300807441e110782d07103c074070b101c031110b05100074130100303e42040b8600500e135500900402140140362000f1070743d20741d0b1601c01c0804503811100903008074440c9480c00c6807944003020314070040546408 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 626512598 1250 626511348 626511359
    0x120c17030709030515010306110705030a0e0a170f0114040f03030b01090504050f0703110c03070609060b06160302060903091c020a0e0108010e15040201081b1c05070806041122 77
    0x20400d03071030311608003105d02c961451a1400c1070704c203000421004080705011079000200c000098408004013070620711a8114101c000c151004880c0d0b02111002d0312a00c1e841d40c01c0e99000c950729520380c01d0400280810303078074408040000f0b10b090710b0041041e2a04000300000c40e11a81c440510b1030310514040c2400c582d140005015500199130f804010030b4080240190113406200e058010001101f005040c80200700d445512402132100c00b40960751142c4441003004102e5124410001c0010300711901c803859102da405030001c2507a01140548a081c010943e03180d0008155680004000d1490207c0f000c0e0b40c1c440c803800e042000040b42c01911006011410112280350785020701807400000461045030070450346005124000d03002c90700809070034440583d030f004494650103c80030000e0384640407a180a840701d4817621b04100c0300c0c40c650105602c0d013181c00340c009602915840e5105085512a10100800c03511024108034036110200865400118031104c3d8002c075a0301c4988000c40035071b483c0d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 626513848 1250 626512598 626512603
    0x15040305030a0914010206010303080c18030f0102040515090a03022b05160915062006070509090c0a0206060f0109050d0b01051f020c010c0c090c0903120c170307090305 74
    0x102c41c1e4004185a51014000d1090786908100d074803501344020170480d403450718003130b140b80c50150014601c00c0c1c00041c950065207a40b005140e0890000d41101c6822155108481c003c0d0064003d40d0b00c110341101408070b02c2280c403c02d0768401c40d0004c14074290f040c51036080055a0f2840b1034a9449071141c02420001d1010000f0542000c9000f02c01070008448414001e081000140e04151400d506c0d01c682d00044c0070001451034103494603402e103d550300c12000c0000307020008541c2410b4903442a1004c11404c1540704014204031107056440c904640c03600d4040a81c0340c007850554100582c0204002419841d0655900c8045038060611118440e110400714201d0200042e050b59546d0340180108441c0c203000c50488101030541c0504140f60824030030007501d4149141200b0304012080e0b180d83c080c400e1088540009082d510010400026070080243c21002d00e44000c0d61400c0546141c1441d090140ea07555030b1403544004202e040420110308001903401c081d2490042214501c804000a03104 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 626515098 1250 626513848 626513857
    0xa0c1104090f020a05010203070305040302120c0306040510181a0711030a080105090a0c140f13060e0a0503010614060f12012301020106060c02091f120201111b1504030503 75
    0x60112180c800b8590051181e010005d50080381150b00400003400400c5d0311501351419650304890800c00c064129258074601001407003402e07854080c540c03d120400c000011a0080441500000c0c081d8080c4040d00002045450074003400040c1d8044a00b2100f0841e50a40c3d0307881032290078200382000c50b020445141d07801c0348042001017400e15006000380c1c6811200e07640c1c045914117050003c2c080300c0c1c100420310007035850848400300001c940e880703030030080d001901c0c03484905074114506160b031903400505100300c0028260003050b40d52404281c0703090601541043e6040003443d5102d03400c440301401107a0f8010300711640c20810174007420351042e0918038607500030071000715181008604807882c1030b41c03404a0748219041d680740c0700c3d0800034a03801452032019030380c048a1b0b45020740e54120800086a07203c1d1200d900204c1d15005c0440c1400150349494213860003a66401d1040e036401002a40e42c0315170383d035009d5032040002103030040d52400d09641d481b0a044050a1401c0c42c1d03503641c41600e113811 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 626516348 1250 626515098 626515103
    0x40b0a270b0c070e16140c031801080a06081e0f0730030836100606031103150109080703030c02090901051303050306041409150108030705030a0c110409 67
    0x1810070008804000400181c0104d040701801d40c02c0000f600401c11041c0b01d00e4206011080750803002d224a11020b0302c04030107803a4161ba43c2c0c6e40092a80c043c0b014000c403001e60110314004e010600c2608144500c000340c0d000743c00240103400d4042c0c00041e15a071410f84103e410302c1001c144a50408051081030010314410075800030300c20041100d00303c0440c82e011054146c0c082140c0c1d42000c00d074031030720f001e070801c440342c0110340401403580d20194100d1b980041c08541c000c64100303081124000041102982c00702d24001c224154a42008074242da10446a103e080032007070000c01c4004121403500c201c803110504102d00402c1d0388130105420409107500c10340116124040c40025030425018445d80002d113600200f0607864a814400f188011001020b81000404000507c190b1665440310a800d100c04500a00b24500b107502c243c0d642a01c002c00d003400300142000003800d00c9000059965455000b00030f142416440d02c0304403110b40c100102501e034441a4481d0003041d0712680302d0b4030295130 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 626517598 1250 626516348 626516369
    0x40f20150912150106030c120e0604111815010215070e0a0f030203060a0504050c040f05061003050403140d0b1302070303050609070504030605061311040f050303040b0a27 75
    0x80581c41005106288002c005440d40c0107009295101c0b850707505103e054407218100041c108850341002c6540c10b1a9029a84017a0300c0c101c0003072610400040c00d207114038843c001c969002d01210741440130b40780120070207001501090010408a1101010102aa8406104a504502e074040c4528a181400c0d16681d010440c0c07510301301d0450420810f841c020f81242d020703a895583c510b07030200356108001030244003071956138000b0401b00130050107030a03041c0070018801d0085541d01c03250140100f0042d81d4a900c11441100d601e20300500a000d05031095800d900c0e840c1c07a00d031180c11590701c0307980a506030341541942c032442414117649071002840f0180d2944401a203d6a4a1501600300d036030103045503226002ca81c00f00081d8a03409021102070300d42c44030740412217444050108444c000f03a1600ba440c11418121100c46800100c000390040790f48505002803000d643d8000d050b10b070b01c01ca028084558008025030042503000354450750903200070f101000e505600d2902c030200380442c1508a600c081 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 626518848 1250 626517598 626517607
    0x317070c0f03030212120105010507060608010f0c090503060103030f08070201150f0305241803120a020306091302060711010c0f0c150305011202010c020d0b010b041508040f2015 78
    0x5076040011780b200c4100d4140341894112142074426a80300148a020304110b4000f5484c401c002c41d58201400a00d0400028400000c6584a043c042d1080c8a9a000014004d59002406180011b0f000e8103c07901502e86104245511100b2210100e0041204007913640b1040c01641c0d071032415856900800a00d1040e05285042d494414140304402090440042000c2c00891311b0340d400004181d085101c140b41110610a100451815030051207a8664082c0c4040b003000110001e03a0002c40c4100b9040344d02c82055550b40c940000d140100d81c002031f4000e5010320000d400141c1d410200f000d14101410040842107003503883c032003250f5004208075101000040200030003888054600c1038801c0c0d5090901040d81030003d105582c50401c0c40207410802e180780004259159400b00d80d0b80140c222425056039a11446400742550041c85100600c41140e6100c400729480359071080d010f2070f030000d9040000409600c030300c0c2416100000c1100042000707241088540c2d20923201e40d40c1d42044100f42c9494 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 626520098 1250 626518848 626518853
    0xc172205030d0902010f020307030f0f02010e06090601092306090a06080f010b0f0f0105030c180619021b3321060d050a03230703170c090a0317070c0f03 67
    0x1c0869034449401552300601c2104000b980105001d4411070152425254801404004a01604207507032140c0c6240289018007a82ca80b0200380d0a05a900e04c4409000c07601c8001c0c07041c006044100031480502c1801c5000c1000e81c940140e17481c1d0020071884020074465102d000c0103003000c40800c411469030f99108045203036410003d038592100c5400b00c03043c04200946100107445403000900f0346070350a0001503c4440c21044503054007800b50007030185610380c8811012400600d006103c8100036100c2c1c010540154086940d240b45a039001418030214440c46080c008440201d202c0303000f211881464100300090550b50250100401c4600030304110702078940006110305003e880070340904034a01ea607401003140060000328550740342c036103652554011303411001000300465040c00c003c80000f03941014140c3c0802c0c0c2c03e206c600c4580701d40955450b0302ea684d40316407042c160800e03005009074004001003a1503c2c1c403c4a10004148030501e030565950721000c01008940003102d240c3d9040314123005 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 626521348 1250 626520098 626520107
    0x170a0207030315080a02010819060f240c060e010f0c031e0612021c020603071706040605030706320a11032718010e0a0c172205030d090201 61
    0x43d801c40c4121040729079040c6a01c2035180c0c4c40014000c0e042c401101c001c200c1511401c8050201d0340b80b044410450345881e00c0c2e49883c2c4190070f104580406524988231407524030b0207544000150100d40b2110942003550340d603076000d0b000c400190111550380b9095044210060700a412261000d55000141c030060000303228140303610a6942d05045240c00014060560b1088141442a404550480310220b00c2028442181c02e00000203410078008803e0204082d0005100d0748015503443c54100c81350f13141810721084480520820364507502a92080262038000c8902c40c4406524001f42d20521251242c120b01c03e01e071841d001c0782c440c500064243e15503036110226803524000000590314012410103181c0c24400b80030000301030958a103010405942d194407070051100075090482c3d9896032f461405070b500e5001241c2c0301d0046410034103031b00c611921440c44020002e0341c02190000940b1100c2d904101d801181141d151400c031000924404910200302505c40d0010b004408074070301100740300040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 626522598 1250 626521348 626521361
    0x10306060801050d031b0c0303170708040c0302091012110913080d0c0504090e010e010506010e09041104020f0c0f011a06030604090203030d09140705030708030f0901170a02070303 79
    0x10402210748010b22041d80c03a40c09038480d003070b0035180456041880350314a145c20b940241c4014202445004000308140d0070859011042d000220f00794100c1d591000160780e441d0048500401204440b07405200514202c030303010b60090380c203608400083d030300c5545d04503219086000948104056008400040c68107910700b6500c80310080c0048080c4684d6511240d0b42d0103031544804d005d64841d043d605140d0701c5202620700030a01c1a200b440590540b00c102402404002001c0c0c90650810001841c0d5500501d2480441c100c0548071407a15651900c0b06480e5240202c0090f5018ad000c100c2c44c230414240d40041c040b890440030213041544d804031916800c54041c4081c0d0b850892099000e0452030340c8600c25290b0080042c0e6021032125217a200180c15481161070309034a452070076241380b0501208080260007402c800b000c4070010742c0c0702e2042682c0d48400f84500d81c02039004211140f061103c0300058a00c514060422030715440d000755031b98a0401089801c017000c1a404036640d02403691500602 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 626523848 1250 626522598 626522609
    0xe0307080f100c050d0b040f141006052104061d030a020c010e130209030109021201021b03030405030306100519080f1008031e040e090106050918070302120f0601080309010306 77
    0x30866541000d1019185010b100900d00c0507035981d51341688280c03030750341040d0480399141c1c202704015000724021641100065a00800705403120901082c1c0e580520210b50303a20843c4d840d9043d0180b207514542c1e0300124010b000f00e8030300e0b85540340c10f111100c1c03003400140c03d9140d038005142c507140020700c02480c0460b1000003504024105224a9058440311580102c4011034000540d0b40d406e503c01090142160600c0290410042e404140c503664041d4050007850201000c1100184159800160f40707001c1a503018100341c20410126201d40707000c100382c20560f015810f05508080e09005180d620304100303000c1d42c0110700048104042110031400c000d030701c41e0000c21414225401c00d400c5503601d01030011910301c0e480050041d14054048070ac107880c01000e006003003084910300303280301c180078211600c14240907250950204540c40c042c5110020118100401840410710b950200300c0d8105441315420501d01859500c140d44030b4050100501030800080215a6050f1b0074000408940195100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 626525098 1250 626523848 626523851
    0xa020607110106180c0e1f020d0504030b010b031003060c0807030b031c050f070507081612050a200d0302011b03020a021f0b0916080c0a0503070f0e0307080f10 70
    0x4d00241030031212445644005100024810320b0441003603039034042d02c86007140e00424000040a030a101d41341e00450107411a4241d0304154003144c0e05850038025408018078501341030340180a0645008080c1d03502504e440c440d040c9103030b920384940d1b0848500102c000000340742c440c108040341d60035009402e4400d81c154024070301e01c3d01010148415040d00d84070602002000500342d1245595a400e41e43c0c40354100c000e80361032640e1528851303175880e041a0b000c031941400c0310000418006507980c06041540000c050b00c0681466500c2d04804084012035100074a040708100303030755840307800181c02c11511a8000080c086400650320390729030724448403141054010403010b00019030101d440585161140303402c00c241035039100018043c102002000741c000901e0010064110304441d1440703104541030720795180c2038440300b4402c0c00511480d6003500200f84100045403081c1d100303450702d40720303c200c500e03143c0c00304208040000d041886d1f990142519501c1b0f40d80c00009100140b210041550f1121340 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 626526348 1250 626525098 626525111
    0x120609090a03080403020c0a0f08010f020901090306020c0a0f240e15040807080307080109050106021c0507020f0402030c0a020c030706080f0a0f110703021908030a020c120a0206071101 81
    0x35416601d001005004041290381400300d42094020800e90001100040000b6112501e07502030f0180781c110391040344003541c00c2c41c200076001112442192a001070603543c013544d03c0e0640c0c8440c406507100c1e80c091046807180183c40400310750380c2c4100c404ca262142c03a07a085141640f0100304100841c0003400c0c000c4600c0d201c801000d001d0000751801001c190240d42c26019038031070401e540c160041d000702030b00b888400402c114090768000c0750342c0d06880518908000e181d80f900c004a0f61a01250340d0360000b10396017801403075421b004001801a5501c01405400e01c4c9100340c020400340e8000b5103061700b1040c4049a4640d8554050000000610054008144c1549030450003444240040c4c400c0692071701c850041101d440f80d5030040d450312103421b0024016504409035424656002d003038103030014020304407601800b600c4421040d00c41c0350040c0d8000d041d9290803511b08000d5110086810961044203460344010700640c020b4401d911940e000f41c8000d04d480080601002402c0d40b00000fa82d24020 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 626527598 1250 626526348 626526361
    0xb10020c0604151b03030203040c0608040203060f1807090c030b09061804170403030c02090c0c0c1005091201020406031d0d35010f0f050306060d05150705120609 71
    0x2e030740440d0300745055480c400d1102d02d82980c0d0308040103480c1d0b000c2100542e000c401e06415400842c040da102d8460080810394820085400340b0302a80c000b03515402a00210701484000c02a40e0713000114403051080c07a06842000c1403a003121684018190f48e1111661400c44d5018401c1507035100040d10381840b140303007283c001884443d041a4180c90f04c00c07000007050a1014a120050800d41e195406ea81d49a803a828050003a109104c001c0340b10700480d800040450b50301c04241d450200300c1e98028581c03c04503400300b003204c034a9401c081041110a100080c082d980b08400c901d090f0814500059403181089001801e448134641744e10700542000f1140230b0f509000003540d0112603c24604070301c0d0f44e000010b064000c4440c1052005108030040a09541407400301e0700c4038103c880c81050042c3c002d58070b1707490710800c2441d84502a41a08250005082c5041000942d03076012301c207805450270b03205460340310700c581c0c80d065959a0004038042542030862a800d0b2070160094411038a01849281c1070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 626528848 1250 626527598 626527609
    0x20606100c080c03072406050103180f020111010f02030109050c040503060723071104050a0c020706080c040b04060206011508012102030109021302070c1508010b0f0405130b10020c 79
    0x480c0002c15054000507080328a400070310558070202e41c080002c170703003c012203401e1104a4021460000d41c13940f82000000b1158001e00c24501c224000065800c8404415156540d100c1c0300ad0506078140113080840e000d00c1c072030070f10030491361840c820750042e1a541004008800c5440003444c03501d0216003004244855a00001d03c1507101c0b00c00c1c036001802203802101e08680440401c03009542d16070100e41c860401800c41d80071010004103503001c201070399501d00c4a0043d91801d400b07a601613000100d041c4500d502c03e0707040ea580701c0d0a20302514039050351042e030000e00d03a220740d000c240140c00c58001444008049500422400c01d01d10b4444103d5050640d400002c40c2c210500c160000a83c10111003151000c0d0403600703035242c0042624031509a60b5035004081c6d4405142150074880c0d0320408941a03100321800c0701d508600d035a4086481e820040705941a41c42241001034080d414040001c080e0341b2512107603d072400f502004a0329051a0040c401060080c036145410754201c4680b20390983c440 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 626530098 1250 626528848 626528867
    0x1d060609131e021c05100911060901050f130e1803030a0b030f0a1b091b0806030a200414070e060912030304080405031203090a060504020f03100c02060610 68
    0x5141c0400c0c82c1109100460b00980d80800290030a030805628410040421450741da15400f803800d64400a1400d00901c00301d9100450040440000068441c02401c050002e40095a01810203034a40389255061070701a0308010440f9a444120403028072200e9640d5002a81084110b180c0e55070368200300c01c185850307000c000c141e6203540d96107000c031100c240c0d02000130030001a822400d4a10503001402c01c51940c00c2d40070001d40090f00c0c0c1040000d0000c4140c8900c0d0b10b9a0220300c00c03204031200c021812180c2100140c903041c0c0c144038400c0080301060541c1d941371101d201550011060050171020f00007956a100400494a85800e0420511907049040044100320460780c107951000c2400008142c072400c0043c03d8864407012081000f000700030700040c001d03103008400b00e6039041212280800380d4070003100c1c1d03207a0b1500044c00140009016410a5400c035200a0110b80100f5001012901e0140b410454181c2d03070b912000d4008083e03405104d03054100360151070f014400d103026417018004400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 626531348 1250 626530098 626530103
    0xf05011e0e0604030807150e0706350c090f09010302180a1b090305010b0306040203030d0f0906050f070f030b0d0b1506030103050304030c050a12020d050106091d06060913 75
    0x1c80755965140d0b550b5010481e00955442800307161181c01a00740700c2e002c043c0302030f0040310051500d400f01417940b6000031440d0171101a41d0751044540d080c4a032038647c807285050003182015210080440b0a8241325080c1c0c032030401e903041143c49152400411801d48802c0760500e000b580d90310014400b58a0320200750249081c41040c001c05c1d503c0f000d80e1035004040d5070341e800700c80790291181c41143d154040410780880e0700400081c407508101108060f21403509840c000e6040d401042110320b1b18041d5041062211828000002c801e255600d514094800844101c13000810800030010219000b8a04540b1b06100707280400c04c0c0106100461246150300310013400c156060000521140115420216098005400149c4070b5079245401c0b030f82d82d000f07400b04030b074820f0b84103001049505109152404031010a40e40038051711a5800f4400400c1010000f52155500d81d580402c601e11a405003052094500b0380418009008107110b50600c600500420302c03c100013800d1011201c0b00c2c100a140e0680c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 626532598 1250 626531348 626531357
    0xc041d060310020a09060806030106060503070c030e1302120f15040b06040504090b010302031b09131a011e080a020306270d18060e2202220f05011e 65
    0x100d80d600000c1c03808000d40701c8200c605000290b60b208581d413000500044900c2030b1201085515501e04241c203946140c06143c0000f2414000600c3c00352140243c58805402401c02c03c0a42150070040b03402c41d850030141e1034000e9000648500c0b0300c2e6995000603032201840c0120402410074240300c0080e00440500f5900c41c0f0348a40540096549441c200c40041000038010071600c5601d107004151403009200c241d209004010031183c14440000d082c01240da03008204080965640f580850310f8071240109460781d1011105408030118a4140207028003002050030300419503c41202040740c40940200403590480b06e80c5000685001410940084403a2903c88140388a89000d404000c50891a400749201c0c2c1240d0f81ca4031600f00c1008150401034009414449032140c0003560442106401140c009445000100035030040007207068030303900b2859026140000b01002554003000d0079001121000c4000c00c00c10460f03c1d56842d1000500703080c03e200025002e158007800f50326643c1c40c0c0150921 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 626533848 1250 626532598 626532601
    0x1030f0b09090601030308060904030c03080703020403060c0c1101050427090803070e030705330c0a1b060f12020d0b060703050a17010f0b0f13120302060c041d 70
    0x119150811100303080058100d94035441c00042440c1e40d624203201c15408a801507002c1001800d0005420b48540e03019181c1171001040c0350307021903884000802d1002050760a110210014015000d100c10b80c014503603400a4a4101d070800400a60b442c402c86414040e007000708102d0f114000c480ca0302498490100da02c00a4840d001d0304001d4040035400801201c400810011616003058030a19881c8098003140d191030f40351014007081e04201c00100046a590407404000495014000c418010300600d2440c1040001101030f0701c2c103043c881d000c88007a100d0440704d01c1e0144050b001c00d0018412813601547e40c8614680180c440003a400c40d80d44800d800041c1c411006c4050b0700030b4851401e0281c4603503a50405810b008080b500810101d8000138540405100805203d4561505a540300072081900034541452100550700034210021655010300c20510030560f2141c9030402058207000c00c0301c6010f507614000341048402014900c2c03052007400705000c40014500007001d000403261020045 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 626535098 1250 626533848 626533871
    0x20a021915110f01020c0709050c07020d02090a0b0909070501020609010203010e45010b010e0303090d021903030f021e0d12020d0914010f0203060f0f01110604060501050f010201020a0e0103 83
    0x41180701e80410109600020b84450302250000d003000448d1101001080540c542c500009480d12410102a512412000344000035251281d041274001c0e00d4100001140410b040100303050308000c030303080002c50300264400c114650301440781650010104000710302e5503040c0b060900074071402404c075544002904120003510aa00e880c0c010300f95a402c2803440944908610581e4000a201d0710404c083d400c0000500665000d00091014801c00030040c60a2640b40c82c2400851000c0c18800c0c0c0c0e0103800358800c8103058805a0002c0061402642d8120341c919800b00064a0403846c0c125a15441c05400040141e03080d01003407040d2200d9451400c00f00d80c1091701c0c84000640905854030000d00d11300780d860402c01802c0e00c502000d144000b4001c0c000c0c0c2a60f68103003001c0340000c917080768100280e100c4011840c41c000d07111080140c4141007a6070035801d0035100760314040c01198204d0f03034269a14011720880c50719000700c40c4c0e0510240300035894501c442c48014032002110305da10b4145074403043c02044 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 626536348 1250 626535098 626535103
    0x9040507031112060f060111060601080109050618010306020a1b08070f2d030801090c17270d02280303150b0c010204052106011a070b0106020a02191511 67
    0xc8035202d62003200c0542c01c051110421160050750300700e003c0707108041a23115903c0c022840c1c81c42400b0503110695107070700e4058010b019040040915078484c4000c0d448852a004844000303001e10b000d0040141c51303860f0044040e122040c0900c0221150840400800000d840d40d4111922035a02a69104400c00c8602d0254a58147e014041c00d101c84c1d2250058980b004141c44d94140c40e0007540e40d411141d036a4645401200c0c100c03c514000a05007001d01522041c1e412007064200c2660700444204a040900b43d12420240c95800e5a20350460002020781a504200c00f04c4c0481800760007041031202c9400800d56008450402800e150722070b4444801600f20048010080100990850345d60b0000c92a00d8001d41c01402014421134100221000744006400b0384480d840302400204656424003403000c40c160b242c0307a000e480100d0200700420015074030002d010b0086c803650b0020051089184100109407594002c0300e120f2980b051820400004583c028140889250503d041040a01800e00c3d0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 626537598 1250 626536348 626536369
    0x100c0503071707060f11090d02030a0203190606062c0109031407180204050f090405031612080f1006030c09050d110111010207020d060b12011b030b090405070311 71
    0x40041402212a4045800b00c40c01440101e00c9a0000c2025143c0c074000001284c04035100c6d1080000c1c103100b82e807038a0902e2112545590f000130202e40f0031040c140e00191619034201940302c00300b440003106504002513400361202400ba00d08200a00344094400c803100200e40a003c01d20000c540007441036180d008094501c007854202644a41189060071110341d94900c1c0e05c50903288a84190f020800200c0600c01c1c3d9068a10081c203c11890743c41c401000121240504155803034042004100d0741d00d0040d00c1942d48444c40750017180440000701d000504243c0380140700c2d4034051200c4e410800000c01c2041e4601c181c90981c100000c80484c208003c40d09050702e40c01c495088440d000b45482032000b43c2c030080d50088801d81c2c0d4006512100290f036803e03030240d004000d4000c984c110007540000c141d90803220b81035a0160001241c80c0c8c11990890030b44540c002c1207045048000d000c0103e00c0e40c103000c0d0382c00052041e15500960b041c13555403555214164400603006801d260700c143c60907590804940c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 626538848 1250 626537598 626537603
    0x91f090308060925051b061510050c1f060e1512010212040503220305030f0a0c05011d010b0a0f0308030c0c03040906060f1713060b06040f0f050609100c050307 70
    0x16025130b04104098119801034421681c40b01228404502001c03001845a1140e460f0034034070b00e5502010814010a105150b1462052010602000c50302d5001086400940b201c0e00b10102629030780c0350761080854625802c0b4501441084c000c018040e60300c0340b03403100825401c0d1262800c81c0b0303d81c244a03009016041c4000703142c001040c240801d026000010381503240d441742e1040302500210361402d211403034510004200d60800d001034020a5010320160200e2005424101c0c48040d45584860071540c4001c280c080c540244113004803516003d20603051051130994502038202d081103890003140840340700081c131034040080018a42925041603440280300702c4100c0e41c8440e26011000041c1c843c0f4080d80f800600b10030008200356109051220a1691014607404640c035040701000c07000d80704240c15122240c8445a44403640c42d40c200900040100b01a00e61049003072641d8019104415400140705203014000807803107569042e0100400409410560440d04540c98040e0440c002e07030740007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 626540098 1250 626538848 626538901
    0x30c300e16150206040203300c060a24180f091505130b06010c030c080c010c0e0a030b1314010504030e19150e04090605091f0903080609 60
    0x12201c01203044080001e45401c50449804074006440407642d80c1001c44003e54540d0182410104281401d1010b14401840100c1000d40c000d80d14110034a0740e01c40341c02141c565000c1403c00002540601c18040008140521048441006d120700214000030b0b0180b0042c06424600344841d03408a58445074244884610a12410702c3c40d041c040c2c080e9440e9800141c44074108800500c1401c00f02c4112061a03030b00c05035140d86a01c44200448005400540c12001e114100d032004000c80e0030080a0902c0e00c0c2b07a14004900d0741d80c10300008260400304c040380c41c002c4040c6003080c00080c442b5850313182e1003001c200034084192030300e003460714040c5205404a18203500c1c000920040c10352041c030580a040d0240e900364000346480034030321703d054054451286280c40e8458240f10080c031400400e8800000103001059040c0c0d40d031035a108403107054420020f141c1c810805542c10341c1503004070340000300405130100200e41661b2000340045d800102964824050340c400035280c0c1d082e1a101d03010341781e4160780 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 626541348 1250 626540098 626540113
    0x2060123031605101715040e1506011106100b0a0212040609210c030201110a1a180609030f03060a18060501080105040b011418030a0c06030c300e 64
    0x51074040045502401c4d0094040800a41d030150241520603614a8008014055940c43e80c0c509041b44015155580d8407075111090004042010462101c0d40d00520054a40e40d080040024007030100610300403000760800d104110000340201060300803124840d020941c0c2d410307110000c0b420840c3c81302d252032850307002040c04181302d644524040d050301d01e40200e024441c2460604041240702081009043c504a0403080c0015441412050981c8a07403004032a84402540e880c042c901c46030541641140380000d081040c25605005041a40510800940350500b02181020340340c0c0b0030054a08203a850000c08246151924070300040140501800c0c201c0340000b2b16546806003843e44075003800a402000045079914007481500000139052311140c0d252624000309000070b80210740c2500c0c401071448041c1d601520180700041302e05200d442c01004141c1044405402c03220b10341200d50070000702003408040050085400c2005081d1003991084a418030060403003d0600c02c42d044c240c5009404 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 626542598 1250 626541348 626541373
    0x31b09360a03091211011110090b0609060904030503160903020a0b0d0501170a02040518010204060908060a0c1709071809061a09010513060305010603031215060206012303 75
    0x200001024400c3c0e46190300140d07502a80002c68490328005001100965250030130340d070150707203080b140101c010182d074002001001c0400c11280700c10402c0c1c50186403101042445d1800744d0b10346511000403aa2003086040589008145000040c1110a100e80c8d40b02c48440141c01240c0c0b0b43d00556004214030300c0d558441801500e0b0360400302c3e5001c800303410200041a00849a030041c0c3c0b5031500d040050101d500781b81c00300000f500c0050030414108000f070300e40300948003080c002040501165180c0b240f6840c60035288a143c80c07030041441d541145420000e40081da03000500da21110b082c00101c5d0140d45070542650304201542d13004032034884908a0011520250f0341240c02107070f0084600b00007404622002c0c40c0d0481101c440070b80e01c60042401030040717150001040d100d9076000400010081e0b1256a42e500f12409038000383c001c00d084601c4000a80e0309401410b01e01c2c0f000344880360b442890002e019540e41c0040c0030303092000e00062019100c0045a800c2030460f941d000702195000381c1c400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 626543848 1250 626542598 626542603
    0x2041806051c020303030a02090d050d05070203070b16030c05190501050114060712030e030f04121718041d15070f021501030813080607030506031b0936 67
    0x244507032401285204104103480d0a00c86004040d02d070050040c5155644524225000358091010240e0101014030301c0c1c80400c204004140d0002c00c60340700c1555848250042518050351503000d044442c80c1004213400c20030f131110701c0c2071280f5450700342503054a4161601c5810310417540707410800f0200b5044d880041c00740c150440b904899424180b041d0b501003113014020b6522582c64007070401183c00d03e0121301240300e903105148001e02202928180a591005a4800d5004c0d90000b18a11200b20904061006100081851100c40c0700300c149804032008030580414600c0c14154820356480304400070003c4c1d08c003600f1001094200aa0b5498403950f00b4520303041c4804d945100010b92031845084006000080c00c6201c85d00c044500d5807070341e1031580c8019003035201e0449041d540351003e00009158200b088400c1c003401c03403910046400c0c5080028075180916081c0d048450b114082844802a10703201e4546400c81c900b00e10034031114410051958001884000c00e1240902d01c00381203a151901 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 626545098 1250 626543848 626543861
    0xb070f020a05030a020306180c0315060906120a0f0204152d0608040809010c060f1a0604060903060e03090907050c010c180e041b0602030a081e0c070501020418 70
    0x84822181e840e4503502890756030f010401009415501c044040b505107040b21803500710f1010441c00312000200b00001003418880c0035004440303286008001d00c04240b4000003680e070b000700203032005006d07107950210507a81c1b00242c0401a10f00e0781603590074415900da03078200502c803079081c01009480b80d81d2003a1080100e0f0f80b100d121091305550586005031121181d001c4e40c02ca4240703a0301e0860a03103d5885888590740300500300c0b414094440340c4a030006600f8080c5002800384182c00203280300c0f116411003080015054558447c450800c818440203400c00b64000603240c01540c00110300c106010050b146108807000b940e030194120b0100142d00394088014003902040c0d10080c0006d03840c9060690314011490007459080d1013a5209010320f0010700840c5130300500462203103003003100407a80400036401c180c0007100103800000c0d68154542d042034803140c019001c060340c02c4854002c0380c1e51000c00f003030107001c5108031400010120180320f000d4040d13070041c010010b14040300800380c18400008095 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 626546348 1250 626545098 626545103
    0x9160e131a1c080306010819050a1a01090f060e04020f04030f02011d0a030305030702160b031b0f040302190306020a0315090506031513050a120905060c0309040507090b070f 76
    0x300d201e00d00c1602c400e00c956031451650055103142107460b1000156840310005001c0380d002643e201d01510401040c0c01640d00500015400082d600051001d4804441c0511340841c18031000c482c0411101122020300350458480e40341c00e40c0000303942800100a8401c0c0503003e1084000445c01000340440c00c00c403500128400d8a4540e00b04d407800400c000c40340082e019907580480340c064200042401540210fa100180d4416183d0303454010301f03610142021500300001200f00801004201503003015100594442e0304a81ea04102c8401c4020590303218038000280101c990b041a07001050341c0d004404003030b40d4021810754130f603584214020000c14110114070480c42d50050300260103240341c840c407401000e019014011804004040d01b2107418042c00c604d04420603512802c0100304240701c607003625072041901c2e42c8003025040000305203c07a5604028440e031010846810010030000c12203801c0ca400341d80200b1243c0c1c58000c01d40d824140c581c010542c040000490100b00106448036448852 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 626547598 1250 626546348 626546359
    0xa09020d050105101418031e0c011704021203040e13060f02040b1e0906041206060608070c030c08090a060e1203040f051c05031204050c09160e131a 65
    0x2a038030010009150100a100343c040b460380c0c100d24901030343c0d0500504010108201000c000d050206c0448e00e8004000c60b481c200d01040700070403511100a2200300c10020007403924190600e00c048817842860740250009104105000041030b0541091040e60001c00d0343c00526279103803400320034a201d44100c100044481a00e0a01e40b248424424030170748050700d018144180c05d01745a1005580168241501c00100e000184010b140c607075100c5006201600101a408020440070f1a041d001d64180760003807030034452000100807072594400d07240d0220f0380c0c041c948102034507142e040c440224401d00c560f03035401c0340c403c0102140154015a0004441c8070a460812078440c080000540303c2c05640a00b03801d94011a00410079450110400c5c494403458540707212003560365980f0146954492480b602070400c82c24100310a00c44240038032901d43c00244c039881c50902d069a04500075140c0600081c0c14414030361800c58240d00c079800c64402c0d980382080308000804200e0040031003900d4a040003031058 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 626548848 1250 626547598 626547601
    0x3603010615090b0a171003020a0b0d060b0c06070f050408070621050c0a031a0303070b06100203030f161e0302030a0c140406030504031b0b04020f12070905060a050a09020d05 76
    0x3d0400b088130410800341d50b41582403a241910b02c4908900540903200851840c0c02c04400740e0307a200d80b60300c02418028803403075982120301540b8040d00c400743d001203444803081c0a0070041074404902d103a1711203118a00b04070802545941a6054002c3ea00060f52502ca6a040482d40c1900464901c0604042c521900c0410002d00010340943e03078110b071550009241446940351080c080d41200384070508030b404422001413940c001c2440c40e0484c0c0015203942180209000d0789052020180000c04036603c055440c1d8600411883e560740380180c401c000c040f402c411030300850f83c8201d0740580004004052850070680c50300d0010081c1d00142c98000b8400d2030000c032a200103020300ba040f400294100384190406151503019401004000c00a40500c804010714280c1d0040311250540b10034800c100c490040e0410780184503a40200303080c40c1d4054060484850445800064250210392f08200c01147c10303592400480c80391425680a941c001510b400082031154654000e007106508030b1a040085 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 626550098 1250 626548848 626548859
    0x40b090f0415030212030d0f091a090c0108100306050403080702072114011e0903020705041814100e15060612041214040b030f0c360301061509 63
    0x222800c0701002c4121240d100380400041c00c0c425083c218030301e420b50035641840034215840041d00c1c4000010340c480b560350380c3c0c4002000080e000b00082d22a082c010550305140c400300207555110440300c0039041c0880100088cac1940031002052010b1130f803000040c80a8106032401810011064452001501030f001c2c01107504410034128500d00540300b07075800c81184060302c8102c2000015410800706540710407001da0015900c0302001482c40b4801c4000420210b541402410500c40b40c1145224038100311a0460a1506070003408060703421001030700c882011003000710b00c0d040030140740030b4541e8145020030400b008040b507000034502e1031015003003995884008000044c411048a411910201c8010030f000c100141c1301c0170203407081400c1210710a03290890205190304070703901442420341e000040229031040f2414454000401c0c1c00c07503905140d60308040c0c051004141d213102c40d01480b8940342d07001c544441301c150311106002130002c02815440300051384000104502040200b180c1c0100001c4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 626551348 1250 626550098 626550101
    0x4170a021e03030a0c060603020409140f060105060a030e15130c080d08190e0709240506090613090213060f08060d020d030c0219060905240915040b090f04 68
    0x803000024065071802180280544540315260000d461b00ca60390440030005848900c5507442c3c1078060b100f81c2d030000c0d040c0080e03075260841c1180b0104440d0803020041149442d10030a0320440b12140c2000f04220f84040109441d14051240c030f0104907441c113060104141400744030200f0389010b5810101c0d02519580211794868012490900181400001880562201810a50720540b80c18041000203501403401c0c40d0040300d030809068035581d180c01085030495420030007108812540781d0702d00189072000107026409413043c400e005440000d2464440c00310b000c00c2c403001e004446030454840c4074030342000060282d10f0042c200420540c0c0c681e0700445000b4200350f441030328014a0011031440c2c5038244604102c00075130403400d2041070049900107075941000700c3d000c84510040b042e000391800d600104011660b40c04180169100c2041182a0101000607020700c00200b43c9203a40701c104401003545003501e44210700c020500820041200341003280140b01d580782c1140c4c04100d001da03002c00c100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 626552598 1250 626551348 626551399
    0x90608010608030304110a030f0303150e130210030e010216030201233103020c1009081203100506070b0103111813110307090905070602060c0a1404170a02 68
    0x4160f034010300c00640021183d054960034480c011f000b8201e40ca5030381ea03400300340e008117000071400b0a0720341e9400f8446007109607451004020142c03407a503103814419540d0302410400d91002c0c0c0540b4200302c07000c00b010700a4212000200000d4000c55035a214500c42c2142c01e42250402c4006500349a044034200f00310a8403a1301c08203030b10700e00c1001900c0f0740440f50300e2100400503401c01c0c0c910070301c0d80800381c414610402081c14041e401415044210201300050310100c8280c0000b80400d00d4418004003a0006008071414006080d0503a00e40354004e5a040348903d030780c000350340900005084070412942d0240301d41241d100d114012030644030841048044100c1840365000c4003808000610325071074002d00310507401c0c09100701418403100c140c003085c1000303101d8004401c1c0301d1301c030008a001c011080001e5401410a8400b5023018180030420700d81b140303d540501c000308050800f409540c205903a085078002d03d00c01a109102405100d40b442d183c0c5c07014401039210f10b844115a4511207002003910 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 626553848 1250 626552598 626552609
    0x10090e090303160e0f04141b042102030f0a0312140705090d06060e09010b0306011406031b0c01020406110c0d020901050409080706090803061005091c060212100906080106 75
    0xf000031904142040b200c0c040e681d0542580140d070901280400e4031644981c2c95040600e28003000545001d4200d45052492000c50105d440810001002991441c5902183d035860716001d1519040750341c00042c2c45c10340091004135050090540c10300070981c00c08a0020790943c00001408440400c503a4200304410480d4500b0101f06d082014181c249010204a40c0e491301c2003100044d11612045120b501d0501203505001d20b80d0345443c542d0007032404001d4540101403515218241c00303500c4001c04c0480c0005000064849a0065801c07200c00416090700d14440e0380e440210b4481c2c5e40d902c0001c1042080c0d0350541281e015401c1c040941c0d0601030300c2600384c140c0150030f510f29640780006020041401034000e4a450006100a000040050090903002802045031580f02c1c10040104460145e0010011003403100400141415464a0100b5128240031000c580690710040c24048041c0c80b40a50400300c0701251020818401c40c12417a010640303842d4041040a1501d402c004d50072076005001e82e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 626555098 1250 626553848 626553871
    0x1020703150212070e040b091e07020a0b04050313062d1404080604020f0d0b04030c030e04140103121d0904020406080607090504050f0402210c10090e090303 69
    0x5201003a4000448034920341d000c84018546415a901c2e8444120266402800100028801d00c01460030380140304094030111407161480c00c000b01b804a40b5508218071000b01d203200d50000704c5283c0203010345500107030491261170032454940b50141d241d0344407080d802c11058010300f011920b68424001004500c6513034603900f000c8000418000380c9009103503103d1080140000b846160768500c0710281c0b0050560703200070b10341401c061040003800460401c0540c007462202040901003020f42c80041d0b0800d40600b44442c080085080031240c28a01c0d80c1d01540003400c0000e00311070541200c40c414104c80c0241c1d00745000f159000350031a208103130001c48529204844052440e10320b00b1012503500144000c00000e0060364076104181081c4040f2101c102149900130300b004982400d000300b40d480078000c0082592441d050b40001c9034100750a10a8410b04089101c480c10020104018a02140014041140c1402140005201e86501d00450683c58448000720303000403c00401d0b2030040301640304 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 626556348 1250 626555098 626555113
    0xb0115020303150f0607030201021c0c0507110d02060f07060f0c0e0f06160c210c090207060f0518100501140607080f030f070f0f09120f050304080a0507060e0102 71
    0x4100180d0960890582d8800007405075131380c103541c4030001840070780c0c40398001607299443c1072826441010b0340b016006085051003a0141c1180c2c1c0407044a40b00c50344043c0381c074800f0702c035540403a0b280b034074080000b9049500082d49007010b0b010000504000380c0314000c1403124200f580c03544000d40340f00c1c4c5080c03001301e241c607101e03022685001c50400b2002d04000e04007601305040308003500d8502811400c00e942505248105024810f51021030320040c0f103240303400c07200c0510190780e240040e040741c0c80303680d402ea030303000c40c8090802c9155000501030394139418051019040a803d9180c81002044428003944902c1e0300103600c10984c0c1c001e040c1210500400d00d14001d064805000140d402f88404a4132441c040211044c0b24000c14055402401d64044200941c81c0c0428050324a5600106003403d0186074210360642d2035002c202903003079400e490230740c24034110946400d2030040396004009100e80404034000c0380ea04000140360ba04c580c01241168a0541d40d0f890940302c00d902c0007590340c010b820118 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 626557598 1250 626556348 626556361
    0x25200d0e0d02040e1b2404091d0109110a0501080c0a03090503130e04151401090f060306090605070e0a0e040605190507080412020c0d0f03090b040b04030b0115020303 73
    0x4440c0d003000b40042c10104001413029401820500e40518445886041944000c4141000031100c0d8400d1842006041155004401d045441c0103600c200c040241d15901070500355440380c007505580d105034400030b100b551450700c0c01c00c4001951441842c020b900000700050550f214600050050303a04e40c000e1490803100710f82c00c9003c2c040c041d0040d10644030412007280d120f40039140381d400030720b80c1f40101c26007400c00d864468020b00b403c01c152141c00d42800c0b140b0081e4030048032940d0441d0090280090800c02c50080035019241580c000707440980791413048001e206080e0885032140e80180e407050fa01801000402005010500681124410b6031b0300140c009a4554480c40e0841c407080c0803c01c6084100340074134140c4070202c808000040d0240244020001c504607003800e84a014005002c04003c200c021a03400019003101801403905c01040409040c02b03070040c400039002c0b88001a035183d841c1c1a0f0026668014402100c0d0606880d000080442c1001d008000300707c41c44d0302440c550345521 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 626558848 1250 626557598 626557609
    0x10030c03021c0b16020601090b031507020f010c05090405010602120a03050a09080a021b0301020301150503041a1305070602030702010905090619090c12050408040e25200d0e 76
    0x40c1500212868001071100c081010039a0f450311542c00c030442509034011030b000081c00e10708103901049266080089612950307401040c00042071620f1202041740780d8469904a103440d1003111450159480d00920450050b0322200070300c8800d02c1941e050203140d03130340c8004076980e40b00c0002c445803050090120400e001c1c0320b5006241c010202e100c0206900800d52591800e56102030b0100025901400107020407042900e100c0040c45070481c0214255894a00ca075040d2600040c10b02c0c0c20403000000007020400c1c03044080d048003003802d5070340d1001e01e000e00a0401600c505901664144241000020401e200000725610f06a06a40d2501c000d0314010901c04891009000198055090350b40003000b04a0200e0703000041c030600002007528a442e00e409005810230b04004c0c1c099500b00010080480d230040300b1a0201d07198034820321601c2d03503420030141160340e6082c1c818440101c402c900300b0220303074004a501008500c0707002600c3d0146010440d50b80c0c402d8a480c0705070205040c06111225860030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 626560098 1250 626558848 626558869
    0x15060108190237090305060c0c190b07081003030e120f010c0e120604211101050114130213061b05030f0414060412020409020f0d0606030b10030c0302 66
    0x3101000340c100411a840415a0050040c0c1008108000c141e0725180001e208003c0311903852a042c4010154216180c0329100d1500800348c040624000601842503402001346840302d4101a2108411014514001c0200002a00c0c0c2600054010380800c3c44181c206504004496240c2c58090010600d0401d0009014006501c241e181c01407004445000c0428000c03590802c40e1952410600500801044440f464510381c80000c0d41c0544100720001c0c2d51443c0c0200c090b000002e07214010307040c4c040208d40c0c0d40003001440c4425424031000150740c18041e07403d42d500340d100301c615006000ca2400c0050480c003c15201c0d0803491106c0e41c003042071074000c000380b020301510514901c040203000c3e00e429242d07910030f41441142c0c8200203800c01080c05840440343d0f0003042210400e203054a410910840c0810048020744a10f540ba9401c8046659600c02040e140704007401e03000010070b103820580d0040020340310681c0d0510840c0009110348111a2440c0107507030b4451002c0d5841400e540030300405603070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 626561348 1250 626560098 626560141
    0xa0e010908061006032d0f0207050f070302031002270a080706080a0b0319031d0409060207030f08060a06050711060f0c010e010605010c020f0109090c0f0215060108 72
    0x84400001c1440c810521515120f6602000d900d5240341c54002c0003001c844410000158414640e1001c17000e2041c02402440e04009118000c20590700501c07490000b40704900004009214194008208100214010303007128000c4054443c6a050f140940c3c05034860915904809a030780300c586048100042d00032120a1805403084a8840d110503000b4030b80303809900701b4808a980c840400643c9441c50158051141c0140c3c060200c8503002c024807000400b6006004051102c5043c0381400c500c210000558440b100400c107006043c000e06141000303510109007500001c540a0104402501428050340501c2c806080ca012071881c10400711010340000504584501c0701d0844600781e580d075003000c0c0000300c1c1c991203001d540d11001203404e42101d0401d020540a030341000420000c07a038101400c840040c1c2c041d01d01100311442000103c170500b40707a403c00c2c512640ba202094034010381c01220b1500282c196006c8400700450b80341e6002e1401c40460303503980000c4210000841003041032036550f07544907 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 626562598 1250 626561348 626561357
    0x1d0f0405040302250e16020c011d060f1206040920040209091510031a040f020706050a060503010c050f0f07020a0824070e0f060a02100213080c150a0e01 67
    0xc04c091824100318444450340ca4152800c000307120b000d01801c4104d030000010503003020340710648000a9100c06401c10380c3c9060140e0301f02101d0500941b2050066000c4009009698843d03c000d107440c01508462015442c0007000000203c90381040d10542d101030b81c101c0e118a02c941c91104070054030112580400313401580900c4003082944030b14001501400043c5c485000443d0220b0501000c00c81e2a81c80c08201801e02031402081000c01c2c0941120324016940071490b001040c007404081c0c4a008001000309103000300f004420360490780b155080d43d40c100c0c024007032003001c1d8208861038050f5400032403030a2030410981c0b81d2503a01e0300041440d81d10141012240540d510b0100d801e1080003c013181076000024001040745110f45903685e409402414290f0a0224800200d9010581d00400c3c0d8054040040c0740c803012802040a000904509401907681d83c2891410b80304903001440b07034207030a10403421202464540303a01c1c00c80583d07a070038400d1400c0c40700c254003c07241c90003408070300d50600 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 626563848 1250 626562598 626562613
    0x140a03060c17011401020f160620150a0b04110d09060905060106080610032304051906021803151621050709050a05101d120604031d0f0405040302 64
    0x20329402c81140202207840c08000c1c800302a0002909103403200c42c4008094224130029001442043c0e40340040e50000d26003220802621040d0501c22480440701c0e0300340d40b194000805028013805c42951140c4414041444201140320a02040d5030261180d1019184d09000280d95000c00754003120150b40940c034042103035003440d160320b401c00c40203801c020300141c0c4280c02c01100d814501900402800d49203800c0008000c1e0426407084003800c0c201d1706640b40ea01e07030f0128080c000c081240b400b400014001e40021450b5515081000f03611807101000058030001101f00743e40707000300303492841555440c07100e40c840c0e884111840820503e11941d00911801c1010140b00b16202c21241030010094000041e0904041401808000303c0382e00051080030720103400e010315107407007000c0d00300c0c10140c1c1000c00040005031a03800c01e045013010050f4000b1000780b0600003070107002649501a6004e03440740003441054006a40745103100d0624540c001c0400400c882e0241095806158024000e2040e035100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 626565098 1250 626563848 626563877
    0x12050a052221030828090606080d05120c2a0307060204030602092e0309031b030203041d330a03120210020726040b030c0d06140a03060c 60
    0x800720702d12095000442c1c140c1d511410150400d8846030041c80380e81e0500c40049030000040740f50801c4a00b00801c2c41d0302c030038110f01040825007204014040e28025100d103c0b030600c40040c4280c0200840c420019411404503078146498021203410a40749030b007251113805d4220785001841c1002003005524402008440041581ca2020300b0180d48100d4025955041220030000f49495516003030400020322401e1000001c11840c019880901c2401c4c08180c5000318142903801e00c2a818441c03040c824020320810070190b001c8010001d580c00d032200c160510704c00d0001122821800c60f80c1404000c1078020361403600c1681d80b20080082071145206100e1a2900c010601c03408281d07004503150b50030401c01000c6690103100761020741503480382c11401e021751621340000382d00b41e2881d9441c08100c280601e81d8081c0f20312040302c020740500700c00e244d9030b402c003411845000c7d0300c030b440c0880b6450b00d07102c0003144125200038100c92810000303244a80c0d842c25520780c030004100030040a010300c0380400c0300008 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 626566348 1250 626565098 626565119
    0x302100203070206040c0801050906060f040e010603061d0a0f031d060a0215061917010204051504091103040f17041e09060e0615090d0b09010912050a0522 68
    0xb1a00031503002e403a0307900f414605400c5003120360b040100310343d041078100b0003611400141d99500c41c41c221000581e803101031020034000c2000200c07044903542020008000d000c5140c100300c0705040d0001000182c00d0305540030039110b10340301e40000c101c0a0703400d01540109205201d816000d1507080c04002409149100040866000700041405a0406125503041e24440060a588081c058421901c44441481110381104490050240002241c140200892070940c192006030001804110b2400c041ca0f0701c0318038a8100e482130010640c101640c88501c103044400743c034061a4803161113610441e844e0394040e01c0e04d14103403003c0c0500d90188030000d0002d10406500618505100c1c01c2c00d0030790f0904c1946010744180750006044a407402d003c0c8038840d2503850b009a6201e900155450300e8400c0d00700040c13a860240b00c0040c2106c1c0f00c02007800300d094010340c0b0404c181d07880b4007004a0011001c1030190303001c0c0100c4030f107040459400d200506006c08a0380c1001d8402d2142c4071001c0507141c40da1036054 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 626567598 1250 626566348 626566351
    0xe0403020c0a09020a0e01030f090b130b0a06030201082706010f1a0f09090702030708040f050918030301170a050a030809160320211c0305090c09040302100203 70
    0x8005900c00d400d41c804030306200c165034000d4140da143c2940350403c48400508606d4801504904255440314428081d10700c0390f200130362140c3e200c2c0b0900306c541011000c0102030707460290301b907400280e050085101015684110b9007201e50684a440755a9100398801000150f154103080103090700b1451602c10100c10701c101800390503809000ea0506d801c0641c180000c0d50403804148050b03008208544007002450142c404640080b140ba940b250380c1c00200300d0650164803001000030402140100b40400424010700a41d8000d5441040558869490b0b43d032502c000b003400102900200011302510b010131800d040c501098004031a09030031030340c2d5241d140202c1c0c484c040d0001500c20b403c0c4148180140000d242c43c0ea2a84210407003d0f00310703260b1102440c00c4d40c005054022041c05034000588445070a04200c4010710642815014000c030490703141e01501104003400c2e420400c2402c041802031040500420401c002040000300040500c100b944002d0400e60641c4a20081522100700a00066 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 626568848 1250 626567598 626567603
    0x6050903190809300a170708040e0703060315180b06120a060b01030b06040e011412030a02010501030506060402130e0411030f0f1e0316030e040e0606090c041802030a060e04 76
    0xf0b0041611300001d942d28801d28840d2040c0541103581c101d8085480b81041560140031102a15503030394051a00154034401c66104030369240c2548200150b0070341591211084030b000348000c140c01d26948201004440c075030000d181c01d00444521000114400d042d415610407030180404495000d0610541d10b4001800d0341101c1254444413030125a503410700640040c540140d403100d0419090250241d40036205019480d20b02d40710340310040440e40c45038450b620440d060001d5030b50320508220000d01800e0240015945881144040fa0b4507003403d100311494070040c880c0c06502e15042c220840d2883c00003600994a40700b03000c01e0032519580620042d801105040e00400304418111022420940d80041ea81c685003144c4050300c0340585d0101c12184140100d820a400004040c541581c1005d120080b05400c24540049101c25080000f0300c1e9004480855203070020f43e6075000142c5403446a80141c41180545c6a407244007158640c000d1500300b10048404500280c032991440840071045070103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 626570098 1250 626568848 626568889
    0x1e1302010e04021b10111909030b07020609012d050c0706020c03070c05100903060c0908010606050c0115051f09090c080f10050f19090513030906050903190809 70
    0x51107410f04001c141503565040708180000000140200c03042e00405411044800c0705814440d4094850706001c802746500043d00c00070b07400c00da00005d40d1810200c400007515884e210340011011081070000c100d80c411110590080a1102c1c40c2e0406400c2c05810084a42400d0100400040c5240042d12254015100940d10f8200e182030030104a138481d0f00490140d64110941107041d82d101429209594000714049002190340130120340591702d81c0d010103a954645400407500d2940040200759605181009010201d00402e00d80c00c4048540314090b07000d4001d14801c0030b900610400c40110040a0403c648010b40e02c0c0e07402d00544203841c440400240307485040014101c841a101a01f00340c080995484131802c1401250300a4101010311344580540400520310b03002d5901000b018110304a018442424410750807002c0c80f0f14110102c01184c0d005a02050711445001620003965004008041031421110f8480c81a0100c0300c082d10f0440c02004085601d07140c00e8a080e258070000000d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 626571348 1250 626570098 626570137
    0x4110915250f111c03032910081305011404150b030703171b010e0d0c05061609030501021206011b05060c0306010309020a03030c02091e1302010e0402 66
    0x100c5240c20041c02464105007941d1900d404003088100d01402201544560f00b48041419074001504282501c5000c1200300307441d54920b000c060703040c1c02c111440d03a40d16030000007000b003000d0b0382801c00c04200f0010b9004007040107a501c0e0346100308801a0442d045480d41c0048103908d484040c2035803181032020346850094018441000700c44150324080c0c640c0588100102141c030b0000039101c609900c0060700600c00b0b040e280202411503011a00300031011042c1c00d104101c0b000701c06020b1b00003000e14051a0051400c49030f5141c2c081c03000c1c8005a584400a0082995440700f91401208454488800c00c40c140402000081091005185440c4002c050b605240780c81c2703000403d003040d007078401d03981e4150794901e07540010307000560190800ca4000c8007585a40d03400004800801000402960020021000100f8580c11680d03240c402ca00980702065255101c0003008101c86401030b15261590002001403a29030008410350758451052506c0c5c5480755855000409982140000c1440e0b1602000c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 626572598 1250 626571348 626571367
    0x304020103062c10060c031805060c010f0e01050601081303090504020d0b0a0501030e03091e03030301031505090304150e01140f0d1503030503010512010207060c0302030f131104110915 81
    0x400d810780c400c16104c00c50000c2030421800400141c506100101405509440000c415042c4810300b005048058401038131800208065400713030400340b01c3d101e07040745025480030155406005040c420300303040c5c4440503181c580314810552803034100403e904100d41c00c9030104042d642c500003054203c061006c0499060712031401c0116151140c2d04c42c03418146002d2180000340d00100907a0701c00c0c0d02c01c40d90b070380c4214688821800c01c3c8071401c00190317040c0070020011040043d001135060480180c040d0400140c0ea80762681ca541c0e225601603510340f0f0300d4040c01c40c0070783c5100d002d20005010301850641154410b884c101e0445400c004800c01c0000710100d000c0405400034410000b00d00c008a10b8101902e156441c0901030b88010701800f4000e401c2c00318401d813424401d404460382164040002c001c0c4508d0258010001d40042e035500c00031000c0140814040d816100c0c0e00b0703842c103400c402c0381e000c044801c5c42000b0081a628030300c41010201803010b035a20350344003c0041002010003445039138444128 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 626573848 1250 626572598 626572679
    0xb15010e0108060109180209042a08011d04050a0605042001050f0921030c030319020702011e090e090715050309060a0908040302130605030c010302090d0602030402010306 75
    0x103540c9810809040c2c01c0190a1380c0c0040320303408941c080c5102e4801001100545c401030720490202e80c0c1c015060900f207554113603040400d00c0d042c0c01c02d00080b001601240200b1102a42c0030b04c10307000d003446211203c001a40c6a40a5036400c00d02c600219802001142d0b00c0e641907031003c480598000101a0f41c90443e03143c1d840150314404400d1170068508118001c0549050043c03490240c02a85068241c3c5600741c0c0001c0c1c0380420391040d40c01c40740c41e0031968017642d0b92a803003155902424404d050061410b2680344c000e83d02c8040e41611440158204101d5101e0381c0174803400c8103c01c0108044000a040503600c1d441402881190041c0c0910b90801c052034a203141814109010040101b00300051000d021038015004401014003164820185c10880014003840c1c201a610800c440c0e407801a492090303001d00115013040c0c0c25104031b4900c140054049000f00310689801010402c1f43c5400143c26a0045070720507c14100013408603152030040e0344d40b4800791401e04c40f074000000400e4050080 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 626575098 1250 626573848 626573867
    0xd02160c060206091f051e0109020a0e0a14010c0c0506070602090906030a020d03110319031506020105220203190f060f06030804060c060e0d020709060b0f0f13030b1501 74
    0x20500140300c440c030110743d111000c4902003850301c90940d40b0400704890300c40440b401001d1306807d486c107140f15612010941c0003907200104410206401481c000f02d1410b19140d2207080f625500b203c10311040f01e0300010f40c3c20000420080768503801c0d544000c140780e0b0390007014041a074040c031001620740010800340301403d24094640c5210b903001c4111400182c2d00e1698070400f86178103207864030342c00c9aa815524914082c0811601c220301200000540c840c3d81135001040044c030410040081c5940c81000364200c1e0003da503010084c0300c1504420041d40c811900c030890702031018080b5814644030704244180301540344400c4840070700421181c02030003500d014020341640084020090b06240d5038400381c56119600c280d20074000004000002d018440d80142030580004081c5c950000302404001d40b101114010a281036240150100c0c0900e9004182c46586420300e41035481c02c0c0283c0c00c0c801e901c0c0c0000314401e00000d101400480004c000c00402d5001310100009842c08041030f90000d040d491a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 626576348 1250 626575098 626575111
    0x61b10090f030c03030b0406120210110d03021809130b01080f03030105091e040813061404050d1401090f1205070f060b1215010602150106050405060d02160c060206 72
    0x200312448022402054840102590606001c50315a483d40b40070b501524454030410f07446490f1040004007041c1940d1808400d84c4201c0e0f0804c034290700508290340c010080d140c146400d520540301b50f50724a000341c0c01008005902540503158011a13400200c0204003221407920764414040c89404000c6440c030710b41e0141021a001c0c20007500d819040035500e0205108240c4101c003c100441c1500c5040710040c40b60050a004204540c40e00d81007080c180d0b03010b2054100001001c90002601a00c14014003c40e9200f143d9050316140c500010800d01003d051800c0d60300c1c1b103141c8000301c0001000d01ca03a601c641e1040300498894041810b2400000742c2e10014036090210810808001404800900c0e40c40f07640300c040000c0aa1818000c030303a0f510070149a480403803040303540ca8680f02030b400007544e040341d00355400c59610000c40d00720544042c0b020320802c000314006101c14400e40c5001d801500100c81800001401e26940c20300c000d294200201c1c064034168030509003804940d6040c80110751250 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 626577598 1250 626576348 626576351
    0x311101e060f230112050a1a01020102130302210609100b04050f060415091a04051008060a1e020f0a090603022a0a02060f040f0e01151b02061b10 64
    0x6280146401d5500c040e54074a484110f880c40c91500c40b80e00805564901041240040041d45070580f074080080605595031500090f03c040542600d43c414000c607500c1a50f648202e00069203540d0a0013100c000140b488540369443c1400741e203941504000452184402034010190007091f1280a412210103c6c1014061b90600d4204495040840040340c0c10280c103580014450300525034401382c420090300308607940303802c0c03181100580140c0340807804644800c44003000541c69044042e46900940d11885940c0c0c0c2083c3d0004008403030590000226410f0280c8410034500e50450080890b8841c1d895110465004219030810a500c120a107018100e035090862a00800c1075400300004403420701040d1403002141c82c4c1d106003206020b04182aa809040380742c403040008101c030a280c00a0203070501c4c40d0246d48000840000e1a1f83d41e50480b80010406082d00c41c03031590460728603140c08406101d08809121120060700c8020040c40b145921202c1d40e10b0800c002940c1e14208065900100c0065 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 626578848 1250 626577598 626577629
    0x9080303010b09130b130f0e031603260c0c0f010b010e1c0611072105190c050f0303180a08040603050718180c1b0311101e06 55
    0xb0403980444072010401c40f10b070b6001c800c07501c0140c00a040310f040d0b0a03070020241d5a00c08110040c0d900114a41485810140209100130a0b25666809150520211008004011710100340544e03205155452110f41c07030700c0c0341c810b04518404080c5041d6600c03d640000000d5040390755005203d4400712a00800090081700031200000307001c60700368414188905920002c94408085101c010107159500100c140180009241506141d82260400303503268000c1d4044e00255038205d50f10340030f00e07405540300c05080c40502c410440c011a40c54485000788062a540d9501250081050014042200d8002e540da42f504414100c0c40b134000080b8400b080d8060481c98001070103003404d80c2c0c1a981c90740340c00035603690b40e5082103a542100c0c4012100c000030600c00451100c0001c2080d003408076145806200491060104540b020342200c410a45001c0f20f041c030303a002920035280c0712100c8180c070382111500700d0740c0c1d26260200e5440c0d407000e007142c0040410f07020b804146805844010800080b95490070f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 626580098 1250 626578848 626578859
    0x30402030a0215070b0c211315060302030105150a15021002130e0702010c081501200c180405070803032403160303020109030e06040f120204020c010c0801060908030301 74
    0x141c15103050000c0c8180000c2041e41261034442003581c2c10640c20545181041c14504800000c540c400d1140d40e01c142c802d003004d03640e031015490070325010300401300c043d0807050fa41d6155460500000300302071401c2e50b04c40300008050b85e02405024080c00d10142100720b0911850104030041999034401c80c50030a1081160740b40507004502080034049000015a403840100398165001205c1d0b08810000d401203410700c41e246a05501c072076200800760715907070382945072030071078445c0c802290034032500185460049032034490130703a0340c04d0307007950103000807209107640c160002518100311544150500307541c04104006c0c00320400c1a040181440c0d805907145042c8643c204200c2d180c1c244406240f1000703243c90741c41c5070310104001074600c00c0c40c5a10103c45600d03450b000780a422044001c0e0001010244071120a00d0400200c03011500c04100c0b20340c042e40b420f15084018910410f05990017a400e00c22800551001e0061a9401d4515030341c0c00320640c10400060b2854680b604584820751003440140300 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 626581348 1250 626580098 626580103
    0xa05060a090507020714040921080a1803050d2717181c02030a080a0e030c10030f020708030f010510170f0c090a1511010b1e06040e0903040303031103040203 69
    0xd8500021b8901140c150400105024080c1120700a21000124188040da4200c0404004440c179607581c401c0c0007511150004410360f41c2c0c2d0103e41501c0540b0000f00c1c00064062070081c245003000000c0440c545100154010801d0790702c6441c803c07400c0708624201d00300038040312a040445d9100c44880d0030011840040c4685c525119101e07805000304416000000300329035041c0a115a004040b41c1e5042a1407410041c5030300b240204201003040000800f00500d130205503101d003600701400e11100c01c020700804501a010724090543d01d181e00704210300201d86c40e030006621038644422034001070b514003402d12082c4000e10041000b009181c4450401c0114607804550b0043d200c2c855401140c1c4804d00404450b11a0540680d44403083c5240090840000c4402d95120311058072901e0300c513858241d520382600c4004440300d91010304410107408150098078504102c6d20060b103003d042c15120f038600f62071541c09036114440c40c0e001250030800c0641c50700801c1000e0b454030001504600309940400da = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 626582598 1250 626581348 626581363
    0x17060f04020f122a031b01080c1b0a0b0903280e03150906100807090e010902120105090d03090b0403032a111603050d03050907030b0a05060a09050702 66
    0xb4400c00760071a000d034182e80c0c0d1036008100645044280d408400b010960030000c02c0b820300c01e00e0804500200c000505207000310b502c807a030344d59807010482e541044900441c1c145500601c01c2c0c40b218000c1c030415414040c0031014012020b0a8401852145254144004446401043c1482642c02001540d600c4e0f082c410044000d244801a49418825000c0c0190764a10248070440d40501c00c491050740305078036403121540108202401d84429072900c851a540b104045c1c083c41c15982d0005104100b0010b03182d00c800c001080003000041d81d4041c1e5070000d042d01520340e8006038030345e4541d0700340642c1c1b1005020402c0d07425618241000740d4a1255900341d035100e8000d00c00350078135030b0f1038111070040000070404903208808070300d08001e00d0341e0050010744143d40328000800706109001164039160b0281c0f88413003c0d66003184c003d0440f0000480101c010b407100900c00c0a0318040c507040000000c1c500800c080c0120303110346d00802c02d498000280001501a94000c1d2441c509100600c490b5540124240 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 626583848 1250 626582598 626582603
    0xa1a0f0a02030724110903030a0e031e15010f03021503270a03020606100801030f0f0206041d0a09030504090b010e03060103230a02030c01050a03200417060f04 70
    0x203038640c0c04000040e4198014a40c0c05445000300b500780c1c402c0f40a0540000408a442d540100f103820441340010840d03004454025030581d004101c00003680703003c3c0e074a40140000090440d124002c1c0d20741842e5240d0240044001d49510101c409010640c0c40280300c0d0260400c200101806451600002d50391182d000e8284912003000006c102303100c0c041c0ba07984c03410904403142901c9c00c04030401c0c0d16564900c4d8440540040c0201004500c861903e0f40c540785d45d0003030641c0c2d1400c04c0d9003940c8a1203600b400050080b5101c030041d0702d030040180c48032409000100340610003a444218400714406100c40000d01441700e00745012070742d40000350008241d500f42d44d1307031000001e02c20103104010703140100300001c1e490f810700c0762a0000040201611012100c29140e01c0c290110040c901800d60b501c650000b402945900540703889020f951240d00508044d90080c50f010030310241c1901c1140d10111406400740743c40c50005410b00102480280043c00c200380503004188502d403c80b59070b416400041d000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 626585098 1250 626583848 626583877
    0x31201170a0b040305120108030903070509190b130e0102040905090f0d081005041107050106120c0909080d18050708030c1213051f0305010b250303020409060e01050a1a 74
    0x810141803040003960a46c48074031441c2946541c591185550b685c005007115842449600404109414010102800b03081311861b1428000008188100a401c0d000340107508500c1d100061503041c5054000d1060050354000010303900c1d070800307210070300f9594024103880080c2c1c4090282d0318022000282c0c1178a201c1c0c58034000c00703c0d4944041c854001101980015401030800080c00c504501c1000100000e07445440200000380c6e980000c5140d9560007034018000002d0200b0420080000e50414142c05108105003490140000c40000880d0800813022440000007180903042101c01c10400c006030105038000c5040c001c01c03010465549129a240f0110038401080d1980c4120b40c8440d210301a08006050b010f555000b55070350640c0444070708604000038145030001401512103012180d1280c418040000d101107103500304804810000d06c21410107a00300400610b0b44903034481d0201425100d50042c06c80e514003420001c0c0e1082a4001050060050a0400c0600d6884c804c544400518124 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 626586348 1250 626585098 626585101
    0x10e01050d0b011407050f0f0d091203020a06050a0f05060405060d030315090606080a0f0212040209100906120303050603060709050919020406030519331205031201170a0b 75
    0x407245013000a5120340d00b16008541c20b0200300002c5500102d030a41c01003100c442c2040802100e559140c80c00002d4049240a0002d02c10b41d48065008c0c1242400b90045800f5044281c0e0b6000454004a61400c01507a84e041102204070b801d001c2c050304510202d80621440c20000c000603203581c100351780202030555507455000c41c4101540c5540013001540c808201c00396640202508140301183c4000c0788900d00301080202c3d0500340309881445001c1c0035111510f81d126424030013500005445e400400700c50420019070241036002d5040944480009004113030500e00c0d02606490003d80b10b144203401c040100990389074400e2040b400c1312022900d0a00c15141c05c031034484e42d55800b0500ca586103000041c042021a015085036000c0e5006013070446d5603103114201407080710b00c403030281c4629a8801c3d032103080a1042c98421901300000042000000740c0c1c58207481e504050208044405810114001c1c508551a140440c01448140490a07a4460260940703442d244c0c5c4c204000e181020040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 626587598 1250 626586348 626586371
    0x30c09010c1e170a090315020c0d05040f060905090403140c0f070e060303071109061207080a02310f0905060f0117031303060e0a0512030405010b010e01050d 69
    0x225819150380c11030b82200b01c03010321004815915048000903202100800000140a400b1070100c50a1494903030303403c80e095095640d440402c600040310024084e0702172044000c0e45400b441000600425516025503903881c1414500000419901a10512100303060821184c0c440303d4100e035205600d4641091803083c4102403041a01072840010903621854002c0c0303401d6030700000c02000780c400c242d4075698aa540c500c20181c0c2c0f4032a14100524049404520340306a04000b0700b004d400140007001c45010200300710003107140c000305501a0741c03a41d021139980000d60074010b01008903012070741d042400c1c0b00c0b0380400301c40342d0500c8a00340c110200e03a06c0481c0c60800000b0b90101c0c0c45280d0044c00d41f501402c00705248400105c0a001b100d2648061400070301c480f0a0001c1141c5281c0c42050101a050f4590303103c040c0240342d0081c6880c807901540e41401c001540501c2080c10300041400b51503124241401c2c00d500710b591010301d86040c002050140c44560703030441d040d203102c030b0b0142001060941200 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 626588848 1250 626587598 626587607
    0x4030f0b060a0b07051609050402010e190504020a032703080705070c030f03030f2f0c0724091208042d090c03180b063a0521030c0901 59
    0x10f921641a0f12808140c0c40d0802c00085100d480315420103a0f202c0c0b45544a030710140c200e6070282c4009011031304014181d10740d424084c01040e4142c000f41240c84041e660f032000f1606a9000c00d022000207907a0700c00f9041c1841e042554180710060044141800c2070065402400d08000544864284100400e9030710070800204460009580d019242c1d0188050070700d009000b6000c04500002c096041580b01e008030344212580711108031583c1d000b1804a8003601c03008040e640b0107107152019000d88800407511040c0880c80b40e00d141c0c609548810075848444005004880507003104146201500408010078135000030348081e039650801e40800c00c0e40445003804140180c0d40481c0426a90307540c0003480784526803107140c50004580701444110444001c0001401507100300a108030408404250b01c1c2c20b080d1600d070101c0540503100c2c203401038448244484510403680801e0841144240102004000c1c8080ca045407030800c26250560420200d02400340002004a1000d080100d070303443c141c1e84103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 626590098 1250 626588848 626588869
    0x70c140a051f02071514420301052703031504021c090501060906051c06020714011a040f14060105130e0c07020f06031b090411030709170304030f0b06 66
    0x40304200301098520580004c0c0240210020800140b11b0000300860744030f10060b25a40610b084110390748a54980d070106c098400070960721003d00c94091030442d61400d1180c580140541403000380009100a01840403010a204202403508248140a8140b03181040c10311110000c0300c026841d0707e40404400c0c0d40c0210031084402080c1820190002d01106502c403038151084d81c039061050310388070405d0221299122134903e201030810000d03800451610f034050b01d0114480c0030b071181440b0009408a003540c005071003502898940040d600450b1406208840c003045072020244102125020882042c8100408241c144400000ea607240710560816020181c00050f6070351203542005030b017001c2c0c1038011682c2207006452000c105c1000c0e207060000d0701d20500440d5101002003041101700c504030b800490700e0942154a03024001c08104401d0040d45c443c503042e50b50307000c1c80341c0380040227000a019469855260b03001000b081c80420344412840700b0b416082218180700741c4a810114042c2e007103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 626591348 1250 626590098 626590103
    0xa2d02040212160c03080406090c0e090705100f230c010e06010f17060106140f1801030b1e0409230d090501031103040b06030a0209070c140a051f0207 66
    0x1c005440800001e11540342e602411203404a0444031500b45016124040304e0100500072404c000d0014001030740c01d400c05503103103100302c18210200d903880211a05640003640c60f0055034015000c10303c880d04185540c9a080096454003030110445108080c0081545a8403c007055588854000c0040410001c13119000c030428001c0228400c0e13090000e071608020301030301d442c03403000203c00110030b20007226240a10203542d002d000c050346022010b44907603200c4071214100d84420b1009507400c01841001c0c0126443d4040400f100034105400101100d440310000d9114103c1210641d80300181d080c042400000242c0300081c244902c4d0030901480703550780514540060007101d01e80d50300d407004150400101d031161200072340c10751100015000e40b00100b115003d400800d00c00280410341e20100c1503003080c00079040d501d12a1490700401c646c104100d8012000c030b031070264000100403a001c544220100780c038004e84204106070b5034160715803140008005016400508055520181d641200c84169 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 626592598 1250 626591348 626591351
    0x90d0206032712040b030702070b041401170910020c070531020913020d02071703240303070b0405070f150905010c02180717010801020702040606020a2d0204 69
    0xb0308207210390b450307401c1c800a1211001c405022181410000502c0010014140003102c0c1041c1c249080c9401c02e42000304610b046202c1c407103001400f100c4035001000500100030902c0400f000b0400054100360382010b541081d000b5290421581c14004644004010300c0b1800250744c4100c0009401c0ca408040d4015a80c050f601085061000f4183c0c10707540c00300518582101101104c0c080000101d010742d84586801200d030018440560103154010000320840003001404c1060b5911620020390301e0840d41c2c2c038000320000030311000902c11100440c040c91840343c640b07140442640880e4480c02041c80041400440c05c01103410400180a610302800035111018030320f681d240e001d0740e080d056903800c407404107501050104155101c0c0c0c03c00300c0c100d034004c0c1030b070200d000d40811481c0380e00c0c1c001000d844c101b2004102c214200080c24400a0080c0809400507072511100d0040004592003540b00c84250f512101c0c40c403000680b004100007548403000c2c41c6c14104030700c2074004554294010340003580325 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 626593848 1250 626592598 626592601
    0x5090a05040302010b06030906010e040201050c01020a11070503070803120a200901090e0105010e210f01020c01050c07020a0e0702011b0c0b0603070627270c03061208090d020603 78
    0x1240594050303480749001e07600034490405441c1c180252440300352030720816900701000501200d420b10440c15006403040c50800d1402c44c600e0407950881c1c00165040f40004d010030ba031901400420040040604022800361951a242c00d07251617887c8501c0e032110314103210b9130001604000e816482910f00d200c0d20319201d20b10b006484800c041c507900600056000c82c034681030104001843c8846207068074410b85421004420380c0c8104a0110204255802c0202c20600e40f0800d0b81002d1040c0205501500c00158a84844d05c1649081d42c2e0003c0681c001c1d0300045c4a020003507a50541e00d14103d4001d03074020f00c441c1e102d0340070490141c00c02c56011403465810034400501e0310352190945642c180180307201605034136803404050b1580c403a032091a0000d80801d0350183c503d8999100007018102c0c005840802555500991700c00700c0211880301d15080d030580104c2241c40c140d0041c2c1111111501e4100440c60402200f600080c6591034083d00600000c2801840c2e030316810500c0204039001800c20780c89 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 626595098 1250 626593848 626593861
    0x6090c0f09081507320405120303160513050306010e041e2003150a090c060306050d320f0d1106010e04020d120203091519180509 57
    0x2400d2a8a4840006208000c0010b16088007040072051441c075036401d0356040d203031842e049410408082550302035001c420440346009000c0c007000c1003601d20b042c448540380c501e000100300c00b100e480700e40b0901e16041001000340d403401c83c01d4044e20402035801e010341c4860b2402a60300202155410081e054032030000089040140010f9051103144503146168620081c1180d0888044140030002c0000003000e8540500604005100a03084006401c072200740d9402e0094020014080d078421103440d13902e03640007050002086040c2e0250007982800d100b45403400c00411841d02054038094968290b864603810f403880138418041012404141c410000140d58000f25121080e00c4200c4d04036100f00c0b29206142405a121500c84a10000c0680440e03860850314034102c050081c0120f174404040400303440040c0038580c40b40d00044240d0b00450315081007001340002803aa1510000d02c080051068246841564840071107a003070394544100c002035074000f61030a6050f140c220742c2d8030859407400c0112 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 626596348 1250 626595098 626595107
    0x10501060503240d0201031a091905070f090501050a030f0e0c032404020609060c030d09110f031b030106080106031119050d0b04020d14010507110601060207090f06090c 74
    0x20018000c0c1140b01c50240f564242026100b42250b40c0c0144000e20044003642c000e900104026004c4403140804030020300000d00044801c272544410028032000d005001c004920409900c15800c0c24805c0745218804e90241820b15288a42c130304101b40011030021035403003600b251341303804c82409050100e440384c610000d848000304070791103000b40302d40840d401c5143ca6406001184218982e08c1402a40380c3d50240242c1d640000358071900080c0c100030385403082038100000d0200407603101e0000388c0b41c94180340105070082840e010501c201080b140216450794007088901400510030201e50b000b04842c1d001ca400f400066000c0c0655504e4148000140b0910200905440701d003140e4141040050010031aa01e5046000c0c8a8000d648081e0202c000741e010b00c240c40e0803a00003012780c2041e40040d40ca0781603002002c0c032004200d944920a011050ba04405a00038032310b85540540115070418034002d6598841e44600301400381c03610030018680e4a950f01010160001e81014402e50303e03403000180 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 626597598 1250 626596348 626596351
    0x11010e0d210e0120070302030a03080a0609051e040314031f15052209060f0509070c11040c050f0f03061203040509060103091121010b0402120403051308010501060503 73
    0x15640940440000210751042e00301512000050711011010060620403004984210200d00a280f1a0940c00700c056a41007001b40611886540c2c0c0700c101c1c2c0341c821b2034001a03c840385c0c40300034aa4145003e0210441c1d2003c520f5080f2580007100c2e04907a030b02c2e41000c4944400211007e0820302c000010310989443c001c041c02c81c1808101300300e16840d961070480036260160b0000d22000210305101880220300e209200c20303c0380d600c1100300600f40791680200b80c115040c03030b0300c000d0704443e00715020052401c004514603803040b01c0b41404840c100d016240c9650000c003941d2081c1c07260303950315444c4542600880c20b48003444480b103009070712600100c1200c4400d6006581142c42070b40d203400f43c1c1d13070001400000c42c0c00341d0b0f40c05014840251181b100640c054800b0316011076000a961a44064946400c400c071101840d452100900c2840340074403007421142030200311b5000318010045940701d00703031685616401c2503143c504960749000c001a002c1003070b40c0c1900100d0040d420b107c00050440c0d44203000e103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 626598848 1250 626597598 626597633
    0x40203150f070e010c02090406200a03021e031b030901090803160801080d0c12030204090e0a03080c1206060c0c03030c07030506060105031e0604020c0d08010911070b0411010e0d 78
    0xd600031030f24100540f01240b40b40030003503100115500080005140f40c02501c00350346560100b05806281d0b1900480d00c3c2c011440c0c0900082d0b02080912410f455001e200c425002ca03178190301c0c80c600b0f0250203024507010949155000c04400400f20b5400182548201022a0000500ea84900304043d42c8004c581503d140100000c0398600046645000070807101081140c80c0c84042580800c1e42c6ea4000702c00c241542e0805141d0b00b17200c0050341042c140905ca0b042c160f50005448028100d00e0046d00308480502054440701051196a44410405201da40c220303d08a9a41e900c1e8110840303402d01c0c0003500b10003203030103002c0802c07010800040006d0368815244104191607039640c510b001100c10f03000c06c4900311520400590350703030854000c04020302d800180c068005850199001c3d0954503101801c520640001c800c0c60040020706c18500c103900598809005d440e280c03402a1b15036914a82c00504041d0200316140d4014100b40c0c0103e00c4007031261400343c2801d07100415810000301d400c0c81d0940c00c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 626600098 1250 626598848 626598857
    0x408030d02120703020a020d0c0c050a031505071d1c06140106030524040518010e030913060f05060d06080604080301030b07030e07120807050709060f090510030b040203150f07 77
    0xc14040f900900075915541c1e0580d004007201c81c064031080b40c5006140e0b03401d840c8440d8032500801e2640f14018154082c40c01403042c84100c510481c0808220f4500a020108024012100004442d01c0d00410380042c1c030201c60041c40c498407003000c1d000407003128800910310b0780362401d05158a40040c0c1c02c14100c80041d18204640c2d0b44481240d070002e801c5445001c03902c0c41042e09102c0c5031070140d2001d90400d400c0b00803541101c1208003c1d03821140d40440c485083c0e400072030750300d01c9440c0c441c40009024400c0c41081c041a0315090300240800c007940038003072165001143c01c0d41441001d078498402418a030040312407c0c103140c00c020b40241e00031300044c0d07030a504400011b15038500030700600c1d624010b0340004007020752a00c0c00142500c0c10b244811a0014020004240071403400c0060314040c0c02401d00015840385842c03646410304030154002c448180c20f140030809819a00301007030003265081010a4003e5407280300113810402c101c3e41070002c1c001c1030014010043d015101091041055856 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 626601348 1250 626600098 626600101
    0x1a1207171504060903030b1003020c120c030703140c030703180b28030e0106030b01061107030c411c0c0b0c030903060103050a0201020622060903050408030d0212 71
    0x80c05448400d8480d181001e2121140401d00007042c6a022411240c042e01e000074004030070303100045607514442c1c0c5140002e5004500c3c1eaa80890900880701b01ca0190041c80e4601044101c01940341e000300d000c003400f400b602c480e119000b84d44e050220744114010b041500e9590a6a15000c1c05400b101e02c0082c3d19013021b28008140034244200f116107500d0300890303d081d44004a100c19440a450f171804004241d216040c0c411405001d016040285101e1200d0300d915604080b401407181303100c4041051694080071080000c0381540340c00209139038800010540c225000803202a404c445422080d1800e010b18032000076008100007010382c0c4000855410807615400080b529503044079000c05015100810346c00c00140d4580001042c114001006407410b03c05880d0010b401c02c10264001e554a40103841d040085683c11b20085920485044800b15a0b8148001300748041c400c06900030240340d5601d054105160007101034400a2603010b00f01d0b503541070740050ba00041d42081030001030b09080d510 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 626602598 1250 626601348 626601389
    0x90e0a050103231f090203010e06060904061a10080a0b030318010804061d0a05060903070f080307200705130203040506061909050c0a0f020a03121a1207 67
    0x82074101d070341080200c5110380a14001581501d00201044098030400c1d000381d41d10003104030402228078980c10001442e19250040c5030941d4070628150780141c0108080210590301d16040342e804c203400400008080482404a0500745240001180d0143d904d00710030881d1a8081d60252203000c035020203001283c40503040c50368074000c25503400e40c401e2803000f01070b2195220b083c03500c1d440fa0240ca800b05030000c00380c0e40c444405c840c07100390950329000010070390b05120040001d550041c21080040d440c200b05074444c0e12a0010803507000f800e1290000109405c07034032592034803294040703101e064800807016203d802c0d91000c0c54407900d8000c08907038840c86801c041c03600c241c034800e40c1c1060260403ea554441000032a00c00d002e03421035406501500031411604ea4403a40b803040303140e00c0710182c0c2c461040e8005844da910780e4080104641c0489501c5002035071100701d901c8910f22080c004204034515040e900300e5010f244500300e4120049146270109100c0000d544400c071402003070880f11400390303003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 626603848 1250 626602598 626602601
    0x50f070b091b060a050d020708040e16110c010305071e020606010f031407030b0d08070620090d0206030606120c07031e0219060212040b0105040b010c0201080402061315090e0a 77
    0xb41206035001c0001d100d81c01140740110001d0900d2034140c00011b251440e0350396445420b4009800107410343e41410208a4215005501c1a04074400340c1406210210607030310156940a040c0c1c51241010b40314008220301e03e01401c0440d410049020045044e040d441034029690903048a10f180010b8802c0a250015402881600c071816a210728445140d65071100a030054100c0341c84543d00711003d031203508003041c04000035146103486070101040180c90058400422040c1c0b0003084041201004200c03503955401040c011041d5050b0381c040c2d12559668000741e480d004070101e4619100700361003000185039514001740b13aaa4440c0d01c0b03048182c2c4041c586007906040c200107010159008540d0300480040c4c0c03465a0303402c18458400945001c0703c501180c02c1c620002d076011a40c0900c0c1d5001805585014054640c6840c0b0a2904589010311600002d101e9040035002a005d1200019140300e1250402c4500004c0c05052040090325910200000c1419025101d038900f013019480c08030303003100d455 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 626605098 1250 626603848 626603893
    0x150918110415050d0311030f030a11210a0608030708370804050a2003010c030e07090b061327060609052701060905030705090f1303050f070b09 63
    0x70940c0801980b420401400031081303002000307405106810801102601c0200300a003410250700d64860740b41e0604d15804002d03070b8400780e4004801c039801d10012082e1900452503010940c860034650001c1c1d200d2156000080001d5000000103010000b82481400b03400300062400742070361340f0703604030000c507150762460040c000e40c1c00e800c000c080c980035840b10244925000768101e406007003034074400e080d01e81e5214181490034181e46c0300c1e100c550421140c203203400e1003080c4103d070040c1028001101e02c01345c40c9481d51002e01500d4100c1d035803000c06884544848054400520a94400201141c1c80e2280d1281580d500103c2c0761452a1740c044442c019225801a10100d91241d00c1c1c4145041c00c6c07004000620b040b150b2a108080403081e81c010300581800c00d070500270407854986405d581d0400b410b1600302100390300b100d03000d0351060301405032090104500315444102c41d8441c0888001c41d2130201e945110302c0c20a501c40542c045281e42c00e20054400e401c0c0102c8241c0200c0d0f041034201e04000860303808 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 626606348 1250 626605098 626605121
    0x3030412020a091a10020c0a031212061a0a031103150909010207031409061204241a0d0302071a0d1a01020c1306030b0108010507030b0a0b09041509181104 68
    0x4c54070b040403180c10020820900c920301c1e80160343c0741407a20404190b9010b01644152602b03141d00840010711034118020340620001a50240202070800c028031803603c1c80e0341d1102010000000702011900e10031740c400904000441c210300e0792420a00301040440c840c01c103459108000740b80205041050501c01c4514a6605480c0c0383d45070b03803142c9001c0701d40d60060900c0031303003040303081083c07060f4450484000d511443c0b04640b900c0e00c200c800d01c44030149138603481042c4440740c6492031030048190300c14a0010668400c071422400e01e681460100d081c500180e11141540b2640b10f0007030103000e4808003030f0500180c0210100042c11b218000d00b01100125028580980c102c5241090b032410001c80c4034501c208100c80205815903030780da5030403250100741d1042d40c203655183e090040e01e581c18001c0d541c9503030307040f2810f80c034060a201d50111203200b041441c88c4190b079211b180e0f800e6846244001c90050548a0081154402a01c0c2d1004e10b45030a4404885d59a01c0001d5000310346841d2168540c3c040c2d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 626607598 1250 626606348 626606381
    0x102070305060a1d060a1a10090b03090a14010614060a0e040510120302010b0f010c030206070c060b090a0b04060b04062a0b0903120714072003030412020a09 69
    0x44643d1207040c0108852032030048401c078640c04034002201c041103014040c041d8082e0000d00c0e1106100e211a0507200c41e0002482603401d03440c00c591840e802000401624621950700381d503900c50502071441c1c108040c0d001030030705013011480511801c0c1940400c1c03c4422480803ca004507660f410840d03188116031640c030104009401c0515141850b900255100318560a9050030742c0d165040540d220300e0500c021030051b9112120021103040215041c5881c0c542824034200c0c4800d05d80e006510f0350801411502041701b034100700c100b402034603080042c00e068098601c888500705003440c10040d11a1032690f500407800c00c08000303010b500100440b422217a86645207000c141c003c415501d00305020912080c41d10b01c0c0700c078282e000b054424110ba40641403c60086548003c52410341e5249040248a103051090404100da00045a40101c4000c550b1012510781c202c1189000c04240800d5401080d400d071001240205289241056980309980200d0fa030403240c0b90780f00c1511301615400c039100154603 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 626608848 1250 626607598 626607601
    0x80607171b0d0b12100e010501050a0e09100c0e0118050a120302030d05130b0903040e040f02041509061d06031b13051003030f03090309140117100e0105010207030506 73
    0xe1640c00054100e0800601010442c44103881c00a1442d02044c1c0b031082464001c02a00d1141105c14410b2980401076000280103540c9450f0021346150707035030300c40e111910b418100003544098041c1700703a09820344149030810860214040c0100b141d034030744440a000c0b070030702205c1d0300140000c005604101c80004200401a6081c90118003126850900450a601c42401080885071490158921500030500d24441249a90900421125010f8044821030b0401c102c28418041000301041e4015001082840f80b200b552001c100240f0254909203182d0045000105d2214041d400603421184255400b2456400c00d0741c03a121030035006c2d00d41640c0740d80000d0b00b80038803200c20554144445c600510300f60244450004460507543c0c00c03140c040390101a14400d00405401114500610b14141350070007074810940e4024103100564003034249090403088554240f13a10171003003d510503424040340d2180b070400d0780f4820311404c42c03805400c00d4640d08100119255200241344411039420900070b141c0b0303 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 626610098 1250 626608848 626608891
    0xa03080a050414182e0e04060c08090a020114070b04060507030e190b070306241d0616020f10020610140a060503150d0b04030807110d03110c0708060717 67
    0x1550b01d0030320704480c1d52031170034400000c1400ea84038400600102812000360315151501400311241500a8414803401c002842510000000e5860030142d0a0800380020080816000c9441c054883c2c02030008070307103204010411603c1d4008030701030441510248400541c105880340c40381014100f50009100480d0ba803404641155185030300180b41d4280010007a440722030b200c00c038030304440004054050188860035910340c0b206070104400c44c510104240d1402880005d60184503c0000c0000503100354401401e554030301d039001298003402000304060340100c04002e901c645040761103942c0303030100d03000c0010b01d07200400704084440e40080600883c6810010151340c90381014101c65501e1040341441d14254032800c80c110301c11402407544035440e24103441c000f01400c000070085400c014000c0d059a400b1800090381850008182c00d0101c2c1c000b035500a200102c0c010110109075501c6003840000d00e810010a10324002c0b101680c230110010b2444a80202c0c0d1346094a0b0440e10040c0316610480c0b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 626611348 1250 626610098 626610121
    0x406150320090d15050c03011d01120303020903150a0906061d06090a090203070306020409050a0618180b010b04030201110a020a05010e030309090106030c0f020a051203060a03080a05041418 83
    0x5181c0704d401403510301e080045519084890448984c4e10844002006101d608880082c0300c0a100c103000b071294440d81032041902d440680c0d02c1c0c0c01401d0503008034120500f84e905002440c1141241c0e5001310552401000c80805002c0601c81038030301500d0600301080c1040c1503800320240364203043e0104800c3c6c0b11102800152030b0000c00d0000003130341ea4008840165400d1081000840c06100e0168807241090b1001003102c40107440aa40c541c07900c40100840a206650040d80c04d013100f800044105d04000c001d40c1b00b480000005201e4104040003044811f511406801924000c2c0d940626103030400d18603954980480c240613502c41c050250070800f540c41000701040050014083d2828403410801103002d00f030b800c0e000480402d45a40380d807110740c2d500182d0000058070790b00c01000803400b107449a540343d020154120801400c00000500592501805080150b600c062a59a5800b00140081c10382d00140103012200711038030701e1801c403490051842d074a2000c024045102d59160700a1080 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 626612598 1250 626611348 626611369
    0x60d0206070f06060b190f0207091505060d021e04230f0d05060703110906030c09150712030f02030108031207020f030c0a02030c010315180605040615032009 69
    0x2c81e4542807004030000a45240100b10042c90201d1419883c2c2440c000400580840c1d140920200414a28410740d601d030300190200031540100400610345184040e41d40242c1c8042d088903412120002d00c441a01c907560380202903245408485c40341a64402e1075a244c50b10503403089525440b0303100c116080c2854120210080c0010003001c80c102c2c1e8440f40086a841042504150340e40c0e0000c40400c8401038041c0264290085039194843c80c0031050000514503020103403507030201d0500400c110940b40c03200f0580c444000c0c090034086480b60a0b034945000c0c0c4064019040c07000a003409242500c501c80c0c1c0c001d490580e0b00001c00745003010045400040f44030b10041c6490700310301c1885080d12115600340000d100003c40c0c81c001e05591905401454078013004c184806040500d440c0c00c91714020301c000030000c142c5156050405410242c1c0484202801654020039071041c50410001754100740c403105441c40801c19102401205002c0a100280304040d400350000e10b0010020a501c0b45003050192 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 626613848 1250 626612598 626612603
    0x709020c0d1101060e041112010c0507060b0a0806010b131a0a030203092b030e0f191a0a0b13060608010504020f040305060907031707020a2120040606030203060d020607 74
    0xd411340e40d5030000c00c00c04506903403d42c0c0c0365100711002c5e43c803400c1c8140d110890545500003440786482c035070380041c040c0c4601d9038007500442d035a0300b4484c0d2030366400c50b6a000500300d050803202d07a035850b0a40c51881e070344440c01500c2040c41e1f0b0600008c9040c09842400c1140112601030b80c10310184a00c141d02940c001040e544e554080d00001800c19080b40ca050200310120307030f60440c03110001381c00c0074080720180040b10310254003050210700a600b000616941c41c0c03414241030f0007514203500d48002c80c90a0300540c45401603210081040185240c1c0c04154035141c00c0314810200c0c20340c18500e0044490500030080000c040f400140150b04041e002840c1a0301c204604a00c1c050392515900d0070b005080d6000210b54110420030010b00c0304044a032401110f0305480d8034a00388095000492865076445040d4010001c0d03800706c0d01e0301a41c421002c002c2500071059080c82c003000450140110709943d00180b003540703070680105200d48a4401d42c1c1c0705000151001000c0f5003d0340801090f500400001c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 626615098 1250 626613848 626613851
    0x180201030f0b040603080a1d0f10050d0e0114010e13120c0503070809091b030432010605190303050d1518020a0305060607030e1509040c110709020c0d1101 68
    0x8a854a495a03c00c0c1380040d801501c0568444031102801407115071110041185500d01c3c0c0804d1104d9518454507202c480811524041c1c13050000700251998060440f80004482c5840f245403081401900403070095043c00720004442d81c1c031201d510038101d20507a0079400798800c0001600c0018810583c00711802c0341c40c00d00303c000203219540c0a19541c0601004c66161601140c0e12405040040321a900100c50100c009000002c03000c0039840307400700400142039204a030500c5550441000b6800800e880d6003416040c1182d01e8125445c040c1c00c8074415a4001c159003408460402c0c10b01900301c0036298507a0b612842d080380c104520010b81307030449a150240c9094030f0002044245120889c0c503403005400d0258440d20309440140460b4802420f0b070380a44010000400000e80c0158040d162141c1200c54805661540300c03c0f6003e40942c111b03845c1c0103031030140f480081580214000500d2088001161030081d180d0a03881c1c01e90154070420b034007070351042c218045554003540c2c2104020801000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 626616348 1250 626615098 626615111
    0x2805010f1e0219050a050105010b0c0a0305090a0504050a020a08010b0a0903170c0609071e051f11060a0920090610050706053c1902040b04240201180201030f 69
    0xc980907000101030f04079043c2c0e10075000364041103800c0c000c803401061412100d50414540144280d03c81c185510000c040000005130260155100c03000c41002e048094000c00262402ca0f003d64020340c440700316200490596400080c070f00401d8001c544080350141d40d9005020314590350b04411036843c03080c242a4880620680620040c100a1584502c07003403002042081e2800780810000c00b00303122880c001d01c2040c3d4042c03141d61207070100c122000c6007442308100070808440741101c140d14107201e01c01407030141c0e0040c050002110313000700b0400c174010a1101007201d500841c6605442c14400225040b00600c800540c46140210028228070a5401c0040c030b04011a55214101c41e4100c501040203181e11101d00724070302c8003c1c00117500000444452410b08d4140d09210518000108442520300b10f82c0740071181d440f8241c050380c00034146210403d80311500c2e07118000310030001c00040c04c1d080151025655613144140220010145100c810b4021502590011000b81400c0d40761102c0a644844 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 626617598 1250 626616348 626616373
    0x204091505040b070908070b030601021905010501060944060708010f09020a17180a050d180b040513092901151202182805010f1e02 58
    0x1400c094a503108458002103519207450700b81c0320050081c040a04000b0f0304a000d200c0c0381c1c0001140400e0700c4107220344c0358884d80c03500f004074680320090b51035500c00c82d20722688000f00036054000038181c40150b01c41e50111921051009481c049000b040002841e8010118412500d09403032480b40a1a9620280352003000c65100307882c254096802c5c200092160004102d8500b414032440090304011605602d4400c40d61801008014403c04000760101e40d0000705400e0110300d200001c03580807031800c0d501d01c0102c9042c020740f15103002514a000c68108c8069aa02259480080b010340707000c2c400c6242043e003030400303100b44440c005040350a4140d861219801003625268180103072031201c001a11001c030b000d07400c0780e5040740617888904d81144140b00e12021a40200050440c24400c00006840b01e0300b032035084050300307580c0300f04540080701c6642c0166500450449413001600069101f40c80d42c0d40c0300011a0241c5441d2400e600041e28003104070400583c2c18101c0b503100740c02d031040b0358492291a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 626618705 1107 626617598 626617613
    0x1003090f0b10050d0c0906061e050307030605130903020c01020d021b03120a050a11060408030c031803040603150e0c1b1912111204050409020409 64
    0x500006036000742014070b01c00050030300401801280025040c10114101d450060910980c01c1400200f41240501300c802e042c1c01c2100e10801040c0c1074040221207540000d8060010191100c000240c190345985003460501c212b03080003d008031107442c000e85040130784950b4a0542d00119082c082e6160003085604c5c1c0e90341605044000f5418020019090010103c442d007020840030030704c00c00032039105000d0040250316480c2d002c9001140c0301c555559900490340109103500402c002100c00c01d0300300c00380da0000804080c1d5402910240d501c1d41c2181c21035040040002e507200c4500076081d05060000008100c440b130300301e4032801e003040f54071114814a01c81442d00100b81c01c52040c108400c00400700c5030029001e5010381c10382d06152900d446c480c03200b189030028665801803002a04082444107400d010207010501e0a464032040c407020300384400c2d044c0e038031075640d1450001113900d1 = true := by decide +kernel

theorem cover : BRFrame.Cov 626438848 626618705 := by
  have h0 := BRFrame.cov_init 626438848
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626438848 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 626438848 ≤ n) (h2 : n < 626618705) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
