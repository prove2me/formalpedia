-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2192
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:57:13.178847+00:00
-- url     : https://prove2.me/submissions/d99a0786-1504-4580-b084-0004850614bb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 394064748 ≤ n < 394244604 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 394065998 1250 394064748 394064753
    0x306170312090f190c1e060f03050f07080a1e0f0b190e040302030f03010f03060e0a0c2303100e07170a0b07031805030d060e1005150c10051b0304 64
    0x184c0d24008252448109080f10301c286042005c2d2070740c41e0400c3c00c000c031500903599585942c01c4202411210240c84509207182c001c0002c030241c0317400f00c40d0a03403914455070100b40703410711958000d50700c5005030000007180700b186030105108030340045207036180948462250b0a8400b0034890403400c0042110302c036643c00c01c1c405030815003004a1145103503841c0b00100040916001344205c550001c02c0c0d00000e5a69078461042030308a00403400b054078654a0103076034160316000014141e2590307420a01c582c0c0210f00e8030341c64a00b404030040030002d04850100ca414a15141001004103041c01d001c000700b9640030030008140741950f56485801484c0004102002d07402e40854110400c0e0340254414400d80d69100b810750240003440d00740891030b043c10103c03034280080400607040012000d24180300c0e80b035442d14011580700e0140c8841c0400010755404018038508440c030700358844a4101868280035188810904003504505020103194541c81003003a56550703a01c07424000c080e40030100b400e505068 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 394067248 1250 394065998 394066003
    0x9060509160305091603030215010801141611030304150e0a0812040204090206120a1109030304120507030807080d061203050318030903010e100507030204060503160306170312090f 79
    0x201c0c4040145507841021407881803050103001c01c80003540500080c140c0c1c0e2480d009542c1d000031000701c50fa2254000020a5244043c09049924420b8a10004054550740420308807110301c295103106100071101c00342d00800080c009075115034001c009602030354a620403038a055072080c60010040d904203a80c0c90000490100c10f580c8c1c429000c425031012540c941c03000c0b030b0007401c0711040654030681c040354004840741303d03541040c46550342c0001842550f2180641c02074500655031180d51540040c401841440180307a003c0c26064015412102540c0c0d80b6140c1c0801c40e031005030252140c0300d00082c01d42c401e40c51801944000c220349100074480e0100c6d514010540e01028003481003104240d000143d007405c040081d244d41c144e005008020444120307240544d40c1d0901d80c1d0603820f05041c51700103803001e0b00900c00d8608407407050f1501d0745140c1d03c642d0400d00755114030104109060381c404010481000704603012040e040f081d0011540d0780c114400c0d40c500000020501e106030350010800030001c01c0302 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 394068498 1250 394067248 394067281
    0x60a09020f090406030b0a0b09150105070c050409051c1b02090601110d0f081602120c01021611030c0a240201020708210708090601050d020612010f09060509 69
    0x401030301e603a40e4844844181c424145010703842428141c021080c007a100d041180111007100040200340d02d01018000500002c40300c90886d081211400c04065005400410280e40300d400c0b00c0c003100d5140c000240403140641ea0580e5107501008011140f10407620410809402a0900c9210080840d403444140700003500c0081c040c08001000c00c50b264010b40c000d42c00d01042e030068510404141030001d01e50410703d00c0300d40001d013414011a10310180d5100300001c01c2e00d594003034580604d189031900e140f684201c5e203840241d9802c100407804400d9021000495038440d460030340c050b8148108040c6020305041c0f1032446926418401c00000c45000c1465504e00c03d0024220b18041440b14140d009000c2d00c400580420b0780090740d209103d50f2540d55014100c40328101c15216114814125603020302128140a10707484100180154500002d02d081a035100030030700c0346098040c2100c0c10a1302d40030703445098120300a04061007010180d004600c09000150fa0034080c0c0c1c940110004103402a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 394069748 1250 394068498 394068509
    0x5090703060c0507051f060506040b3c0403060e16030204180204021303031130091f0210090309050d0317010b040e0604060302010f0810080f07080d0503060a 69
    0xd6401404040c03a000b80c0c00e070313420b10380c2080070ba885c80c01601030060700d03410b851840d09051900d050000b03d0b00f0710300714042da42500c3c1e000031611f040248051a66030702d10348400c0ca51146003201085200303014000400d109020f0721102000382c542c0c6c6545403801c01da41182c507030030750b072600000e031200003503420710b03c80404607501158089144c00900304035a221000c61440031b904580001000391515082c410f01204030781c03280d41c4126060b01a400541d40780c040c11742e04210840281c0c0d840c10a070403090340d0b40088540010906600d0409094001042540071140605088410404441d502601400001050200040305110441d8103a038000c0200891740075940c03041c824000d842c401d251045880d1344408800201254465842d54002421500544600c507100400d0000083c0d40d41018000c030003c8a90685034810260380043d015075041d48000c00055031804110f000080c1150208042880c0d82c8080000d014264100040c140c18039002009400c1844010800d004260b19001c0c0d245080b40c9 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 394070998 1250 394069748 394069751
    0x1060f17250e0607030201021801050304020d06090602040e150901080c10050d0605060f220f0e18010c410717031e06030a0302060a110c0616080a0509070306 69
    0x9804801942c620b10000081030b00058003188010404d83c055008001903010216151480810f440044403d1701c003c40d0002e4020050400c03150025078a41c00c54888103104090160402d40c855120803c0144100e40390170150b1541004c0e001c0a0a04004a50141800001502c20600014045205509000c40c027000300f0000140140420302e061303000f00042c7c400104250fa41c0e921401041c0d40e42e42004a0ba001c541007408001e06800f02e0b803050281c01c4030b0f081d6164151161420180d00c59900c4010310400c0040b08041c8029660042803040185001c0306445400010451041c001080c100020f501100d956032002e00300341d0602d1056940c150400524112030f9106800d18008014192034940c00141c06804424403440392000c00c0600816111440c0115859640e1000c0554402c01c0040240147e0084400b280c44007040c1d0700312030700c0a11680e5403145012100310200740b40000440d20a80f108440c2030640690b582d020061940001d0002d03414030603400d001c0300203915800c2c2d600c070040c2441d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 394072248 1250 394070998 394071061
    0x5070306031e02150c010b060a0225150f170c0a02070504110909040804030c0602060a0b030102180603070513030c06140309060705090d08030712060b0c06010b160b01060f17 76
    0x1017003d4000e08030b068800752a0340d4441641400113540d80b029070070700f40c01c245526084808051f6078444d130b00085854021640c5240c07980c10005a0b25030f440c80c1500c404000c0f002c4401d605070100c1a440c20301680e41c01c000981d540c410000028201006070308010300c00c50030004000c0e00880c00c2ca0907280e1744502101c8040309901c8918017141e540c412603000900e180039114002840a03004160030f807060000c484140628020001058200e10038035200000c01882c03074084000034100300307010750344c0003604d401c3c800c0c40c01d03044035091440d94060341c0c0110350420543d03005000050380005840340075001401160305604200455540300c04009001c0401c100c00826040c0c80c0b41d9030210b0b00405a50000082c50b81c80c00d110708001c1c06001001c04080103d400c0c103034000f6600c04904204e96520b0040000703008a0390820554501a40c0152141d41c41c051800010501140c0d8a49409000f0301c0942c030f50280b0480d280001038000045810601c2c20083c15608101040f65158282850b07990841c4034076025 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 394073498 1250 394072248 394072267
    0x41506030e031222050f0106030209060604030506070e0604050a0801020c0d030e1018020d0b15150f03042136182901031a1f0509030105070306031e0215 67
    0x80c03001130000e0003500c69450920403024065104500392802175422201d26074451083c0305c0144501d00c0018620340c0700c038001605d940c2c820601c0d2045404010b00c1a4501075a4100080d11440150000c0400365400602140041420044242602600d040501040e801c0280300c0f41c52320328048000b04c0c0c1c00d03140c4460317000400c050b4035200c002640c003e00000112283d8102034003240c00855840044c01481180c070655440d060f000030300140e0035074405a1611414880b000303050340002d4406c4500e4402144540c820290201c120540c440061780d60144807031000e0540c41003114540b5003140c440c000c0c110b100d41d010aaa50f00e2506840d020300d240c00c001c0c00c00d2a00040104910358050401548403c1c1111014200003c0c0020202d001d980070300000840380803c13a505925492681e500c0f8120a1503c0d208840d02000e0100880842c1041810101940c000c04e0a40d48112148800243c2d80d40c801e0040050b240564110781d8883e428410b000d030104e03408103561030158a400c1d2092800481e0b083c0c1b1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 394074748 1250 394073498 394073551
    0x1a090a0204120c15020a05030a0e0a0513020306030d09030c06030c0c0609030302030714040e040308040321200702010e0411040302030f0307020f1e090a0209041506030e0312 76
    0x6168107044480911201c0c100b114543c000e0f070094018100801140d11029440043c0c0300403d2a00700014504d0704030320000980740400c038411030302e40040c0c5401002030741d503440f40300348992401d00290160b03a9140001c1014104829030364100c003071050003401800454010340581059800a00300060082d480610a032aa00c0c21108000d003207a050a80340c0041540c981c001d14012a42d9032500c101d1074451045d85443c83c0901d0107a40c9021400d82c0008010a00ca095081e8005019052030707411801d1502c500c0308110b84a40c07040c2c03030441d181d074859192004031850400301140d00c80c04285c00c122459000806c803079001070360148100d48035400001440c60b414121001958002c08403003549040c400320b9910781d0410a0140e02c2002440030700c0307241303040150480041c800010001c3d9421a400c10070490390001c081c0c08407031041d0382440900801d44075803207107540208100c407214604501e4804000d00742e409202e040000b0b9040ad201022000d04c400351016084041010404610500e2464120 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 394075998 1250 394074748 394074757
    0x6171b01030603081c0b01030207050c0f061b0607140705190602190305010e1006140c0109020d0819020304320d0b010305063303010b0a0b0a080603011a090a02 70
    0x3800b00d4030005401c1c6018107040032005c401d4a0310744091100c03910620041d000c1b401140406042604801c95540041ca420a544003072400010501410b0000f601d5490404803019801021603500071000d00400c990855851222089020209413a00706103603156034580303135030303150541c00350400420302c10801c4641d80648406450001c0c0c1c0340310ba9042e0120080103060284940c4643c0d85500340403c01c914030103403088084e11056218030189684858142810350b01808121542d5540c0d10040c00040c2e40740106071a1060061101e1512074101c0642c001c4006100421001550300800081200c402503100340c035107100803c0c5072040c20202d1880e24040d401c24200f4803030b92052443d10500d00b00074800200364142c034000e4084a510b5604c11400303c80e580c0740c8181c41c002910320203030800c00304540f1f003030745420203503000d0b001041034039154000c1604600e1540013086400340220700c01c48003e40c03002103681d1020089000b4001000e07802900c490f04064080554080c0710358400062610000e83c0450b03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 394077248 1250 394075998 394076003
    0x3030c0d09140d02070e01090b0616030314010b0712080403141c05010608091005010305070e0618070201050703150f2c0c07061a0a09021605060a0506030106171b01030603 75
    0x22410031001e0030000f0744894142c043d41c00040c6c4002c00100d40d8006902c54500510805407900380b800c040c03049034181c0744c18080b404504040d02c03058000c1c1c0c21b5124042e22802000d0040c64113844542c28030700312403a504402c003003204100c1840d08000210343d101d200c22180c02d40d0701424a65504d68108058170031152280041103003030801000240c6140d000701218805c0741010141c91881e1000d0800e90282c0d202840064482e9001038018018140e61941c1c0c250400d4004206601e8011140701d640c800c1c403021219200581d42d15002c00c88100d0305401074031481218480d02800090910781d134081e00c19024040c8010030740c104003016407061140e05007188c0100d0302c4446c2c0611442c1100056006611280c0115055070420803401c0902d0340c69142c00400210080c1860025420050340500030341000031300320002c100405c0c3d10004144203002c141e005206c03403480401c0c0b0385015000d0500f561013070b40c0443d01c0e450340c810031200d5414002c00c001d03030440480000d82c40340201c1140120f02910725078101 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 394078498 1250 394077248 394077253
    0x303121e1a09010f030210021c05030709150309031101060521070e100513020a050a210f02090405181c02010b0909010218010201020903030403020415032102070803030c0d0914 77
    0x41048a0842404c02c210780c406c07291205050844802203849804003000040003800d80004001840d00400217154003202034500780e01280e0707580d820107403148142d111300300120396074540c48401c0c150701990851482c2d08250003405842e207450042280300c5000b08074880360a0750000502e88225090110303c00811201142071080d09003c0c81301008580301e449031600c1807006007101000041c0074000d50740c8904082d1140d81c10001807041c1076500240c00780c040342d03105160005200c0c032000c030741c85040c288185038440161030f0513600042c03204648001c0c05440305444840c900c480942c07000078030780d56050061441156580c4e00404285d000d01140002d25034000300c1d09003080081d510540c0600b8000c040c02c1d0314548120b0000e0010f9080b4402c4940c01c1d43c06800810042c03000d41070076000000e0340f20300a0603000740c4664946842003040d50b60419141e51110396465040680d80c10010300b0080c1404401940c5103040c02e0018542c54401c646c010199113880d084680c050003000c03044a20303c481c0b20001e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 394079748 1250 394078498 394078501
    0x233d060e063a0510030b0601030906020d06080c030a1707062703021c02340303030b03060a0b060d0b060c100509070b030c03041e05160303121e1a09 65
    0x720403001c0d200305035010824100007a04012100203e00586010383c491140c3c002c403460039500d4100c00d030840200818140750322002c903080091a036100030b1a4020b40100e000400134105400c0f6030412141e81c00e00e91280c0d2240c04a00b01040500f03c07000c4141034200c141ca87d1b560164502107010781045001000d0442410000e01d9801040f580740c5103000d4400d40c2950b000c04d03070007244400c1080d440400c3c4001680169841164501480a902034844808140c4a41e4100c43d404031a9040703540d0f0002c50000340c4800c940c05a90070304100443d0818407005080c400c4041070004580079001712202010030340e0b1107014983c09500c8040c2100d40300c07070380c4000390b81c05070036000f42c8c00740038041c103403151a258800c403000003410000000070350703010b2a51105000c0c610b0300c0c0d545030207000d400c0c603500611001e81d6481095000903020040f10103100c8180d03e8000d802c41c07441c05c01403c501c1c003080142901074148071007031480880751140000041d110980c000b0701001451101c44448551032012a0031825000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 394080998 1250 394079748 394079797
    0xc041512030207050f240f130b0d050c03090a1506122409030c06020a02070f09060602070b0a020a03080703060b0708090a06021906233d060e06 63
    0x140b0405880050b03030300607200e20005044c01940c0148600b0f0300f00c41244070445103509100c6c00014007044114159403401c04020b0351406547e43c0c40d5a1007c1c5654034000341c94013201b102d80c018150b225050b4542c142c150b00d84011001e0f201d0070550b030001c0c4481c1c020581d200c51200c050307110a0151800210500048000d86042c0d000410032550340e00da2004164685008a0340a01aa280c4194140d40703200030480c1641e00d040c0070303410000911081d030082c0000841c031910b031054076000600c03070180003240345443c1810103800c000450b0030040e1405c5c0c0401c00d602840741c001842d00d100700d5061a101000e40e407243c9040b001061541c0018102c0c07440010741e14180805440940900d440403910703054403981d94041603942d840d400e6181205088401c0144012030746503885680341c000403039030018400c811490b81810140b400c030341880c07881d024004510070b81d0000c001082199000c50101c9603424890215400c801c03c0355200c3c0e0010803082c0b42c00703810544c80301c105440b880f288441030358490700d4045 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 394082248 1250 394080998 394081003
    0x150c0c060f02010b1f0c05031b030a120902150c120a020a1109010e06100e0402120103120905061b0102040f03350711030c031b10020604050c0415120302 67
    0x4079103110040d0300f0580342c2401c030714002d40c0c40c50030a10741d803003d07900c3d0030030140058890600f092015101030009210030800c0e08aa410460003480b0404082c680d20050a500a0902540352104213a0585000c40d4100107031034080c440001d4070099a18541c4400e02030b10003074a890018429012500d0000c54484903c5400140d00c0e003c0902c550b002c00c6800256000f4044260003d12996208500d240041219420880004c84d2684510714080c220070020034041401d0ba4003610609021030041401081442141c0d0741000f0494847e26040e10307001e02e00000070700a0701586c0750006000c0b4400303500098298095044070010095000714000c0300742e480c1850016403d010342000788105084008560b080044d002c0c80410801c07030f8405d9400c108040c0c4511020003081011140c1620420b00302e2640d03035504000b2406540c10700501700b00500c0003c1e0601440003010b01c840d4081d03504c00e03014480007800c081000d00e00010103450014200034544010444915103030705c45c030500344280b0380303100030705a02 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 394083498 1250 394082248 394082267
    0x302041e060609080d020619020c0a050d0806040c0314070509030c03060f070305060d050a030f03022208070510020703020f01140c010c1409060a08060604170106080c04020c07150c0c06 81
    0x181002d4500245e694001070b612035030111003208030000401001c0c40e407030380c0340c0d4041c004000a040c1119202c0400b0741e82c03030780740c01c2541b0710801c08620000104885880e150144c46041000fa1500703003c80e8018420300100540c001c3c00f12030034081c1c00b242204e1151010002c4258109000b030850b01141090700103642205c2c0c060b0b035042e0010b800c1000081c10f0341894110b180744c00781d03c00028074038120a901c0840d554841030401e0010580c08002107030607601c00c2d000701c184140b0f450b0105511185844200c03072600605600550044062503448643c9580206404003200e4040d201d00c200708041100484403a685003028036082c92022a4200d41518154041c50120b01107403100b07107900c15040684d01c805d00401690319801041040140c0400344a0f070403840e0031000180c2414103083d160094030018115807501080169901c030000c01c1403076002c20001c00c03e01000c2d04c045146c110300340d0100ba1034050a0050401da03444144102c4403051040a5100005411010140e00181c64003001000e5002 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 394084748 1250 394083498 394083509
    0xa030b13090215031e180d0807051606060504050702070f0e0c0304240227042007030c02060a08090d09080c0d030c080f030618040209010302041e060609 67
    0x9025242080c0d4603120300c2901090740d0000c003c0b00d0784042d025007404803603200802c11142010707041c02a102d607402d02603c007070180c0d00c82c00c0941c03940c400035600c1c01d00c2c0c2a500021070b0100006002808405504441200c1140000700181601c0917000d041c01c0001c3e003150343c01160003c1c904010031041d6a404211007064996a0003860b858659954103580711600c161040d162001003040441d0000e4119010103503071700d2407548416407044100301a0001ca0300104080110f00300c02045400c03855000d080100c0b00110100d504011641c0b25000307601c1014003489001080c072000040c44028107000e8004141440c3d4001d03c0340d9500c00c40e98a0040614000351440c1c2c4091061007104006280200c4843c41500c02d40ca0040803508585010484180c078521010f905100703800120002080600c4020004240079a00159507030906000b03000070300b02d03142e2400b24503280020074403005a6980c220b460441c2c0c1c04035008600a0744040b0500505242901c0c080390b00c070714081001840e244c0040344102100c2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 394085998 1250 394084748 394084759
    0x903100b0a0605040b122806090c020102070f0f0f0c03150c030b030c01031d15091612030309080c03030a06050910060c0f0f080c03040915081b03120a030b 68
    0xd035601400c0c3c502e406503000e2240095000d101480c1005103007540f40303500030201303280592005001e9201c0810800c0100d1000200c640341c8030103000b125541d00403000481c4241c0300031480c000f402d03214075800304542000202402140c0f603850081c41401f50224040d00d41010b041d121181d680d00c0c10350340c1240e150540105141c10015403824040c000c0c42040a42c0e03401134041c00c41b62032420011401070182c284084a803200c42041d075200b04904210042d500090311089070b810b4285452414944490440014040b01b0680e0b0140600b491944010207080c1e41410003043c20503891078100c2c2a400740d2021072000c0c0c403001c001c0182070205500810112081500c04040b552100344109584680f030b401950041103034021302c400052032907440061003501030f4452900082040d99100304c1d0380e10580b5003900c9503002003030074000d40c900c501c2500d0b440014031030f80a0380704c1d2405111a8403100380c408042d001e00040d030a05c024544041c4411000d0030100307113407107540b0f04003e000035000b0b080d1028011f0064 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 394087248 1250 394085998 394086019
    0x30703060e0604050c070f030912050102040f0803090a031101022407120515270106080118230a1104080d030e0c0312030702670201020903100b 63
    0x38140f82c844c0c83d0081d180041c0480c80c00b41076460390506080501011003c20076201e1000619072210032181000a20905c00560b603545814901e08540605422a404070307001009003a00035030310300c1a89401c4a40c0030403d0680d152408005034180428260304203640503040300861007001e040c0c40700031b201d00d01e591124003414040d0340350201107a40840341d00700f41c15007c607502100d514009038407403204d82d80f0044140c1e03022000b914680c0b02c110283d0281003c01c01050040c03051560360084051540a280c0c010010030810300d40c22200440d030360141c0781d460a042c00100d514084c8517040000206074030200030383e0701d07581c03400b41e2903035498010f14010019107080b0614040500200f0b081c0e1010302c0050041c030780c041110840905660001e0168001c0d4428100000c003a1941c0d2040020000d0035180800c6501c10402c1000c400070700d0308440c102c070303205602e101840c0c0c2031800040c5d069885044600225040c18540c003c2c1e009204040c040c640c03510511031509962041500040700d1f0725400e80b86071140 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 394088498 1250 394087248 394087261
    0x8120a0e0d020705010c0510090b040308090a03021b0f0a0305070801060f0e0606130e090c1c020918010905070e01060306050d0c23041d0d0908060604051b030703060e 73
    0x1a100d0744082440140c0154030304015940c403c00a6840b11405142075980104030211500101c2d100c0c65800c98500240f101004145070708061441c0d0b20140c00c0025211201c0c150b40c0094642c180440030b10021074071402d541140e81c4800c078044040c420040c2c12021855200e080c0380d03655000d03d11407181d140d8240000412142d0880100008032003140c500000261682c9007008000d400040800c0440e03d03d10400080f040d102e100340c1809114458082d06070ba2803020107002d030704d01c7c580705003482608070313034840c0001a1030394481203500501c1508080002001300324114007410741110050010312604030041190320080c0c0c4a64120f81c0c2c103850400413650b5800500c05071503814100540000d00240d003c0090007442810601d94109170569203105514082c00601200c0a040f92070b600d000c0121403501924008020010901001e030030030302c055a143c250425604c100c020302140c00790303071648040344040340800ca82c4000031101155064480c034101030024001e001c60b1040318030030410040810311 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 394089748 1250 394088498 394088503
    0x503071a0619030b07020f070e010f0608040812040320070e1b03010b030c0706050c09010305060a2303071511070603051519080613150c0507020111010908120a0e 71
    0x3510b484240b201200620b0341d21400140203008002800354010b441c0003440d10001400580b01500c0c20708010401541088070060b040071054001b4400d01003d903090002049440d002e40e02208802c1802e22020382e6985005c861441090400c801d001040c0d00a4050180000c1410303404c0d140c00412034025a5640c90382864242a2410700260800c0b041005008460342c0c1c000540e801810ad991040c90500a5520394045a208a603035a04010001c28480050761380b600030550410b1040724005071190401d0b094000001c0c85540e0030f064520402180b84135500e060002ca0002d18079182e0340608105040000360600c84200210405402041d90104216000344241030043d10118060150215241c040c00518102c1101d10358100407060b0000410315020084180300380c00144040b07a006020b4a80200044080107070038072220309040d0300d82d001a44c46003d64400d0b40d0240f030000030b483d984c012001d00410303000320041d04000c400900640b8540c5600c000c0c6002d221540001c0100403d5110b20301d8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 394090998 1250 394089748 394089769
    0x615090b060909061212030403030501210b010506070c03080406030c021c140903012d18050d05130e0a090317040f0312060906030f021906080c03130503071a06 70
    0x941c032520a4011070440d0800c0c5000846a000100c01c4071b9800fa091560110340da0005c440072400251190b0060211801085408030603510308140440f9003007059455480848050040501404000c280c40c0d040c00084a03002d0006d6801c161846d80e103507160b840007409882c845107c40c0241c464000c00c0c0701d465000c250f0034a0120440d680308078841e01403411118603030f808038000550640d2140141c0c91b21591780e117060400116201255a00881035011443c01c0e908064048003845410355030300404110041400804048035180883e6924085241600b01d000c254111039903102000f02040102942640595442030003030321146200c8040d280902c121712411940200291042a40782d00020f000300000e1310502c99400002c07402c035884100c000100c43e010741c420394140b90320040d003a095080015403c024005040304401038107041c90b0001c2d0041e01c01400d03417144844000006074040710074000c2c0400241d840342c2560ba9640c50350415000b4000d0201400e4140307510303200410b050340b90500414 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 394092248 1250 394090998 394091017
    0xb010506161101050903101d010e19030207030512121012060b040e2b0302040e0c0a180b03060307060905010e0904020a0308030f010f050d030c0813030615090b06 71
    0x2414a0310315a904500c0100811482d070520005100d15103207a941440400c0c2c070441d44000010303402ea0050811455601c0c10000030000381d01d410a40c2e280310402240c1d4071940212000000740744a5613150403442e00e440d079813020300580183c621240210601030000c001080d51868590b0164580107007014483d0401e00c030700320446441c802d15100040940d000740701401e41c01440002c5130941560124103080c500101440c188111880d041c035170448401c2e41990200300d078a001c504241c1000320038100824003421303010195001090b0305040c18801e45c010a4240350340300d1a0844c02d40d95400441c81d030b41054400610034041c01102148103442841c4101c200d0f04169a03d11f1048010000e000103030740080c109a0f0440600c040200104840e0740085020324040b40312415190324041d140f020700344040e004580b06554401f007650109c0d80c4842168040b03500301c108540e841d0382c8811042140301085c1d1008020b00d042000039020b1004040200303080f124220018848100c19804005c007a1040c0c1298 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 394093498 1250 394092248 394092277
    0x803010e250804060b03030328090c03022215080d031e021809010e06011106010e0105060c150403090807050109050a0306021b010f051e0613050907090e010203040b010506 75
    0x240a0790341d1140c801c10350018050350001400c003402c0d00110341154422660482c221311074018403d070307140071808001800444498100a4400b040d80d800c203101c0040e11020b84200c01800740d4100b56080b60b0344841c1c61941c1610701b04200030b560090400c10f00c400c3c0c07042000c14015903081e00e40d100d0080c011005800c0142c020600d45100201c1c950000350014201040c200e000a8040c4046455645002e80a8065034a2000052500900040035000403000b000082c0d04510010803031807404070440760545408440c91a00c5107a0484510300e4400701007030350301c14003030890288018140c0000304441034400040503075801c03a44620064504030381e02d20500b1380202d11504200301003900341c2c0c060720000043c055141c5401c84144081801d44040304591441c461b651003d11141014181c00c0190030b030740010303102900e4540140010040aa10720f030400c1500d0701c0368001002034505005030000381c0706800003004000b00e00b0300118003d400c200c034105c2e40465440004242c03454204107888281c20f11010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 394094748 1250 394093498 394093561
    0x10c0806060c1f0f020d0203042603060d03050918010e0108010e190804080724090e07030902010908070303020a120822020301020403151506050306010903021216030803010e 76
    0x140c04a40f40594091441c400c1d03900e90804540c525540004c0c20b5001d500e080250b240d0038242418800d20508050707907210b090300512442e000702d03025000d61741d0203001200c0c841d8064605080581d403130300c1002042075111400703018407400c040c4901e48181c141c03064228032078180d0703072100c9145080381c40c3d00216000b10341c804003648580607058030b50904814414030302d050a02e0b5550f248540f03000140d400c4064001d1100184981e070200940c2c01c1c0f03003a07400707600d0024405460b00e0750003a00343c0805070026040540b00c000c0e180030369000c0c0318030b08024104d010440703d2190790307400d0003911180074a02c00c0b07a460b0010500003d4480c45516401d0107008058a05054880101032003d12510781c2c08080740c1554007480000f01182c04102c0c19903e40c158180e000c9a5011400c0e454001d6103a03e41214061050501c10b005150340c1c0302411100340c83e4182c46102c84404018504e46c6408440025141e232180981e03000f00800003101c000e10b04031424901007480d00d07100ca404110240c03242280c241e0300a0240321 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 394095998 1250 394094748 394094773
    0x31d01030b1e0406171c05070b0c0c0a081801020105090a08090910090908091003060f0b160501020a0905030f0a121b020d050303060f040506030c0f12030408010c0806060c 75
    0x14080c2c0320b005401840001c4e40d0303948184003001040d122641030000c3e0440d103055030707001c2807078114030244800c0c62805030301d44111b5950780b02d4070000141c050040d00030b000c1643c0b0a041d00800540b91019003040903a07440e0200c400d540700149a59a04d050300550a0901203400d56034001000f40c1c96907400034403241420168014801040c000802c03400168030741c0c160000300340c9a54071030700754000c3c001d5207140da5441c9484248103a2048080402017054a080c008001d103c540e0040c600a4841701c0320300c1c03a6103041e01c40080301600d2140c000a0595403001807020402a004914981101c50660a542d59090b162035919228410b13010064030004002c01412010b07445000000415a11a0b207103000c11001c98001c10b40742e0740180c01c1114268400800e018441c688102680c0040c8000c403000e00861401c180800c3d00d03107481079002d50040c15802c10340e4034035035036035042c89540700365110840b074855680d4501c00d07018000100b0080d01242094010405d036051000844540b95824402408003981c2c84 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 394097248 1250 394095998 394096039
    0x4051c0302030409050702070e070219081608030c090a0503030a0516020a1511070803040602070506090609130c030b0d110910050604030803090d0c26040909031d01030b 74
    0x12141141103000800010031111401e104007030207411168010440e030b60030200010103100c070181000c0299032050100d41142c400581c4d200000590144003140c49604070803641d8502c244100008082c3c110210400207e140e05801608005401715254440b05547d003040c16140d05c07901000c0d0300011000c100307002a142c20003c681001510241021034410382d10b14940b820b40750500b001c400000e41c0b8030741d20340c10903908124130300150007490045d6140515107540a543e0385500c0c458030380a0307130b00803035411400e44d0303004103540107044003a000440082a2010543c001c2c041c0d820380c0b40102e8075240c03500d003082c2400c1c184901c08035400020038061110070010000402402084140c0e5100341d6a40400c60780c85a40181000354410b60040303440b030800c0c03080c0f1030a0003207004e060b40400c085400c0020109050507060003060601c00c08034002c401155003000d005104a4010420f1a41040000e00c1016840303c0c1d0103010003008503c0d14007240e040c00044003a11490b0303a44a41c412141c003a00302a00108 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 394098498 1250 394097248 394097299
    0xf1806081b0309060c030411090f0402040506010e030d1101020405031207120201090b01030b06120d03021201050d0203030703140702030d050a0f080c0a0e030c0901090605130c05040608071107091a060405 89
    0x1c844071400401588c0c0059200903045550654503020003013404210f08083c05400e800030003d00307080c0700101c00b2902095544003000100010000060300300c4040080a604a03000707424098143d41070302074002d4900c8255441540101d031410605540c90610920611030030407104d600451842d01740c0d28585800c000c84d20060700d003d6020041000408060b201080300c114401029240541c48600c0d81da201048498142c0c0036a020f400840d400702e0050b500481107805055040c02c2405410240380301d0b01c4141d0055141c001d4240c460744450340c002d5074021003e00080c5c07010341c0e02c40c0c080c01d00c0b0902c1180c3e034420544e6005106003003800301c002d0290248110880c00034000c2c003190101c503d5a000150442802c1c0d110400003a034400e014001e03030901565a00340c1004102c07007480551040540100b40384514403c410800c01d406010515042c441c0f441c504021021a00b250b46460319040b0a500808100c0207034606404491003803001c0f0b0030680f090b81e00f2108020440e15001c0c040c103900285140c0b9 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 394099748 1250 394098498 394098503
    0x60a0b011b2003190f0c08030706150b090a05100318080c060c0f04060f14030f0603061008030304020409030306180501091107120f1806081b0309060c0304 68
    0x14040c1c18003200710810114403401a009000308544611940c014078840e04494207080c0c001c0d000142c00c4403036000b034219403c11080d80030150148104160400d40304101031600000c01364000019080280f12540d00b0240502400c102e800030465a07440b0110303264814074030211b40080544008104a00d464021134401c6262400c0100b10320f00715408880710410720301c50445107227002092147d00020108002d650144c0d034180303070a25009903010400c0441c05584140d03070420a0140d10790a0703107846526903000440711622981d88034100203552151203201210310f14001d1168500068082029036061011107031400301640c03440d00e490b000c0c040038142c2e44005074141038803440300254048020840c15003110440200181035410701c80e0b12800e503005d0b0400f5602c030390f00521880012420f0a80704a240d40450f0420301c1301d4111090095480c0b6400d205100050482103900082c242d8102d0700c213034800c1c3c40c1c1002d01c003413000000c0704001d004d0106550301c0341c0523030150002441d421401401507030410b0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 394100998 1250 394099748 394099757
    0xc020d030903022125170a05070b040510090b09060c031b031f030308041e0c05040209010c0206190801080601030c0611160b0711101d1f02030a020607050903060a0b01 73
    0x65045480c0c07003c45001c03625210108000c4510050003d0013070180386c028003203680b6034940701c542280200680100b8001a128000341408030302040750802c151448401c51650a0041e0340383c41c02d003840340c50800c452080d141c1c051800000c140714901021248105141402c104403844480c48465640c2c0000f0686d544c05081075945040c220540080708001f0351080c0e4a0f624249820301c2d1009840c0c2d40c00d24181c000340881481c401c00290b01c0c1c1c04d01001d4500a0768010703128040c410048075818a0000081d411050000387d84040b00307000601c4100250b0a0b807551301080e641c49078890741c2c4070024031004d892203450751014041079120b400f0080c840028103044030a01b00c44518809611100c41e0300c0030a4882e0009134000c100111541a40402c642c00c035401c2c2c100d1051030034042c0c440f02d041c1d050078208483c101c103c3c91a80d62813200103001030422880c03040304102e403003001030740e03951110034001c01600c1032000099082d4415812503864050103809404161070f081e407903001510500d8016810301 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 394102248 1250 394100998 394101007
    0x8100b010f030c030b37050f060702041523060306030a110d0b0c04180207150b010507080c01020d0b092809050f0717071a03060a180c020d0309030221 66
    0x1943e42c1c400c441103090b0004000c403942d914803072007151b4000109154850030700691104202c259291b154010a0a80680303110703548141c107100080c0145106c02846501c41c8034580081200320800b41c1883e0348102a01600c1c085e440304104110050004861590345039210b01107607000159212103800001c44c000d4201c00a1015540d50349624450440d200c034041000450108000018001c0510520b241c14000f10700c1c00030152070b100e40041c49080042c004540703c20207100c540c0d114400b00c656064010f007146032540c1a1000f41c40c082d6201442c403429090070700c020301c1d03c036162030500303030303010b540401010303030411000132003d151801808200c0f0882030303036800310381c4042101030045000380901c2c2c001811901d4100b4000c48101d043c05403000e409a403040310144a00c40c1075543d928000d005254819031a603031840c0c0010b41c0d040c1d0940041b0f03d66505802c00c81070300c0307132150031890b44a6000c0c1c09440c016200f04008030110380503d00046d005038031038191032034800750140c2c03000e00c0654006010381c0340 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 394103498 1250 394102248 394102271
    0x4050f0d170711031606120e120d050603070e0f0103060902130e160b04080c150d09032c01050304110d0c1e14030624030109060608100b010f030c03 65
    0x40781c218a5043d1800c0150b4010701c1c120b0301c1c040c4000030382d2a0100c1030a11500d402e01d040140524040096500001e55035081501104010400c0119440650b01c11a41d1114480800340180030305582403800380c4581c000c0800c2e144808184039115100308410304840d680386494100150110001c140c0e0000280c0e0180c1d1044007560003980301410b1100000c3c0500c00c00300e10b40850400e069031103005a03e4050205100c541c40c007090a54444104903072400c0c2417140c840800c01244900003a00744014a000d1450007010b400c0000a01d40750380c80c09051192401100b9900d0344101c030720440a00041d01000081c2c00500188404503128102800149a90250b960340b4148100c0036005801c03030f56041aa252030211a004200000c0c00d622040440c0c0d400131300000c203a03a840301600d20071400c00004460000409403044442040c04000e00034001240142090380082c00c2900407241c440c0144000305840f00d0160260903c8042d040c2d42d44c0d540050400b004600030084800c0c048100350310303401d09454 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 394104748 1250 394103498 394103543
    0x506070b0612011a120c0a03030305010e090c0a0501031a100306090e070312050313051504110f010c140a020301020d0b01020606090903070321050405150c04050f0d 72
    0x2562003040d034040d09041001c1000604848140d8000300e50307042c00c25103c0c0a144a40a40881350411744802040d41450f0b1200b42c04c0400803d2420307081089802c1c00000e0640c10f070441d0b4101c4040f81039883c4942c445950254803210900601504072000610404c4139504c45c0c1d000e078100781d002194038841b0110540c00541c04503000700344079001a48a403070901c044079003480317a105420b030714100a0102c0d520795076824101903840641e000502c90048000703544089400d406111440e4824241d500c0201506e0030072220130801d49094410740f5100f0607440203420a01300324040312805858400e117104481c0c0c0c0d48400101311880d040300c58014150040c00580b003d0000e01600c03100140017007030a4050b407000a1410384000d20341032080c000101405501d0030007108481885806242210002d036140303220720580d01040c2c0c10643c42d03619180800052010104c0c6800003581c491a0909043c0c40b1041d440301140910301820fa840700041d108400d0301c1c90315040c151078a5204901003000c950280b4038540 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 394105998 1250 394104748 394104757
    0x40c0c080708091f03060602070b120109020309030c0d02160509041a040809030a0c09050c132c07050a0f0201050631021204060c03110927010803120c0a020d050d060506 74
    0x1011a07100d51092011f150140901ca014001b40004541405a10040550025418806c40c00641d50000c0480c003041014400c40f4104602c0000b1100d1414480074005c2d610100f544003e06500040070011a851a000c2c803018010303a00102c0c2816140380205500545005c05041214441070400000030b43d910180110010310f4003a003405011a40350117082419100002c08501c00d0a42c1040459144104280150252164080f0030324461034818200320744160500100f614000c03011041101c210750003c0103142c964107030b6840144080301d18809909072102901d410b607129041c8041d80810410b2404000820340e01040b4a8250301501070154089900c0800c2400710002200108001c0c01503078054103910300040d00d0b0800c172408209103609803a01401c200701d4814901c43c50154940100400051040e01100d0004480c65a48645080c0d0340c1d40401d4581c00c000d0b00600c00070780000d6400707081e20740b0415207402914840c43c0c1e034141118158492402c0101c2d0643e180b03001f06a41e192103000d003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 394107248 1250 394105998 394106059
    0x1060f020615101205011511011808070c1a09120d0e01110709020c240415050406020d0f0506271618080102040603181a130f0b06040c0c08070809 64
    0x90100c9142460010042c0240f0702420072140e0402b0f00d080d281c0406411174a545039004501c4540300c00840c51315841c802c0550b48528840d1403081807070001c24903501d00070300c1b07031000444110190f20301c1500b440da01c0d04030601d44540424144100e00f901e9500411035030441c1c20440d400e603040c075a25070550101300c1e0040208210564880d140d038200510910190f40261403420b81c804455181590f50808894a00b0340d401c8181130700c80003c6420010590151045004031350018070480111500110091204465042c487c54200042c0a0761005114008042100142603845c06a68880d1662000c4086c056144d00700415044c00881140481041d48054803410001580d2686000001002c1d60780c40700410a217110a0020b174800114802c03400302c00c0c2c8040c00c0c40ca461a98aa10920301c50f4841e0480c043d04441c40b13005048100010031110074400c1d0320890f0f0411504d030b500743c0100c07008050b003980103101300c50030402c40d008a8000800340c200e8450040c1008401011040c0842c0f802d600e50381d54 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 394108498 1250 394107248 394107269
    0x706050c16080a0512190e0111060702150c070507050405250903020103060e16031a100302030402040c0804050a06052d07081506040315090c03050601060f02061510120501 75
    0x1010304003c002c1c800242d4804100c5c102a0409200720721709034080e502e0b00c01500611007a146982d42590280c1411404250307000266142d501d003404000c0d4a030380c40f20451074114400c400004c3c80038044101a1006d6a41000040080905160900c8000d1402074030036980740200c98145001541d044070f13024070984080c0e03a0500030341c0c61031001400350380d0150400421642100c1c03c0020422180c0344e2141c024200f440c011aa44100f40c800480c4103076440c075101d41011461070344050003a05500114029032003500c0030041c05114100c00ca94005056500401c01d80003031841c5004600581c00007500040d940c0d810181444260300c1401031240c0100711040003004200030010b41c20741000d00c4c00d5001e07104000310108100b00400282c1f140c0710760b0000418591320420b0300030ba807211903172080208a600030301d01e120396a182d0802c140d54660912621000850914050000500c00708009014000304001d144010340c032541003107000d0403610030890410003c002d1200e081c81480c0691402826580034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 394109748 1250 394108498 394108513
    0x20a08010509100506010c1a0403140c0a020a05030109240605060403240603050613030302121519050904060c0309060507030e0c01020f030301140102030d0c09050f01030e0706050c1608 81
    0x30001136500081510381809050441c920100c1c0c0040110030010a080204d4443d6035502e150568840d6980b4050110203140440c0e50b41410f04000394030340c40316008503050204c0551312400c1609071114004000c0c0140a0307040b41001102e8620811248040780840215040e9120408907850f40c029034010ba8210b0282c0880800000000004019403245101c003802920304517125245c2d14000038100c4200d0345060705034902030510950680c0c200001c400303004c50082c1072888084149940c0116414410742d6000001d042100740c20481c1d0701150800b510f80b0030541e80f1516018014100b02c0914024180c90700e0220000520610406205950a03180012107a1800d100c8510f09003440820a040d5840041c00e100c1145000080d203044980c00d02c0e0000c890310300c0400403070546c040d0344034092032142052003010401e60004080c8003503900940c4d401ca40a0b028800441c140d49100821140a070440401030000f988603030300610500c0000c0782210b58860340100c0003210720241d9480b808164001e0031 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 394110998 1250 394109748 394109773
    0x6031a101203021005060907090506090307260f0303130615090207140105090c09060f01091701020c061605090f04021e0918041505060d0605090f0706110307020607020a08010509 78
    0x2117215008030b019a500c07115448c200101514140050050910441c804210070b00c4690301008074501502020b500d070000d803600c0b82d4900b00600104884d002c62802101000150a00c2c00800d9138070a560b0000140074440d55501c40308020101c900d00c0c104481c0703407a0008180e43d1f007240028501c0622900d01c003418200003043c100d003160000b51100205400414000d181e5982da004540c0c3c0203c03003103850351000140c103001070b00da02c01c00b5400315030104150030220351004419405000e2840c0751000750f41e170030ba6541d900b10840d0091010600041f903014000ca00076400c000341d02c1c03210303400040d100614108070400c0180d0641c07880e00c0001d41c40382001603050040d082003044c01c50042c0700100150f42c0341c00c10703981d100b5851000c4018083c001b6940c0300050241d5403100c0c00045205e4012400300494103140c0303a06074448070048210707a4075105183c0e00090551058074000b5030440e090000d5802d107405a0b00300040d44d44900360981c0d1000c04803601064010003031060070700890020340102a80e09910303 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 394112248 1250 394110998 394111001
    0xc0c0c0108010518060406080d11010c080c0304080d0b0310090c0b070b0c0304050a081218070302010203040911090411220e010905090a0b040b07090906031a1012030210 74
    0x900824100201c4400401c07454848400344007140401610103000345ea2000007140060080380d000100c03c2c80791310107070500b03150011156408010250b00034881d07100722480644415909440d440d107071800400014001c14500c9024103058400700d80d001c50f07101e0344180001d2a2179a1080065441c0c1d5541030084100882a030103c3c0041840940f080d06003103107515001141e0740300800c2c0314034014002000404102042c42101d9000d6445881582c5422501c05291f44120086941001541c000d83c80c600748150001034003c210783c0c0c16030003140340505118048020304010721010707200d001c0501807102555114044c032500350305032820503034644440348148496801c0c0340c2c504c0f040700c1028410910250701c0d41089075064418001c1e01142a0322001a40c91074003070b0491303019018070403840610003000300004450b40183c0352503640f9064540c85280807000c0b41d006101c0108800c0f06540d5542030220000da9255103c452284c009031900d81d215510aa002a005000c900681007880c41798825200c9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 394113498 1250 394112248 394112263
    0x2010f0e100f0605150a09081209040b04140a020d060f0e100501080106022a0603090a020a060f02060f070c0f150f0b0d11120312040b161d06120c0c 65
    0x1c0d420b083c00b1880c6000003181c45d0700346024004e07207039140000d91141254007400c181002402440200d9405043d0422110356607040005030310303c070354108140b0b905035240500984c008001d40c1e42c800040d58940f032540794000c0d0301c6448172a540ba074403008006091421000034034018100c4a801880515041403065090350346d0f43c0040c0c0c10701c1894801072180d9640010850941c009048004c11503800848088080416115040b684080000204a9020000700d4030300701862003580d061403a1a1520030986030071592900300001648030800003915003d036100c64582100b920304101d0800e001c0c54407401d01008054205540c05030040c80300300072a0380c003403261640400580c90304101c1200000d000503c4408051405070911540801407015951000a800100b03410380080303e560f002003984000380300400f15400d4500c050410000703400c02e103080c00c00c031036111416690050390b24102c00c441094484510b0020360004070520811000d07500d450103c030300504d8440000c5072140342101d0b000e441c00300c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 394114748 1250 394113498 394113521
    0xb03012102272e18200a0305070206011805040206070609210c150506130c122f0307050d020310030210030c1b1b03030309020a090b030d0c0302010f0e10 67
    0x1c046540c1d5980f00b200c18914029203010b580d801201a004130b405030003420303a9071101d03022100d540110b03001840302c1d02d0042940a880d52402d000e00d41c1c4101e03099031245400d10551259920501440f21005140c5d80282d030b0061004001c0f904055540d10b80a0032070313005400455640001d000c20700d03030058010403200b80d82400c91074170310490b01481d03a612001d490100003420b105501d60012484941d1b44000d501d91103446510100010005940d004041d0700c4114080300449142c04005000b40e0181d03500d010340c000b16400e0340703214980825a00c0320503a0004100104100d02440b400d02d60554a000460260441c0103c141125085004021100304026404410716190444c5009096000103054020b0304207812282d58480f8941015034035006006400c8503291040070001c020036170151b200a0142b4000d841d0741d0400c90315640250105c4284401065066003e549103c034003901c100c8000c0c1203980300e0310010501000100702c4106031462003100010030340140d01004003000c1c40f80300b122520708 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 394115998 1250 394114748 394114801
    0x1021c090c210311010e0a030302040f060c02060406050304170c0d030b03010b030a1e1514010b07200f0904030e010f0f0c0f02061201080109020301060b0301210227 72
    0x26030340c075800318162002c0203000342071000c501365070ba03581e000a5014101080740380c2c007586e001040c03e00d4010300071340c050700503000301441009001c1074207071082c2e80d08541c01d0703802b030000342c03400741880019641500f0041040356256880e040400240c10f08401070300c0c4829038200208410040820045d040d2010501c0b000e00980c0f60800072086981c00142c81800281c120b401ea400d140f40c5002c100884041905002d030180d203044140d111001c40079840340c400f0002d0080c884c041030362030742e150484030720440c000607080d44488c00004415002c000001d86508800820021440340700360046642c0c0042204c00780c0204119083c403c201d540c101d02e0400800c1038921b003c0400c1040c0d540040c01a45c0044005014a48030010680131921001c003110402148222844c1896a4420101780a012912000c0f0b0003035003003000004100700403c3c10740b4103841160760400f680c07125034081e421541101c0c00059038020400c03901846146e06810220540014005200e0814500640098a0004a01c03c03410416 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 394117248 1250 394115998 394116029
    0xc2006040306020706141e04110301021b1b0d1104061206050a05010f081203060d0204150807060f0909020c010f05011814070206070c0804030236010b09060a0201021c090c 75
    0x4464890781001f01c3c60301d80f044408143c545080c50004558102c50003074041d80b0006004902085811426249442c0314040b0b1f4048458409103480711801184000e0b000340304070811030001485107d20a8120001410002d1119696070300d0350b14603080c0103025540c055a940030700ca081e91003401002c0c01f40003400240c19226280c840b60f0350381c41c075810b0b40c0c008440030301001141c01e0b80e80d8020b4010095800420500c058422031000f98a402c0d41c41c0b20305a942d10880000181a41c0070381e0814082d00416100c80f40303031510303110b001d2000c0c1d0f2004866965035541c40305180180907242c4201806004d0580c51080d402502804100c100c0d4a640c2c030130000345861400304410b150b40050225448445c40c6000c00b082c031031074600620b180c080d0382c1000358040c400009031811a1f080c0d00c40000d006098541ca06480c2e0750420555030044400c1c0519086d0303000412140c8880d0911400070f140000f0103200040c034105140045104200c0c130803460f60003103a100c80654007801242c10703030304d005081c4034501303800030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 394118498 1250 394117248 394117261
    0x60c0d050d0b0303160308160f030c2028020117060607061b021018110a090f050601080f0601020a1103070b0c012f09090c0f070308250c200604030602070614 69
    0x24a2746000399004040e104c0899894051140340d80a8641882036419203401100d00011030300c81703102911188041c01140400800c96200450140405806845904030701000350550010104000c158a070042010000c1c140010303214411540c07100380600901d0315403084a000213050481c840d840075049410130b0441040e00f1600b00081030b910342d01c2a20f180307801c6014808a8040714042d404001d0b540c5c07802c00c0c24100003000e60001c1388511000d0782c400d640c0e55180c80b001000d80c0d00965000f07006a000040348000101e8800f0b04d40b01c68040102203c03075459540e1704800641e4040701030044240d44950f1800001d120b50707c0b1410345603103034880d02240c0c541507008242c680e000c2c4a8202c0d12512001700400c08040c40142140d010100700d007a050341c2c035150350070701070320440303059600c00071750650b10b1030107007810304155181810070b4a9540d400c0d1800d42d60741c65031024030907640c1e0107609441e04003400c3c0034a0341d1920010320083d40300340d00243e101c905604040c07007102c02c210420b220081156080040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 394119748 1250 394118498 394118507
    0x80609011b090f150c0507080a06150b0702101e02070e060111060a090f080d090323040e15180901061a0318010e070b18060c0d050d0b030316030816 65
    0x84c4d03440c90580d180f40300c00c071200403540e0f41c5482c0c2002d00680031f4040b004c075045c480031410900144c000d4000740800c1204a0310070301000024800d00002060134803522006203044c0381e410302000c629281094081408410452580c4070700c0da010b001603400344100300030106151003982d0740403100b400c0c18a07011828601c0b9a403248401000400c1290782c42030074204000c40c00c442440040e402603c0c3d10f45404ca00c0032007200500080c0340660103d10420351313499080300349020150702d41880800003410145401e252560034040580130201d4041c18800f0341180761600300c06892010382c03000c9150301390308003030207204e003102c269402445070700000b0480314040714440703800c698020007964800700991824030b0701c081c01000000d8041099003e0400300241441032840644206448001c0e842001070010080003902e10940041d05c3c031030b4129900c0c40110303174014009403609010411021501e15100000641551310a008241800798648903450603d90302c10041a403001e01c0e00040b41200b03990650180 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 394120998 1250 394119748 394119779
    0xe0f0c030a02181b1201140a0803091e030307061b05030103110f0102010f0c030b010e030a02030a0f020d0501020a020d1b030e040515060f09030d05030708130309080609011b09 77
    0x1c10002c444404600304112854841e00b04d00c2070b4521064445405022032042800280310781000a20b4880703400400c0e2a00081d01c0c01254044002185001014428060f400c0034540032116000035081d240f01840d00e09000407d006841820001042c480c025401228040800481000c12100744018000030f03000d54074070502d82d681102c1d0035245590050040f17014102924021002c513050096100030725425401c00d01421409880d01480d400401d03090560b40c04d001e01c40030754140d01200320400450503000b090f5203c40e0000d04519840c03501519540c1c01c0e81d0000000030016031016601c01561680b1202d105210f1030700246504103400682c400820b2640f0340001c4504c10f603a030744082280100d889120389400780024100d5601c5039007140c00701d44d054100302c007182d0007801500701207142c903407099080324440d0702c0c5070316841c11a403909641004520b03203001c011000d100e481200804c155004003c128070480707000b0300104081c441d0341400403244540c07440e41014003e01410900650503a846500d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 394122248 1250 394120998 394121029
    0x60c050c090a0e0f0109030f1701090c020c030f0a03090506090d02040b060c011802090108010c08132f310221040b01061b080901030507020703060e0f0c030a02 70
    0x70449030b1a458210401460100201200b9100b00441e09071240c0064000880ca24026210130701744d10310b80c410903a0f03072500080030380c441e540360400107005481d015030150740c104809204846801000d2008245025006000d800807036214603103d1f41055130003003c40c1c010301410b590260800e03610b9000300d11807484084c0300030f110715110030309010b541e16500269440540400300a200c4001032107901c0d41030f070510140980c058042c100000c1400d400c14000d10802d11555658075000b5500c9540510130405080001c070340551a900743c1c0f030381c02c4a0540e00c002c000600300c0c028001d0346400e44100050341003030107031240c42903080e100010345d00d40782704428017001d20b0f0304c05c0d01694881e0b0000c500ca241492280c41109091103c5041c0014084000159410390300d098492440101a00d03200441078444000004c21541c030130007032194554800d402a54019044d4012140290344aa039190180c46030540390300110381c07041000b881c0c80c0c2030800c00d200320303e84240c028140e00341d2150041104400c2e40000f2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 394123498 1250 394122248 394122259
    0x3120a09020f041e0f0b030d11031315020d030501050306070e0a05030d08040201091e05040f0b0904050f0705061201120c0e0405010f05090f100b0409080d020301030c060c050c 77
    0x1d548540b488009400c20003001000302c0e011841c1002c030320b12106403411003203e1504e6070018084081c3c6c41204118003004005040319070410200b165281d4503107581a0040c00248603a5580c1003140381c0b41805000d00d1003a520090030b0b4090000c1c980345203840400c00b05403d02004001ea5107001c511140c00c041146810041070207441d021800000040e0710541e094807035216015a410b500c03e4143e405a0700c00d99800a0311070703a80305001362101d00600328880040241c04200702c00d150544c82100c98000a8a0105941c2140d9001071100001141c054805420003113514000103024401100074090448400f0700b400481070038034080c0d81c2c0c1402081601d284951aa4043c0981e60880500070300c0c00c906503009510300f074030f0030b603028204018100d601203040c00081240240c010804140032004900102450300c0c00c0010a000f5090b03841c9440e03006a43e48000c0c40205074a200101a51500381001503580d501d0340c541440540b16590282d4100510040b9440014402054115100178121a0b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 394124748 1250 394123498 394123511
    0xf020d0815030a0f0501230106021c0314090715090e0c090604030f0c090c0807051207180321020601060c0b15120f0c0915010804080c010504030801140303120a 70
    0x860f1400b0b18004000d001603a0342c4540d0010000c0542201040c50071700d858030302504401204a0321402001c2c010840540c00c4051a81020030200d81c1040c1d14142628010800082c0d5411901d1402c1d0250780078201a009810180032011a0b96094038038026a80380081003149440a0400d042c1d002904508803250009516484c607500c40003a40c1c00307981c001c0c40d84110041039103401040703102148145268142403003074918200e802a10b034144242c0c100e03112145800c00e07054041c6004803008000d001030224241c020007220340220210800b66200d44001c4150100c1c0c528031015898000d185041194003050051145507480540720841585c810683d0401e40c450b08240340700910640c0e2401c2d0018003405e40c0702c0503030380e000a203021004a0442030303810303020413801405400641200c444c10310b403200c000c030075007594400c0c1d0509600c24000c45140d8107140407039002c41c0c00d51f403040e2804d400003480c41d00140031089100c800c061420208030300031450311881c00c40d40103105078000d04142c0c4c0c2c13507560340 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 394125998 1250 394124748 394124791
    0x50a0e070806011b021c1a090c1e04090c2105010e0a050703121707120b0405100b07080702130207030f0908060f0c0d15140904110d021815010f020d08 66
    0x11b96000d00558000c1603c041e64410241c010355580d0205e4100441c0d109442180015040503203c520584600c0902d81c00c4828450007488003800d1101c400721404c41401e880014001c801c070752800fa110300400d044441c00407860410b00d003520030300e040c2c001140d040300403200c0000e10001244000c0b42e0744040c007060307511f00072030054802c4400440203c1c810340b01d00040207480c0da13010310f0100c28201b5022042000c800c144003840120b410403540702c0c0b004402c0c0c480034400349580a001c0c00d40c07144550002c40c946851a404200c600c0070070340c0690300098000c2120810503401081d02c0c064200e030f52800b0413401c2d00d4004a1507840e40c015010300802111800842c441c00741c420100c40c87d21801c0d00d01400264500080c0c404040740611511840010307540c038a032140e10303010401d02d00540c1c203d00312005091040c0100001c603440800102c1e481034600c4240342646450041c020701c243c2039a0300044141100c03d0014000b01481c078044021508500c0d01042d0f03290304900c0039600902ca0a002543ca504410f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 394127248 1250 394125998 394126039
    0x603050702101a130b0334030c0905060319030309171201060801090207020303190c0f050d230a081b0403140c03030405031203040309050a0e070806011b02 68
    0x1c102c8001c4450404591400c00003050401112807401540d132040b08500d50581c00303044808940726a039154111f03004012582d4144220715894503504076000c4003600c440d440b54040ea01d41640211440103008000b080301d00300c288511039000b00e064000d801d500007003804101d0707a903110b40e100509155030f4008000506c503801803039010551034114107665412003500b581448180912030b410004d11088008200c181c0d1a0013550301c0158003800440c01c1c008255014291410303180c11110811203011003000c01b10749291001d4884500500c00303064442d02c24480103145040c0c4104407404582d0030740c03451251050380411119915403519068140384c54000046014000003030030b454040301e0200f4040240903542d070840b59850300740b200300c0701b000703288805040c1c80340a54802d442e8540c12035090407611403290801558406c4c400c1c0350510509840e107002070b108601c0d07138201d0b040003913170081000501a04468200d0b049282420704016081400c480e0210307040045100a0054001030a000700b02c0c43c14 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 394128498 1250 394127248 394127263
    0x706111005040c0b1c050112060b010e0307030204020d0e010207030c0309050109060806040207020414070e0301140906010b03070c02040c0503010626070c14010203090c030601090c1407080702030d02030a030b0a0f0603050702 98
    0x404405006c00e50b03403400444040c480c5010b05480c000d1030500250f0b215800b40c0d030605110000500503050309441c540801c0000d40011500c2081c0580b502c0e00c00301d100c1c000b0310040040702c3c07194403a40d401d5992401c2c014100382c3c03da08560b040c031031080414005540c02118807a030011040383c02581d240024408680070f01390051000413036444102c140f21010340c21003519010a40c00f80c000300810307458544004d4504c4810741c2c680310f00e82c105d200103001c82000c4400a40d8400e11070309007610110700c1d65000c1011286054035100c0022000300040c00703034039440b0905c1303070090485d07039241e20280c5d8048202560004000d030030303007040c458003031003001c1004100d002c080d000c00c5604000719202e01c0c04405040e00d6003900d03400244680a4540003240b080b85504c645400c061041c1e552003040380e16000d240c5041c0c1e0006400355903101d02448450016074003044000030606030703075001d1501c2c0c0416000c041c080e1600003c0040c4031714480003043c80348901242040044a1161402194507280c2c40b0007a8101002e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 394129748 1250 394128498 394128547
    0x602060c04051e0f4b010c020d0f08030a0c050315042c0309010e011812021f02011409071409060f0a0b0304031403010303200304080706111005040c0b 66
    0x40782c8607400420340741c0601e19589003802c9112030882030501900d45c4c1d429100c1a0107400310600c2d0001002c04e501c280140015984007030992601505203440d040c0189100760b0040f030b02d51034008200000905a402034185c141344a081040c10b501f4004540c0c06134001000b1003501070340e07598079032202d040b5000200340c1c082c074003109040890848100e8500d440790300154025000c1605c0d803050140ba948501801c507a015280302020301468200f0104885480350b0020903a800a045800c240010080c0311040b06140700759000011584a00800b00700350741c400400c0081240c008000800090f80301c01ca8070105008211104403c50740c035180020200910510242c0c0c00502403140031402c0b80c00c840c01540035034020741715440d080c80003480304112403000f40801400546c850194024820000c802181c003403d00c502941d0609031100360540c58000c203030f07200c0000903200e10f441d590b16040601580400240c00007045c4020300e0141c55100307010405110322140040d000607003d40400741c24150729907800 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 394130998 1250 394129748 394129759
    0x2010e0a0308032a0d020702040b24180405090609010c02033408070b0406150f0504020c010908030a2004080309131404060906140f0601120b03060103030203040602060c04051e0f 78
    0xb940e85200b0340003500f201f901240140e03e03201500c1414545140107d40c0344d400e0001d40341c26807524810840407a000307095180c09200076602c3c0741050b9a524040c01d48210742240003403241e8544000e94500b0b4580302c0c80c0744002e41d0010814500b07181120b20071141c42d4a40000c00d01016401d40001014202200101800021000c100c050400c0b40c0510b8250146002e00d0092040b5241da00c50404501c45038858182c250f1070080e000c00007400c1a4002d04818110500000b904240c1c5441c0c0d40d100f6401111000300903581c842c41c80d00200c2c0b0303105460654400b801c408508080c10030103466500e00c90f008140f03200300080380400da080409a0002081880b0714410248039041c50319004010f4202d0600072100e03d420500780708a150610901d03180b003042015083c80da103403540c0d0010f50f404080002e140ca141511a9000700154800300a0540210b03c6076006607a290b180000090030404c019010b1401000100400c0041d6607900c1e40c0d140c41012400c0d07064110041c01000503900c090602d0f01242c021 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 394132248 1250 394130998 394131007
    0x14010e061e09010b2206020a0b0c0d09060501090e0c0a171903020106150c020a031e0b011409070912020f120d0e040c020d0212131206050402010e0a0308032a 69
    0x5130591405800c51007000c1d6620142d4880c4412442e0b03c03c241400785900590040305828042007081021982186100112038a0703c01e08221200c1038411500781528500c3c3c9440c01044945103c0c400c1c44942c050740c4000d490603903602c100044145a1610078420f10700350300220040807050600c17258003175a504000c0c0c03940400943c5801b030b0103003203076120746190515860000c07561140650021402503900a202c041003d05560340d10781020024072507001049801071000c00081d400c2030003103018200101c02500050207680400503040001040307402000400c030030800a900d818884401043d5040700c0651140f4840c501062041043c1a030980f024458161513484068000180001118060721b05106180510800b66981c3c14200c48040040e40440508002c000d5110040c0400242c008010015a17507110030700a161400700c00e050321207660b07074006c0c44110341c0c016903615412542610107001b01031458a0f404202d02001b03000c49404056288004001600d00d442030820f05840f00f80f03903845c1c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 394133498 1250 394132248 394132259
    0xa0209090403030605190503100e070b04030309031124070201051c0c120615030509010605060301081006050a061b032309330c030702030a1514010e061e0901 69
    0x4d0219886068081c0138900307101e0903020060b107030200998a018006065142003a514040205090401022030380140c14002c202552071038000c00081d80280c2c0d601075881e06500b0000201c04c800d0034372034400c0e07507405082c04180716803c0001042221002c0720940b41d01982c00141c4041c407420881d481c158000110400c0c0726074041d8800c2403002c680c0da07912400440051b510700c00301c9040b8007460020f10184652000c01c2446a0071450348201c0c90f400200d012541c0e03002140040d00203801503005d03600124601c91441c019446908028030040b02c0808040c0c0c9000c1004d081002c0e440d4040e0303200001c0304251000e260003122050b00780c9103c402c0d02c5098101d400c00840c21500700c0c801c03480c410a0001040b0705040040ca10088200d9030004011181080c909108000d580c0100b144a40a000c1403044402596040c026500185e010301d4003007420350188000e440440d201800701c0d800384000301c0014400c070b4122001d2079600c568166414003110700e04000d0b00b08410900121a9400250030001045 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 394134748 1250 394133498 394133501
    0x11011d0405010e09010b040903020c040c110313080f0102070b01050d030e1e0f040614090613060b030415091104020d0f05011502061b030406050a061806180212010306050a020909040303 81
    0x401c4d05854020041084141c1c10002500d25170b0301c029005a0000300ca000207480c041d1f210303090300c400b981860259034082c10031441c1103410070005900c0c3d442c260a000c0100c0d5106206030001106008000c51902e402a42c81ca005100180243c0740120703200e1100f181014040d4507500c02d03200004142d002d200b522403001d01101c03a24000306602503014440e81140c80d041c28020201644c3c50500c4400502ca10070042c04a140130007010182d01c242800440c400d40c59003480b400005d04049441c4070b0b80c81c5490f0074409034034034064074a4000686003018000c045000740c1c81e8191145030840c2d025a41c1e500d40502507014050390142422058940030000a0300d242070304410b4500001034081d14129994208090131458481e02d07100700c1f40104000150000b0002e900c00f5038040c3d202800001e4068485101450034050b684007850010785e120014410035200300195101c082e0254801d52401000b200740c02e000140c1844000c0242c4d407200080703190b042980e0166914880c002e061400030b031505040040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 394135998 1250 394134748 394134751
    0x60905010902010e061204020d050a022d01090612050603030d020f030109061707030602030901020d06030803060102060a06051c050102221505090108070804020a03050f030d140411011d0405010e 85
    0x901180300c9482c00440c50400c02e098035146c9207102664907080da80e5809114004075180000c0301c01c4d003d03984002d00140e603880366007101c520344584034040700541d40f620000b80c2400105164144034440004115040e4884076442c1404080c91000c40d2980780d03000841d10314010044890209400450003e240c24001c0d409181254040081404050b68034500e128442d0b000710086003035038100d070b80b0510110b48550004d54002442500040c40d05203552003403070440e200c1d500102d440c032000000381b0135150303810010190404c0791200100038662800300065113404050700486081d03011422507070140700013036041e1491400d04414440d40701581210150b9001e24a004209030500020041b894040c82041900d8034200c0c1a1110b210548569200380e464000044c0102d80c04441c80001000044082c403844003801c04c00001151524030301d800400a8070706085645074225400e00400000c504400c045443c11442820840d004029000013666800f030b901c00c596030408d08000000407040407070326083c0e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 394137248 1250 394135998 394136003
    0x5060d02180f06030c030705090405010b1b0c031c0c08040e01030c080f1f020706090b090c01030b061e0c010606020a110306040f02100507022d0901030803150109030609050109 77
    0x5910303010142001038410b40010169000101440003440c040208030080d500031506082250a29110f6030000d0305407a000d0304410410440070402c0d10b10200c1203070f0340c000c15500c00c001a2a507034051501081da81e11410f88203165800140000c403000501501102c1031a0307400180550f039031b540303600111000500c21310080311460000480010311150101d4808000000200945400c40c0c444181c0d1200d0b4101e81e400c14051b0b942044078000103440d81c8030314500e080c410044000d0910b0154010760078100c4c032143d61410305051158004c01595000d086482060155181c007106540c1c204003407a140c058600c1d4811198a000c40205104d42c00240031b030310407407285003904003102c0100149601c480303080c0c1d4020490340c600d04501740107282910b191030000066107801403c1140c0d80c1c0004001c900f4180300c2c048100c03015a0043c040908000c448524a5015601c0d0251545150307504c8107684801030130004103c895456090980c1e1050020000a47c4c0043c01444050100c1c2072035130003048016001c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 394138498 1250 394137248 394137277
    0xf0601060807090e060a0b0304060504140c0307050424030f0507060e13090303020d0c0c050f010513060f18120905010212040302011112040b0a140f071b05060d02 71
    0x2603518440c005062082015035683d68071240b80c01c1090f200104081c00d56640303d40340740707408252014000083d40c81540511404280c2c0d0a007030429242c6104215034140c21600213002c01501c07038800240400480f04169800940700d00114108004052891200d8910080e03020001051280544200038201d00030000c4da0300039a40d400040c1d0b480d105039407515401041880203003d1159550340175292440c02414007601d0660034550b030074110303121264000040341c2c8100185c001e01c5800c1100d09120034003134008002a0604804001102e220307104024409a110312540008401c16000b44144bd021030414450310b15103450f00a108c001c0c900550800a41e40c040005402d6200041206510f07070001022071902d4150b40045580004030907030181d0798421454681c9404064200030402408a040d08582b100355032500117207414842861010422014449443e00000c01e0b41260301c0243c1c882c0320030317108041081c50701e1000c07015940880d034403c4010075814003030102600280a1201910078 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 394139748 1250 394138498 394138501
    0x2100f02120403020906010c0201020a06020a0906030e060408090603090f0a06050a1a150c12040306020a0801080705060d0203090f15010f0f0f29040b0702092404020d0207140f06 78
    0x701050107010360710019620428140108a0550040244008550040c030640b4842811603c0320070a1740e0290304a0300004025607000c01c031031a8144602c40c004031110703000d01601d041544403203e042c002d10100724030031100000410f081c0d060410840f58a09601d40a0b1070841c501410000000d107000c03124107402505040402502c03501e0800004801c0d10010014484440d0f0f80e0070345030550304540d550032110703c0340002450a80c0b00b0380002d00011441014017503501c01040d44000c24041040c2d21103402a40304c40030500555442805a0304404e5100e000141c4030383e12000050301d000182c00308002d013409500d480405803011000d00718183d6008141e09801e080d0b0b1400b00f0030000d0140d1052480480070b56005010084208c2008506000e071800d0844c01c041b0700b0004800d4662007135100c464182c000180e100c08509000c07151660240b4074201d1010078500841f4000440000008950322603540080c0c201d020b602658156074401c1e420100401d0282c21308640d030340e0b88040e4500c2c2d03002c1e46e115980 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 394140998 1250 394139748 394139773
    0x51612030603060e0d080a11070b04080903011d0a2010030605091006022a060a0c030e040c020c0f010201060906030605012102031005060a0b07050d031d07180902100f02 74
    0xd178000c0c0c101955580d41a5503540c0c41400c10090101e04514580d00400700f09001c041109042a64007840c094480955144407420402d0b0841d41d00401d200c82003201c1e48030b254804207011643c009a10742001114042b00c031070030540c0541c0c0362390f000792a6001c1207070b140c1e1455040d810390140c81030300c00030b0f1000b030034540301c4103100b00000c0d032507114a070010b0b80b050001200c403886c2031015440820b4414504644000c600c40014140c0d0844444000015600782c208414981d000141440042d030a4800f004071101d095002500d076000c0b000f04901a480c58a107044880c0d10035400180108120b0b0030400c2055200e00c1e150303001d00002e01c540c1000309040c5940c10b0210f0510060105440d90050041017800090707802080506002441242d101801200c0003552031000002808210310800240421030503441c00541100c91031024a1903410104201d442d070784800080407000e030386602040400d410300d1811400042c140c0900002e4001418010000702181c003c148002c4c2c0c5141e075000d1380d182100c4030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 394142248 1250 394140998 394141003
    0x6032307050f0f040b0a05091801050a05040308041b091d0c040204060c0222020f21010305030d0f021315120b030d050c01021b0601060e030a080307051612030603060e 73
    0x24000b140d0104422003510f5282c41d2951001104185c0904540740040d03450002818548080781e0811400ca000041c4500c1c25000f071003407681c0410502c13002c001c14206520001c12002c1c005100610401c406032540789030b00c03004581c030001403007064014030002c100000415545624018108100e2052081e81142880c040c02070b6401e81704190f44641400c202e039001c002070700c4600c000380d142541080e00c0ea0003014009000504500d03140b044d20541d25400500010007a1040c00c44001c48604001c005100194004c81201c00c81d03054000e01083e0350040141d007030000c1c03040804d02090301e41e01c0e0400140142c0e4254401c814101103807182004400102401c070155480c0e120101d6142c4c1000e441c40e4611405070b07000d840c0403504070000508100328843c00e8442e4201111894965903c101c00400181e940702c8540500c50100350050010b8201030f40d0f030a0340ca0301019000ea002d01c0400700b41c000504d45001008840e00e900000c00e614031190300c040181c01030620f40810f4555a05103042d055101000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 394143498 1250 394142248 394142269
    0x7060207051504051c320d06140a0801141501030e0a060c03060b03070c080f042601230a09050c0d20060901050703030f11070b1806011a0d0603230705 66
    0x303c0d410344200400c0c0440d03500c003075040348010310800c901c28001300f00d00c1d1f0080d200d11006415900f002c0102c1c1c1c0400c00c1041580041030780001042d0b81042280603442c0c100c5031142c2d030040400c0031103021b01c6040e040141c0142c00f88014040140c03150001000900240382c000c49040b10701510100802c944803200f02c07450740f108550090114007001c49400000f0044402410240922082c103824136490724250000303001030240c8136a8034040c40c1c0314559165400c3c0f103500010000700d106404000d00d80f400314030080c940140f500d248981c3c1e0344c0c58181132000601c0320b6044a40002c00303000f1243c07005e1030f004840c14110901c044204160188250490400078102d80e088141612040c0c206001303564104c0c00b52425240010142d611041c00c2d05c0507110400c080c0850a108646050035458000740d001e09111000181c250541e00120040012890103404000d1514594804a80c0c41c020031500b00064134041d400144031600800032140075000070312040c00300c102404c0a94010503078601c10403981a11 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 394144748 1250 394143498 394143527
    0xf0609060b07030507060b060301060c0c0602061302040b030c030d09030506101d090a170d050c0301051005031b0d09020f12031b0705090c090901090c0507060207051504051c 76
    0x41040b502e00070900070700c0503101030b80c428400440c1c0f040d41c1c0b074003140c0c00d900207a00072000325591182c0343c0c0801111081d08005070031207100412080c07400b050394038402c050501003c0c1c040d9035036000346480c90302c0610103541c0c0704030090101c1c0d801048030500100401e543d444155020701607507010864a034811440341048509500c20404251500359290f917103003001601261052003150740840004100904a14002c2c00c2c0340203280e1074181c80c901c5042555030061a1a50001040005001e503030388480c400d00c04034a061400d82c0d225942d8054030403881e40407040c184518078012414880c40d64cc544c000301503291084e40c48001c410310090034481c88a010090381c280b540c00600203040c18003030b10384c51500625142f5007155600c580c0d030400728484550603120303500c15080000d002c44103800d0045041e401002641c40c02c01c0000d110f880014024010048004c000c40c1d0000703904014444100002c2c5080040d1611900d051705003071424039a500c000c010f400124190900c86440d01030b0003801840302044 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 394145998 1250 394144748 394144769
    0x71203030506030a020a09020414010c02151303060504110a06051216020c0d05280b0105060f040e09010501060e010512130602210105041b020c0f031e010f060906 71
    0x16540660142000921560701803203026108405a950107410700003e0400a20061f6124100410003200203550580315050100b40851440103031078004080c04100d801c2851662101c136101c4072000d401c07007241d00140c29141000140b200b4008802c0c603a40702800c0c12500304d070451340d85280c10b40b51406145c100c4400c03541c000001404202c0e40d000d0103c126062131050f24820501440001c8a80e00005400c1d82c0c0e42c4c0c40800c22188040744d51139101c0c04c1c05590f080f0881601d52550701c0c450324110501840e030142e41c011440c6800050420191400340c000c8610080b1545050003e00780208401d1140301c000a03060451003032a54058000c0301e801c030440d02241d0f0440d0340c4098401204e2402c2080c1159810f81c00c0094118180603c4000c0c01c10705104120003045500d00001c00c0240d40c921031000302d240b80c4d191003800d0b0640e00000d60131100041500d402c0c50349104000080e04181d410711041c54184085c1d40d040f60741400660106404407050201001502e443d81c05d600101ca64a000e41c0c0041b1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 394147248 1250 394145998 394146029
    0x31b0d031a0d05010b03100506040c0219060e0a0206070303020711041509110f04080a050607050a1d1f0302070b0903030606090d0804030204060e040302010507140a030b06040911120907 81
    0x1400c254140c1100c0381c3c020000802d5801c144c0f03000c24a01884440c03004415a0342d6424000c0e28070307050141c180700001c244003c00000e0054440c0d40aa4058407500a140550700c08010140340320500400b500640c00401c00354540800f820050081c0d4004001210700c0300d0350086100070703480c261181810781901e0411300c001c07443c2800400300c000c000c003260759800d05209211040103100217000a03c0903041080203002c04680c18a00240752440c054510390602206101030100558014030341600700440104510f1401c4007500422155a00104192412549004007680541d0035070001c1071824403602007a00c0d2a5500d2144a40380d00069540d594481d0040248485a140c002c3e42c60310481d005942c0580751517901d5000404895441e40101c0e4124804801c20062540a05c50940e1203411414020006200c84403010224407401d900c02c0c041c99920700784d2159039103544c4155030103805c890700e0030045c07801e20302c040042940100e00c02d000344071031110008542d4800440c0308001c075815000012180f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 394148498 1250 394147248 394147301
    0x5010b09040305090f0d0f0c03030f0e01020c010c080d1b0f17010e0601090b03040303061d1501180b0f040f06090e01030b0606210a0b010e09010323031b0d03 69
    0x2969005c03070303450340108054403540109070250304020301248205883c082070303895480e020b400e10410075244024804a0034030515980d80224241d500034400b40b030000410752030751404002d030b4001c0e03044031030105181c6410700859420101d6845490400c13600d81200605148008549044101c4550903880181d0303001000740e80041c0c0744607034000c40c050401c2c20b0041e845070202d0000740c000f00c40642c0040c2d11200300308a0000c0b00309110800889180d400f003501e190901c001007031f008103000003504200455407040d80c1d00c03500014280280062200703240c0d4441001c03807076900070340140c024079420f46504200024403c3c00744610f07104071407000c07062150336840c64844211100005142c00d8210300c003040f880080c89403031364070b02000310800c28110710b850901c101d5103411245c0600545040c0300030300131140c6050340d0f498000d60440780c3c01003c031850440d40742859034007211074074940c1c0d104d48400304070b1981a541c1d055101e40000903100443e031503484002c8085054490080345180c180c954070722041c03031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 394149748 1250 394148498 394148509
    0x114030c040b0f0a0914180c0d0c02070317030103030f0f05090a06031517030405060c070503010608030a110d0806040b1f090f0506040b09090912040e0405010b0904030509 75
    0x5002140c0c08000341003a41c0c8484079505948000500300b00d512001403140d0b46160003400c8a000303840003c0080d50410200c00102d02405c0c81090240110740008000035001d00642040b0740c0b41c0c800c01d08007400410344c00a4065038038140c601040310344516000015100350151390542c0e0485c0c3d090341d2030031510f00000d41d00781e6103035a43c0702c1900204a01046100e101e505c50590220041605503400500b010141860b0180c51419801000b0403080c3c0c075065415080f130000075201a114101c0304140c0e50302c5c050041914190350307680510303059400c0180020359280c012005d08a00000740d15001c008003100031500e41c550011005900100d1406000b248045c20030394418652108081c0449000140c0080d00710080000301580c040002c50a003000c1c0421070200c1001d4000f09000c0e1078860030681000545103007400341c40440c5000d00810310010308c4840b0b00300042c1800414004042e41d5039500ca00c0c240000c1c1d882101e05480d150300b040090b20f424182000b020f0301ca07a426039203807070030484008100318 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 394150998 1250 394149748 394149751
    0x31507020708010c0e03010b0a08102a03020703110a02030a120c050633090a020f040b070605070e1008060111070504050108030703030e0712020d021503150109080a02011403 76
    0x408600c00c0c03520110b819202403040d44040c0f040c43d11340c035074860b042071300301800d40702140101070060009040c104214000001c44550f0300030307107200c00b24507110b1b4841c0d0b00034414140b1400000b806420343e2417040b202e4056005102c0c00d4000e80d60129240f41e080005030341c609800307a0094150b4080c403c60342c04180c0c1490802c885441501c3c02520032802600d4080c60840c0940c0c10b006244c4040c1035200807800d21981034a81d021444001410b29a004c0d00010302201008214110240e00042d01c00c0c50142424212000b40401084a035245d1080781841d400902088035108040b0700910004140c6d460809000c4d480407032645e4407140305503140300044807208004e442150b04c0748151000030480d40e94038000c1c1806404107074021526094141001001c0e514084010561504121824845186035040350606a038042e1003250384004a0300c08038003c0c064100c2c440f8602c44011081c000d050a010508070000d003402d0707954069994a64031010788945202c1d20090200300e40c59a4601003002c480040c5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 394152248 1250 394150998 394151011
    0x30a080d1e0c02011d0304050108190213080f070602060a020703090503031813050112030e0f3313060f0224040501152607030c0b1908011a0304050703210305090307020315 75
    0xd50342c802f500c1c1d0040240e800003001322440790341119007482143c9040040d90107101c0004001d191f803501d01072001c1d441d103402401c0300c81101d40000d040d00505000e0340301c5200a15010b07003165951402c40f24140400910058000d1054a070365840416000450103160f040e281c80740028000c442041e40d0685581060344806a049006045664140d55a1181d070710310000114400340c1402e003012031008420303000d8540f0740141d01018003c0c2c211400614100c0301c250b811a0614001140222000340d15280500b1b1040b0030200c50315004c4c19050b4001c250460045c0c2c403c0c0300a004404100c4410b4090514501801030540c0408100752181a501c10710102042c6045e805c1d00c095039140e4a440103440f449801020441d08009510081109900e501000d4040345190480f903950401102400b108140950080074010100110302445000c0c00076100540d48a11070819940b2a010304040306507507125001c0c0801c4c07a1000280100f01c000c022142a03550050140c9205444000d4a5401e000c0c0034010 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 394153498 1250 394152248 394152271
    0x509010f21060603140619150c05061510020615131b03090b01060f0203070201030507050910030e0d0804080403080a020f030a0c0605090a02030a080d1e0c02011d0304050108 76
    0x10140d4030030700c078812000034042c0da60303001c0380c00c5035080c102c400100c0d006400d4502980042c07066a08090030288a0b1098410b0005041050032040c0300071200c502040300040c000340920000c1c018458040b074500b03952020705840030008000456800e0fa281d640880c0d01e0807104041800180c81490412034018090000250006010f102c0070440da070f40e10040b030710640c00300b130343c0b01109400c2c490305201c40c0740188a28542443e140f5134903c0025101c6c02000d40003410302d52600017266410303000700140c5841000c0507103200c100d8024040020702419401451604a0082450320102541702e42d4544e4810703034000444500d82403440e80c3d440c0c03c41e4400e03030044045004440c0620501e40342800205042d21690341c03074909883c01d9050203030440340e000c1c0820350740e03600040d0b6000060300c5c042414440250070150103901c03000300041c680040e265007100364032808460400304e00303108107130740c070100c1c15070020390007008586062402ea2071000d149540e401040c1c1e00a000821103503200303004040e8442c151298 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 394154748 1250 394153498 394153547
    0x909020307092d0807060e100c031209060911010906050c1f11030a090c0506070209060d0203011b0c1b051509041104141813020f1f090e070509010f 65
    0x200203111400d84c20410540e00001001c1040e03d03448101243c01500c12a180c0d07410342c0c0200c0028021041155009091200c1c186c0f2150300b113001c9034054a2010b0700306038107000440841c0317014802d2400882e0070a011454a04003c50390900c202c085c1c81c80350b6802001441000d0300c0c80403401c7c5011640e403440b6515a218880c09101c199084d0280d070050701e8034000401c2e40855450019000c030303083e402050080c442401482d0140e6501c40f0301d02d40101041e600e002d000c50490011a005d84414030a00d00c500e281c1c0100c4160490748044ca6101c6140640030040d2000640541402d15110034840c8d03552000341c01400400c1c6545420050070444001000001c800711021400307213644d04581c1c000d4600d403a03629030141242c140358018110300c81140b0f0035083c0c00e07d0407904070b80c606038814001a0040f1003100449030385403142141d00001c1c540050200400e41c12190000340703050b070140541d001070500710012070940c45c000c0b0700361050b05105845103c0c0802598508442c80441d805100400b00e01400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 394155998 1250 394154748 394154819
    0x3130b0c04030c061206080c0105030109020c210702091311060d0612080901030b010804020a15020c03030f0c070b0313111c0c05010f08040f14101506090902030709 72
    0x842c440c00500041d1211090001e03082c17070b0700c0e0445001e03501680454010b24002e410903a480f404603410748140700c500688483c6d540c1c483c5482c105114000c0241c14107480080d07001030401e0b002801540b031086460030b100e60b43d01e0407070030300c180041c4000800c0d07901614080717403251401c01d001c1d00f0140d450503030001e002036880cad140030b641c2c041445059404403400110000e640d41e040c0144148880207003019190742c28550302013841441e4a05c200030800340c890030b00c2c1c1c07331980c401c0c0158a0001c0004046036220030061a510200358008ca40e091420b2083c2000007401c81d0035403050305c0c03140d0003c0d06901c4070403000e41c0782d040c2c000c0001e0404603409061001c1504030b01c1c102203110010716024803000700e5803d00b8440094a030f0f0303484949400c1841401010000003403400c15030291000d83c00318106054014074200d9a2404148186e88051541440b00120b010701c20300c1a0300049801541c1c85050072592400c0340412840300362040c03400074001020a000110660381c5043c0000702041e50040a0071514 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 394157248 1250 394155998 394156013
    0x2160c03110405180c06130317031f0303050d02030a110d0507080a110405120a0807110f040e1005180304090506211911120d03050c03130b0c0403 64
    0x58004980e60003052000401c01d00b0a8401e59502401010350910305031040e40740180d603050440c01d4281b04241c005000004000c0484d0ba0034000c40c0d00000095010340b10211409207074004944002d810340b00006481103400407041044102c0f40c041e11070500d082841d0300d80c80e0281d40000c08660400d83c81c1c0c40400c00701504c0d080181604100c0c108009500d080600740205904009010102c1803401c00103200404221f400c115030032160111001c1529801003101e00d804c3c16131039000503151500c0403800600307201f0204040c1c543c42c00222508498004c201e800c01c030440300211010110b551100190b400071036107039848030707412a240c400f9588100c100300d14402d01d140c1c01504103248003a181ca00748075041c105944000d52011064540242e210a0310202903520104005c100c069031010808002c00c1c002d2040b1650003898000d0b001d506407441e001816a41c4040f50300c507001c00a0b14103400213505100345d10a4900800c070b0300f624559000f1454403070220b40c0e94003620140308040101300001c00511030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 394158498 1250 394157248 394157273
    0x80706090f1416091b0c0c0503030304050a110607031209020103090203060c0903070503030301061e122909010806010501031d06040c061b0308070f02100e0c120307050a060216 77
    0x1400001d00d440c0c04003550f000c40c012125130008020600f4200a8086256500c14211341441c842c50103410040389410305084505031644902d405020020034001802000710318101128021721030040d2028028007400024828898060002180c001058030007030303841d401058582d801450007003810103294000a00301038065a0000304101300040c812190304043c0101b400a28084000e18107561400c54040d044034003000c185080076825044000200740100c41c841584480410704011034507d0307801c050b40880035500c0080701000b0010740c1404621304032421a040c0c0b141080501174991800005401400c0d0b51160040d4002d254521030f104d020003004828400c0d4012000100554600540503003084050510040240441c10f088000f203a0000f1115412016a251070020904501e034124205000004405a07080c02c1c2504405003034400210300c17425a004488468548158511040d030380e21801d003000381650422050748001c0b5800c1e0303016200103132140b1031005007206280d46143e060600c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 394159748 1250 394158498 394158533
    0x1030b03100203160503040b061c0507120611130504020a260609060111060f0c04030206070606090b010f020a080a09080f071406030402030616050d1109031504080706090f 75
    0x5000c010001c0c0300e030070142c0c44c541c00c0050341000c0d842c50800361500c0140c904010003990042806200b2040c2d40c00c051604040740c2c4d6000020380c0c10890302d441035a80601c40540341030b0380050400000358010100101260300300e0480d00448020b192626090001a41014850005001d04110120001e0919162a441c0b151101001040d145020b40030400703240c00c050320950411550f91003040d1108000504150003201034100c00d00350340c0d5032900040c404c0c420390b00000d401c920003040c00ca04001d545c0c0c00147c150381034030380706028081220004641d07840400c2c11050050b84170403411000301e00d80c2c1004010064991a004905540b16140185005441448003c2d030340d00c01942003044100c00a0f01d20b0010790100c6140b0314600706138000079a5800040c0101c41400049155150a01c0c0548211003000107442410310640e80d820848451640191280d075000b4003a049600748044044d644041c86203511148103810310401d80c80e404000c0c48107100031225000c940840300c0100324505403407524840e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 394160998 1250 394159748 394159751
    0x606020705040615171003142407020304060813080703110705060708191701060908060603013b1225030f05070206071703011d071d01030b0310 63
    0x5203041d092004503885039000364402401000380300140b9500281c007000c2c2540003000d90740e141e1030308581c1100060b034a510052952001c03100d1200d1412000c00c1d000c030986e00a03038a2240501d80d0451000e000442110700400681040109001c0d5601484034035401c003001030071181d13801501d0f981e90b01039a0b03c5480700760b0110315410b0580025000070040d82e07004c0c0c041540c80130709096899984070780e1405062107564188008410041e005c501c070750700b210744e024031900303078481956540d501c0503140001c13900905034503001d51400a0a10f0405005900d0b28505081020342100c44510b5064403c2c91040d400c0700015003221001c450005080004600c0342c22241c0e0031550701c28005004521003206294200d500c446184450701c08640c0186101d92112414100300c7c5e56913500d40300107070207482988001013003203d800300110185c0d20401c02460690b040140605806107154542c10005001100c00e400014000b40c1c103800a0880e207200c0e0b21019406040105409106400007810040e5548041d180315 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 394162248 1250 394160998 394161013
    0x3030605090c0304120302190c1a01090b0406080606090103030c021c05340308030c09061801030c0c0507121a0702061005190314030f07031205010e22050709060602 72
    0x42080c09070345c5242421030904600d0040c400c02000600b100c40b02d10320080c040c170008640140890f45494089101c035081164002c3c1d80c64888031401003c5a104840c0941c0c0750042c08624088000344e22030141800800b40c698903841d5035000c440405240c04100d8010b0542c464014402020141c003003151071150001c1d00d074a000500c0d0900303407266100500d1038103041c4102c042d080306400300c4052051726017020341c981c2d40e540d0300703500804c9030703c02c40a0701a00b00c400001c0074210b18481c5480322501201c261707010300642201881c210b40040c030400c0e014000d5002100c08106910a450226020138400c40003280e440c1071500c00c84000c80700c11140f410150700920100f00300244442000f02c003800e012159050041f954440807031b801c003000e010081c554036061070202c6c0d0312003041044d20100c2c031031880030550301c40350303480c004254220340c210940400d401d100021034410110041d003889850461880d060308009130201081003800d0900070f50305401030050100320f106582c0a02009480e0580041040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 394163498 1250 394162248 394162253
    0x60e04020904022103210105061b1204032004050f1513090f050c12030a03021806071b050406120807021801120c09020306010207051909051008060906012103030605090c0304 76
    0x140302d80301ca401e1b1400301e080c00504c5190388440a464058640c020544500402502c1c0c0a14100078207165000038280410004100400448008102045500c0a11b601c076100402e11050300c0c02920f9140a00c60400001800c0f00900d6154490740d030b400402d0342150032500f004590407500501020b840000450385101d060001c104901c1c00c0320081559411200d200d0210140e07120300508401c0c1040503000195031b071407880030704140c03134400900030000f541e2048246050700c2007100d51003400c5080f800d8070400060b280307130601c101e0b001c03565024001002ca407250345d1461040ea0014000302d0340420b0201c1000c90303607100c00c014540a000d0a003059480380445e0b05006d0200106944030800c42401001040000e980c0440c0407803c40340e0541d0036050048020b18041c20f15950340e000340040c54600001c0281401c24800424101c401e843c003920b4940d211360103000c0e200e0800b4010760007007101d100c80c160310b49840000780b0401d060203840c0c0015003a4454000409241c41606d21065046010050009 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 394164748 1250 394163498 394163527
    0x20f0409060321050315031f0203060306010f0303050a030c1e0f0311031303110a0b0a050a0b030d08060f0a0815070e010906080f070e0301020c0f0709060e04020904022103 75
    0x415144440f030301031005110040c02c2c0d120081002c00c12001e50418a40315031010000c0d0310502116895000000c556050008025001169110f200c1c0c800c820000503024009500501503a4155650718a440b01010003a40034081c0c10b60b041c0d040016842c0300002e0f0180c0c80d9482991503440c0d40c1c0382007200710391400003025107140c5140400e1074001002841001003038151103451841d89402c1800c001c05900d00d01d2410f0601c9981e003c4c005407425801c104081c2d0466201c248500440081000310100c0202807550701ca0344480b038240490803640100b10903180842e02c440401100400032400503444811450a200540a908100a00e500c080c44282a001080310061050030701e4a907012a00d4150b0003060f042d0050f26812100590101145c00745120f41005281c10340302400035569283c0500718075036113a640704c4041026009404001c901e844590050306c04484403110458590b40340c036003c0200a940c0076204030b901450204000d28000c0301c0140380310385c0c0d46e1350b08051078840f07004580b440c2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 394165998 1250 394164748 394164773
    0x2030114040b24040f020909040b090d05031e1005030f0309130b0315040302160618060f020c210601120c05010206160c0302120d1d070501170901020f04090603 70
    0x481c080003e540d40c58855402440840c800c0c1c80881c1c02044400059902d200203100714502c498000420340200014441c00425560150354020100c40840301028000c966600007a00c142d0120701c21050490180780403206a1a0801700405903824400d0343d6030006844c1100341c6944628a400110b1282141c1c50080002e18041d4a221001d110015584c00000c0d2203d4120315103a061031048000b103000d15100308005050ac6510b030011200b103540381d44026103074100790038503070207040d40030800410500e104030b003680304501c01c2e90020041c08510f041080403080d0005041503103100408014018030b5810480786d4020081c468802030024403506006240904540125055500580a0101c070b00c005500c040500400c525196404c54464035049040521180c45030a1850000c102c3c103807040c409500c411143c480d001c944c20400c040102c5c0c050380380c4110748078050104107030101261941c0b0801d01006e50020300440018905107110011b1010764026800080185540325424020810240c2910 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 394167248 1250 394165998 394166011
    0x2d0f0f011401090213050d03031407111605090726010e07120507020703200d12030c0c110d080c0105010305030a090605090d110607140307031b031e090302030114040b 73
    0xc0d440c0c2003c2e11301d020501d04040c1b2815010b104952982c4060610aa1000b4640240c0c8e40001103942051940240300ca420115600e1070f034005d0490150301d40008104200840c7d1020301131003226582c01000b9286030380800b252918081d00d0101000000708000040d50192000f240040c40038144100c2c020094100602c900800c645401c0603c1142500012003504481c4d007e400310104013404040f0602105054a20541000c0c02035823242c01c000d040004940d80212550b010130200100f600116519018008040e1500698079141d03122400c118124000d00d50050040e00d00e000c51030440c0e40e00311030307090b4015980341c0c01c04140307940950f40c408602401041540342c1142400044400110700344242e0b038004000c00381c1c000f20104a80c442d902600c6484e9048029054185280601140c030307540602011070014a54003140341440c0c4001b182607110395007654900e00d66098810001b05500022440702c020321118040010050b81c09008455201c1c028070011084d909242c03802d00709406024010 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 394168498 1250 394167248 394167251
    0x40e01061d010e1005060a03090209040b0114060702060409020315030d051201062a020f100309110a151107170d030c0e0609040506150c0a0c082d0f0f01140109 70
    0x600004c86812a5407106856040750940d030385100703102d819002003211182c000d412551480400050001201010b4120741d06004064180d100c11020001203104080d00298007035030a05c024000303060507a018550180c0420030000c0c0b601584400a8075041c00007650340c0029a0014280d910301c110000618010195420802103c0550401000c0400c81a0030b2683d00e055441c0d000c0401d66880a9031250a901c018105a41010703481000a0140c04a21400d488403601411031380510b060041c05d413012561021040f03582c03141801401c848241c0c008820b8401031040c071401140300204107008052210201c401440381c821003047c05425034280006c29801d0014001146e9484e8440c4811100342c1202104e0010380e80e500e000004640b03404420748440f031350001196004094100051030b0040d18014035440924640d100e41c200d44d2800f03920451210903400d103a0003070012000c0c45035070040000504c1035940451804020901d131440d00c141c080c000d070b9100c0741018584d0140054850140085000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 394169748 1250 394168498 394168501
    0xe09060108040807020d12020d0314010308070f0f122a0809151c1e15090509030c100b01260f06030a0c0605090f04090c03020f040e01061d010e 63
    0x81c00c1103030700820140a09400040d03000455443d000640c1200b80c0c0240a95000300041c00001c1d86c5d01504500340c808a03180507401010682c0304802e20341220f03070000d07240e803424001d90303103d1320214a2880c003104d080d03c5040c00800081c2042c1440d440400650361517090817484004607502d20844e2041d49503989800320304c80c41c045510601156803480c0b003030b5904400841d81001005444c41400348074041001500000c50442c101c64002c21004080008420454400c2d0248601220a5048030503040c21400d1400c00c00501513410840d8444510400e0304c4c18503208010321420700d10207481582107140d440e184013102d9070300709040090511800251522011443c11035200c050406040040d84219080009299540c10000004030941c42240b01010a55401001d41603400098450788a1010510014013034102441421503181e00982c100140794a50b809100c03200ca080c0d0646074100ba00e0b095941e900c0482406440000e00d0020641580c14103c1c0c020b5060021060b046000e42c0b40201c0c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 394170998 1250 394169748 394169761
    0x14090a0504150209010e0d080409110c03090f0a08060a0605040c170f04060e0a050d030f09050a0b0c040b0c06062e14071a15010306180f150f03030e09 66
    0x4400b0b1901920642c00507a00c10707403800103a035240e1192010350750040d44085100100f08d24000900b040b01e1001e182840a4151256444943d0042001600302580180251600d0b40b802d0f60000d030b0080030207172030600c003d5252001c2c181041d07400c47c2c401107100e4440074100302908151140700d400e01d05c01d10b0038060550703c3d400e10301c03660000904154918502c4401140c14440c8942c09403503e042e032882292161842442c02e00c0d04d50000411402c0401c0ca130140d66800011a80114507a050b440805440c840c0c40348c0c0c2d80e414149c4009040c10045d01004c0c00045101c001c600000d0510411940082c046440d00c90704108024040001e0840391003018220a01200242c03200b180d500b2002d800c00e40c290300003e2030500b0f854092428060301a0384c000c141c00714001d6111040e64080d0036000650302d11032520340015425079400c2d108010300401c2c800c08640994045a000d00d0504802e404045002490703001d07003401070405500049101200400704108164001b07401040f0048240d40680c064541b24 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 394172248 1250 394170998 394171013
    0x10801050a0b070204020f0c0a1a01150c030e0406170709020901090b070f08070609031701030b0a150f141c1505040f0f0308010819050c040213030b0114090a0504 71
    0xb03100e2040480c2001c54010219138a42d01036890461640c1c941c50b4983e00380501c0c599070b4109104054640d01090781d40c20303207540c02c0c4c140c680b8141c0e0402c055880da034140884040301c0891100c0c00603020040340528125241c1d81d9400b50340010f1044025882c40d8090003c00203080108070340c0854403007403041103601c0040e41c00a11072000c565024041c5510303000c4c02d08100f000c003000c1280c0141007420000701d410801c2519440074415a0080c0d64101d0034039410031060001c41001e01001e0710441d200400902c0d0b020351504408504600c001a1184540d40e41001880c502c0700c982150210001132030103d01242401c0c40f1040110250a440030340307841503525824030b44c1c1c04586000c1140780d16000054288104d002d02d2060265206500451050450900411388002801b494000d40284041c02c002b600301c40c4030b89190300e500314016040c0c00810100f080b00952109880d040f0442203201e0000104155101145c020700018404604e401d4074801001503040d002440210307118507000520001c500c98 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 394173498 1250 394172248 394172269
    0x124050a090515150d060308070b01080d021e0a02090c030106080f01030c23060d060e070c020906090601020c0d0312110c061f0b07150b0907170601030609020d05060f01080105 77
    0x1d0f2098004a8000c0340c1c4c0c0c41c0c0034801d0f001140d0115003081c200000300301e507050041c1420340c012902c440d020303603c0e106042d40b200d41200f0364000590201c83c81c400c0c22001550140c1c040708060301198405807003a80415001c0700201c983c0701658001000410a00341c101c5602548820088042e034241d60441d5503007076440125004100c8800d4a6140203042d005014848640b10076006011988613108101c804000d003185005421840c00c0c00804503405034085c8110683d4245d008110f9080340d9205070500a0f000300c000c104504501c1000c642c09800e0301d0f90001c1c01b01c2a40250703518100103408a0044050b108519007170805001c0070880644207900100705150005000070b40c00d409005607181c65101040e5580041c0003244c0006a81c00030040d2000b43e0035400c0c007012000f448007060301c400700203040c0320890300b07175010805181d41e1500c0142100c1006511400504000079080e07120090b10b4100d802242401034950381e14403e200c85072408000c040c00b800003d190103070266040c035001c641807804 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 394174748 1250 394173498 394173541
    0x5100203030a1e0e01090201020d080c04091a152104030c08180406080102220e0708090a0b01230301050c0405040f0e03070602040302120d0503060607050124050a0905 73
    0x1c0d00d030540010b905450003249111103940d03d052000300c55885007a802031030320020880c05885029056141c0902500c21103101d4111010150304052401c07490102402403804050295107005203441c1095440816410760410030034041034075004504800b040643c05200d0040b20042520100000650711000316072201d680040d01903110301caa85207042e0f41001941301541d0040c20a040811070800541c05488124104003081c9000b003181c404c00c0140c0714160055841840d029030001c1d5100b802074070080d4009a400c0c0803034a00a100c0e032104c00c5508803c0e081212035150307001aa808c0408450414103d85004a000700040d0a000c0d60b828030303500c03c0d441118021916440c021000b408141d0001b200004c080e4192682d504091811310002d42c05400100c0c41010590520714440c06c0004002c0c0c0344420342e8491030302c2c40e00c8007400c11100d5007021004941039900e91040d801c6e41300f2520b845c1400f8180e040400880e0030b00f048200858100e154004044503803a0100700801403c0e8100081802e11 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 394175998 1250 394174748 394174751
    0x30509190b0406090f0c2403020c1b010921030905060c0703030f23040509010803041406090a05041d06070f0c0f02010c0b070801060e09060907111f0e0705100203030a 73
    0x300e840c1000c1c2c14010900c001c1d06c0c2d04030002000038040000c0c001540702e4a48600700d643c602401040039004c80c00f4000304000582d004c0c8003d0f41f1100445411200eaa8105050041c911941c40c0341414218101d910300310321004516510100301900015000d01400045403c1403d01d0342e915012136880480384005810002207040302484180074441d0140d4108600f540561814101d60503a601c50b072050bc11070340540c030080000a8011008015101990510a9204c014007107200400240b034201c144041d611008002000034507554900c66040440084c003544001000322100301707420710000900040078004c04c10350a6054641c0086a64401c590003881c00e400b0702190b0004903280404da0700c00810403410241401411354002000724101c0354180d6552074045004414845210320648020f60031044080c00700f2111409001550b1516075014119001624030078041070409071301c5400e81f1440d6030740b410815510799080c04134102401040d1040840d00c4c0180c10002e503a0300c002000301d603506 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 394177248 1250 394175998 394176011
    0x30a051905280306210209090303060306040311010b0a1e142b0605091c05070308062e09170105061f030204030c03030e18010f0909020105040e07030509190b0406 71
    0x3406a81300360082d1600d01091000d20588000e2000e8504440d1400da00c9952607900107500719000200310783c4902800f8001c0d240d45c0c4c4442d5001c0e0f40100e01c0751182619552918a404229218045141d0003441182c8101046d40a003880408541ca0603402503040c1c4031070840000740b9501c4201c000c1c001180f402001d09034104005140c91648040c20100800c43e508250511260b80000602551130048200203280d2404980c442070b0303500d02c41e18000030b000c29001d00001d082450032100c00c1d030b20580d0b001c0c44455044290701e4841c40c1a1404003148010031041c400038411043c140c60400e07421421603000b0404c0d800e0140008405001220b03a41201e403c3e141d00310007886100f50152070080d680b0121040542d51207150146c01c107400c0400b22400f07003c03002c401010344c3e0902004981202d00c0310303060907522424201610040d140c0140b003641884400c000c009020b90a8000880c4603131000d907400610383c1403401140b42025081094141c000f0703100343c20075020a9032400c4507a0031039880940080d05 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 394178498 1250 394177248 394177327
    0x15050301060e0d02061e040f09050106110109020a0501111009060c020d0e0a09020a170c030a051509010b0a05070c090e0d0203040b030106211b0318051c0e03030a051905 74
    0x1b24459500325030400712120f600014098020740109060321019107600740c85502545d201403c072520400b02a600200503402004030f9401440400000ba0742001661828920b55040d40181c07004000102c9030103070381d03546641043e903060100d19003d088502e81882400807010000d000852a8051591110350000da0307603045a000700245880d00320656110840d40c60250800c00300b80e0070840d106403405007441c000901c0c40c01b002408071040c05006203121074230390809510380d0280c3c120014403024044100a00d03c01f194100d50b840b8010024840c01090710803034030788510705011500d034489041d07610902c0240300146041040d40d040d036900345807000c84e82d0f100e109500440340c0b400428141340c51405103404014030600e005580041c0840d00e0600c000c8a8241c80307446c10641061014060ba04156034802c2c03514070f111102d910082491418450703c0c0c00c2e1200103400c551204540f4000304400084241c0716004001c0303503010b21000c5042040c1131050a24000d4182c0e001d8104001a00e80d184842e00c81 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 394179748 1250 394178498 394178557
    0x801061403030d0b120d030603060f02030903191101090b0618071d030309040204060f1e1d0d020405010e070305010f0608010b090310020a0903050106050a080a03051315050301060e0d0206 82
    0x5e100040003100c40542d081c41016000b40181c1c04190380e9981062010300c110241402103034018007041d0003e40c6841d00342e0011000240b4030001c500c007004030220315008514000d00845c041d03640261050301d103505101c0200020b0240301b80a90030342000d80010480e184e0340140407244480c81c005003806001941c0c00010f810b41c400d1340000da80c41761000c80c0108000da408880300a4200f00e5442d5191034030304824800b070411194a04510004807020304410803441d800072481054070010b0411880da070940d900044c1503690981040c040852000c1c1049480c503418010f0700d0040884a40100c1c200c0c0c00c0010080070700d00140100780c0c2007100010303000c005031800c00800b411140004011511054022030052000c5114402942c007503003811130105e200c0c54040e00d000c04070765481009012104481d1740030b4580d50020103803810507407001c0c0c80004602d4645880c0d030702e009c0c016540e403a69a606010010300011040d4010901950280021100589500d41202c0d000300c3c10400381c0c00000b054034007502 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 394180998 1250 394179748 394179769
    0xd1a1c02240417161a0a050f030403020303060102120a0806010f0c0605190e01110403020415090e01050a3c0621140a110904020a080102130801061403030d0b 69
    0x100584800240003d60003904803100000d020b2201c207a40c8070340b8004140800c0721005014441d4102c0d1100319443c40b58440000601048244e400e105083c0b0040440041c856001102c0072750140c0c0002040010070b607414000c0f001a41c1c80355540909040024070010100e1400428090602050042d842005030240310311922159001c03000f80418541018104800c00c00100e010f100f01e42844104000720344180180380d41c042a401c440380c2028035540810003d48247d98504201b507180103000726800b8424016003070441410000451582030000100c001c0310144141c52140c50a40a1000e0007007116202c48281d01454118902c1d803800c0c245e40c00030040803a5440555240366001002841c003c07000b4401715054007a0340641e13002000c50075400d4451109910041071145180900075a40c60b2010003103070001e0018042440c1e1540b183d5500d400c981c45001407500d00243d91508024070f550074068a00038200307030343e10001c01102040211b0b070b44c0d00544880b4000d160b203412192926440d031301d000d070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 394182248 1250 394180998 394181059
    0x507120309030516140f070623040e010909030e0402070803070809190b0402090703060b03130f121d1f030905210a030c030c0c02091b0d1a1c02 63
    0x7004400305480c114000400140765101e02d4007400c3d0200586d040041a00004c981c0e044d120100800c1c01c51038943d0003483e00b8414410481014000403c2d00d0211004240c0a081d041e1000641c0c2c0b0000c6c1006014060f1040c0501d100d5801044000d0009544c5000e42c5e070012200d0500b511280c40b21140c0034100b01e0201141c00d00442500c0c03400c0288000d0070b04141c0103d009a0b0f0340a455120007000702c0c1512102d01039445074880400108000480350000401c01e00d00030b0b008005d251165a8480920843d55100c11001525046209480c010942c0580740304080841e45c00c0721240c10035041c0304040e026032030702c2c1080c1941c4400350350600406000001c1014251843e40b518021494400810364000d810311340002071500048142d1180079204030f13010b0740902c1d1142d0200141d69400c0107602c00006004404c5091800d495805400c8108041c010390000c0b44008203009029140d494048681300449600c5040e43c480d82d00c141511649400d4490340e0150b07000121080712102001c11032420b841d21 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 394183498 1250 394182248 394182277
    0x10f050d03030c110d020703140105070804120207080d030f0e2a060d050c0c10060617041a0403030b2d040908160f0b1f0b03060f030304080606040c05071203090305 72
    0x40ca05c140c1c040383c00b80a4030320444540200e06880020103088607400c071060f2021030b5180000c5030101c2d41c1900303403460380708503403044990061b02d1360b04842c20706100201820100b52211100404605c00b4002c0d03541001c2c1c808010110300005440030081d1441801c000008070744124158011529038604030751598083c04801d01c803d003070103140300c260703944001d151940500070020180c140c45100d00843d4200c6e14203654003158210300e41c010b00c0b421a009442140e950158803289001e4840904c0c840e44128000c0d100010314100400038010040000c040d10800c4802201c060f06038481440d11044008009407400139980102d440c15034035500c01c1840f014960342c50800403008000c50b100c80d0720700b135500c140403030b0300c00d0344400c1d94940f020301c40400e82c2c41d0002c0070580b09100c040c140001a41c0e000764020081e0503c140d40c00042170655015801a10058020408200c1c4034141070040400541662620741c1c07030600107490b0a488800001d0070b600c20141c4034220340c014148103106a030048080c1460 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 394184748 1250 394183498 394183513
    0x1090e2e05090c03100f0b040e0606160b180309150a0507020d0c23010203070f0302010b15030103110604180b06090406090e01060b090d0b040c032108010f050d03030c11 74
    0x501c503801c0d00200e0343d0b440740c82117060f00880d03014042c21400044407030604207542802d040c580d20b6180c815001b0f0260f078001e0301c20301c040000400015490524180548002c8000741003250140380401c502120b070b040d8030717842000b0201d070a40311400c0e00041d409110000e1510b5a001c14011a4680300d1050069801500400400c0a1021a0f20705c00100d0300c2800030b04031000000303490600072084a82d0f4a030b002d0303002800359002081d80d86d80711654951082c0b00015141031901e000428501d401009520140030100040c0b040011703500144c400c0440c110f074540e0505150609404840090445c81c01140351100050501c613155203045c1c0707100070300080080c003000391100300c21001400f040d03003014403541c01c140e40000c0c0503c141046500c0c82c500501503a00004485c2c45d0190740300d0000d401110324040b050b00000218401d03840d40c09848170301095101c0140e060150003009040180c0003521f90907541c00d001c104542d1200002c6540344c0e403604022542d445460810745071051498050005802400d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 394185998 1250 394184748 394184761
    0x31c1b051e0106060f121e0501081e01090c1701060b0f0901081303080105100c06051e07090506030109050c07020d0c090c0504080309061e040e0601090e2e0509 70
    0x40c100000c4410002003040b035560303440c04c98401c40300103031010101d01600324804050006401005554182c00e0340e00403a0000010309504880c0241c0c0508020b8001d01039a80300000c03000003414884bc14140240070150081e200c02c034000d54144108418403008071400c41c0300e00d0080d042078000b800d041c0c08007500c5281080c054884e56000356900e50003c5e1103c00029100050001c82140b0b06801d943e694400343e08000078001e204811220440600c0300300c0211500240550144610507000004c5010903202c0c810717541514840c000d0543e01c00d2281040341802551900400e5a0445410740c80215954a0340324002105210300309010303400c40e8504c405903050054089220048694041c0200303c070009600c000ca82c503010f680a1403003d41c03c10420310240d441d054019044418100390500f580f640da0a0024205900c9940680655603940701008403d61b084800c140080440c0381002c040c510780340c500980c1c103030460f942c4954883c0103140340211031078100c0c0103503004d0940580140b40702d0400230b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 394187248 1250 394185998 394186033
    0x90c020d030501080f0a031128020f06160b1008060a0e0708121605070b07240513030311130303050301050907020f070603050714070b040b06031c1b05 66
    0x26103580c400300341068000500a10005061403c50074144050315000c0c03001d50341210115108120804a44500c0b5941d0b585141d20800a07034010310241c0a520301481a0320600c61b950406c0344c41103116403030074440c1107a4507400b0f0100b20b50180c1c0c0309c486418580d8810000c44c808180580000f17a5a1046a0410408460903445459140381c43c20031213a8151f903071a44103984a4802090b0a24074100f80b01d5880b42c0c0c035000c0e1246403268810020ba610040c0c440580740d00c150071103141625038103d41c0700100e4003030f00101160090b60026145c180994500700d0707543c1c01003010b075290040c10950f079400740003904c5060000703076584058401031071060a03130b4030308001b02543c1082c081c1c103100b1080b00001c151114000206056401400406800c07098a00002503000b003100408000c10702400c62040034000c03203294002e0108501c0390303107929001d084c10700b01342020303040040c03045000e580060035254041311080204070000c0b04a160240c0805d401640c08440044200c2000307247c2e1042e441400500c00c000e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 394188498 1250 394187248 394187263
    0x16080a290f09070f0b040611010b04020a0f0e030604080f0a09030203031b010608070302010f14160b091011090607140102030a2003070f03022808270316020307090c02 73
    0x50044601c01511130000318034810b03e41c80f40d4001000100000c10000e40552021403086610400005111805901042c02c1e80d0000180100084032020421071054014083e10381004003900100220300d06940c50159602c1401c03a0011545e9000c40d0340e0000d40e00c51156200511ba01038144c81c0c442c206424407548182800720054110b5091581c007103200ca10008400d01101d805035229000d890582ea0b05440c0d51090300c5410905040c10002581a00c000c841085400c0c0d104008038102490001d14060910201201c0803140030b003841e521240792255041501d025980407200c107555142c8602d001e119080b00003802504550001c0200403103901aa846a842880502106060b0180c9250303000c90504c021202840440c6134100030541c1700b0700c2640030f05480d00c20085c010031024204074075503d403403081512070800640711100300b001e102601c0491481c0c605d100889015003854a03580c0b03a40341e0189100750007d172001060020290350302005080002e0182c99070820810f0011400252640c01 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 394189748 1250 394188498 394188511
    0xc1419030e0a0b0906030f100305030c1f0203100e2701051602060c07061a090a150602010b09010e0c040f0807061b030804031815020c0316080a290f 65
    0x1d500b00d0014080c0b251400703c0b5203a2000030f110034510340d104500440003900142200c00c0d1803040c0312000c00000e000f04010024161050001d0070583c2e1010f00c44881f207283c5c0390000740c00302d0040c414804041d8054100070203494203140c41030308940c1e030b0260401d003190400384d019038180503e40c0e0301e000d19401907009a000d0300b80888a1041020500d000303a81c0c640e029507916a40c903504000150100f4442d51040c4494030304502e42d42840d003400070028041d56001d54050f00c141e80c1c0c6040e49140c3c1d0030089022001002d141c002030002645800010340380c03040512070411501d03031030300c0043c0744041150101d80c06040c1551a1488603520f5400003035444405005200100c0da0070f03901c840d484c3c05400b0201400f00c1e456500c0321915a505c2d03400315890358407401a2008000d56081c0400d1a03501017003001880380c0300d03274010012203403542d0400d032920500d0480c010b055122003505000c96100031418200182d04011190040100a1400303c00402c80001d11104420200c0500a600c000079486502542 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 394190998 1250 394189748 394189759
    0x2070501050f22030c080711010305102913120b0601052b15120507120b0c0319050c03010303080907140f0102010209030a03020c010f09060c1419030e 66
    0x81e180080c0850301c010030750f64407510820110000d05000b40b10034100440c640700340b0309414030105a94504195420a2400700d6040700501d03104c0e0025641441390326807080305035010140c0c840c602500c1c00c50780040d2480e0140c2e80400d480892403000150011a21441018080b4400196a40e4a007001c500341c48c13502100e01c011071201060315580705000b500d000104c400f90410440c0400b0419601c003821094407000400c0c1c541052101000500d55804e009108980d10003800401174038200342041540e4010b07960740710031291b10341c0109074061200c50340300d074504403c00e50301e8072201c00a4404104040c9a800d0f940e0901080110029014000d141240e100e500d0b001e000703889540503551108840d004802040d0b603400a45480761030700500c00700b589641800018688149100424200a00c2840980240e402000c10f0419540d1290b050708000300d05140c6921403504118000704854541c1030b019010b04020b40c1c0c0321104503420f01c04071038003981500d045102008186006050041400003661058 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 394192248 1250 394190998 394191001
    0x2070305060106081906230409060e070f121e02130e0c01090501020d120209040f020f041d09060705070303020c0f0c1c0f020d060902121b0d0f0201030c210207050105 73
    0x240d099002d902c050701c7c01003030300e4080317007695001e0071a11261400040b6441130301c4805003004602940b00364904503141002400b10740c4d06101034084070105990240206240007038002c1e01046600030329514030080c040310807280f4091400010501850b000315030074418a4400b0055804a0000741c1c0d01c080e04081e01ca09070a203580e0b44c016612101d61a2100c004521503501516a201c01d950042208803001040002d01000c8450542c0407600004482552000002018401180c1112040011007522000c85000d4605203203102c0d01c49002070a003500b400301c0820207004150107501922010315120701292196401c042c00c072503aa660820040c0e01954172302c0000c5400311f0480d1294001c0b41c1d00010407402d41e16050742404061a84000141caa4a0341c0300c80140c01a621103070040d511181d010000c251800c1104810b2030314004182407907109050b4504c0b50400920300d0700303409c00c1640e024240002c1c240c59610b42601c040450206000c0508200740011103001c106074043c140481c019002080745 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 394193498 1250 394192248 394192291
    0x201091205090907080a1e0603062d050c0f12040c0603060b1614060106020d08060901050108070c02130c110f011a281d060102010501061d010207030506010608 70
    0x2948142c45601d80c102c1041030000c1d4100d0b0259003440d0700014a450006094070109442411786003602e00885d0100751140c80170000e00015008210190b292580c2c0503e0303a00c010704050031060b00609039484081c2d241c000050700c40019105880841400c2d4110540d02d104290b2007044a10080300c00301c4810b060b10001003000c3d4440c0c410703441540d040b400891301c1c1c40944003411104120f400c80c11200b40c03c01c3c241010b10b80070180003440c003e0085400424824501c0e60024081150040503c0c0c003075560800100103981c2d00c10b40342600940103080014000401e40003152940d200d1182c411146400e2a5041c02c22581c00015002c40c80840d20130784181c3c5640f900312600f40d6180380010024510b03940000c000502e440361300704071040501050040442c1d038504da40080142140c0c818284091491912125000c80b050520790101003480204850342c1440006000d44d0b85c480712107613004404500030091a4000c100610246402604407134081d13946e01401013503298101c442d40012604910241da2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 394194748 1250 394193498 394193507
    0x2a120a05071106060303031513020f0301080f03070f060f020d050403020304090f0b1509010908100b150c0d05030903070b010305060a0b1806090403030f02270d0f0b090f060702010912 80
    0x56130010007861441d102c44a01c0c44108044034166a4070071043e5165a4844e0500c0c4000d01404032003000c0c0720b441c2d41c507102407203051144000c0203403c0c0341c004100e8407001521440510b0040c90b0300c0341c070000e40d40d5415803d0720020b014560340c0c0680d1754903040c00e01c810705400101400c100d6509580c103001030003031513000300d044c0c0d6000054207800000a480fa03204440502000d08800315040c074102c00120782d1610310901d01280d0b5010340320300590f5130386104154101700b03140408004040c020036180030071010b00320303682d241d2a810b400704100d001f00c0429140c0009000b2140a150402c1c0002c50715616401c1c51500c440041d02d1200e130041c5858802c2c6018100904d86004050f0f4220080a103076450000740721200c040148210100340e0384042d0039690341c03880c2c80a0241521119020b0049901d950002e540510315540703298412102c60005c1c0001461700520f500d03266070302245028150b26035942141c6444070002c3e07461b2460085004001441d0342c15032000c1c600302e000f000d01107002285c5000544 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 394195998 1250 394194748 394194751
    0x90306021b16050603040605060118030323180d03020c0607030306180603050a0803061f080603070902030910020702040e03041701060e0f070f1818050f2a120a05071106 74
    0x9070800400e00c00140403600c154008c1ea4031100604140c05810034440003030a00c1030305074000f100844c170942408041c0741d000c4004045500003d2aa40e0f181100f8644444004c04d55429000c0c80b5490114035035041520070b12103c450f00e1006042c15803100000e15024002d040f40c0d0040c03544018425400c0d103824211401303a401184e0300000942a03006d03450711652030304c1d0b00040440c1c0d0012007030a620606166030352500c140a1000340d84280041c1401d07420503041c192a540300321503407030061062041034000852007800940d0880d01c01070f034900f140c1c4081406800c14040d520064040030500048440010112680404141c2d0003001381d20388544400e030060314166a2401c1c2c803103c600000c0c01d5103001c0c40c5007190b000d400d410301413400c04140c01da803c6042005d4000c8680710712810302e8181000384e00c2c051641c1040014034a41403902e001c0380c2160484054000d4050040400300842c11282100ca085030391094002904190a181240d0720b032016007000e0310143c0026507003406000d071003d008506103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 394197248 1250 394195998 394196009
    0x1207151b020f0118050d0b07020c03060103020906010e031609020a02070812030612031620150304030513080f1c030c1202090a0e04060c0807050c0a06020a090306021b16 74
    0x30482c0b01940c0119560016405403401c0800301100118180d62015403404503d071203070003000c440d481d02043c028284031242c11940e000b40c1c040401440160b49400c0101e40c005801c0c60101340d003070652400a40360090b1030528603003080b03100c02c001c185c40d0b42603001031022a5042d0215100309a0f02c030503580e0341e0b020092400015001c1800428020325000041407411801c0da0105d07030400e030001c007402c441078005000031103050074004a00b4800b0f41c0307a841001c2019008554452100b508030001140c58803008000804200000410514004e5041c0082000d055104210381981101d0062150f4409401503a40b0048c0603200c2e1515001e03200740605030610301c1595550b0a010a440f003038602a400c00462690700510304540031030301131508403095118600505010034080c140303407005854160007800d0102084401c1210000c440c1000904100301c550003400140e5a1039044030441c0c0188031034100602190000030007444e0240c1264020b22054100e00076140d4081c440304408a0142c020b1103038 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 394198498 1250 394197248 394197259
    0x51e06030f0c0d020409080c060703050109020c030f1b070e010306050c0901021f0609090605060901051f050c070e01030501140c0306030a08030a02090a030507030309090203041a061207151b02 84
    0x302c0a60704102c102c81006510240c4007285d407410940d920000da0700000840c11a5501c4241013040070703136040c06040d005001040086140001125005480303214891148005030400250402e50b07803d0f0f0004103580d101480195081030383c071000030055444080c80140c800ea030078000400c0c609078103c0215080d03410305130014488182180b6200d8180034a0000440c101641c44600003110301c03903405541a00342c4500301c0054103140a80804c07030300031410f030400c0c1d02030504203071001d440c035614050742607444465003030950302c0b002c0d6604181d10b441d1058001c5541a003001d4000000c102c01500309032080e01c0c0c1290b05011907502c861010440c2c1c001101c560b58154410181d55010079612001160444050a809031030300141c0360105d01c255040ba0300860b5aa8130064080003810303445211800075000e100404c0d40385040541303546a2068180d18180b6a00c800c54000c03c40039616810071808030311030b120030f84101c070b90b440c0b080c0c10b06102ca000391000480c1d124044904103400ca520280c0289500070b08 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 394199748 1250 394198498 394198513
    0x6080414030a0c03200111070507120209070c06020f040e0f0604050f06041a0a03110102190c1401030e0a03110d0203040b0301031101050706020c06010315021c0c12051e06030f 77
    0x113048a010400640010410601d0700c1d4003840d61100380100c1c0d10580040014a81d202d00034a407280c90000390780c0c05040c614040c90700c0c02d4016501c094880f074204d0f006241c201109150341c20a54000e101e911099800e00302c00040000e0180c1c401c1400910807203005443e03620359644c03072042c007007581c90840d01d00040c401d220002400d0741c54030390300540741c41e90082c1c03480c600ea64042e80422011581904141c842c00d6105d100d1030b402e90b0b4101f2120301040701c50116030050000c01e5540c02c1c4140c4080c00f440c18203200b04032100c8c4c0240d03ca54050001140c99004840c1d1f0751206080242c02c07459441c0c4130208c1405018a042c251a00000440d021604c139204403500c0c44e8a0b6450780b080c1c40000e1908941003203000c2044102282c41030000d03103400ba8160b40500540e501d146403002560415511001c207041c014845201c801c2204400c0c100500046d990101e001140c0f81806c84184d41030306000030180346804144200294018140a6440b6a04c0b80c0c0d0315054460a08050303460b080d81c1d0800b903055100c2070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 394200998 1250 394199748 394199753
    0x304020d021504091104030606080d120221190e07030308060609040b03030a120b0a0501050712020c1e0405070203070503190504030f12021e03121302040606080414030a0c 75
    0x161040b1061411004660030940c492007180d0035190031040403a0300078804030307041c024080c280c400d080092139117000500141c4481d01c0080c00003900c404408540070790104298100c0201c280440790300300e580740c0b0188014642142044202d100b200800c1a03840d28144207038204200005146040c1c0303815403540a001d540301030422800350311a0005035001030301d4a0199250ba14108040d000b524103e890315040c2c48208855601142d00d80380300c40b4410340450a0400c203d90300301c400c0f504100d410078401269040b50040503442c121120b0743c459081450b2521f011281840401c1440b0030907400c403000d02154480e500100d0b03481c020f55a010701650401c000c400305d24492100012007500442c203103181032603a81d4481ca071416003d14016210f0944128540e007220703606200c08802c01264036000c1c0e094140d40302d41607035a40900b440f8a1514048040424042e440c0c4049a0007000d500400900600f51035010042c0440b02c2501d00321403000d81d070100700984201c08400d41d0341e900d14540d102e0202410320b8 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 394202248 1250 394200998 394201009
    0x109051203010f0b0304051009050d02100605060d020c0708071404060b0f030606070c09050a0501031a10140d020301111c09080d050703090b0103294302060114060304020d02 76
    0x34000300d604e840348c80c12110404030396004240095002d407015084554a140003c1e0420000380c440c05441031400c0c00c14045035554005890040f200a2001a1241c0d401e00c1e18510705880f41d00480ca02e131064602c00100c1c12030303201140054040541e0244003190751400c0c00340311401850310b034010694003030001030366a0070440003400c04103002d04514200540e44201c002c0889100f550804082c9403524014001d21104402110300014484240c0280b460840d103400c0e07402d42c02e40111043c800c4007903c410300075a52080740428145c0c0080082090a1040404036810b61100703101c00f01185805498103101c0081d4482c0c0c6c442c0581007140380e468404010236000042c0b40061801c0300703040d6102c40d03070030101d04060802c5000c0e510900c2d55042d03d000551060721104110000040031090350800c000d00010402c04500b900303850035402c805c940605a102205000c0034000840c03044042c0f91078188140c1d40041c0c0c06040750302000c030710401c2811040a021161208440107500300032071300c00c0c920041c02e02 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 394203498 1250 394202248 394202251
    0x11220803030105040908071b03120c050a02060c0f070f06020705240a12140604050a090c150504050d0302032502100c060f0e0102030a0f05070212031e01080109051203010f0b03 77
    0x60840d9911f08103895541e400e001843c06149001c40390301d01818400c100600f1042c010340c8806040c508c0c4c2c40300d07003039542551310140010024024000401c105110140030400e51000e0b42c181401e41d20f14030f86a04640000704528400c000c0144540c4400217810305144081c10080e10000325043d850950fa080b5145485d800231800300100714030043d00e608850140d1187c0101d01d200c004c01c480c00c030300300281003105841001d441034002d50314144890700050744820011086401d20015110640c0c1000d001703942c2409180c1c002c5401c8051031841000705940400144401d05a05200302235a007491804441122440040250441202131004250038020240703640100c2c46950302050620041451609490020344070005c41d03074001c414005486054041d505074441e03844c004101c28a010380780256248404007581d132128900102048214890202509506200306283d800c9075a44800b442e0080c005103200341d50034083c004150940c44000c00480381210055100c980b1365a090070072040e0745500 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 394204748 1250 394203498 394203503
    0xb0604170a150b151830160e040501020403120503220f030815061306021b09060d03030e1603030e090f0613090f05031b010606080408160501112208030301050409 71
    0x100450300030345c075659408030b2800021010300c2106010703900d00c0e008008a0f001d0340f42c145032a040031104561038043c62601504403517007020800d115131518100640248900d0b00085c059a0703451001c0012107400c00c008500804014140c008a6006550050049a001c2c000202030340e82c0d040062020a2003207d00030313001b8007190f041141400328540051095804080014010f00c0c03a01c0b0304120040d0144484a06240c0c0c005400c02c042e03e14000150b280312000f4011803082c42c1907281c1c0b109043c42680321500400d01402100c1918114112440000c3d696200460008401d412040c100381400580742d0300401014038615211303111101004119008a4003103001031355036031106400b242c00d0141e40c00507280130302d000d0365880421904c0140d0000e100340394154540e0601504000380e5074080400c0c0e5100303030070807503081d01e5040b1f144082da5014980c400103005503091020301c02e0080b101c41c000b1710480801c000640032160b8100300c02c01050b41103114642054100b4801081307036040903000034240c00d1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 394205998 1250 394204748 394204777
    0x3090405070e18150a0f050118030f050604020907020d2c03060c040915150e060c03030703050a230103140f0f01020703030b04110d0b0604170a150b15 66
    0x18524002c95200da80c0c403d00320400890030020700840d408030356049154800c0a84110000d54104920710032000f08510030300d810811030404000391007070346501c00009542d2101c0300c042c807801c40303041c02d075950001078030245c0c07250142c10046680d5034000103840300040f805466a10911410420540b03058036a040482140022520320010310340e0140180342c412a42444000d03140d5040031002001c42d801c448456004190840d018007120103580c494282001c000e24007007001d11121004984a8021082c0e40400e6101c040140540c03a034060300150301c5010101c0081190700d00604500c601c0c0250b50b05010450401c1d14010301c081440030303040f90340704245407044a034141c0307061501510380380032296002c84696001c50040201a07042c041c03500d0200c0101c0341031000365248056598203104810b040d12105583d00240c0740c4a4941d6016a80241a8880480442d0640180344e0b91541e044c401d00701d901e400715034020b1461015512408160407400303480c0c680801100b1302070f0000e9502c00341c0003000340c1b03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 394207248 1250 394205998 394206017
    0x60406120b01051905030115051303110a0306061205060c190806060f04030506091903081f0803030703150504090804060c0c0905160305180d05070609060504060b090c04080309040507 80
    0x803040b01070014062140f03640e104d07620361400c4a18808c018440142c10300700301c001c2007114840340c6081c151000356600160440c460105803800125910440c1c0e04c0104054100703100050352003061401b00105030300070029207134981d582200c045d43c0e82c403802c02c0e986802042d00d9991850140304800300355201c08003424240c07800c009030001c18140c1e0403d030300890300d540c070440070810358040a10500000a1451000c42c2000b201540c0242c440c51008000c0d09206070803001d0555186000107190b0300034034035402035a64904146a00034064022130300b0504280401000028544c00c00e4890010103581012103207003005e0038118212500024954142c0748042c1c40540030030b00780414402e86004a0104440311140e0b07850100140c140ea4000b0b080d4000507180710340008070030b0030108840f034284070740b441e07d41d5584d016481c00c00001d040441014001d949040200420030600e40d102428014044a85040c1c030354136203038950078a100318040d4442d16001800780103030508140e0400303500440b1909010586 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 394208498 1250 394207248 394207267
    0xa050f0a06082a0613050a1401020307060c210b1509030316020d080a120e031e03100e01121a1603021809070309020405130c0312020f030c07050f060406120b0105 71
    0xe030300000e8000c1c1d2a05c441000c10461441d114034601c0c020600800d02c032684150080010703407a8010341c5e5000d040e194464080040700c500c030711152800660b04011a04c1a0548070b000d01300200400441540500b110402d00354048c00c0b0001a0340140d030f002401145041d9800d60030b503110309045503041303030405140c07544100018400009451524841d98a030502d00c0c0c0341a4843c030660b81200a460b10541040001d0f814180307152140a240302d126807209683c90300ca0321450b8031a40d83ca507100c42c440c0c80d003160000c909043c0b4110000c0100b401060300e81c1d003c0d08201ca21005e032020546000c121071000700800055070340260080c11445100071000d000e0700d070324080814071800c412100040047c0d034a07640c100852405208940e0448022524500c5020603a651100c0b002d08a00014000c41030329091580040c3c030030807204200e46040c1c07081d2500c4030b0384818881d50320b40b4240592403240c14601e41100c1d01d414818181d408940203a51a00ca07104060752400005040c265240c504010013040540c20 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 394209748 1250 394208498 394208509
    0x100e0c0904060308221a030402040b0f040c03150603052802070606080d1701080d03050c0903120301030b0108010209060307030f0b0406170c0d0b16090302090a050f0a06082a 76
    0x81701c054690a020280d6100b400c03191403245401280c01c5503908600c1030059162041034a500a40c140c50004044010000107070300e000c0565200369100b401e01100e0703011150300d40c1050381800300104109191944442040d82550f108a40d0340d0a510b41082e40c0407100360380740611a1705407981410040c03504080d40c81c0c0b00c1c1501d0154124ad640d0754800c984040002e40e2007600000803801c4420a1040b82d410312000c1910340581e001110101030300c80c0085400580d0000031240c25003402412a81d03000c140800c1540140c000340f106031174421450b8000a00c01d241802103e180301c100800c1d580c55a511404150b008044e880711002e806640c60340306000a441c0d40c444c20010340a02a175440e44558010889403030302e41f00305d0403c0e024200380076881000914800b5003c1c0c0000b00c038200302c070101c00108800c0300c0f03440e003a82c0041d60051140d001d003c148075050380005e004400101e603507035440d0740d503001e100280d600364421000c440d4445023005108400c0145000c1c4130020303030a410300140118000240 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 394210998 1250 394209748 394209757
    0x4030210080708090f070b0a0509180702100b03071814010b04050a0501030b03060403030513080f0a11010c02060105120c03010e0c0a061701091d0d0305070206100e0c0904060308 78
    0x1000301e0800701c140180a9000685142d020300c0c0e820040200f6066011400e440700103901c1a20340880f000300b600316125016400f03542c03c024028141c4401c04000281c45003404105a4100008d07005064044082d00910701641001071009070042400a2030721980a80700c1807a00d941c46180c5989551f040c04084411813454000d100900c0d0107130701c072809d00007040b41001c92039001078140741c5801c0e542c0c0300d240c42c0451690303801901030400065580c4c88000302108194580703c02410b0140002ea4141c0684290000d406010001d0345e811403840100d420311402c9900c0c1d051540090780c0440010840792400801405407003000c1000e8404989200b00841c4c2510040f0000c0181340d00400010341590810f0040c0d05d005040e24900700c0107292542e42d11200e140c4040c01380b18042c0740c03941820300550100c4840444105031034000c4a0304482c0110000303005000907105400140a60380105218002050200d0140d8009a0128926031601c6611280c15440003030002e8005440d602c000010804010280 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 394212248 1250 394210998 394211029
    0x715020d090b06030d05040f170c0d0c09060e0105130e0313061e05090a1206061206050f0708010501021e07080d0c030809030403232d150f0f0408040302 67
    0x251071030400e041014200500035141c6010001c0507c010802100020b07485000c452511b003420045001c0b4954241c00c0100e07584030b0315040094094107604211038800c06c40c2c12070b051031104114103030b12070b103ca900c0c0170002c0c8a10f9511103c4404814030b16442c0d40d104c0d0103002e01d50002c60b1315085041c131800c405848143e100c000464904d105c2a001100500070072030040c080d9140c924a880243c80001e504c480305400340e00d001c0700d400e803c80802c00c090350b8401700140c20207101c0c40c0d0800180c0d207892006058100c6010000c5444034000c503140703074026032920b8107850058002c0c1000c0d0081e04c0c550700240c40025000d1195204410000900a0041c4072222941c2d1903981c0d030100c814a541400b49c40a58050200c2100d540b08000820124460203603180041c41031001d84c491803661801034903e40194504141010007159890007030001c01448480130b00f004003002e4840c0c20300c000104080e00542281d0128004a401d0002048444c4a1540590061051000c42e040075243c0d00071a581483c0345105 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 394213498 1250 394212248 394212263
    0x30c0b0d090215041a121303020a05010f050403030b011d150f04080c03150412030509010b09100f08010b0f0d020a0b0d06050f030a031e090815040c06080405030715020d09 75
    0x45c4003c0400c00922500d000131440b69600d0030401600300c4640c0c0100401c5443c440490799605c00c20035200740004d069071070b0040d00903c5483c0c00002450b0003444169000c0300406d190280d0b00303070554064820604e08010303104050403003d07808010721030495440150500795007030410070440a41c0820001e4006009038100910100c5020020b251802d4098000c0400c8501c4070130410000401c0c090144080c06064580804c0540394415400e014141075184142d00c480e030308082001d04101090480202c68544028544c05550350021600700c50b4840455504100c6e00c040445040c140251203203401417026001c500c00070307901c8030b1800d500d4008102c0c00b858680c44284c00c02080c03a2040750301054510880180480550071769014002d88690800c1e000d02c03410ba11401c01c1c3c603d0003482c0b100001c0c4207940540c1c076420020f01500b10041d1045600b164201002d60003c5201c500c500304c50f62295511000071850031181d502d8802c40784031800c18843c00c40b41c00f0017008408000b10700176020704501c114038 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 394214748 1250 394213498 394213507
    0x2160801061a03010b030403030f0605030109033902040b061309020408060c030106120e280512041a0d0914010203041119060c02030309090c030108060106030204030c0b0d090215 78
    0x11450507140038100c142c0c5507401440103101e44546202282e400ca503160030000b130080d181400310b0020b00300300c6d401180e040d440d040f60030085c550089600c9401c0802c00e2071041c0342260490498442c0d9042c2c201001c01c51120300780c0900181003550100c1e9008070300601d014105400101103640b072628a801038111250041420051300c5010010503070840741c0020aa401c0d9810a80300030503004103c44104003041d11501d060440303400600202c14110b184405a554102240039501d0401000d940210340324420a0440c1e4a4504e02e0b1040e03505955582c034405025200c0c0780340300040c03600403049042c1100c0d070740c1111074002000074585504450744800050384a14050038101c030185503415034039000d10601c120882c1c4c0f005a8040403021b4a815050078078603500c503400801e1850040440690b0030a01450a005d000603800c0080c41c12681c0820488020f60303252107040b01640038610005005c1604450140300591607032000d040c010f9040d500010300d19140d600010b0241801c44082c0100800015 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 394215998 1250 394214748 394214759
    0x620010c0c1403090121110c0a05101a0d17160b070f270e042312030c0c0c0a06030f0b0109080715051306080709051f0f0216080106 58
    0x1048040d00807a010040c50038200130f200081c200c280b15100c0c080307a485803c4a00b480c01c42d110f17030150881034030381c0785600c2d02d079085d40c2e01403035840d032030180255858456060aa40c406010b4010486d0f00c46007008a400740c40c42480a1005e0b203940c4560031581103580c0c100d0b80d03140d0303114100509800541c103104100d40039628102800c01d084040c1c4440100001c1e51481426590400f080c00d4241d03c0d90001003c24a05001c0040001c0c0c1b01600a000940366540c03d00041c808601c0000c0c1c10703072500c0c2900468410141c58000c2e594003a107007101d00c600070b0910014000840180151a0609461050780c0112007900002440320344030303070841c4022907620702600034801e00c1e070703c030707000c007281c030070b003051756040303040440b07003aa2086207102d030b0a08005410000d05c0e07428403031000d80b08244c80c8007a20000850302c864003c2c2140400f140c0180000d07449190000b01440c050307100781502400f02c03484040c4203040f6442100e0b00460f504000c425071007445c0d03981b07582491942030303880103041c20400000c0c101d0400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 394217248 1250 394215998 394216013
    0x109080304021503070806100c050a0623090a020904060603020315040302070807061d010e0a03050a020f100509090405030405030d170c04030203030a0302031e011d07020607090620010c0c 82
    0x3003c000400000e200700042950002c01031030b04980c0454220405114018049502a0b4040790090241c042e100c01d55041103515048100070110900303030881d54445a645040c400c0d40304880c03940140d80040d024070003501b841114250040d001d00d0010448070744a1b00800d10b015129080705504d00c2c00c080c04c0006241d4107011142c0a0314802024041861a2220003004141d40c800710380442142c0c814410b18030303030150390510400702001d4070b040445030b6a41030058072020005010780c0144d8501400020520381001c11540e00c0d0150703141c01c0d007020714160501400610040c0f04841500c020400441d0566040140000301c0d401503403090110b0180e10940100000c0161030302110a00501c0b0a0005035000b2066a4034880c903032500503101e5590714070080d0302502c03214a0036408400d920020803202c844000505c18112000d480800302d4640070402c036502c0400315100c40c009001072005000c864841c0000f81c80d001d8a40d01c2910702c0e640c8818409003114004890500070650a52203541048002c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 394218498 1250 394217248 394217269
    0xd0203190509061522050108161a0f0c101e061223071203030b01020d090308090d0807060f0504020909010c0801050f060c060c181e09090f010908030402 67
    0x318050039050a20140d246030800000c40b2280c49400c041780301005103a0b105586911542104c0c0050081f9603440c894103844a1071031401205507801d80501103540b00e08982d0024100600c00714042c58540b00c007600d42c21a40200d0b40b0021b443c003803040d2002d4105050b000302400c0199801c3c001c0014805011440102c40481e4440200c1c1c511100c23641c400320381245401c2c0042c2e03405150034004001e903401e08a0819038030f5004a0380210348013100e001450b07856404103010100a8003103d1020300c0d03201c0c0544842d110392000916030482002190039906014080124035403181e1155820030900759075400648e0382003005098000d07660801c01041d4500101081c0c3c00000e00c60081000102400700108511414014140504500740d41161070361201e00440b48400c003d2801d4072401e0400c0780503054107600c0f001d004801e03200341d5015112146010f01903000741080100000c1041468081130094000006104640b01c0c05072100c06c0404d20003c0c0a4070080920411200e507592520740304100c0d02c25038 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 394219748 1250 394218498 394218511
    0x10110d0c030e0a030c05120c0109031205040203070302150706090b060102010c08150d0c1e1403010605010804120c020a030c0504050a0c0c0b0402060d021614010c12020903030d02031905 81
    0xd08072418018600441c086100c0f541618141403401d4031414030a00e001490803410882c0d50002a507052891010b40c845020b192003550b46026030b070403503900c04007170b204140e078042e5058000d450100018609650300c4c0103020755803003101d400d00c030b4540c071290300b2140002c40c01d64202e01f0000c104030003580d081c45070403240c451a041c4000e450514a40030004008030308002070180d015039510405025450448000800aa40350007120f00d00c0c20702206041e80d87c610910b514060094030340c005501c1c060280509641069413018a44d40c0c1d15201d4114003c248d02400091100d50a030420142c0c40f1600380303001850240c100707800071500d451b05100860b0030040028003031618240b02c0854140c0d02400b101c42440d004041c903a01d44d01e0700d00005001d8415074161345a124400a00c140300c0ca880e5440341e20100740a1101c1c03000400b544188a4280e405858014000801800c03039000500c07541c0d8040d0418050203401c4034102a020007480c0c0499000399010000c940103405664141c040074003440d0b62000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 394220998 1250 394219748 394219751
    0x1080601030b01030f030504051c3003020d200408070902040b030114220902090916230603130219030305030604110c06010b040e010f080c01050c10110d0c03 69
    0x40c0745440d141404030043c00001d090440c100e4903101490310900964018080c01090f4a2240d9250750304074a4140b02c0b040102d5a8a002e003e481c96000035460300340e600c2c0c3c02c042d051108034800c4034004030001d60101d0326680d1425a5014144500b20007554540b0400b450300709201c0d81d45085c44c0a05240c0083c0380c0c010031015004020602c43d0b01250b00690341191200c15941c05409038100006159000010302d00085100c0841c0d0400008840e0708400c00843c0282c0d01b296040c0c59802c40b0b60f850780603078502000d069801820800103a40301c031000032002c800c2c0001d4409425009400200d041d0300c16501414500c0b0a0080e45095103400070140703032102c0541c0c0c280291980765a030007802c6404000e010902c50382e40c6003a11080d610060045030700002544095846a42c3c4403000c091aa400070300402003082c400c0400440c00f80c041c10700100070744660368000e119280c02107004548603441014265924080d0b00e49515009505010390146d400e1141c0110381c07a010002c4012007200c010441c04002c05 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 394222248 1250 394220998 394221001
    0xa090801020c0c040c031d01050a0e0a120804080c0109050303060406051e150903010f1b0f1d0d0506090c040e0304032015040e0406050709080c0108090f160806010806 73
    0x441c000f801c3c24040c42d0079a80402d5243c450b60080e001010703141101710b40440c601c6a04c41c41c0d48010340c0580d1003105e0b081020840b1441003000e246da20060a0b500800443c03501a86031480c078003a42e9513552062240f903034245050250310416094420055040705e0701c2d4404170902c000b074a0036000e110058231044d10380340b0342c1d01c4107400e41c200b01a002072030700b074080e60280e4031800e01900900116114118041e00034440d514445a150000780030989129850110044031845110311800e48415801d0301a90346940c151645000402c644c1c040c2d400d056403000b004aa1900050011b1010912851030400a0300010448038244025038100d11000e400d2900f04000900c00a910f54065803a050408113801107000450408551740c1f00700b24540c0c1008980214000a144420342a0b0b0303071090703204400505c00c80c0c41e28241529203124a005004140c3c11202085440d54401d4202d00d074030103c0201262072240f010001241002d0040c0d51001020990032014003040c80d040203010b00400310000240310a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 394223498 1250 394222248 394222267
    0x70e040b04060b030f07030c051e15180a271b080402030106050301090f11030601150c030e0a1503140610050c03091903020f0409110f04150b0a09080102 67
    0x36408010801020259a44003426241e2400c001211805d0000400c0f110815203d0400032603250051144a22540300000b0040380500318400c1000c91200252200040c803400c070546c0845d64000303845403040702040300d0f1302c0c080540c2c07400030810007401800d0b040c9900c80c6042c2c0e0703103081220907102104911410540108019041410648400b00182c904030129440c6c074400a40540711682c06558150b0030104000300348034440107000300045c1f081424424000e0210245031f03d42600344a6856486003609207020854050720f5503108140c882d141006d1a000310000158070440d56070004080c101c5c01e100320f1700706650944600690415201c41c041c6083c50b00c1ca0020b44c100c040b0130840030800c04003050500000404000307640c00c010303000300448108401000c01c2041142103202c264881c60341031000d840710741814401c1c001c005070400d800c0e11003903c1e280d0510144c40400500705c1e03001541c6090340b00890490080c1e400c0585205182c0e5550b440c070722440104032030446c0e0050040c03644100600d000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 394224748 1250 394223498 394223513
    0xf03091002070e0f070912030912110d03030f110301121e060204060807270605031509090303100519030f060605090a0903020106080d080a1a030d080405070e04 70
    0x1092001100ca660044994040c01c074100320302c0354007103411200e15030240032408054108280c4161702698410800c2c941c0c0d0749285001e407000c1308000c0c0108409101c1800300c0c27106440c0300000d280c011000100d84c03070901c802148840354100c1c4140d000960f145880b00d000d05080c090f40c0000d0030362540d114115410b1030108001d01200c44001040008841c111001d00c1481c8040108d180360003d00441d12260742d0072016002c044115030b20340010343d00b812132640a4981e2000e540c1c0380a42000d502c00c01c0360404100350b41651001d4114102c14160600c141c0c5199103410034a07125100000c05141c032270404d400700c203a10300c03101e4201134400c56008424403d0a03026600020440740c1101c0000701d440c0d49418807000402040d004160003d2002d02040008000382d0404400c80c1d00c47d030f008202c0349070b8400d40c0e40c0d00c03a2019407840c00010841c80c08521170510581200b00f0010031902c2e81003251081c100040e01d0583d0a54004020800013806c22050002c1842241e005052440d02c101c400d140c241d54622 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 394225998 1250 394224748 394224757
    0x405010504110d0903020109020a0e04033b190326030948190f090b061909090b040204030807060504050c1003020c010f02070807290c03010312020f03 66
    0x542481d40c13646007606140c0301f500b00107070164025181820700c2d5207074040401c80c0f81044406070042004800c02c0488181819034010640010801e00c503828849806600c00800c41040d981c0d5014203104083d08010101320020401540714400603542050a501c1d528225941d01e072501001180038400c03ca0b05d0031005c903c0a2513010400047c2c00f200e40176400c54900380000c006505060b060004a15480c081414403640403103c04a502e00802c2e01c1101000c8582c81450207100c499a0404404004129894002d0029500c0081806040801808803c0b880043c0e1105010004281000c200030303011880c81025001c0e84107075020342c40c190031a1640c03081449940b9005001c296a04006000d001c828040c684038a10000d200d84400d40d071021009001c0d41262403440455460301c0040c1603024850b20032030320115405190242011010345404106441005c0d2454103a2010040300d00024207103510740d4071036640000c0c19502c950442c1080940b1b03026540fa418113640c071030032000818000c00000d45 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 394227248 1250 394225998 394226017
    0x308031306060b070b07080a062301090b12040309090207030503070c0206280306050904050709152c1e01050f010306050405090703030f08010b0f1620040501050411 72
    0x4030300848203182a000030b0000354040350003000c1c04686401005403c81659000e06656034035030b6003c1d00d0704440101103804c244503241403e000b9000032590300182d0190b824130000f05040200e105542ca02a2a800b03610000b18080603c0d0350030200010550007082c90806080c2c00402117017401c003285c0d40039005200c00350280051049888060086542e40c000312061100891580f42c601801000833880d00c03407018220343e0100381841c0300401d090500746213407489660130070010060140340040b598000c10310101d4422030302c24803c0020642e200070701060304503c1a04684a40760300c840307221424190b500503103e03c07840020f20711104482007030f8040240c15a4422503198080d4014140142d004150320761000d60441c3c14402001210724001c41c80b081100c0c000d4880240100040000f00e481030f20900070104415800d0150010321026072000d440c480051680d014001000b0751100740c4041051140d43d8000d00446481c2c034800c1c1803034020140140f105a805100001e84140c990156014000e4003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 394228498 1250 394227248 394227271
    0x6181e070203030c1608091009050a0504020f0f0906070b09071d09061503010e01090f05011803080705180a09020a030c030506030d120902040e1005010506070b040204090f0b010b04080c030304030803 87
    0x100c40c06e01070401304440052200821a60410b800c1401c00fa200901394800d9511a010451001503141003030300843e800c480e01c03103107841d190007041001070070b040c0c10904200d50410010300c1040c0c00a405000141e004880b03403c020b1403030b50300d01460144100505505e41c089200c40300c3c144a00103070b00050440c1c000020358004600c01c155040800e00614178461101c43c19800c14102c00c00b480b43d2206c0c0215403c0c003a8009110540000030700733003d080300d25a4000c00050219000a409511070307405020702e00ca0b081c11b00941421142d00040581d6955000711440da907001504001c4940c061140001044441c00c00b40500c0c6840c0001a03107910a20441d80b06001154205200310302d13440d17000100d4194000d104000614030310b20040c2d6182940d100d10006103162000200301858000103507445070364071072a05c507600c1d0794030703030078071001e451151800c45003420300c0011b9000040000380b02502811022000d17944a620708642145407561901c03400740290020401032000c11250b80440740d000506104 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 394229748 1250 394228498 394228537
    0x1d180f040f08041202030705060304020105041206020c0303010611150105030c21010203250c021507080705060c0c071d0106180b0c010f0b04050f040b06181e070203030c 74
    0x1400864030a8070500141102400100801c1c14034004ca80e08001500030340444413010f40724801d110040c4402e0301c0107804658180000c00130010340050b14a4070603c905c00160078090100b02d0039246030820b0304000013041c4450178044890b5010400c111110100c0d20002030305524100c00b083d10b9030b1408031500d002e07280c104d80342440c20000380c0310204540c510800840d940d00d0201c601d100c8100b00c080444107a04541018920710920408003090582d400514504402c803840595088541c032840003112000b82c140400c070080350302031010a1082c83d0341031a6a94541e0691082e50a0142a0f0410500d19540045481041801c950404e040d18060304060b050f940b000031103c420041c00398068250b130040007808040e104419044070550108400090015101c04801c00c000c0c1d690850703610185a10340c0d40024003290000e072b5440e41094011304042000640c0c130041e4545004112080440c0f80c0456424108078205107085991140e01480071354158109103172104064810a51540410412441d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 394230998 1250 394229748 394229753
    0x3080c03180f090402130e0a1104060f06080a0c110327060c0618010b09190b010c0203030d090804052e1b0b041113050a05060a080c130204080604031d180f04 69
    0xb0f000d5041c03940c07c1c2044510381c81c054a000403c540c0c0350f241a0380100c0c1030500c00154418400100000e50f070094840a03002e42c0c51070140e00040c041c040c240c0c0c04120036a0a0381960100500c010000c50b21841d00c9a1000304420803015000c009030715400340220300c10454040280800f013644c40c2c100402910312038101044140f40340c090700d00c1080b919400703600c4100340a0341d0703005800c2c0090650f40090041c00745400346401550312804158010b90075400401001342540034030341c0440c0720310f03116a1800d8101138a40b0003060b64211032071000042e214520f188210b00741c08401c409000d81c5000d180003459485442d01d407104007001c0d80c50003051905040c0100d01007004114504828038800b9004140300d4460f592210090304050b01d0800c101483c01300401c1013402e0801d030010580341c0100081664018200038018482c943c0c458244d01203500744004035504000380041c0340100d00075600c404020144142c41d80902d041d145095101d00000440c0c03010b611250208198006c440c1c06440c0103a5844c1d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 394232248 1250 394230998 394231001
    0x190306050612011806050601080106210f020408160f0302010e22020a050a0e0a0f060e0d05151006030603020a180906240902030108190c03080c03180f09040213 70
    0x10b21555a5401c2004407040b02d2480c030b42540d110360150b40d080c0f002d501c0c0c180042d10105000e00641c00001c1c4581c60702214078200540d01030a9141c034070720000b40c0b0211014920b0481c0c02580000380260801804111410170614009002d0012240c5c840240c82c61079001818004070068041d018404035075190744100c8408140d05003440c0307a01c0d001d6558010944008026a0240701d1080214440540100450070310f42803920980302c020011101103803c00e00705079681403100422961004035907040c100051300034000303102034501011400440e410059400c0940c2e074907a402c42000c0501d0401300f00b0140c0e032010720080803524145c08014601c6148070782c2d0000390425031800341c061420420303280c000d000309580402003100f090742e9005115071100b0391502603200a01c2000141d43c000d01032681001812652549a2803080c401c0c2000103070782c1d03500e0060320f400c00680c080e6150000b00341040748400c0c00200f1510000c0407070b00d518541e1000b50005000e0030025101034040c20b110310080c020484030f03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 394233498 1250 394232248 394232269
    0x605041407060206271203040f020a060e01020a060e191a0108060709030204020d0209090f01060201180804150915110c1c0b07050906070606090e0604031b03120204060503040c051903060506 83
    0x4041c061f43e99141c07500b00180d01c0ca6a0980890141c85044c400040c054412150000e110310142d014010a012603111000500100c940080050003031030507089500c0d0b01100480403c91041042214000c00500c800c411250144c0c01468182c100b0000c1010182c0c1c8480a00c0c180d0707034121030060700c03030121000030780090080b002503a03042184e110600500d5080118120704aa10540c0240302820380d2604c3c410b0003111074180200001d001f88070034021000c10b01c92110a001c070903d0311142066690139132040c0048803040d0304010900012091705800421b11101226907402d03640078154034071480152480904180c40034059000c003a002c02c0742d01f40310f401141c42070303c0020301c1e540d1540c00c0d500b804e800400183c800c01640603d040380b000303581070780455520700c9030703416480d000030b503800d60182d0136078110406808070104942043d100d02c540c2c2d407a00c00384c4043d02c86640c42e1501c9103060718004a40062a40085102e0385440d0700340000d040001c07925000381c3ea03101c10007091a4850501082e801e600 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 394234748 1250 394233498 394233523
    0x50c12070818190504020717070803041110050a030c0c050304270b030606011d180106081b0a050a1e0201050f162a060504140706020627 60
    0x4002940000340041c00000e08100c0784046421480c5401ca841040340760301071407110742015a05403d0401807842c280d8068925240507142d203d2158040503224111603011070001c1710420008070500062007150042c2c0749083c10280c1340364650228000002e4032601600181104040c2c03603460f000c034254452031070f0b00010b684c0002100c2d2a551105104180700e2414403d020303080070034141405404405015000c0310050240142209480e88030046441940725a6815640140c01541c0001e984407602d4490414482091103491035040840003007941c003010346840091100031440480c503107000003c56009601a04042c2c0d42d4030360050040d2a0094040600001c0d0343e4142c954581d095010b40240d4407910003801960016a542c41007a04c403040070742420400501d40c1070b60300b9041500000800380c0501080f150721041c0105940300816036804a03802c460300840d45180e00303007103942003050302c3c040e1805d40043d083c94903000c0201d41010301900c035089040c1c521002c10b07542800003404414912207 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 394235998 1250 394234748 394234783
    0x80909060d14030406110a0c06050a090e01090b010e013f0905010e16060c110a2402060601020106061706010903151a0906030d080603071d0618010303050a050c 70
    0x42d0081000340d16604644070751004103071100e41e000801c2802060b1140241e40c4440c0e61400c190804030b04441036001502600280f112003017010070185050b00102e0700903c100440400c18a460b5000100703407442d03001c00d0506014038610350021a1001405441a44200b00c1c14420f800307050314640f400c0744059002c070940c140e01d8411514240301c019000102c1d00131134075003200c1d80541c41c1c0c4481d0301000503d208030b800042c914a0f2010010711134224001120740001c0141200c036490300c50042d08460b00e04003040140902e000302c94440381d0144002c0f98400d03404d0008000c15460860061318040d400703030152110741d0000c4005801603000d01d004c640610342107142c4030800304043d400600204030304100380d104e880b03c2821007156440c06141ea58030616014000e025428550310095070101d9010b0412980b50007520320220b40b0b4401c01e603030316a4020021006d44c0031070503d0014021500c120406002800350514014030100c1d0b08102211140300c86d07890460b603142c1160b0007140c201400300482740c0008 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 394237248 1250 394235998 394236023
    0x1206010e1815010503010b0403080f0405150901030f02160308130b090f1516050702010201091e030e04090f120201060503120403050d0e0a06050c012c0f030403080909060d 75
    0x650000907118480c00032403040c11165032082d001540d01d400244509248001e0420041c8005140c030f401410742542c1440319541400e8451000500344001c0031008003110300e02043c1890b41e5a81409a101c2074407410004514083d0440c2551298010481f005001d202c1c5050200c0e181240c032400048146400c00403520039400c00c0e520075500c9440c3e041140c1490f2040d0b0b44180c0c2e0008200341424047c2807514400d90800150040541e0b00344c01c0b03000d06034159580c441822001c00c5da0214405c040f0b540d00f04115131540001e160107031400c9070403030714140520b203422055000500c01000f0030f84013035007203410505035200400e8102d0242080d50442901030080940d015842c0004c00c001e4801e591080b03058998001e11848101c8583d0b01e881d02d1294880242c08042104a019000401e05500d0650020800040340c4480855151200b91280c0901040724061310030401c0a214000090380c4d10350107940381c9807a580712080e050043c1d14000c5d118085100110380da954540ca03014059503400303401c10414 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 394238498 1250 394237248 394237279
    0x504120c2a0f060806010504030221010f0b03010c03110409050402060705012a0203070c060809011418070605030403120218180f0105010903030203040b1e031008010b0603010b1206010e 81
    0x41c2680d11038803084200d40720b40841c905015032401486443d0603510746041600d15020000c0c1000e10309241c04e00c281000d0580720b03180400380900d65808050500c0401c2d464641c50505084804000520b82094500000006845508004c64007110510003020845071214000207002e41300d1007000401540ca0300d16659404648a0840303c0307804c0405200d40313401244200305a03103038441c0d200020047d44402105105283c01540c0d0103400060b004000075600e1624800c0000c03000c1e00f86c6810415003d40d8104215807402004208064a010b2901500310f00742543c01500403051a03140c9000c054011400314104001d030f00c850f80c20080700401c44405490307542d540c00c20341e51050324170445080300d20001140035406030510404496040c0d000f18581841c00515000307540140410030781100c480c0c5101310781c10012002550203014001d841602461400d40c4150842d50742014180c0034820a00040104007a4942900c0d6030404500041c0388550382c3d10012038402000c0d42009030301030031714106c15a1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 394239748 1250 394238498 394238573
    0x312050c1009060f02030c0307080a0e03070f02190e0f0402060d4508070f02040e0f06071b02040c1e0509030c0a08030708131206090b06040504120c 65
    0x4070180105000c21007401507420004c281d101c11601c003010610100040340295216589145d4002c07401031002030b81100c4c4039030310303400d5600a28058801c42c688040c0101036107491500b40314003d0b030a44603d040300749411032544412800910703c0702542d9003d0009000c1d511a80129109410b094204005680358070142d4940901c00c90b441d681d0002c0b61074110407851440d4540c21310003c0350203c0191814149a4031102d10760b00000d0206c0349288c10921250060321a80074030a800000c00c0041c0070900740e150ba1061500038024040c0c01002807a2181f820364002101d03400c4000ca4040d5400300303602104400c1500d4454101c00103260245c9070130914040e80c0d40c0800604680c00b030841c00c1c1e0b4940c03040c000401c01079800740d0240f0500b68004021030000580404001c01c13661824071880200144d85a01c5900c42011928050300c1c1c0c1c80c1c851250004000c0c42508095000104480800060a207500c9003803a00100031688024003519031904401d00c11588000c0f0001140c1001c0c0349a01ca00d40c0401e0321 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 394240998 1250 394239748 394239761
    0x1303090302180a150e220b10080d02150705030c13090b0f1503150d0f0605041101030507120e070f030c1a031b07030509090a06080c06130312050c10 65
    0x440c1e4a499840121310304042202000c80308001000050340c3c540c0b00308281700080c1096400303050100302d101c550009841d414124400d15550b900d582082d40350415080c201a9105407003003c640201014510618541800a412110710300d0b0840d10703540c1d02c01c0603e20038404c600199400d1030520800041c0300d2519048140c0141042e0365100d140600d142c01d000100c00046d06d1003403010828000520751400244015203000c10084c40d24080b0811620382403102c0322100c006684442c0c0b104100424006c0701d005028003898203190410482c9040308001f8000d00d610a921060a43c4803009200c03100010802403005e000417840c80c04100303550b4038040303886a00b0352017400e001075100024074400c40000d03401d070f922800020140d00581c82c102c0c00c0c0c020080d031003018100e0500c2000e20114000d40c40301d103a810711a04c050907000544a042905a5203030488082402d44568000c0040b13552380d41c45020102c04032580410007600c1c00700e4032042a01c2e18010442007001c0d80c0300d044008003101c88582c0008 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 394242248 1250 394240998 394241011
    0x207020d0f110a0b0c030301090b040204050d0b010e15030d080711011a0a0801050601052b020a05031e010803160c031e06140c190c02040203010803091206040506130309030218 77
    0x161420395a21350010080c000c0e4a41c440d125001440104206074981d0032000c0b07020780040006103003540b16000610b216012140940d281c0104030018803035000300c00d81c510b07041010014103400c90300d0307c040002c1c0d0f540d6584114004010101011501140c05501d10101d8000040001e10403e01821740720381d1a5000b00031034911940c03825100181c40344061042c41c0c003615040c2d4502707103414142c17090025154640300700c40348500460312640c01c0c18003246c0701502c541c0109544081e070301e040c1030001003242c1d03614003a0440300c00c0c0f04074010465000000200c518801d05d201d84c4102c200d02506080c0c0103241c0c246c2c40075006a00000e43c00ba4841a0b000084011034490380b0100002a1480802c402040040300e2941a0003400c0017041130f03030344ac120101f161000c0f440c941240d00b0082c903404a000c0e6003007a4000d07082544045000c5459141c0001008010402c00d4000c0000385003685600780d9030350b805017980800002d04803000041c140700b0320b10714029540203170000c03400e070050603103121a44904561702c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 394243498 1250 394242248 394242259
    0x90a02090f0f1804080d02030117010b030d05041809080a0519020a0b010303110c0d030e15091c02032404021203130603020a032406200a060207020d0f11 67
    0x40c600e20700c0c1001d80c038400624050f02c40c0c41c400d03140c040090000c40d0007a00030340d4100828800203810201e64001140a0403549041c03a401004a0b2880c034291900d40a18038820303003107120074026069100041d039013101d480d4a00c03441401d42c220305441c0181039000000c3d001c2c03c0006030480b08183c0180081c100c080c40d08102068104540300c0803602c4418400c0001d0901098000410100b8803030350081b06070105200c00c0d00c00c4072241d6000074000f10501c03441240030510414540d4000e15201d4500c0100800e1504154a4804080000b442c0200d50801d40b6140c3d031443c01c2520190348003000014031505200c003e000d24540207040300070303039202c00301e03400c900ca01c0b40300315015241c96000c001d650424203984c003081855400d010050780603410010001c4100341d036501c00300400034441600001d07150208802d00020300c2c00d2500003018000090403003441c00e4480c0203140e485190000d140e4100030380040006849980c00e1000030300c00400303c240603201030448104032003484070b4405202588001140c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 394244604 1106 394243498 394243519
    0x20d02040b19080d0512181504030e13231b0406120b0103230618091006080d0903031409030d09090c02010605060702010f0905090a0209 60
    0x103900c94030003400c040c03c1084020a200e070500e64000b501d0030b5464011000c1c1c1d0340201a01c003515005c281041c070b008160030ba4034180314007900010502c55450450800b030800a100f894418049841100704000c0c2c082035042c0c52159018450703000f1500304044000704451a0a10001040b2681d02450142c8018100001200610280409841d8120b142090348841e00c00c807807824580038107262510500640a00019817100760150769601c81d0010b5a8602020500e1000903c1041782c5c6085210140041004003045108420074403c03000c00100d680c03540c440d59244c000414400c04510410000d1021074402c2c1000804407840360011403500c4203540200b45016818429580054281001407155000c3c0340521032010034207100900c512400d00001408911038218001e051000c0042105042170013500d2090040500400589043ca060004500650300c03440207203204280448 = true := by decide +kernel

theorem cover : BRFrame.Cov 394064748 394244604 := by
  have h0 := BRFrame.cov_init 394064748
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 394064748 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 394064748 ≤ n) (h2 : n < 394244604) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
