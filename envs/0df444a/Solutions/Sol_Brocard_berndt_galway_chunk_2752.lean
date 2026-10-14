-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2752
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:38:19.155038+00:00
-- url     : https://prove2.me/submissions/bd93eb9e-75bd-4cc6-b145-8f6296a1895b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 494784172 ≤ n < 494964028 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 494785422 1250 494784172 494784179
    0xc04021b010912110d0807030515030f01020417070b1911160e0c0c0a02060f040815160804020d02040510050607050604060b04020c0715120501030b040209160905011d0301020c07 78
    0x8280e4221001c690b0380f00e03481707051490405a0407024881d0300070007030303d0041042d0740c4480300d65006008940145402d0f10404054486000f41174007e003041e148000103641002d4000488150f40e80720b1032080c2016034070100083d55001e80150f0f12980004041e08190890483d101d00c000c2c9410720480704d03041c00f00d007079104c184054810014510340145410344a6818141d07881a525150954810001e10a09001030ba5440b807040e803400390b50003090080103540100e01c41240101c99109c0c00c65541c4d0a039050808441080f0b8000c9142c0e078011a00070b41400d40e9100c2942c00d00004040140c034010f100309169400150581c1c8050080001c58428400303410305007070500e0b0400c00d4039200442c00f88900d0040c05441e02c11800001e080c01200d400801c0c280302007264050940386d4170040b04580c0e8110341400e0022080c000200132117801980b003540e501407155100c021034004203e101000100240080f4002c0201750320400c1e0030f00586085103031b49141c140000c1e0000c0e003242e209521003000c6402014080 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 494786672 1250 494785422 494785427
    0x181e0901090308092a0a0b030106050a02010c030c0504120204110f071505061804110604030809010806010f0909090c0806040b0f0106021c050a030207050d0e030d110c04021b010912 79
    0x68000c0c8040e07000700441d100400c1c0c00281c10300c0c101501c0005c4078050035103941c00c1c2d0f40c0304d420b2001010542d0240d07542e0b5131907140050940e4490301e0140c0c0950308000c003400940744640f24048002c100b66860030f00f000d04156009188000000003031781d2090700c0300c0010400002c4a03009000c80303a151041140c4c1d450341440e0040103000c0c410796001015150908018181d1100e0628044000d0300b040409115502c03440d119074400e8009188580084c2c0106000c4100030355100140100c0d00d003600c074584241c1e00d04e00111004114010a8000a805940100409a515008588046e100300d170510a00b40d2141360303491811070700311029600c41c0001c00c14401c50043c3c00d460079002d8401c07803018280d00801c00c2c00130400b50565400c41340c1000000507284032603511943c103031745070143c0c020183c1f030b0f4451200c980281000d540e491014405d008682454280b103000d1202d4142640000c4040e00703400a210007040001d41000017040c51803003500e802c00581400030302c100e12200d0b120b013021401d540c00340c0701c00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 494787922 1250 494786672 494786687
    0x140c071509050f09040b070c0507030b011d24041e150b040b070f230a05100603051213030c1707060c1104090512070b0609090309181e09010903 63
    0x169000300c40070f040d24612616901d41103580a0f404c03001c04001521800740c01c8424100c0104040c011303001d982d0010007002039540d213290488030309201452002d400b00b8581c003c006030503201420051084000d90b1400c00c0f00d807851034401c100060002614284580703900c4004500d0320705885000d81e98140c03030324400d0080e02c082000707004013096642c20300c0c1c00e05d02c04000500c5559030251145d500509040e0801030060b030074200c0314902c41050480381a041c000359548040542c001c640c140200c51b0070b002a06014803401d01229000b2b0b0052140b200f075207841e4a001e0740103520002c0301240e540c40102c0890002103117040200194014044001030303808490b8107090040e0442001c000088440740e02060702080d104804010031600058080380324501036240c221904003551300f000700428410309211981108900c1910251400380807a60340e00034894407032285440440c4c1c0454681c01c02241c8600040d02c15034030034103100310303110512016604a00040404c5034109a2691188400340030164070011 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 494789172 1250 494787922 494787929
    0x141309061a0301031a0405010b100509040b091506071103030412051603030509120106090f0902011107080a170403021c062d020c0312250c03080106140c071509 70
    0x101282154116078551080c1e1164180303213401c5c3c40300000421300780f020030360203c000c0550080a440580f142040b0207441d0f6048440050310540c98103805000c0741c14000102481410b01029058260000808010850308908410354040500150b0b078411a2001c000a00107030240300706484200302c4070b18260b864a001541044800034040f00c0400010b504001507640c441021500d000b8511101c015981c010700341070b0702415046092a50300c0507000c03c170398000c94009001380c0c1d500068442400025a640b8002c1c41418001e41c0242d008502060b69007091f00000c00070103074010f180544da5000140080c0b250040105114103440e804810400b1307510600c20701503199a0790010705440c005866031140541c0c0c10703c0031016000200c2108194041c42103401400007013000c1c01160802c041d80e51040d031208003d10800c80000f496000c180303030003902d038041c0c05036040c2e03140b0071560b08107541115410713107884140c24180014020442031180920018000d014150004100a900b0002c01091100c0c2a030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 494790422 1250 494789172 494789219
    0xe030c0d110307060c0e0306010906050a060815010c0302070f08030d0506010c0c05090613051303022a0427121d0306130813060c03020c06120714130906 67
    0x8282007450300080191104181c00000000b080f2540f40c10031340300c00710203031030342c03581402518004950142940c0c08001518415140010700940b04c0d0742c155a600019292000340003403001400c2e0300396208103180c1034005c0c0305e8415205100c0e910803480e203041d00c042d00400381036040491710000d1000d1500c0b0385039200e4401d19080c0f0b44076040340c079a450480100e0056030f0145c400034001030001e440d28000421107240250b0108807900e081094500c3c1c0000c1e00508a005010701f0f80b03148000040d1f0003030007030007046040180503144040c0e004c0000800b07610081c001c5c095566140c006030303c182c01030220942030040d000140e40354142480200003402d007104140c2d514040c5040c4607160340340094650360080d036444400d0302c51138440c18140e4035801000300c940a08103804202160341a445410a00d605119400704c40b010107a400403c0418001c04215480d040304000019060511034007518090712050f128051600b040d0200780c58110303c654200001807038541c40c042006610400441e4617100841 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 494791672 1250 494790422 494790437
    0x705030c010f18141c0512070c021e01020703061112010b0a05040e0c1b070e0c182202031305060604020705030f0315041503060b03010501050603010521010e030c0d 72
    0x1514150304984400f074082d1241002c1c0e0302112012030b041102c11610112203860541c103000c0a1780040007580054418480344500c0008564010300070200c1c3c20805a00030403026647d10544c841c1500c02041c11030703550440c0f00b041d00000220b510752203121a42c4509102c26075440000c68000c0002207010380c007503000810100804860164058103680c16100d903544808440c3c0c40c0c65200e0301441c094250400d50403011140c60210360880090010212922a08500003d0383c820140400c140242c00c0c0e0400994204030548009181c58050341e403048911401c5980d440c0b203a0b02031001260000c44005d041c81b0136914070041403140821100b0350020040320700b5450042c070340e65625228010072202c140058400f0000c01c1c441c5c85040403e8080140240040054541d4041140c1e0010001e12082c2d51091030a203078060141410b001e200d042e00c9015117151300e103920b4642846018a0034481d804000c5040340c12000030400207000d0980040c104030001c41d11000b003082d00d28180400b01012509020f0307413 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 494792922 1250 494791672 494791691
    0x60320060f0c0a05070603051e06031c03020d060f092702010e0612040516050616021005040f030b061005031003030f12141b0f1e07080705030c010f 65
    0x4110403100c07540342034403074251158a040c00d141e00c1c00c180f503180100940a1000d0100348103a1651101e4859128101c030a046000304151074848400e0594a1540640000b814032082d4002c9a50705040c240b004c0c03074014501515001414100d49541e000780c500800011420044000c10340500c1501c070501c800380c0d10046448102003455030040c40c10017414410600056901c60351082c0c2900e04d10803008010100354506843c0854940b214100f01c1c80c0010086200464141812070030384031203000440d200e45d00890320b5020880701580c0740443c1c00821a08007c0490303426000300103e4003d5102f202440554200902001944c11103103503050b0806c031040c0100310310402242080c00449805081c4483c4a40b42070104036440d0200a82e440e034424108010955128904640035220380810b08468030b40300c4503c003450b0414420b00c125542036071002d001080c4954100d00000545410207200a4541102990382c1e46250b0806c1000391040e42001c11008400351080c09541e443c000165810802c4609 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 494794172 1250 494792922 494792929
    0xc0f0201060f0e0a1d030702040515030d0e030c130915110301140117090a0b010501020706020d110703020909030711030309060712030b03010501081e010608061801060f09060320 78
    0xc55200f000340b0040c41c1004035030390340010380c03150301410728503580012008000c0383ea00d903803a404a0422400350f85040c000462800d00e20b0912401460010050301c00285a0182102d02c2444170034017641c540a40b040110707840e590100c00140c0c080010340080344c0101c083c08e10005081c1800c1c584d030406401c09445d68007620124003142e05403411203461000190301c07540101d40040e22544007882c08050f0301c0c1403000c00c2e0400101580e241c5e01c558a22591607803620012616a0f45078440c1078050fa02401800c485c0f03c2c040c09854846d01c0a1104030740455a603a00000d10381d1710b045c0e401c070140e41c100090000034498154008800f510054004600d00f41c046008120248542500035245407501c020340251280b0a4225540c10000140248400d584509240341c8030104400b4a0744002c1613505400502007060050200301c48011025204642d00c0c0181000000384010199041d95604c14000c581d50401d401450301800343d0940010300c003030070344c644a180e4800c52002e494000800000a40403030b076 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 494795422 1250 494794172 494794199
    0x150c05070f1703180c01030911120a06020d020306010207060905011e18090e0c09010e0c0a020709050f10080105090703081308070305010504230c04050c09130c0f020106 74
    0x398000c00000a8200c541005018120303805610b008190780002407003280b1080701690061441c5103c20b0740c003010380d0480103400315941400010700c07240c10348440100502d40180c55a0000c2c01d582c0c25114816500c0c5d40d140200e0384101d5280282a42c04000d025107540e0400142000d8442400c0038043d203800c0400290988610a032095845002030301c2c0c088280388540110038241075540c4600c0c000f1519401d5440240030440910f07121481441040896844c0000e0028101c5030582c8080c04641c07100005010a9800040040190304c9140c0001400003414490517108896218180c003603030620f0f1040c10340d01c0110783e0000030140c2c104014400d81803c080b600b641101e034000e450b07594034080c1e021004d8070882c980c1c3c04080d55000b030b20300004c02c0c098190082c92003180704440d41e05c1002d4800010b83c0301104511403046540c1c1c09520034035201d04080d4002c640240c084942d142c00c0582e100001001e0060321295402065260380320b190541d81c00002d00090b0a0300c42c002401294141900c46001d03a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 494796672 1250 494795422 494795437
    0x105090f0f0a11190e06070f020f03010207050303100509070c1515051003090b09060405060106050304150903020f0f0304320d200105040b090603070905090a0603150c05 74
    0x1c82140071075070b84446a030014040d03c0102c00d115484042c4820808048241200c10801141912521761180d00d0100121051280e209560040c03110490b000c1c0031000388000212901590f00304104008101e0800c003440c8102ca0092076900d005051506211380000007034000d00c148403808840c0b100042c0e40c003030b1400d8658540c03600003d143e0505100940400760941c81103030020160008658000c1c2d260300a08107032401510b923048641c039000c11b031036660001144e010b82a0307000140140400c600c80c00c01590040c0c0100d51000308000f0301080e203c1202c81c1010100e0250348042ca0b03001c5503c0043c050400211030b9440038608040c6001d074400c0c0b210550280e2141c0a44091200b0540d0030140202e882c2c000c840a0024007100a092074480300c000282848078020321080030840341e080d88100100c4090f526900c040504105904080c040a43c0000e001c910a0006184010406455081841d44612000380703001c508c0b2803540c00c0c50009003e00040d21085036003000c6100c208190807408454a8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 494797922 1250 494796672 494796691
    0x20307030923150c1b01080f13020a14010809010b1c0204090b10030317100320031f1404020303031305030f031911091f0306090f0903080105090f 64
    0x4180d454200c07880d422100ca01c59003c1010350381e8000304070080d00500344d1a00355108540700390280e80e0101e8441626058001e00064503c00018010708030900f0045c0c0000c601001e400e40041300b40d00064500040703408c0031141c41452407800070150b911039120364125011000800a848018012a01c1d24081c50207075088800e00071801401c648851744160302480e00201403075903031b0800c0c20103103000c1001880150000b6010300d0b1542e0030840c40c41101070080486640300d02c00245036654045078030010010351921440c0d00020b50b10702d91001d00c5125550007802403000f9041c012400b1a1045488443d034480030480c1c04810440140c8000007165001580e01c00709005561951400328507501c500400107168081c04802e2110100451409030060411044103100580d54121240342a02078014030692240308050500500310171000b6008040b1003500e4081203070341e00c40454030240e0701c10107a0424401d6a0310220424550700030000360151108a50f107081034140340544119a800140c0020710 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 494799172 1250 494797922 494797949
    0x5060114030f0f1b0907020607030b040908030708011703070203060a02090d0c03050a1a070c0f0c0506040f0f050d030c0b070306030c08030a0201140603030a0c061805030d0c0203070309 81
    0x500d99401c0001c419601c85490458041084684900740c80300303150400d100000c45002c0c4584024508a11818462030069009111580e590441203000d4000054050b402948e514a21804154600011841410540c95848041d450302c4036105200c2890454030320280c0080c8680c00044c3c0d00803401e01d400c1510500056116101800000c0549260700340003002c181520000008000d80418000c003c54010300c3c25451801380c0d0700c1300c000144021030301c8000240c0d03004c001000058000c502003c05600030b489800b40f40c4d0b00c1e82d010401c181d015400c044c2c418504040300300600d40c0d070140b0079005403809550b208425400d903079000d8440f001c40d0740000c068040881c00103400074401c1c0d101c40000c2d50013502c0c055180b941c4002007922a800020700314015404c040d0084d164032246003c007030081c50003800840ca046d0714040308480e440c04100c0220394a40e103034416104843d01a641c1c40a01074001c501642e030b0350b4024480d130000c90701c040131080e0035900180304241c0400d40003482e41c8100e800c0002104c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 494800422 1250 494799172 494799209
    0x41a0a020f0a050f360307060c080d06030c0602010b0f0d02030303012102060721020c060d0903120e033c030402031e030301090b0a0f0b09030703170711040504050601 73
    0x1001e600804000020101640c810415419203540150a11002540c05d900340e2130140300505480e15854002c89020a0107a4111000505003000a10959408600c000750711901c0b941c80410711542503100c500141c1d12800c41d110540b500310b0214091880840b5191107281240d03001c66140c0c00148210300c2401b9244195110f488480403050306110390042c192513072403540e40340c080c00d084640d490000b82c00302011a509110f0f40000340c0050407a5004155904201818848030041c3c800f07124118204126804c0301c105224803405025005211000603540741d00b1150510001013041a031001c0c1200000e500700e0030340d8190f004043c2c2c00401482603982e0303241e82d640040303840d0241c100c00440e906228401400c0040c9000310166050f1040075034244849100d140400c20081e8850190f030420520001c005c0103460295002444000c4014055501175070f926110810751001308003581e810f4140001b05042000b010060081210100701e5041006003801c1d250aa600d202c14020608101358540c0c02d00d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 494801672 1250 494800422 494800447
    0x20606011101200a0c06020c0105100803090102060a0f09021225060f0c030e0306040c14040c170907050d05011a2e021006091d010525050d05041a0a020f0a05 69
    0x240c5d903410003401d41d0340e43e1942805a0080000721941d50b00c0b04e03c241030120302e155001c011256113070310507801001daa031100d07916000240743d03410240350b82d03680c0e5810920044c2c82d0b110000d00314000c2c00e80035102401c01002100380c2543d4800c425580040d00a1052007465000400808404524504641400d803240360907980000001000d40e40340c4034280800c030401411092200566007050f0500c14070903070101c103100075200d901100320003040c41800710841184254001c150b01098603011515078680d00c00c0411000360071017100303594994440c4424010901404e180c04440082592002d8154000c4680c80d001211b1406228142800c01c2c1589100340703100300001c050162078840104502036841d13410400500c0005040707101c00d10007405ca204d004c507040c46520720851440c0502282d02c68080c2440440c209484071010900c04280401d080400a81c030078284218030807200c41040b000c1080310081c040c0c0d4010840440180104481501c90114506507030142203130381400d07038681c000204030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 494802922 1250 494801672 494801687
    0x21603050904022503020c010201181e06050408030a1415190b0a030608010b0301090809210102030703050f0f010303021b01121104030b0705041a0c0102070210020606011101200a 78
    0x1d4064003544503245100004654034400704e0744070703400b2a07071880d441c00016402d0724451a118003542c8040350462000c04e00c002640204460b140d140044644007a80d1f034402262010b03a4251400003010007084548643c504c151196600003a84004003480c00c072501072008045280924019107420240d0050306280d4084d000140c0351585829881e0160f04800030002c100e140729085031503003880c00640042c217045c41948110f0360401c141c2c0f4034200e001d105101c011507009100c1c01d41000c3c10a0654140702081c03001d5806651241d801003000d0410f460a0903002401804d0b400c10b8421807001000003940000e00825601c0186041001d51000040161031111030f01403d60740705820211850140c400c050700400c1503034030a010018058035a4407003282c1d24050f5000c0c20800d01101958072000f0b04082c4003500601da440c400145c41c100c040d5020413061141020340c0f0016900036024405513680121080c80c400c542813000b009682084400702802020100c03403441d503218002a4100c10780d00c00c044 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 494804172 1250 494802922 494802937
    0x1080a02040f0f2f1606020f121f06080906070e030a0c15030e0f0a150b130b031216020910080a2f01122711040f02160305090402 57
    0x4013085802403000c01c40b0b180ba149014400d4500114500c0d00e2198020301c0b090720f0110a0828448460070360035a980c2d80294401003490780b44540900140045010300b4101d2403049414043c40184c0c80c0c498100d8071440c0174a03803c60001d000b030000c100410301070002481980300c1100d181100c5460f00e0f81010a041c801598000380c10300512501c00306080304010b072041180340b1250740410294540c43c4242d074840c210020880b500da004038a0440c0401d030b03100e030581b0b1079200710f110020703d4000c0340d80002c0b00410b20098800c4030688400720804c240c80d0511481c12a68500310510345010040d0b17209400e42002400007d205588e1440400d061607d03011182020703000070412501503042034100b0f001c407100b80040312100c40d1140060054003140780241c0758410501a142c26064a461a007404060f00c441201d02d04007084c0c2c4010842a00011542841c18502806169554442c2c6109100a40e401d41d600901c134036004210700311800a8149604801035051702e2308a840300340c07101c00030b0068460701300e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 494805422 1250 494804172 494804201
    0x15040804180e07120b0f04053a030204180213050303070c08010b030a0b2e1203120912050a02030702271602060c090a0902030705030103150501080a02040f 68
    0x16801e95224669601070524009900100c0d20525035958801418144201d030040500750f902000c01c0b500000c1001c0142c002d849207003542c1c000c124402a01040303150140b40008061040340c2c5088480d5000d40000e8910040e42c501545440d0804840704d061142d00520402400d50010f68010083e4800388040c9c00307840001c003583e03514040c07400c01e000181114040d00311254a80401d0840c00c0c0750000c1d001c030420b6405032403241240c1d90034200080c8c400303601c1b0551700d40c1c2080030150300308070f801d82198030040c02040c00031030950038490030010b118820b400b01003480545080020310105121062400c020040b038030301940c1d1381604c0f610481c118000d40d44003d412401014007a02c8030f0500e200c00360314032150307c14020f40300c0c0da0704000d0400d60041d0600c0000540c0084010540310046a4024102c181c0702501c02c501540e034802486080368003c4030803000043d40800184100202120714132014130501400703210f00d50400c5400d41e107402841000a106941d62801144582d04a41280214a000d039 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 494806672 1250 494805422 494805449
    0x901121401050106170a0b010813061e0f0b191505120411040c030c0906030b0a0b041401030c090f0b09040e01050a05060108064213140603070215040804 67
    0x4c4001510216403880540324190410b0009107050600c0d114a1624010503515140300391030700c0d00040940100780b10142d40207500c4000d41014a80c0003a0402000c042d69000091441450349207a81202e0040c090b0b60302c64000c0303500c00581c0446800003101502c9030140c00203c16100f05800780d5082c403404a00110041c9044200020310050402902040d07000b43d1b400d1100000c1036004034115000605c090300031170816402030007601d102b07601042c103c03e409800c2095080d2540e0350316100e078016034400545584000d600190559140c000c0c0340d0b001c602070420360a01400c001e20b800801d101c50103030000c0d9000105405401359510782080d8204200403008012701e040c454482d1015003011509180401c0e141320100b0201c0c10b1079a4045034002d1044251890356900318100c01660000014145810114051078820703a0042001000c404215911484c1d8461074818035400f11210465494450102402041081900400c0c1e1915804003148566200d41d00d07868800510302032034210810151b000e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 494807922 1250 494806672 494806679
    0x7122306010603061508040b041b050d05031b12070b06211c0806031009060219020703120201020a12020c0a12091409041208070306150f0f020c09011214010501 70
    0x2d50b01c910203035a50109000c0c25050345c07480944450b40240d60080200c0420000140880e100b9040d010300038141281c0f409006507220f001030b000c00c4862809841c260000502c5002d400e0403004410040484072000c2c21400818404400c454060110060003044866000903c9640d404040c00c8041d5040b41011004803100e044480c0d90b254a641c201e0b280d14146040c009410f8002c216451049900600030600703450b11b215054003034801410129201502807065400041c812721110301514083e6004061661031814400030000040c410a019644100050510541d01c6080311900942c075040140c1c0e110001c50507140380020803200509400321103051a90a0b603880154081210241500600c00c01140800c02c019010240c45c020070084904401442080c00b8130400b5034003500302c3c01c0014983d40e030380280070580c03907254600e0030000c2d40b10643c0b003c005801458081140076144010100030f0415000724260640600070802c0b604480c0b1051700400000790525200d008200f8024070640d40d4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 494809172 1250 494807922 494807927
    0x406180303050109050a1a04020f041226120402010c0201020c49060b06071205071203050f2a0412050d11030d02030c1b0d0e0102071223060106 63
    0x800f80211500241040085006c081041c002c00c4030300c0c0b841c110070b00580c0f10344404010081d03001c4450408040d4050000160030000340f100006198050050f03128006201c1c0c2c060140e00340705001c01c200c0714006010206189400400c610b42c002d82c2820700f103054003010300050303240620400e031445d8000384030f07800c804601007c030031489280c40c1e10407080c00340f8a8000c5c070281c80c07070301048000514500c1000c0c0400b000c41d0060704031041d0840040c1150346081c8054490740c0201000d41c02c140c01080d8002066810011f80f026003410100325861304007c0343c28028541c4805080c060000f01c0d10103440090555124111406200c0b9240751900280d80c4543e10020306503803c0b50300783c01341d0b4035000f035200003001e42e030061380c900c1000349095024518045040c4c042e02d000f500090100c59403400c00f84258006070031455088184036441d80010100c0a920f6200180420b802c640c2640c11500410810012030400d9000464159800540102c5107a040100032540520040001c003851082c10f0000170120b8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 494810422 1250 494809172 494809181
    0x1e3008071403041a1b0d0c0606060e01170601030b061902061b0316020f0703060b030d11060f0403050405090f040215040605040302040f0b300d0f1808120c0613030203030403080406180303 82
    0x40c448c1c88240801c030380d01d040940c0c40c0e12000741c411307010481c08040541c84256042c200713640040141000182c1190381c102040b01600944102c00c40e614207072183d11400c41e0108052a44022000105d00c100c40304511420300740c0c04007070000d90b8480c608007500300b0001d0085c400d50030401c9165007211038156507418040e01408a048105000e80203601450f0011403043d00229039024013640106841d450f4402d000343e892200030000e03410041d044c000451180d9501b10a2030284200703960804440c14203004000709010400300e0b40429080400c07041104640042c01c1c1d4040700c0c0c048600007941340c0b030f07000444094000d0390041765008400030803140d14142e80721b06180d6103903100c040e00003010380103842c485d9580c8003907103400004c90926280117824610075007503404800b0070003252450039640d43e0f000303d1401c0d4101d0288060f003039000c0341084101404010b1b880c4c0c88400852001103070415900e000c0e4492102400c0a820400180d002405000c01a00311054880898005000840740fa080003801013 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 494811672 1250 494810422 494810447
    0x1b061109130203090c0d03090b0f040905130308060d170a23040305070302091f090c1d1302091503041505011e3008071403041a1b0d 58
    0x612510699102207011031098a20074903003c0000e0175034813215020460000c540b100210204500b0700c0b404a10359040d0406000c11a02d4a6522610f0b141840101025203000510303000020419100c41b5010941c07014085800131010356884054440341d0406100b402000604100d0b00c4800103025003c0d1584440b8610004060002040000e2040711002015100701c1c40050a95031000005001501d05100400e80003407613007803e05144003900b461002070351000d0303003c080c0b01b95039007280344607850f081620b20058034003500440c181c0861844c00556941011302c2e0102d0805da01140c0300c2100d4588059422502c0f500d000c04646a1030070f40392080034074152804c0b0310640d500300400003c604460350240540d20121f5118110000d05101661501c1c8043c43e4a103a5100520700450075000400c403e0406002d0090412036502c0460f403c08200c80038a1610701c40083d803040104014518424030542c107003c0010b915181e40300350700d00f90600c1c5207401040b0f81c80c040c003030071205160b22a005000d01000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 494812922 1250 494811672 494811679
    0x30f050705010905120703030305150301050901090b10030818040612050303270c090405010605040603030216080606031213090203014104090c080703080c12090f011b061109 76
    0xf030360319034040c08410758035514144c1d1643d010501c1880003e020b40c0202e944203651130300c000f1030300e50075200007420741e00d0a46640314580d54070100c7c1014415400010359001d0031554600c41035070b256640f98429071040e00c492000c03140004898410f196101d07000800280309014007000d41c000700741082c0782c03a40d005842c023400880d003490340c80a0442d0408228440d22107100c0240060781845000e114400e0001003044499542e2100301080e81d603242e2142d40d01660082d40108601d0301e080c2c0102044000399040048170b0f51002d4100b0080d135400040050721143e202c561140c5540004150b040045820b8003c0100d0a0020001043d01c522034410a141c400d511241291003112070b180354014040124888044c0700307004030255000341055040801e100d481a0801125075944640d07103810301c03d0f00d800c1142d6081c40002c003034054180821940c00c2c2100d8141c1c503940707440104400504e070303210301c425080d060045640c280d6100c426648084940c2136003290f404c2c0419074410f149117585a006075481440b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 494814172 1250 494812922 494812937
    0x70c03030f021605011d010306080f0120040e0c07060905061810050609150607021806031006080703030c1a070207051504030206032212090e0c0909160504030f05070501 74
    0x2296000c4101c00129441a1a001149450031030042c4600e00b1405000f4181509c03a403000449100402c1651169145034000141c3c0c5402000711404010a6190001c40803400380005d02500d0300c00e000703c541003c209200c0076591142032a040001d008801e4016205014140c100403a8940b0550b500520007031721300c2610110307820a01c00b030080b640305a90481d04244000c002621010311202d0005002400400b454141900703640001c0b01c51402c02d852005c1712041c00203010b01810200100c06420b298800280709440c2414a442d548520500c170140821160039116800c0c0900760110004413100c841681c00075182405000c2d5480c10741c5d01c1400d006000d01103112076803071002000d9400342c80d8020082899a220a0303840d42018011105000e407600300726110300001091200b04104040711a200c21210615107002c0c40f86103240181903600c0001b0030803842c40e1319526850580c2d402441104140045c44082008580500468000405241c0004030440c240440080e41000310340c42640c4030203 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 494815422 1250 494814172 494814193
    0x5060429070b1b030f1501050c03040308070c082802040605040e06071101060501080103150e060a0e07050109120b093409021c02070614150306011a09090c070c03030f02 74
    0xc141c402190a0700d00b403c40c00e00443c1c6505c4514a1b81c502c036030014034100b401c0100504405043d0b5009601c01c0b250341c000081c1d00c03000c201400c8044402865200701500c029903864070900340c10070355110b0010000e400d54540d841156a5a4030000207032001400030080c00b94640790030b0303540b4181640d140740405c6001d040308488202c14004e24056801c10b035034070001a440c1d0340d514500700d0001784030004050748450174200c842c0010480c045c45404050804141c28003501c0d9068142110ba411a90400101c40b1040c80144801c2070f20f240ca241c0d00011170aa035503185103081c0c0c00c10740321920050172040c14540081404005540d0b07074001c500401d50764140036a40e620440124407031a41c000b20300342c140c1101040444560342c0505403490083c040443c08403408042051b0220702196a0385a0988203500c184480c01c080043d50b015207060302d80c3d5460400c5103000c9210030702030f14071030300d2064014000041d6110743c00c0c010744241c0d5a00c010144001512460083c00101c10045035500521601681c030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 494816672 1250 494815422 494815471
    0x30d1125062913021e220e07050313020603010b180d050705060a1403040c08060f04020922150c020615060d0f021b01150f05060429070b 60
    0x640440c200444a16907100342c0090009003850030001d2100c0e16400c0c040c4c1c10341d090305a4600d00c054401182c0603550b0740e18260b900c90258002a100b948030f40b034180400d10158a45070040c17038004186081007030b100d42d15900ba0007400401c040d402500f0072030210001503003a04a101030100340c440c0c12a0500c40c40249014003d6040040001601690201004100904050000b0200d042c91450805410076622030400c0b400d42c4291001c42e0254111142080300450070700c1180c0c3c00c03021041e0600f0182c103081d0001000910302070000c009031252a80e0014a181e03e01c0040b84149501210000107600d1402e03103180109111528480036015440003e00e0070600c0d42c02200402038024505810300b03180c000c1e110f0091100340c280000c0143d00b0401c5240080c03110340562034000c4140000b04030b102080444416181e0a039011407070010401030188000d07919407003a501521254000c1e200c00c228600d22a040c2c40c4070b600100030540000058040600030203403141c5100380702240c480d0340c1c8200c030140744 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 494817922 1250 494816672 494816711
    0x10e0402090603160216030f0210030b13020a051c091a041505060409140703031d0f12010908040f0603051806060d0503090a0e01050310020903030d112506 68
    0x44903801601000016020780075a103240d0b550007005e00c1207610840e000e842d0080304c0c1070030303130015070f03001c00c03001d10351400c5103401402210242c00340c2c9001d10201580c6004140c580303d05583c903a40041c1c010070340c5182c0c0341c401c800b65094602c19050100b0703004201d5090b0401421400c50641e40d108641ca6400c1900070341040f0b9a008650000c110794036040181100b0004020142c9290341c42619a01024041041100c04048e121a40341c090030780305245181c0500041c00c2e1403241c12003040e070030303030040e00a98440403441c41e501c0d4140c4001120801c2c00340c07514010302e200b03103004040c1d00e40450049000540310801c0030640d003064030204400e8031020a60544007418400ca4038059002800041c00b034201040341c42c983d503214400701e90605008138001092054035401c10540b841c401001000385140400150809211a00301145007a0715240883d03204d10800d09005600761301c404800f6018407109080f0ba2640c0c07800304180321268400d00c42041444d2014400740c80060400c200c006d118542550b2 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 494819172 1250 494817922 494817937
    0x16061b03050c01021b0d050a140304110d0308060103060e01080a0206030915040807030e0303030f01120201120c0c030206010b070b0103121215050f0f0303030106030c05160c030c09020307090e0a090c03050c010e0402 94
    0x201c14a0400c040278142c2900e50004000b15100c0c2c004049544850b25920101d200e164400d0320307012254a0407400041c221500da91201c1c02540300030004204461020920a0419805443d074a5032030741c0c0c240d1494542070601c8251201d1000010410090180d90409855003d01c41c0da0307140051542001003580d60f000c160b8410150340d035400010000300b1030902801419500c11304100304419111007149040312410003914001c90701d001c028a0415906201050140404500c61420f1944c241c03150203100391705000041c40842c04854603501e15000702c01000000700d0f50a010310105100389041d0100c200c1d00c0c441c940c0515040034030003c0f5440d280c500c20b82c00c03038030107001942035078a042d000318007030140300000c0400d00108101d051400800031859a0115000344441a289403851400c115044101e60150800d9481401030001c0b00754085500000c4480c4000c0390450390302d907400003200034410b241300108045a15a00001000804203910301c10350401d8842c1303004000e1a8050000382d124510 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 494820422 1250 494819172 494819177
    0xf0b0a020d090b09060903161403010606020102270315270a030f0f0e040204090204030c051c060b0a0b03150307060e0307030f2f0316061b03050c01021b0d050a 70
    0x72001d03260901d18003412003006d000b0304840301019050100314500c03075103401400e8800032604000720b460600b4040c190003481c0c144001c518100001d004095804c8601207003840320340d86001c0d012030980e000c10800d00000081d46101c4941c0c24142861f2554101238103005029a003094000e040d4403c02103408040d2607010340710460148020b40007140c1c1c0d24004131a1100b40a03102c500d815803a00c40c0d1000c0c0001d440c85020050b03881307045050001d45904294841e61045121000d0a20076640c0d51444058079070340844e011a400d140c2c0030000d00c2944140d0847d8540e6100442000401480c10f0700140303118406500b50386010380c0700d840c01c40d0511603070707c42c09401d544421002c10014032022152a50240030744020b105a078500008a00c480b424080084c540e0350041110039003501e070510441e450f110120b400d0000075850072801401c0c1d1100c0b58020130042108003c010240350180040303525105024000b10b40c6c99182d29019000204441d4043c5614480c505001c0d08150144048907034014068 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 494821672 1250 494820422 494820427
    0x1090c140a0509012904080a060902031b0a0909060219032004062309150a09050d02150328331e081204030605090111030c090a0f0b0a020d090b 63
    0x5c0c1c3e00161080c80315580c1d0090b030000c1000142c07000e07082c021412014072642002c41c40c85a0340c0101807400305c5900d90800507000e03c83c2481640d0340c1b801c1002088881042e030200300140075040100080c0583c00003000c0140382c1c001c000c0b103100d034140e010345000d28507802a48183c9189850030312881c0103030300440000c00c4215600e0f1460901c03d1104030503d00c0d1385c0103a1841e20014001044243d52000c0c034005000c1030109440d40c07415040b0250360301400007030752101c1105032150005011102c08903007014503000300000bc02c407020065182074081c0c4050911040e206100642030400900070740e0500e05c0c1000481503100180807020800c0b042c240c09548560051900b000300200079200a0f4102070300c171100c2c0810014070000d05003e02c1009001110032603071900d03d1800d00d5019588000c100240c1a407600a5560207001000b05980d00144c5011004e83c4600c50b0700e001c11404040da412075010014848800554091050020034040345ccc56801c0c0c4003110b05140f001e8904000b28002c00c0c450303c0c0b09 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 494822922 1250 494821672 494821709
    0xf03160e0f1e0315041a04050d110a20040b0f0f010f110f03030a0f14010303051b010203191b0e15070b090a1b03020306061201090c140a050901 63
    0x41000c20b40312454441c446482d2003501c90000740761404040c140c4a01e010001c040005100c10503c0c0030031007102542581545141ca941c0b5070f901e5032210520941840785048003d148058104454001d80381d205540e01070407c21510b031020b0000746005c0d100d21460403d24140c140b4107007084040b0194401502c2d400e010006200156400c1048000c00000c0210503d081100210100100c0c45940210000340d5500e0a002d00d0b00c0c1d0989000075400480300c1d0422041505034860802101e04403905860a5a113662540c05009129550810140429800032003070011075800310441c459010a40c545c104a218000070440d6a064210b4080720042403d0200d048018104074500301000c2c41c41100162802c0e005603201c84e5a1030040d42c0d800007d60001180008103c042410a200c00105030380341d1070860301d1580025a074010041030386029240915003c03480c00b000350480031125030701010300d0607150380355000d10002e4032541c03442e90b100d0540c441000850341030111800d41178030001d11f15860038103503 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 494824172 1250 494822922 494822929
    0x170115050d0c0c0f0b071e05030a111c050919080f0903030f0304030c15150501031d0d020a0b0f072a05010c050405120c1c03030f020f03160e0f 63
    0x207072088501c24040a40d0700c0d8000694201d403030044280c130840041069051140c0000c003440d01c007420003554507040001e0002c7c050f070810242c9a201c0f0441002264244080354450558041d00c19404800071701902080028151074021920600c502d8040710594800310075424507a040c44100500329903420440c00c4c50306203d804c010182240c1c050112482e040340740c046146142c1c4115805d40001e0031000d144410841f00e141444100d00f441c000521014030012440540e140e1544140c6040c1551101d01054240d09404c920411a00d8101135442406da100006520340d04080800c42e04021800c0009000090861241e80120b420307a0751800e1820f00121070700d11121b40300d1148000700e5060795a020000e80c0900506090360750729a0b4554a40e441c02003402194100400c0040039500140030841d0350740c8552100d507019120419013019680c1c100d0074194004c0c40c4400380100c100f03000040028403104024015406032180e5180440341d054504822112300007911140780e031082404030050f81030314 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 494825422 1250 494824172 494824181
    0x5060d02090a02040e1602100c08011203020a3507110103090327051206152103040909232a0d1a01150537170115050d 52
    0x160502c0042c0340c25224420460342c208221504c04c1c424046000c1d03200a00e60600060050800c801c00500880c0c045030b4001e881c403141401100c890401903414003080c0b61007042001d5991390030802200181e2180e2104400c1d42d240040301c2c10340f4103c40c054a0071070007001c0c001c0395941c035001180301044009030710044024001151054007042a000294480c0340f01030728010074440980f48070344482a02c0c10703084c0700c041c01c4030140e1800c50350440003c103c813030446426406412682110106001c3e412114100c1e2031018242c4203c80920010501003120742290384034410450080e0041510b50504c3d01070401e400320005140c5101d504402d0500f510b900104420308260b09100070b58120350107880c00481c00401008000f51090040114103c5040c1c0800300b103d400b4140e9015001440c06540c40090010b106034240d940d03240e401a400c001424008900003e50414107a00b00707a941240c110780100a174040307810401000c0504800042c9130010003151280200e0701d03803951420311481d900b0407170092 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 494826672 1250 494825422 494825431
    0xf0903030114010c050d020d300b0402120a0b0112022503030b0411070b010905091f0b0d0b040204050a0b030706051b0d120e06070c060902040e030d1e05060d0209 71
    0x1300401d80300d4400034106202c0744400c0304c0c6580c02018038102155000b80001d6010111307c0d020710142501045902002d12220414220b03030002045d100400c0300401c0c000d21440320060f1001410005101042c040c41e04a03028202d426a0703950310450744003100c0c030124840c080300750602510080740600000c0421000e142400e003e8100042c00024003004502500c104e0300000c1114040050240d08100001091902514030184100720b0ba1411441185c1d4880d8814005aa152610400d050b0320903155080b010600b68082e108031500c003120316051000610645049100b1414007001902500301ca02c10500c08010050080620360714020083c0d405074800b0300d5401c00d002900503600d4040e0000c00035503440c154590380b44c840401c82c1c40268401c44a203241d0881041e0000c00c10321031540e51000b6155482ca40014000480c8074451001500400d100c4500d0301d62404041408001a0030560083c0b6010080c504510000f400c050515421510102d038401c1c1d000301041505000340c00c0c00c40341d240e0311 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 494827922 1250 494826672 494826677
    0x90509060a08010c0201140124140408010612050d030b011b06111305010f0306060507060506060d0603110a050d05030f1e041e0e0402131104050402030a05010503060f090303011401 79
    0x901d6180d14041d42500c442c14525000b503911211443d84003040a41940d0040c002e20720416000b0407100088045c42d0000380724401000000d41241c81c04040d8102120000e011a200811040b81c4d142c00c00c412841a0007402da555015031911600820700a0003144505441691008a4171302085540c01e01c08001030020703100503540d0b000c0f8a60612000d4002e1500143e0f03880d405404914001c0010808a451130110b000c040c10404200605a017060907a55000c2c1d1008001c1182e03030300c1401180460182c40d022046840c100030001060105000c0d1450784d4402c04d440510209490703c0510203900b08140c00184603610802c105042c01200002a2180e2801e034102440500084e0100e48115001030700700a41c1249000306800c264048100c103400104482c0c1200c0c61079280940010321700703204003099801c1041d100d1260003d00e0710f0800464014000c000c00464072400e14000c03120003824240540c034002e104000c0031a420040184a5510981c545001113245030700341226030100b0511106414103 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 494829172 1250 494827922 494827939
    0x1a0f131a2a0a1a0105091e0106051b06040c0608010819110103060305060115020d030e0d031109040903030204030605090a051e010b06030109020c12090d0206090d06140a050f0709050906 81
    0x54802c641c02c64260040c0811802c01d541081c00304802c258000e401003d5100b4802c5d032030221240c2d144103203811203030903007803480d11200e901c401d07805400c1c4d8200940c029070080b070703040004001c040715040ec180e038010740c3c400c0c285a0722420020f650f400171100c1c900103007954405810015109094040c4002d2040c50042426941d039650340b0f00d406420b03002108440991503140034040c0c1c0c10018110010381a03c0c0510546001c214510f417a07103440101034007095155045001c0310361940c0300310b070300c0030801920400ca89100303801c0082c0250440d00048421a042201087c071034180080c21782102d54112018040240809268400100c8540d503421202e54a07820503015a54400d009140200340b6180090382d100401c078482401c0c09030300100d440450a0a0100b41d1080d1980508000c00e281e05071a9075590b42040c1c1300290603040d244c28024606400d00d14070824083d00350030202c0c01031491340403e00664507016500d030036101003140e2400c0007070052982008a4070702200c4003a08404003910200 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 494830422 1250 494829172 494829193
    0x4080a03050a08090105150906010903050706020c0109080d090b0d06030614190c2309030f0d0809010b0d0b0a02071b1a0705071a0f131a2a 61
    0x14141888094140c0105802007040c0c03115503084000c603a4410a83d0008022900d01207882c606098003a407001c502035190701e000680640d000f070320f42c000030313640184c11514450366412000790344c4c0d82030401c0c042c0021130700c043c0000c1c0b01d20005820862a580c1c0d0b11780184280c2018800c2d080c0381c000011441890f510343c040000440c8480c031416824080c1100c0c0740326145845a0401d011204141c0c3c8842082d14042510040f954043c07003a007801d80003003001c003002940c0da007030751301140c051200c3c110b606008a45200c3c02c0d080303001070f50f42000280c6440d80b011a40c0d80e010b040d401c076001108030f25041803100a00302c0000305402c00d0540d2081080c2d60050410841c0d0b00d80300c0d0b0301c000450000351a1108000e0900007240c02c212950107180701c40c540035140c00840e230b0714142c9440c1c042c826812a16070880a451415800d1020b907480e40504842e8036482e03003242d44038100c00c00b15500c0b4007000300c440403a440103800b522070100c400a10b400d90350f180f034421000300c0720b84078082c0d20760084c0b44a00030500d002 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 494831672 1250 494830422 494830439
    0x6020c03062a16120311090f06090a0305011b03060e090d0e010521040203010b0a03080702061303020d12120b0d03080c160809030616092c0703050f0c1303110604 71
    0x401c00318050000109140341d15031005d8102d807010801c9140c0d01d4000c1c06000d00790340c0c65600d86407014400b0340b43c441e2188007040101e41c100c540c03500700030031319400d044040c2020001155454074469480e5000e014044d42c40d0005498503c2c01c0d124048030303401513482903000714095000e0101182e410b1618070b241050034a107640868049400030b00c10404100300340400d6190902401c20b68000444240042c03505c0c56503014907512405c1002805010080341d803000b03071440241c2450045802030540e098115803480c2c60b020f04001e01c00d00f800400c06104410700c5a048a1148a000c40b40281403801494055102680c0325007005001c0313503490307804002c2400712092102c050a107541c4501900ca0705d8030680c0742098200304000b4442d055070305030b00100d800c1841e4403228180440e46184c0381907084d10910801d60f031440c1090010500d0345100d04051140e003540c541c1c000c078414400707004d60b4003646d1103070f003100511889502c0d1840312a00c1d28202c10310114a200813802c030000380040400f072805039111030b030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 494832922 1250 494831672 494831707
    0x303181502060915011d040f0206210702060408030a091112010c020601051503040b09150403080108010513080a031107060f0605090a0b0d0308060f03060a050106020c03062a 76
    0x4040050b0004000c3c0440018104002c2d8860444004050713010341c140030103040e064540207078005e503900c0040c012600384a100ca00940480790054411941c0e00b80d580761744003480fa440940c81208650b5580050b007800d1010038090b00072035000d601c40c3c0c40d40d11540c8448000d8000d10030305990340c0b20700603200c81c07155a860003541c7e02d2030b450000110318807842e2070001c2e09000050f0302c602c0c0900303007082401d0081e000c2502200d50003903004034180712030349030810440e240c0400a00f141280c0d0403403a050205050300140c0e443e04076000d07440280026511070380d011041d801c00c2100103001010074060f15580502a8100da009180b282c80c669040410301c0e1610300a813084141d900800903920041400207080070021030303a01100050082c8049640314000c1900d02101c09005003c0000c80342c00b103045aa50704840707142c0601c004003180d80c5800c1c6401d00c400240001e20a02d0098440c1111240c01d07400e011030300e0307417103080e884608000180700000c40e16200c801d00580d856814074100803040b0303407102401c1d1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 494834172 1250 494832922 494832959
    0x30d030906021909080111040509070c030504080102041e081c050328020a030c090b0f030a0b04020309010b130902030309040e0a08190216141018030f02040510050a030318 75
    0x75440704c030528000c1d00700d0864501d4404880203400c1084140865206c031840705070040c9013441e00b00c0d031400c400d090071680ca0056401c0509a54000140007450034412140504801440c20a0f131407031a503258034081d5030343c24025800d08405402032090700c115002e02c002d150b0009410840d0031110742c2088a218018810060001d0002e50104041c0500ca90603c00d682031000103044c00c041080c00d200b1602000d000d00006ca02c100351000002501c4810700d40c0101e11204c40141c000d548074100181d00c20701070240d1107d1a07010394000680c0c580701c0384160003039400c03a41c0c0140186280c04140e80612000e05911420840b2a200d0405208001094a00107040401081000c284079100d41c40009041980c800b4400f0001c0e20600424025402e40c000242920001110b4540c5c411168110035207003c0d41c608a10ba140c1d18030190b0000a01c0100c603d12002c8910850f000c024a0781e4444c900044400a40204c3e80c001900600074400203000700982004590508031540c6c01580e00c45400c0d018025590 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 494835422 1250 494834172 494834177
    0x10b030f0303090d0905240f04060f02060901022b02040503030f03161e05090a03210201151a071505011d0a0606020c0112110c0109020a090506030d0309060219 70
    0x1081000380e00d41402290204d41c42ca1906810262a020000f43c41140703240c40110364848003c00e00c14104011000c03103245400e090034a41e2216600c1c80054005024030765010302601800000411485042c404c540445255084002584101e001c2d8034000d0f204001d05a0b100c19030821000c22950790420180100103a42c84510740d03280342c4400e16441a50101076010148450103940000d0036507082006090403e040c902643c403a41c400340044c0001215500180000300a00a464001c40c0031407001031900602d5002406142141420805142d103a482207c070401c01303408101d20000c0e02140201416801382415540e1040140001401c4440a9004c1c0c50300c1420060802e006051120900c0d40c42981b0a00c1001a6460084042e4540d1440f1940c9810040c00d00384d0740d01c1d901c806501c682c0d0301e81d41d4481c42c01e44810100460500803d00044242e1184003190b10000c3c0320211400f44a00c6071802038050800410b200d441a009403000800407505207800b44900c0c05210006000c0207000a980e9 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 494836672 1250 494835422 494835427
    0x9080d060905160e0603040f030216230d051c0207270509031c1104030f140115060c030c0f0506090a03030506010e0901050f0a08070902030103170901020d080405010b030f03 76
    0x2c540400d002c00f80025102c1c14400310190f004429a214010f580d84070b90071483e5800e0380740d01854124202000c40d0301c0f44010510407440401c820410900300484404900b11051050b002001005914521000e0080959001a00c08851401000c460700030a40550048403000c0f40c9900c050701d0182e04003000300c0c40c0040c14020a10100c152400303666007201c0044061480c110130124040c007400940303520002c240351a80c0400d5882c420402c1200e00541e0001d500d41040c1005192011540c170b642c4003450700542c24040c15100c844590003030b44d0221505611410810841640c007513500310480c500a032842c01c442c2001201140081c0501446005100c0203040c0c80801860050200c4001a0056041200c5095404440d446150506040d160100c4403840d130021031400154000407140c0042c541405440c00006e410031040c4c01a5050780c1c410812449601005004507841d80203400800c2d0060f40701d1442c804049000b405210740003800392001160703000808021030716204035006180441e9100 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 494837922 1250 494836672 494836681
    0x120114031b061206060d110304020a05010e090406050c1911100501120308130618050d0c110d06110c030912070308090603072d080a1e09080d060905 65
    0x5018500c03500e10418542054040c01101141070b9010b43c080f4904460107040104e6400e58584e0b058a141e00103940302030003912800540001b041c8c0080d20124042c000341d16000c51320f5800390508103072200018110340c0440d900c544171840038100141141031243e0042004841c8103d01c428000c1d6425555110350070104401c880841c5020034503448a80701d5468040180700e051180100070034283d030185448540c40d01d499004c0c107020b00c101c000c02002030786050076840f240a041990307a18001d014809440031601c000d441901c940c43c02e038a0040c80034900c484800c40619000301d0100c10640103410000340d0040421220a540d070020703151490640c4003042c02002450000200c1030010499005400d490340b0f5503485441714001d8860381c600c202c41c00701c0001c0b0641d02c204515501c4140c90b81000c5544441c4841400101070a040e400d00000c150b6400a80c80d0038080c014010241d0245005050070001018002e0051a2070682251741e84802c2204561440e881d000d142d0240c01c4107240010103092 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 494839172 1250 494837922 494837929
    0x23040e04050c2e0504050d0b01050907020307050d111609050901180b0a0203042a03150203040c030321050f01080d020d17040c030605090c0a080c0d060c0203120114 72
    0x40c20700045100358480c5035a0034201803102c001c2c0f0101c810000e18803a86400c5450241d0b020f000303d0308000d03084048814154244466402030a0480d98160741400702034840c004101d841e44900540906a81e010f90100c1c01501d2007800f520444400c03060946041c4100410704030070240c1d29500c9005a60344440600190900072711a07080e0f00b80c02503403003480d0003d0715510f03500e04c0714006040d48441c40e030100c001000d00c000450400c2403032030010b0402c00030701c040740c420103408412808251041c40080b420642540c40520072240181e4002407102c2038103185640803680d1402006404a00c40e18a120b03c204200030f5010f81070040ea8142c80c03aa895604083c041842c0070b05d0704080404641c000c9100900203074022001001d40c580c0070343c501c0c1596440c0c0c00c1a040e8070205901c010803c034a48010040034103400b00c0c516070649021200f02c50810b507100c0c0c0070f9590f0715190205c15846081404a400003488070780c0104441011401601d092220a802443c5a1102680190410f16582d01080200e14 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 494840422 1250 494839172 494839183
    0xc0b040c05040b060412080901021e0a1203050135011514090415050a060b1c06140f010509040e06010303020f070b03100306020703090312090f09110a23040e0405 71
    0xf40d05642603800c00345406070400400c050840301500408000070b07540c142d43d01c28012260031207030361010a80c80e01e90721005203644040405007519441e00e50101101d009109008090480e00c0d94a820005c04609164491041843c20701010402940b0304600c0445c20081c040c0100d42000090000c0c001032411004000301000081c1a510a10000c03041000250720900000d030340071401c0c04000341c2692511039020040c201904050030704117000c2a07440c0c5020701e0300714082c04028104400e1103440d0750380f083c0420300550400f48d26800b803240490221b01c1d5104d1405844100c00041c0045800000381500c14105002078100390b0040e04401c0c1400003611003009990000c1c00150000c5140d032030103103c8040b9030340c018040104016000150103003410301c145c0202001d1078000072640c58880b04100081c2003407184d441001e400c14102c001c0003074840c0c01031040400454942c0c01ca0303860295203840c00c40d07540080302015041c10b202190110160450f19004d800500784403c65a100390801e070500500c0d10 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 494841672 1250 494840422 494840441
    0x516021c110d02060a1b060603081c0e0c010e0d12050405030d050304050c010c150c0503071205040b07051e0406020303150d020a03240f0906060f0b190c0b040c0504 72
    0xb844140a500010784450003200d040c14114900903500d170007a804461070b45078514030041c110303508112022061000c04001410341503a121901a0300d020f6050980e030940c3c058014a200030380002d100300c0740d19401103072800c4001100a22000381c01500b40d03610015210303d2141c48002400104081c000f40c18100010700d00c2724600e0030b206045103050340c0d42c2d5903122001c4801e14100081c6596400c20020b07541d0f016201640501c0007401412454600100a034100b1204100010a10030ba0b0303106402c0c142c4110b9000d10782061004c0041c3c0c0e032341001a2160f81c02031080141d1040d85040035550305041e0300240c409040a036019681d00d04000b0001ca100c0b6180710b0400e48904065280e24005030707180c003d000200c3c0ea000d41c600e400380080c5010240344c2c44205442d50941d5003010074208003800e041d1312084225109090030009940c030740c5810802501180a1110109020055500502e001e5106c4010141952500c0446105c40b540d50050f40c54090324100c071a602102d0091241d882d050213100103d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 494842922 1250 494841672 494841679
    0xc120414090612120d0902131b050406020709050402030f070e0703110313020d0302030c160302090114010909240315050906090c01030b1c12021c050a0516021c11 71
    0xd5500881400d03890701480e4a0140144c140003903641d0a9240d01d8010301e0025400400e520b60302070141103558054115403461340020303941d05c0c8640780190301a0051354280c64455004110103400e0100c50b200422024000381ea051140052401185004214407405414040012003140c1002c44015080d2580d0010000c030104092007003000c041c60310001c2d4102a03404444010403200c450409a00b54414840802c0d0280510300110380300040036840c02048074030a0754400751980c0c0e608045100140d0701c42e10f0301d0018280c01d10030404682141c0092100c42006070100101c1d01c1c1800c00140f030640154000c8400381882800000040c409100e080d501002c1903002d4041407904032103070780d2a410040319090601d59030390380c40c0e095503e81d0344d0250103840729124842d01c0c00140e428124104440d050000006200e110301c0c0b012111818054085084800d895050a01c030504030152a9504130f081880d0881640028400c00340c0c0c0c4440c1860301030840c4040c0500f041a8030304011101c0d08120090a01 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 494844172 1250 494842922 494842939
    0x30424020901120c03060803180f03060114090c0f46030906020f0307022a01020606011d0904060e070b0304110d030507060e070905070f0903080c1204140906 69
    0xc2c0d81100850310041c801880c00240b141400f41e0940060255803c400c000e440046196988180340c0010036100500c00ca0b10441c0c007280758010580d0300d000c00d018408003d1001d103500c0d4540d00f020140c66401070303146a400d504000404c201d400ca80d070005150381c1076550200124100601d00140600035004081d11098042010758203d0a010340d40d26002e00c0402da0740d88440403e1102e9039040d1040c1e00b1080113078030380d6800c110300001d656117003e60544448943c6c8800301d440740a01440010307049003041e0007400039561001d0054503c20600002651215602d0684c11040c1d91031280c0c80f4400c0e44200400102c0c0d00c0e0300c030401464074065030011101c40d00c0070814003020803200e400c004112a800c81b400980b5141a24040303445008440000b4182c0341803c1700413a56940120b4a04203440c08020200101c0d070790041e085662010fa05920310111303102034020700116900e40028250303000d60740200c4140baa440038600c1d8030381c0d1050f0300008145541c800130030b5042c546051400d4001008035409030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 494845422 1250 494844172 494844187
    0x21c1407060f02030a020d08060a0512011d0a0b06090a0f09033203060d030c080406050c1908071101200106090c020a050d08070c2001090806070203070f020a08010203042402 76
    0xa640c7c682d0705103010240006440000da007656003001c21400b80c035000d000c1c01c44a100c40d0305030602820010540840c0303d40117000c84c1080f070a00081443c541c0ba00031101c1003aa4882809010b030f00c61000e40307400c3e00c00d0f0316421307030b1240c0750079902900030880c4c848d5541c0d181aa92030500036018030103000e0050454403180c8050b40c4200d2005080e2034110303100f15000410404030b45806d84240c4508030300140100740c0401e0005259070050050010b080540d8180c41c201204030301075548900d01041c00038034404040c0b01820102c2d000d500d0900310000117040030704403000340050b103149821141c00802c00d1a912054148030b4583c0700c1c0a00608441c07540007e00078407e40c2da503402d4881100c201032200b0844c9540000ea121032296800c01c1e80983c202c1002013640c8a802c40420300f912070711503201e020400001303000075422030019a451140340790fa0302943c00e1035aa95140c1e82e82801c4e203c1c00360f034454500240031074420401e1000f90b003c0c0344546c18030b03044c6031186005a071150702c000c81d20320074062043c081304 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 494846672 1250 494845422 494845427
    0x20f1b070602071a0421151407120e0102030a09150c0203071205040e070504050316030222090b0c040501080108070e07110f070b2d07021c1407060f02030a 68
    0x20513142d0450244001c00882c0b503c008040c090b5900503072404c210780c0b0031807038500c80e03400103040054000c200c240003400078501d04001313442ca001620340925851b000000c44061040240c07040d51040c001020a20b140010781550990300243c0f85140507a6550305920100701500c1c0440403000d168000034088501c112a02035100d000b030150140c00c07803903098240001c45110348210380c064910400302c010f80c1c2c24080401420740e00305004031802032203100391400c3d10401c070000304800c8a41c01007104010001c0c94202d480c816245140300182e03142c54407401800a041c1c01c142500c102d141c0300903140c55034500ba00040550350f040e031210b030580d00300b40001e002d403083e003e0120303610a00500b030003107204a8000710305190201c11042c0040074040d0880210f02c1d55440c03c024020b5600290041207003061700380e050245500017498607c0c1591041000c0e40050030172080ba00c40d440c1ca8010101c1c482607041c0c80b142c01d030705c00c04906070410783c00012051080a41080103480e4510241c40118145966104003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 494847922 1250 494846672 494846683
    0x1508060c07020a0806040b0703060803030603100f230411100203030c0711060c100c030e0a060c03140c03011505030402240d020708040503100b1806010e04020f1b070602 74
    0x1104403803500000d0410954568200304002840200120358aa16060030080720550090314201c0000f030a003440010300c030400000781c0340200340007409498591074052a1000030402440c000701401e407541a1080e1207480b910b00d04c01d4000701001c800300070303280505d40244048900c4140d01e1150070317100c440484065001098030f80c0469002e109a907144c24a0800904900c4004403880d0702a03000114101141d0b00880e8503803001c2000c0c007040c0702c68820310303509500b9a188410321a4050340840f81300c0300030459036004060488850700f000906410f1208601c10000c4d8202e91403100c44000000401c9807880910460640c0102450000d0440c2000d6001030020000d51034034101e502c58002100102282e401c00b120002403a00100315551300d80c130300e030010550b001807107420300c28001d00c0c0582c802c0d40f180e40110070396040f004000c1e40110040301141c58a113040940345504010100780c11003e0b0380c807144010950503600940c0f40c0d0b00d40b185001d050480134112402c040c0c075074111660070404541c00207032 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 494849172 1250 494847922 494847931
    0x30d08010905040f0c0303020c042f07110d080a02070b04050612072109210c080c010f060306021c060806010b0901140403143307030b03060910150806 66
    0xc0481c2503100c83c20958900f1103204d00c05400d001c07004000004254001031139040102042d1400c2c0032001c100c05080365101254611070042c00407144070100803554280003002c0081c410084550b02c0344c0040080f0b44000b181400840d115400018a5036216404014100c020006415928a4580ae040120f4014000c0d00360f25640c00342000c011910043c0112343e07080310300550180501c0b25506160030380020703111540047e0b400d040c401804c1d42c1e000c13429405822100078a503c414041c201c007696602c1141d40810700c4030045560354004400030000501954004500828000d40c40342001d000d080d20290301c81100700300e40f0349040c8040140c50008601681111518403a040d1103680310700050300c02700e050a400001c65000080e0100401000c4a840084400d0f40d000f100d0f850b2050502010006000c0d852020032030a01d074642c10f4500d584030b9506540011030349400301d0500c015101103445c0c2201907941c0c201c1c9030440c032403004088155218000202c5480310a10844510340076015031a802d0292 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 494850422 1250 494849172 494849189
    0x10b03161416150b04020910081e100f0e07020a0b0709030206030a050403021e1902120105040312111602131103090714060403021008190c020a020f030d0801 69
    0x88801d9100044209940d10400c07609801d03410070410f80f07821102c000c0d0650402c40054581003201c910b41c1030501c00d80d0300810024000719003299000390b003070340c0381d21008020100040c818211105580c02c5007101e0f500503036042003604003050800751209040381c50740c1c1102c1202154442080b104503400a007a0100c290041420100c5440b00c000844020100307400107900001c0010911070001415400540310f06d0203507003911404106040a0b0942280c2034150303140e9940060082c0300001080322501925a1004241010a0413000011429a0402c42d81039020486000d10584242028010030342d500200d1400b80d85812000440b0101e80601000c01a006004038890080da0008a50203030700f40d0003c540c11030341c40c1d14180c603140341c1c0c454140c001c0349245a25500300d503090f800c1040c20380c0c05a07580144540107450300d4120449103104014007140794040b5102010442d000588902c101ca0080c2e9030290108a01ca801400745104255440d03038081e0b0f20204041884d40c2c0d06c040c100e815940c103031 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 494851672 1250 494850422 494850437
    0x715090608151306091d07090605060304120c0b090604050115151215030c080d0311030c030613021314060a020c01050d020705030d06031104091e0c17060f010b0316 72
    0x14280c0041c00290170900c0c40d10302c0c046080000e200c12001c10b4038001108800c075040380e500e4030802801c1d140e85d48030b25a0000014004100091a0b019010b40d40885519000b21002002d40303407080100300541e8038800d030b50003a42c207100500c102030040070001c101c04407140c1a071070301d06000702030301300010400038081010f4081d140d24100e01c01e030850510000598114100140c490030030303007508e00b040e01c25038106109095848034280c0c043e026024006629480b1030341503656403890a041540001c004070317400002c200e03140d014001075201402e146068015070411450074045400b0840e08030a05071840368030180200c0300140e0340005c2c0c12a0a18003843c0c00707500d45d19407503c2000a4050003100601c80c0c000410381440f001e10b25404031003140c1c0100d01c1824111400030500c01203132669000034183c10090181e444c0980d0a040d20201c81c20b22032891242003e0313035100d2051044940c41030031910b1781c000005001140c4001940340740900440116a455400d0882c40824140040c014440900064 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 494852922 1250 494851672 494851699
    0xa0e06060d1107030203130f080307080901021515010e0301180303090515010305010507080a090f12090e01031415071d0103020706021b190809060c01020903071509060815 75
    0x454209500c503056004100b0f840c0c51240c0341c00394032a042103216400c01e03d010800000c003561486044c2c000c41e0416070247d880c4c0380440d20703440302c03d03803105211605520a14280400da014812582885010700c0b41881003003401400004000d810304003901c2c2e10903810002e076444240780844034820f0f00c0340d260074001a552110f190090401100c460703410f202550300d40001052140c11b4001510502156a40000e035507903541c0700100b107411402002e032043d0008882400001d40030780b20001140e2003410440b1455a8a0240d0f40720070b20241c01c200c44201004c40c600318445c2c070400c511400c881040940d1711207441c0c180f80c001e0105484d440e420f0690110b0130b003d546142d0080d811503a1880d005002590380f03906080442e4501c10360780c2d200004d05e10410041c45200d40321031000314600c0c0d80c044d00c0c9603c0d00c103c440800100380c0005e04011819503081221481958041111800400c8d13a2000d4034242698090050f10341c051580c080c6041c05004001c0200120408039603a43c684401c8902c1d0100041 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 494854172 1250 494852922 494852947
    0x9100303030b031b1e03150702010c0c050a170405131e0b060307030b0d0b090105040506010b1c0518060709060809030723150907030c1706061003090218150a0e0606 72
    0x2005c940c0707405001e04e00d24002810aa400c07060b120301d1154009104c4000b0200e01251042c0c04c03008040c0403600000c00d88000610111802c081c8600e0701d0507540d080c1611180058860b40c14a0110400956183e43d4454a0400980e120b40c488011100c100701c0402c06101094451100600b03510805a550815140743c0e41c0e07100e6010f0b0361070781107110404c6c285042641139001301360540d001c5e20140310761000050b20460000881e07883c0e21a10024a18811641c00c103034028000c041c0c90104201c81889407408108403c000c0184111361076901c0d41c0b400c625040d0050704100d00a006440d403500100850b50104500d40b522a04e03040303003484902e01d074910f81d0501d2414050000201c801d03c140140c28030020150008881d0290380c092880803203401d50340c451a0001007000e040c050740540102e80000c07500d191082d03040c5500c000310308010501c8600740d070001e007640824980b03450494810348244a4081081d00211240890030b03a4410714090030702c9940011904000c5c41c1074410000000c45a40046 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 494855422 1250 494854172 494854219
    0x80304050111030a0c030f1a0f150f0a11030c1b0105071203020408010c020a0b07051c0c0504032015090604030605040803041115072009100303030b031b 67
    0x1c1c4040b05007a140c0c184010600094160300c002c03800024105102100600309a00c22aa44100180300001507076a0010900c61502030304103c0941c01101070720402d06d04400203009224051151860700e0703588102c4030011780140c0c11403405007d207078030601c0041e042c0381c0000f80c0e40900d00d440255210070001035400481e001e20903c0c0000b490900b14919000752142c041e0082c005a4407100001c0c000003100b20000c07a5030380c20030311010b824071894201017540d1500800003003a0101c01c1c1259803c0000c12000c80e081990400c0000c6000134a0018040050203e030051003040e10b40c0b075605001c140001c12000070400984180b00d4880440c00260006407659440116402154805014051444c0a04044002d900121415240c458894140d1542e9141004907508110705503150203080c076000340c1f104c1851282141d5a480010407501d0800025138981d00080e100316484111811139500f1842c0040c00d80382051a035500a601540f01280214a545074192280c0c0007500c0e107448900b0b94000d41d14a15 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 494856672 1250 494855422 494855441
    0x50904020910030506030c0d080711010315082104320a030510050a050601050f131212020d0905060d0b040204030c1d0f15060a090b0c01060801060f0803070803040501 73
    0x201c2c0c4400e10301c00c5401d50400c51080d58103c081e1101600f50030705111041200010050488904004810028030300401c141c0580206140006440004031031300b0000f00f40503008000c45074820389101c00d80e0071052080c48600c03180e001030603040a00e05115003020101443c08125042d02d01007507603219200b058246e280341d48000300031400d066600e0828a4403421a0f032540c1d09641d00380f60003d2040f910394010705004030b106075980c40c9841c0d00907072071540c0c40e0810603070300c5641c10304041c0010f117101007800c02c4003105001e01c00310040383d400113101070718192900c51208288071a03000e0801c0541c3d20501030f65000e80310208007081c14580d540006000348100d820003481c000205001194009548001941460049104d040103441d5200d002c81500c8007143d040c1c0b21919000380c10807990824201400c00d044043c20429040f9440700e544848035040104441e2160395a01010042400b0901800008103d5038002003009810111111740701e224400001e060078600201240070000b0962000001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 494857922 1250 494856672 494856679
    0x409050a0c090311150f1209010e0705130207051b09070206220203010e0f0a1208010807092d151e030201080403050d0c180b03060a03060f110d14070804120509040209 73
    0x31180d8403035a500240e0800300b6040411f0a00500091689505101c0c0f042e41c10482002004030a20f803100b000f289840c854480c580d010340030300c00900060002c006100d20040282c414800001c030000a200d8943c00003002c1d081154824000d01100203014400f0200600c8480102e800b1010325001007805448042c9103100740e849803022500c1e40f1a4040742c40f00c0a548152910140380d00c4240c02218030110a00500c0031580210a007001404a640c0c400e54992528007041e40c2c411003080142c00c0000345007500f0140e95034862403c4d44042c800412a48085c1444148103601d081d0408a20300080e11240002418042d884010800b4140140185c8110454900d4103201040c0b07222001000d43c49d01c18a07074650003c5e02c0794042204100e880549104140182028000c80d241d525180080c0403c0f22006520356a02c002181182c09150000e0100d0810030f000868105c203e40507544048000815010802840905010024030b0001414041c104145001c644807000c00000074020710814031003552 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 494859172 1250 494857922 494857927
    0x30a08070b0402090c07050705040c03060306090506190c3501170d08010b0304060b120a061d010e0303071d0904030c1202061b070f0206030103080409050a0c09031115 73
    0x10401c07162007961080780300390740c051050b441d800048200740c05422002080d0b50800c003000d212070304040c2d000c128032540c28580464004c2e07483e29410101c543c084415101a0003010420200840d00010f206900310351600801c50001d0140c1c00a040c50310664407000300804583d41c09007a43d24195250707445210409a85259581d074a41201100c520380c0b4166445000d491040c2444038014000c00f41290121100f02b803442c0d030b4607520440180310105810341d00001540201011132000c010349503855100714800107d100b110440b2030341411000e00079030304aa0424603508004500481a29002140303810142445c007480580d0307402c140d407040d40e079542091040041205041c1d00100d1070f07010a00500e0b18034039047d00d43d00226190002121445a03036880e006003031110743c0b5450300626106001c2d0b0b400103400c2c01c0070350004896500c00c0e882a01c0540e004542846007061134416203402c1241d1310010009040b8020000d8650b80c007911000e48030307075030b401c24fc0d074800d4880c8400c840c920000c820b030003a03 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 494860422 1250 494859172 494859187
    0x2120702101401060c0b07030906110c0f010615050c0109050d0c120207060818070509011715190506030a0f030f0201060b1c02090a080a030c030807030b0a050f030a08 73
    0x2956880760746441c050050802981d609440048290b25068076419501d41302c0030003264580d90000745020b8000700405aa6074091408079400d80300b200280c1c0c000d1030095950f241c8000007076107003509013030886000303034035010003002009480c07210380031a02d6135810702d035440d01d00303c0d2001d900400450b40058070704e00490028440c080e51200f8845582d038850203c0001c02145294120b98a211a01601c0d0110302c98002103070544007814084555540440110713a031f62a111404207108030420780c4164203483e44058509641c803428801030b242d00d50351400e00d0707149240c460140c0c1c5040b462842c0500f811940c820125880c0d031014011b0320061600905141c03412915450020154101003001a00551034910086080b42440f4100c50403222001026101d44541d500508021b40c081c032561540140340304030000e1403202c28020085503030301076101c004100c8000e040103020268000c001d00f04040c40e00304003403190350701c080c80007054034802c0d82c03804100b050501c0032a25003402c540010340284008103029 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 494861672 1250 494860422 494860427
    0x70917010b0a090216060218120604140d020304051e04230603010b03060a0e0120040f060e030a0b151804060608060613111c020d1d0c13021207 63
    0x5110076981911044400c03543d658102d0201d00039080728100590000601d40c0124035260040d00c0310540088544000c0b402140001e8054081c5c0c4901d20310b00c0d08500104010b200d10300303030049151049a801741c8049400000c4c02903c82c822801002e226000e45212640410700000782c3c0c0e58000d9003d44108413440d000783d0f08800b002c505071185101d2100600005c0c9103414103014000c04d40700090300610054a44c161240082c08017184a1503841d0750300c12800c0007900001400c614001c2080c5001a6114103000030a00155029042030040c46440113920150303440010f02e15283e181c1201070321580761a014864550813445050559010940300851003994900c2401c80c0e00540c800e1030100160740d6071303003171071a1542800c940090f44598140c42d04018900c440d0410000300840135002032500c1c810b0360707081c43c2511402c017134410020350101e1012407000e110310403103149201c0d1071007040c0c2d020f4419229582d00c107480d944e00b0313010740b0740d102d84240419410b4050b58520819505400414544860700 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 494862922 1250 494861672 494861681
    0x8040902090a061115090a050111030406060f05010c060203040c08010507090512060103030c080a02010b03120307020d020a080409020f0904020f0910030203040b01060f27050102070b04080d0807091701 88
    0x1a00c02c07049114001078850061540c2800410284041e0440114074203880044400003411031b0f6503800340410500c00601d00f84500859000b1498071241c607810300307090840c00c582c0e183d000342801d045d440c003080c04960707089450345c41f240394000c601690766601c40c90062040c5c00c031a07001404035800c101c1132000b080d401034203c1058a1065030040801038403485c0c01e65854400f884058040b81c00d41d1542c10110300544010880b8000c00e00000c02c0c1d070140d4102003481c100a6207400744d400d910110601a1480d030501004001d404180b0041500c04234945901131184142e1080810450780003c4401004000c071056441e1500d000b0011501d421414a10400c02e60041030850701c1001540280c626041c024420781c1e000e2a00000e510f5452781c00c03c0001c0c3c1302e420038480203001b442050f803803d9402ca41a601c040312103c504119002c4505d18140019141042503002a00040c034103001c03c0c01300060000b082e841042c10f500d07206241c1e40764501d0a541840032500418070110b9480100140007405400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 494864172 1250 494862922 494862937
    0x4090c08010e06101401020f150a0e06070e360a0b03070605070303020a030902120a021f02030909040f140615060414040f0213120210090503120309030708040902 71
    0x3403000855840d1000d88450301103a10000c4c4201000080c05040e01d10914204055810300403204002101d10000e4503008a0080c000003280c0e21404100c4031070454000d80c1400c42c45c81000741034500300054041d0000021000c07140c022403416014900b07030400200c2c2155007460aa10a081c142800718124000803012203400c0800d6060a0901005040009151085403a542c0e185810700c00d59990413406540040745000c03c141e11443e0315005a61105210380070f18501000500c042801c40c03061201a080c5035030480740b14813024549202c0b20b42c02004640442104a9034040c0036607903443d00c030480d40d2414101510130090703545c0354120380900007551809403942c2ca100a6050f40c01c5010040ca0b445075014075890304910302400d100c1801c1503002007041b2540514094240100c10855000500300f44c1e12210307040062806501c20740c1040d6452003c0c00d000d07031414104850038000800e43d10090032240903c001000000900040410710541e010300380d10070a110b82d41c1e903907540036030040c1d0031090 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 494865422 1250 494864172 494864189
    0x9060403050f0610030f08032a071a010b0d0b06071a100b040b04030b0a110f0a092102011b0606240f1e050f03040309060809010c080f0c070204090c 65
    0x3004621862130783c02c43c0e03404903540490041d40b00c000c141e44c0c01681da080644014543c40c5110310b56121407a603004c1c42090301905124854503034a00c2e0805801196040f03104044100b2400018854035416a044074422484440f02187c1d8032696008100140309032a00540400d1440040c502c59101508506000701e102140600f202501d64030310907981d214511840c0c10017902008208002044007a096170310440c4180005029600c440660303642d0342c0b1001000b40810310020741502890380182c1d510000d0441d09015450400d16285404242501400040c0c14055204d6800c128582001c4074558180d1380004c0a001c619629110100b8813854011001c0c41540800d0455006610940030300b124120a0744d9075901021071406d40c0403101d040c1e41c00c243c0800078100546407512021500440c050342c03107a524514207078a4481c00400002c000b514521941c1d04200e4900002c9078401800c54000024044248a83d100c900c0c80034814441e46000a4115061401d4039080c0407500480304119004007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 494866672 1250 494865422 494865433
    0x70305060916050711010c051e10050c04090e19080403020a051e0411041d01090c1b230a050d03050a020408070b092b062003071409060403050f 63
    0x442040ba214224580c5100001d0060041201203a0b85d20749443c0d00f1081810100355000490300d5080c24203040751661000c0056802540c00412000c0140c030402c840000000c00032414800c501e1442c900c61840344011003130b1240c40c0d01000c072805001450303d0115a400c0691203800034504641c107900284020f07407003071080c0300c00050203007081c45803c80c90b051a5460b0305d4103c42c4881c204001000c800034440b2040300c060001088503684101104410214800400c0c00c5614140c1c0e0142035503840c1a10300c0412803242031040580c000c00312040302155020004001d8203605810105051071a040f2105151113030f89050000d000c00071030301540c041e1240d903041c4029915000d901090348254418500c40d030380280303001c02c84c2c0c41c0c4110141c40e020000508208020000440d401900100c0c0307000d103a00d80d1444030600c0200480c0e4410301e031002600042101100314400e80c090003d000007040e81041c80071490050607a007030000120752a00400903c010f0700c554070382c02c006555844c3c030b0034540c2c100d1141 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 494867922 1250 494866672 494866681
    0x7030e0a0606051f05070b0415020a0507060b0105040503030f0309010b060f0a02010c0e0d0807020d02040c180515090906120f07030311010e03090607110a03390504091a0703050609 79
    0xc441c10255280c0c01ca4a40510305242687c0b6803440210081041d00d94400304403824424400900080c40d640d00d03203903201c503105e841038100f100840b401405502d050050801042210ba00d0100945d8051071040c00031a07229a10580b401d8050142c2c403000c282c1c000c034001100e4004002040241101181d1980200f01c0041920401e40710741043d080c01c580e004404c40890000210740c4002003108a10103400d00c80b654400d0f90104d8144c0f080e00b802c074004900b105403030f10009054000b0380c0703004244c200c401d5008441c81c040040c00a120710070326207005011800010b0300940b520045014038a07042c204858054951b1951103454200c640400c0b400606008a0810519030501850b1102c0346c1c00350103549000080340810906900103e801c86401100c22075428180d41d548005800540c003d41e440000755454000c0e0b85242d80c141a020038580801c90044104032980c683e481c810303200706a41c0000c2d2200d1906002030300240700303112042c03200c0d1207904000d0102e9064010600a9030140c0d003074000d9485 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 494869172 1250 494867922 494867959
    0x2060313030320192c012309120a0f0818040207020609041d03040605030708060405070f12060e15040b0108010b0306060f1b010b0f03010c12020307030e0a060605 71
    0x900d08243c1d8200541401030018800c1c00c1c40c60840026042d04110a09100e03035105900c080c0828003803035500700c403203444049031540c104100002016044c41d05170101c80d1000b20740e42c540d0054011071400b89502059480301e441007045545000c5411110b070007441c2541d45003120041c0d104030020100301000d1540844a810b0a0091b607405941c02025a402c1035944024030004103001c008070002c109181e0b6200e00c0e43e04040c00204007408032a07039500e940c2d10f0034890207402e80c04042c1c1454041c80c40d20342000301d501d502c551500035003001c603d0a1900b407a007682e814000341c02550440402c0200810a005040d840d9840030320301c5000c15075090105240d00b40040d5407900e000d03c6211000c11301003002505915002c80117003564100c0140e0581011029000d45480070081115581c4a81d583c83c00c003103482c5008400c1e81d0940350118007d03c0355008900c0d000302581a40084440310940120104000c00c3c000c0c0c00c0f0329070200418040341d002040d517050071030291413203101d1039000b1013241824810800c4d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 494870422 1250 494869172 494869211
    0x71202150319051302090907170c0136090b030607110d0e3d030c080106030c12140604050105040204050a090b0d050f15092109030a060c03020c0618190c03020603130303 74
    0x143c540380133440c0031191100401c2030044588103200c14500320380e94107118400790000038140c004000100e4100311014145091405000f040c18000c0891008600840008052540e11a28500041b224400102054100c4098520102560340b400300f0048a02e55800030300c2d044c0d00c1034007490080749140840660442c0c0340c0d00c155200143c0305200612000d4081c1e00f2060324000da07803914550f8030303042001c070740100c40c04083c005050300000d030180841131038140545400741c841141c1c110b1030140b40600107002811f8a10661101c1a00c8030100d05140d550b55540c420240c2e040820391702d5010702201166124030816407218044409a404100040c400081c001c020b1807862088102c40b85a0046008041d00002c155130b900d403060302c01300d0002070b0710b5004803030300000241c40160b03e44940740800d9042440041454220807859000c1001044000644141a20091002c0301607911075080c50403c0141c2030304003039000400041070040070340d0680f440e088614081e507020421a00704c410101d6650 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 494871672 1250 494870422 494870443
    0x50609010207120302150f01050301240521030a08071202041d0603011b110c010e09010b0f0d02180a0e07080604110c07120215031905130209090717 65
    0x5034840001800b20400003c00103082c80d00900480344002018080642802c60868010452801180041100303003030034011000031156a44580344101203007291039200e400f803881103a21400e0700010521310040e02d90000300245c13168a00b0340741d4940d40020040c0140d07500f921740703800251031915070841c1e1003264806e070380c143c40243d064001291130252060301c0440010700010780c15562400070a20301782c0300d4280040341c0d11141e02d440751648014040075080070514006e45041c084e41d10f02140d102d65034a600141541c40c03d020058460700644d181c4076070f5002d030365410840130f44001803400074120b00c04684410a40c00b00c41c0080080e48480c41a0644a0140d4010340441c45480c08908145042d800003521252003581c0b02d801c1c00c1c08001640d1802e410307a4001071640040c0700d8408154140035807444540e4481c99142d504d9410054015810300c46e847c1908004903039100c01141c00b00d00f0900652082c82c0e0020704483d01410030f05082600d0b080036105c0c1207000d001c40d070b07400f800384080401c0c505003d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 494872922 1250 494871672 494871677
    0xd030f141801090506180d03141602211015051503061c05030a0c1104060e1906080604080a03020403080f120a0c0c020f03120c0f0f060103020604051009050406090c02010605060901 79
    0x462101c00c01e020464500910440a101004501a48000203d0701400032b00030820303c4020103d01d42d005005a100080b00401703c032030b6200b9059a500c1c400042d80501c14030302d00ca00000c280664030007e81c2e5128281e04419440700d20f5013080321803101c40c0400f6501800b802c80345c0000844010303805488001e082640100b03242c005112022101d80900925200240510603111400650380300140803110250081e1920344059414415084158114001030350070418041140908002810755108401403005092020004419407218425010790b00210350000089d030325003210040c02c40c0c03141c011408284188007414000303602181710380110f00e01c0110546400364005000d40a20060301c0c164000079401d8030440c081c5550642403000180030b03c00e40c40000d009040001e0041d45c2c01d1400342e0f401c440f0113038051300051016a660b0310869007103c0084600c9200006070719000d507074284540d884982d2162a040b000610b081141d000b242140741558000c114150b2540200314140c09550b504500 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 494874172 1250 494872922 494872957
    0xc072c01061b050d030f0e03040f0302060c1f05060103200306060d090506070c0203160f09020705010f0504032111030c070206190207150203090d030f141801090506 72
    0x150302403650b400d01d81d400700650090300041a00c0381458035480e0307801d58002030380d02d1038001c41041c0d16100d58028261000f000c1c0d85001e280c040d180c6584561800068481c040000e8140b0303070202e08001d1981c6500109484040c1c1c0c1c2c01a41c2d00300024a800c80368203020a090000301c10a0306248200e0824660700c800015085d51500001d00a45810219201030030550300d4024030041034003040380d01d204000719640c0a840c0340c8144145404c122003030038000070b45209078500f070214011441c0c041060300d101d4400162121000e007411409071400e203040030071980ca00024002450342c010460303012000003880c40803140b8130000f0800d013154000404100079003002e00c0490184182c02009000b40e90000b48041d082c000d034450060b1400c400320010b50090381c400c1200300441420701c140c90801c2e40b80c60000d0344c1410422001300c1c00d0342e11640360090803c41030061144916000d42500400901d90a0030f064403414080c01d440603518898100c03a001c6100f44000080c0b5103001c90490714440014400d204 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 494875422 1250 494874172 494874179
    0x10311011707050922020403021f050a03090317180f030f0318071a1806030105031b12070e01080f0307030207060509211e011a0f030f030c072c01 64
    0x403640d8102e00045581700444403580542d01c2407961800720704030742180005949a01d1441000080780c000c81d8600c00c00150040c104401c40e030480250b40c5900c0e81804d01017030000003407404031000041f4980d407003044032090781400700d80c840007030900c1d12003030f0b00b030046030b00503803c0e203611995038007a0001c6042454010000902004001d014003071034240581e045911060320707180d900c207248040e42070504462001140f0144001402e14442c2c9c40900305941ca1851035040802080d180e040ca21441041d007410f00c00c03141010303210310261003808041481030783c0b000b6072950504000b118080c45142d100e407041600c002000c60002c400c0f80c407450350540042c15041e00d045c2065176070b07400c1488415800024507000c1c08aa0b42a0100042078444a002400b070422080c1d82039529242414841d000c90b0b0300d040b00d551100300c40c80400c44044801150740040811250001074608102c040001909000208158008140002d80141504e4902400c80e48010512046206260200a209408421813170040 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 494876672 1250 494875422 494875427
    0x40e090f060c03150d15110a09120b1311060c0a0303060905010605090d0303020c0313180903050d15180b01140c0a060b040902150a03180b0f07020f010c08010311011707 74
    0x4910500c20070700c0d00300c440c2c04e1400020441f2401c1000c404c0b41580090015442d90b40445d884014041c000881031b40c8600c15101d120900c0d000400c10359400c0001d0703020006002020040801c500001400c15907030300c031110704060b280c43c0142c4045021900b040400710b0000124090241030340c03075541e030b02c6007410f0742e50080121283c0342050513010316074208400c00000c6014030042042140c0c0d0703115025018039102c1c207640c060f003251103070711407591402c030034080007980c0300c0102c44104020311004035440a11403000380700116076a0000d01c2030000c0d0110130403d21402c3c2c1000d02a600241c03600a402002044000c0840c82030070043c00b41608500b412100240d42c5500c005a00c0d2405880015013400390f43c085125a854540d401105503c04035040095a03854056284080349110881d02241c1140d6103101d101c10f0090080c0216060700c1d40060600e900c00c100d580d4807001140000d02c07800110b4100a0301010081c081a200400502074001030b550203281e9040c2100c5600c02260010790b02e41004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 494877922 1250 494876672 494876689
    0xb060609011803050d0f020114270109060b1005041208210702070f0b04060e04050a02280905090601080f0712090813090903080a0504030302040e090f060c0315 70
    0x103803418000300c1010b40c849040040003100c040c510a0005045c80908804c014202103200011302045a050001e000b04580c50b0f2500d0a402074a04086102c4d01205502d41508504c002c000d02c05096180480000c141305454111021044050352464082040000c0c2150944280c1c0114600140480c1c2c5420000f03034281e000b40f4001d00c2c1900e500b03901c03c014490604000105941010059004035001d0001040c5400f170720004010345032a55103424900070003d4184002e1481d4148640da075580012200718650b01110301c5c0e0358490b402c030100942ca200e000b40252444000900c00641c030b00c2001702c4c4074100210554004c0d034058441c021310f50740e550b07010030b0701040003414101001110240c2801c0040c1c50b01400842c1ca00c980c20090321494002148184026513a2020228a0805041002003a0803031070702d82d040b440c007200201e090741c0e85050540203403140b50b00c406400000b000130469611301c081813540b41c4030032440986400d07458444824081340010341700d10010307010744203081c0c0c51840c15104 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 494879172 1250 494877922 494877937
    0x120f210405191514060102010606110a02121009120e180c07030e060a0905011103092b021302030106170402032a03030408070e07020604050607140c0607050a0306120b0606 75
    0x15100e01120103920541134a0070396181c0a140c0c0a09010300c40690780a001c0c0d800502000d20b03020f184100500d41869072803070003440181c0146002032030500c2184003031240c4a17641c008804207008864040c078100154581145404c400035810741141e420500c0d1000c1b442c010a09018001040c54541c00403030340d4154440ca0048003417181442c55280183c4403100500051030032070700d500310460b00d04000506807240c9031204140d0354004110f44400356540c156036000194139000400d44085a0b20501ea00070404401c01943c0040071100d8200052015002141640c24a549410740011101d0441d40c01d00000d0b10b0082d49078000c407000081c11152820343c00c5c1c00304030000c40702035001a0440803908683c4943c00062460304824000d0001d902c107812401e42182c1584001d0000d803900e52a07164039804094000020824262210760444410350240e45440b0f00761000d941c803905240001904d9907110b030a6103000b09003085000500030599030704c2e04961039000355030b10040e030b5107580401c40f041d444801c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 494880422 1250 494879172 494879183
    0x6050609012615040e060103080708030601170109050a0b040e1b0f041a01020d2a03090e070206091b01231308010903031104061b05120f21040519 64
    0x450903500b106184503d006107003802d803481c0388036098014442511a000306800d00c540c022801040041c0004044943c9690170420064480d1034070001203c036074410000c030520b1458004000f1a004a0b141d01c064025904144104064408074040c08140d4441d0840003016420040a140c2800a040c20104218400900325812507100100040840340403a00c1c813110380101c103a1405240d6010060780b401d03a20305060103000e90100c034604002e40c503c02c40c00180c0d5004c00348071000415015030000d102030038940700c0f001c55500d08510000e6403000d00315030449003849010302032403000c07245c800070f040400010f9468140c549e000782c1c0c000e012038000354116240004200300006c0d00e0720009103194040c0000000128204125007002404c0e00d09031000c1c54500d260800042005035080074280c0100000d000101d406800541015400c0c8441010300d080000d02c002040400040c50a0040005100750f56101c418a4130b00c0d910100f15920480d0000c04035842030305804003031900e4004100b5594481c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 494881672 1250 494880422 494880467
    0x914011409031b090a09081606020403080c030702010e09090d112e05060103180303050402040b09090706200721050a0b07081b0301060c0305041a030f0106030605060901 74
    0x440030900d88100d60f8102c00704901400d901e410390b0b2425000715a00008101000d211048407904c400400703103e0700a8220740251840740742c1e4204803194054800039a081507141e80c40b040e40280007601c0f50f1090000305e0009240d025205590304d42000b5103402240305000030145411102e0050344d524403403078803004062141c45081c0c90301c4030480300e14400b001c0e80520740303c4440c43c400d602e003000c0d1903000e42260706241c20300d2450701f02c21501484a020240d010710300030a164450340041402004940900f6400039110000c008580d000020386208490150790303804181d2030282040c51840c44c252003601405d4000950030018100c1300b07440b0404400714034849421050076651541d14040851804a9106201c641005080d941103016554012002407440c0080300750401e20240c00c1c4014014041800f98040d240d20a141c855016500505623080407181d00107800c9200241582003102e001a00c0402c2c0b40001c11224403d0040d2012104081c00d0700341032080d80001980c1d0342420361104030700312401 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 494882922 1250 494881672 494881687
    0x41802030f01020c070b03160c020d06050a0e0706030510140102070f0f0509010b120a0213080313050907051201030b060d082809030305070f060b030f01051609140114 73
    0x103200070707030030014500c0005a403203254a4845050040c241e21000200800344100411480a00740c1050a03001503c1c1c07095600c801480000d40207101071001070300c818a031404004030002c240d48202ca03110000c40450380c00350360703440044041d0707a000c540c1a034005481040401001d00a4102800b8840050060300e401c81d45804018007084442d13403210407184101d5108214a09040324072502610031620b01ca0320700342520700d080c8400c0101528528901e03500056005030b44446440100143c903c2a050742d640da10903581d05905a00c1c00c1c015241301e020b407000451070140c0078608403428960f40e0b041c103141f10780c6140c0703485000c2c00300208211b8108181c202400700040502000742503035085180c0015040090719441404655002c680f0b0043c004c107040280003094025068926956002440d1200740040d4507001c000780c8080382e46250148a10550b11249140640005118500c01014400b02002c021000c58040c9583d2180c0b001307248000801c9086940b18154401d02ca00b40300000c140340203072 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 494884172 1250 494882922 494882929
    0xa02071716050d0222021305060405061b010605040207111e1c0f080304050109140d021b04020c010504050615040c080a0507030917070b0c033c040f060b030607020309041802 76
    0xe04c683c05c4800207600242c00320351107000305105006402e0542d0400d0070517050102051941c4655241d001c4003a4031000083d28040f42500490042c1501610954540d4900d103080648041d1512466200d401c0304d5521044416494490008018000304410190303081c20f208102d84c080f00360340644500c0c0ca17022030000031441c03180080d400b03944190f00025211002e030511301185460071201500750b400c0b034200003801c0740d800954003141001c20800e2400307403a07144001a000784203000c00d4190329424030041200740900481c40360310500018962900f0707a03131600104002c6403c0500c0c1c12012900c500c01146000b8100e0340720507030100c0b09090008e20344403141c0700c140400da44040ca03108240d00c006618420810b0400c0c91680000e10105c44505608203c00e00e640c0d403556610310040100c0d03600c040807000c5442c0c00d11165218401001c0401c15042c103082c1085e0144000d84190f0b501401e2095a407118240029010300c1811258042d5041141c000d0400020f04901c1c140c00c5440500a903038200980e4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 494885422 1250 494884172 494884219
    0x120403170f07080609060f040b190914011a040e19111902011401122a140306040203070302040b040b18040606080d0806040c050f0a02071716050d02 65
    0x6500441c005454840801007003c50b0040803540152500c809100150712003103140c0c8001d140450380865800c09000105a0f01c001510070040d103403044540025000c1001d81c4145101174001880c2c10440c3e0700d500c260001c00d40000309105910008110811a07501034550080c1c00c0034101c5000c01160300e2603026007060f00c90008070b61506410000d4480c00316020441620701c190b0481c00213014010a600401c0c00c4030714140301d110744034094622940b040100d80a0041d1400d8450241907080b1a224000800c4500c118060f01e40c0c10549800704205501d40052454480d42c1c2c014010580c55055900b0700024001d5400d440f608580c442910f074a46c1c2d035030304509030003400d010342030587c00c0d207014100501074070220b50141400d500325100010030503500c440100c0d404001a1004961001440c00840b068400d54002d81103400010491091069010499000316000b089141d28103200000705aa00c0f030001d0542e01c151006810010855410700826001840d8001800030007021600180e020907070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 494886672 1250 494885422 494885431
    0xc0306010e0316061b050304140f09070c1e050309040c020717161415090f0405070c020a09020937030b040507060e012a0507060c0c081212040317 64
    0x280c81d803605024440c2e011030301401d40c00801c444800c1510a1b6202c09403a48140e000f50483e40c55503610190158403400c659100b01c0380c01a0940300b540c40c05070070040030027a13560011030f02c440d50044841808200d248150000c07a800c41301442c503100c4128204401050b003005000b0179030260000009000408481c500c5544000e0400b41c405d803042254046c3c02103502e50440302c680c055180210364240c0f140080d102c184072072078845076034a0185400140b0003810031480a0792150510713081100090b44255800042c40c800e96603d081c1035252141d40059004000c00c89400042038070700105c14592202e000e100e0440081c010030304450341c0c01880414a0b6071a0000e540c00f40509083c001000f90800c05100100308130b1421140e40500ba10008020070500e4130241c040315520300c600310503002c0e40040400314a510000325a0480e584480144c0510717030b550401e55103044800400222100d0114114585100211906240010250810b0781031080035006404008000082d000d07450104102030707019 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 494887922 1250 494886672 494886703
    0x1050105060a0f270f0e0603070e01030210050702060d0204142d061215030f0106060206010e22110414040c050603040318180b031b150f07260408060c0306010e03 71
    0x302814818003006c2c07002c02070130860181d07204800070440b0340c20211629064943c110f941038052400c860040340d5501030840c0181d8080c00000f5070301c100c03041681c0203004070b44c1e059204800414050741009044140b245203c0034281526044013585060103410074041e610003804035043c5001d00c5080081010119034000400603090384214142c41c040101c0c403180d0382900000d11aa40c10300000944800d818842e0000c0441c0b4803003c0381821240801c81c0c408402c4040c1d0302e145d103540c1c07410144102c802003440c5034016071812801500804600e201c10b4810340d04100b401414900d07040134070055074001032081d4104020441c0c0d0040d6500e2100c202e50003800417900c904101d40f001d5a42c001140c40402080e4402d500120b514040b02175010035410b2560f00442e0640c072014030b4422003070301e14030506000080c0c0e41e600042c3c0c4400c00024004440101c20b060004900c1800441c0343c4950500c280e010b40d0f01542d010b440016607100c0c00c80000e40e4082010f26002060a42c0000840e02e0301e00207040c2d0129 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 494889172 1250 494887922 494887949
    0x3042415030f030e0303031504200a181202030c09070c020d03050a1202090d02010e061c05010305100908070602131205011a0102010219080901110c070801050105060a0f27 75
    0x1410391101404c1d88401c030403005546503042c86014072601c415004c0d01c040c00303151100d05803107810000e01101e4000c2c0d503603020f0696036220b20300c0c1300800c0c01c051058081d9412030f14407008180d806001604051181c0d001e002850755110f42c10812a003c0e0b4010041002c001e0030203200001a2688207400c00c10501c0782c4c07075554a403c031020000d042c840390011040c1c1501c0c414401d03110547d03502e101c80c02c0800c0d020f09114044a5100c0040780a40c480c24010400307504040c050304c40401460780c0001e04a078003900c2a580080082c2065005407102048041d00401c0701340300c3e41d804640568002c041541d031b6039030881200d075603907581da5800080780c1c80181c030580d5441341201c10f644104180800c2c0b0700d60900c02103150003841216030460702c0d695003e04041041d06000a01000003d520485a81a18040d0281c03200344508442c1d541c2d5100c1d00841460b542090000a00c0381407900903142007041680b40c140301040c5101084514644c200e400c00c0d84480501e001003c404c1d80011410080d1118180060 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 494890422 1250 494889172 494889203
    0x408060118021207110f0f0313170d050d0e010c0309140f03160c08030309011e15090504032d02070b120403180305030a08010e0105060304241503 64
    0x841c0c0c20050304614403081e00400a4880043c0034106070b561094650400001030700d10741000d0f42c50040d03407481210592040345900000143c0000203032540c090030311115103019854032190002540648680303003456010358004821103024901828005800c0b40000400815004007103080d01c40c0d03d8040d00c0425a00e818150030701400801e0500340c00c0d007140c010102c039180181e003a6504d00c15140c00d0030f007540200c921001001980f80f80c003002802c507035040b41d88908200303a0705402003041a910032080014030010040035642030080340036a001e005481e450607841c00840e00050200240120108640c6e01d100c070704410580c80030183c0541c076a059120324003180280192418449401207000344400b4000300c140030080c1803485501513414541010300083c10a00c0b0104600103800c020b000d4000446c40f901e420790301041c4c05040700d03075141e0011503999a40d810710980d84400d80e009800f11000c04d141d440c03440c900540000d501444600f000400800906490030f03ca1030030340003196990303c0020303104c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 494891672 1250 494890422 494890439
    0x30406091103150402040e010204030b010f05030d0f090b090f0319061d061f080f0d0801062c0109090204180c030e1015090c0f020120040e13020604080601 68
    0x1c4245400c1600103040b070b1030700c504010390380c081c0041c00240302e0742c0c80b240c0035401c1c0e107000c0d01a64011584400c0704103055031185010700c15440700c0c0c024940a485000b403843c0f1842c0c414540301c0810102600c030590100d0410110720440c1e40328254540e0020005100143e03075880402c01101c041c603000610800354403107803800f0380c05da03404078030141d0351803c10b40058040c2044c00701d5016040441511604a400c0c00f5002d031000d052015400364010f0b010302c0c50324040320a0085000d080010903551a1000c0341e0700c1d1035045d902c5920100d2108240000342c100161400107004890f031440700141006003640390703140e03c10420b0303902039002000411401e59800340300000714003c0c168010b0041c1000d12083c01c01b442040e85d10000c208042c18204c0d1110b40481d5261201c0103410040c00b44e080d405e100356424204041e00c0201880a4400150b2a00c1124149105100f00d0700003038003003505480b46014508249004490009401e00482c501d82405a1006a4454004000030404040605895850701c00b11 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 494892922 1250 494891672 494891693
    0x1403011202041109060a030203090c06041512050c1215040c0903140a1110120218030f2a01090f060207030c0608090309040515030a0302011b1403280203040609 70
    0xd900705000c1c01e00c594085540d85e002511181c400034038005849960f182c105a190800d01d00c40d1682090b00043c3c04a0050044401c0d24512005070b1103601080036000700402c00c48604603100e02000c00c052000380110f85207030084540240b0410107aa40b21721281c1c00081c1103481d14584080414061001001041506200001d1403000100a801490003030703282d05080b141c01c0351300248540701e140e01000b0a18000c1204107044800c0480442d1103c1c40190780c1c416030074030306040c0c81c4244036004002c1c2c003101c4c0000741c800124600220780d1008079650188400510300110096050241358100403503c4c1004180e028001c1c11304d03030300a1100e00d00d103050003403070042ca541240c07080000c1a002c0104440c400811a17810500c103840001d807558803102407090f0640065103103503050140300709903014943d0540000c3e06094043d5611a2400028901a24824500000707016080030034000601007041411341d11481c01d0003a20004240c0132281d212004991013150f045519a07500d8844200f4030041100c0c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 494894172 1250 494892922 494892941
    0x207210807110f120a18030b0a0e0318100215090105010e0106020f12090a17010e100902130b0d02060a05130512100b1207030807050606060a08011401140301120204 72
    0x141501103110381c0320316101e4080001d41300b90340344001108004984103000790300c01000d150302c40700410f64881ca06418a020180e40e00d00c107071420300540c0d548906002c01103070151f2205050010751403070a001031043c6919003800240c190701407520140c212018101440748140c0e44040006165030622000c2c0360000c8068208008542c84220340c40c500d41070005200400d100780c440f55a44070036102c0009401440135400400c806901266026008101504190f802c0c141c1c03502500c880c0100311701c05004440003400048d502c03004c4c150304240c000300103a1001a083c3c8001d000c43c07005140c1d540100c1d0155100910100000386c00003601c19020403603500200141104a03130301203040201407480c6035150020300d0018007856503861851915900c5900e6060760300301c2d210545200640e0b07414164030580000200f511640201d8000070303054a00001110742010581e1140c01450b428069400c1074500111210f9061111540c48500580703207030700140d4020304610044046250a82c818442540e003d0f0300c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 494895422 1250 494894172 494894207
    0x5030f0102270a090e01180302030909160e06130b0a0207060e09010b0304060c09030212010b090a18080a020102070807060e0f010c30060b030f0906010f03060207210807 74
    0x1c09000040e6200a0403001329001040042020b49010702035034014440701c1c404840c039403038854132a42019000f0000e800390910441d202411035940200c000c01994420a403140051001802000c51b8907140e006450f0403001c110720b42840c0f5842d20440201c039440800501d000d6030001c0002c000c1d8036801103021729200404c1c1d41c034940da5407505403603444500002d04001c01c45601c910b01ca0741058480c28036200110703001000e9041e148640c0610a008252403641c11b030041d81518009201c140c454042c2008442a80c00300c0c0a81c841030361990440c41d0080154541155020004e100100310003501800300140140d0000411003050002c151900c140c00e0036aa030f050f410460400c02070f0350081049500781070414140e9004005800492202075640003104409914080c8082070706000c01c0b01641c403d0051400c051a6601c81000a86e9214801d1058655a24040101780001103464004d4410188141140c40c1d58965540c5051002d59580228a00203080c1904100f16160304c82e40b17100194280c0c4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 494896672 1250 494895422 494895487
    0x40606300311010b0a0e070e010c050a060509100908030a050109092109080a0c2d23040c020c0112020a140a0c05030c060702070b04060806040b030705030f0102 70
    0x4109240e22100c0e9003001505000c00c1844003041c4103000c2d00b0801e5450401409085000e440d94844203105401340c940200081c01c0001c42041940140d80407007805410400130451864107588201c0540001080c4c60034034000c4044c0100d0100c201d0042c1458980b190a44ca0703128901080600c04880c4140e005ca0f00280c100790800000c944a046000ea642c0c40340001204c1142c9d904c202641c0300c02c12903211402ca8071a404240b0103101c14002c15005503850200702402e84640c2e0f81407440c3c2004940c81e42c48451945400c03c111045002c01c10400c035200100c85070a00c025080c0000b022074206603407020142e08504100491580c0c00004040c40014040c000c50400004030b0b8020004502d820141c41030780d4000a01812890046450b85030260740034044984e80c030380d1044c1540d22a20183c1c4e00c10090300c01c1e44000b06541d08100c0c2a1000da5440780d44088940d9107610401003e0100b02036020b4142c05000c0300442e032510107101000c80090103100260380c41c141e10510301c04d001c4003a0b41e52402024070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 494897922 1250 494896672 494896739
    0x1309020105091908100e0c01020c0919270c0e0c091512041b150e0402070f0503041203080604020c07060c03030b04090f0b0a05100504090303020f03040606 68
    0x1040c1c42040c00240d5800a41d955070700f281c40f00184441d04010704034450526031110030b013415080f2440c05408503050f107920680c0c020040e03907603401c4041d106074001a6000010380307000f00034100002c44616481c0109001b83c114144803210400d150706c811100402c00002e03400d006440c038155004001103010034499241681106442d402902e2109200300c9508100480c3c0744103201c20307100c0c0600b42201007034060038103241c8003031800b49081e5a150703c40d0210400240011600d2440511a8469120490b031040b44400b044020b500010040790b21007580010719000c00c04c10805000905100c88074880500901d0501610340700e00106400c0c4243e00410a10f8039064022540d032040314020b0800c80340600091509401403c000500700c1d0f01705280c00f42c1d503014401440301803507003a03005080c0500a912034084580540e04102c0d11800b51841c040002c0005060a9005410f2140203140040c100b40f900303055142c0907803040d20f05582c1203458410500032000306550254480c3c01400c1c8803102d403001d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 494899172 1250 494897922 494897927
    0x320c0a0b0a050f04030b01080f19080d05130f0302100b24031009050f011d070c030e0102070e10140901120f080d0c0f020f0109020312031b0c030913090201 68
    0x50300041d50100080840d101e03485002407403c0e940650307403200d404d80302503850f800c0e096950641d2824040c50780c812075000307640c0034003144203031712249805c1004540380c6005145a440500f0b400303814800c3c540000310812011500500d414000307d4840d6000d45520100300d0448015641682e43d0248075140e02c1e05241d00c07007920400a600c00d60170405040b03490760b41e00b03088030342d000c04581c0c01503001600b01400c0082c0140c60340e86582c183d031403110000750002406a0359902d20102141d100c40801d4002c1410000b09001d140313148ac01c01c0e014411100c10580762280c0c103c40c11030940b01c00e81c16105c044000e015040d010a020300d801032040d164401203615003021a802d40000040180044400380781c09024856000d045428a8190803030902c5030501e00d180c001c0c840780700c0142d00350040c001c04001d1a9641c1042c0203030b00c12a600200200581c60008200e01c4d05a400900111641e40c01100a000080060760251540004c0300c805951a409070383c00340024402c1e2120094400c80c6010000b40c0141e8 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 494900422 1250 494899172 494899177
    0x100b030c130c050708070c0602060a0e030a0c140d170c0c071505120103030c02040509030a020c010311120108060a05090c0904030c02010c0803010915050906100804320c0a0b 76
    0x10700c410000b0900c1d2107200d00c15940b07441010320142600c2c00004510044c403040f9608502116425030807200c8540c2c800c0c120070301f144c03289001c0c40550740080111a50040c8141003503599036000d982480c28408143c00ca107443c20f248000200045011040a19581d8030546600ca5000c0d48a90740b1a20345220000c1043d2541824014103101e800f0315400d002c4298419015070341800c03481c4c0200030040d610b90601804940c20030008910a07801c1c04002040c2601c080107403110320001d03800800500740040019800b90945402e0408034682c248003e0600840804a080c02002000083c05e61800c0144101c0141da50040143c031031540306035440c4802e070320b900000b00d5205030540340a6034100d5180c4012030b00401d0140300600403c0340070001084040d0039074490343e5030b01c131038200c5402d040341ea0303c05108440303808035070269012106052a14404e4050b01605902520402039015031414809052012410040c50035590002c000203000340c03000c0811104c20300344400c8034000c61292910b00007170f2262 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 494901672 1250 494900422 494900449
    0x13061d0102030306210709051f0605031b0906040f050319030807110109051209040e0a050a06050c0c01060b0304110301051315020f0f070b0106051305090c09040e100b030c 75
    0x81c0c010011341740000700503542c2224140050004c2d04d0880340d9901000020b0207042d2010007004424071f007014184500d1342c80e81c408070b6940343c82d6207040d40d64489111200410704040410011420006d088159990710f0082001e0302105010f0382e2601e0524090510304030b90002111030030b107090303c0d60a02090300251a50b51141641c6400750091030318005103400340010590091007403142070045580c1d031021502030104007905503402c0001c003400c0070101756a2a503c143c0903080c1e81041d01900042145500420ba001e60a001d81d1842c045040181a0840d00c00c5c1d40844c10750308c408400d010400c203410704820400d001c00c40081c085410003100c0c0b000580e0000e00000c000400350b88501500c0825a01610480b080070040700b92545030701142d440c2c05038807184045540103c03041c000301d040c6028a09841c014075402c143c8441640c241402e010300da10015004007032140d8284500300d100d664900070212916802d1001e000b01c6c80c076004035041a0b44190b0f403418031a03082000c0307030703802ca4a0b5140b011717220 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 494902922 1250 494901672 494901679
    0x607110904020105071b05030c0a063612030e0a030327090e07090516120221150901080d0e130902060c070f060306060e0603100b13061d0102030306 65
    0xd549a600c016909441481da0041c0a610f580c0108201111403440c00005c5600c140c0035200b602517040200406084680106000b1808440c00400c486042c2e6198010510981c030703100701d08852080c626480c0820aa000400a100c0442d40300109607014007245901034050b122140e10b03606540e0040c0000030411004854851052181d034107001301624900001e08542c1000c100304039488004945585844c0200140b00e030810000c100d145000c074003215038030351403130b920071041c10030502900b000b13580080c40824503801009200e0701d0580d0070f110800c4c01001e22680e58207000541c4814001c01038016400030700d460700300758141481d1703d0300a5012207424408955106000d000728800030000d125051000c0d40043c00441d40000780100050550140c400381c00c085a00360350340e00d07402c900307a6504e0f0095000150440448482e1400c140d005540c100e41401c0c401982d1b00d40707601007066540c2200c1030700352003180c80f45003c00015422000039411150550452800c0c2c0d040700e40080d54900c000b501040c003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 494904172 1250 494902922 494902939
    0x50f0702011805040c0201020c16080a12170112060b01020d0207060521010602010e07141804050f10290609101101020a0509010801060e0a1413090b070806060711 71
    0x2c1c00b09418080750107440018400c004540c560740c8024000c2d0803621244006104084403940c448150f000080308444240e4000c0c5120707002e941c0d0f00407105402d20140001e2241c1c0002101100b16080a840c3c00f90060398144000c5802c6030601d01e0540d6100140f890540d0002d040912807039902058071002d48480d410000d590382011031200500781d51710940b109401001c04008110381c0d41c107421000c250303000e68044800c040d03202c0203200c550916507034540c3d50000044032120100d400914009520901a80c10344030003071404841141026461081ca58140d035484c0d41d010410784000c81e40140070302d0303620441c60350148540040390382c52041b400900e00c01e400958101900b940b080400620000601c07000b9074540503a0070002e42290400052170740840c56800000c20014412080740142e00300050903100c8444c5000200e84410a5100026400040d091407650410103240191280184200d01074400f5142c000001001018003030311306c51060300b080080d1000708210300481042a40300302c1302d120 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 494905422 1250 494904172 494904197
    0x703230403020a0308030609011703040509100e04050c030f030c210f040f0f23040507030e031c0f18060203060f04061211010305072a080f0a030b01050f070201 70
    0x80a0049500c002e6015406080c048100300b51034018502030304059400d06a980d1322401100c0d0300a0302202030b601c5990003840104014684070005035080068450704e4008180c8410560070316100840d03044c2c616034800300c5841c0c4070781000c21880602c003c89030041c50800c40c810502c5e0780c90742c0501c1010420f0400d02c001e070301c01a270400d500311b8000c0031000205940c1c0380e03501c454154520055200750710340d51f078858500050101d0b00c501c0441c920924a00220b1106482d4801c00c001002c001e0318000130107548404100e1108010030041802c0244a4003064400c02c4a0301d09101380c1e034440500c00002c81c1000820140c003424607030000300b185d9001101585030b03583d18010502110f042c20038250b00c50b051220000b82c107a542c40d0100c45207070040181c02401640c00c4010740a5480039240b0b00300007901c02c0f844007409980d00140141c5a0454404410044034980b1010400e03000061500c5040c90000358410125426204542c1104828200103040c40e5038402205454084c1c2078010303051001c0a80c080 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 494906672 1250 494905422 494905487
    0x5060f090f0712050f0607080a11040e0a1817090a1d18101a010e010c021c0611030f16020a1a18010608010204050f01030b06030a0207050f06150906060703 68
    0x4544985c541c00c1218251300d01104002c082d500f00340c070360030f6401345030000701c2d49046041011101960615070701c03000c1a072202130200c0300504130081032005905039131011100080c0012510019100e6880c019500d680043c01000244100d07070340010a4020071042079801f034807020182c150302c1140f214581c901d51038a0310085080c044074130220280325103802406200180880010124240c0c00c0e66009401d6210600560305c100304140060340c081c1000040301c44246d4180e1610080034402d05d1702240c56001429580303410b400c15140200ca03071400004008000aa568100c1d00441661000303102c169000c3c1c03a28500d107142200540041c200400000e0603005c01c3c20312004c05910148002c10403d692220028002d41050080b20300c280c1005402206941c0b103801600301040000301100d26507180d00c44140002d600c1090b084810b8052000f0035210b04009000c403a210300d0303041c03c040c9503266014040111000c0c000341140e115aa080c05680c01103030b4402c0003826844110810140d09003c400d951 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 494907922 1250 494906672 494906683
    0x3140d0606020d080705030702070312030905160801050c040e070807142701020102091e0a0308071a0109091112030d02070309080609010b1c1e05060f090f071205 71
    0xa10410506120001665641c0000c0700102c021050340c40301002d454000048450344810b60310000103034030800302070000c0350700300c40e400307030b012045040000320215030707a442c28107284159032100b2940c02821400c0040900a0041541c003070740d1b0840aa18180c100300350941a070030007034044400c002154001580c514015051201c00c0b81382e07000b00b1510f81072540d041d80141d85180820003040280143e1b014403550050082c2d404541d40103240d0055030200c50030848008118405243e0f0105151800001054902c002440900c0c00740ba04414090a211900d400c1520181d100c0a00c1b01e20b080c61036000b044648480a000c124200c50000401c401c000003d440c501803c102d443d03e5500c0080c0c3e1200705134120100e207003201c403000d09551032903803998000340c22600900c444a80080c4c6900849000c901c142074110301191054180d002a104582d00c54500b03c00c98000889484d40b10805114401c062400115030280fc100c000f094841146508980c03181c20910500441520702e8007480700b00b02c0244034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 494909172 1250 494907922 494907937
    0xf080702042d060b0d23041203060608041707050a0827090129130b031f0521030904020309060402150307050a0f020a020301060801060f08010b030a0314 67
    0x41400741040304224004542c00c1280141003841e4010400d0404041070300400c0c007113401e00e00c0d00c1c1d8140308a9401c010301800041295a00000c42c00201e03008000e41807010a00440c0500c080d44050001c0c0700340a000ca0b440e6410500178040608104000141805422558002c11240c0143c6a03c10340c0340261134680030704130007081e5060214009000e07410001c24030082400155064801040300402e108181c202800303560710031600c0080c542c0d010580c041e61078591104401003c0d20703160900a9201c000d0032550842c00070b2590020500030780241c010b2510800044100706101b84c146405d00045050295503540c2c0500184c4c18407445e00541c0a20588070000809007080d5502d103400814503440310404ca50481c402c14100d54650020280c07075050b02d200d90a1900d4203882c1c1243c0080c141c841c0110b411400e0304501c29481c03011300688082c00f4000092410710004104141482404c400300301003601302407401da241c80200342c0170350360000b10345580603054100b00110074541ea00e1144c1500c00c140 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 494910422 1250 494909172 494909179
    0xa06050f09130203060307120b070522060305010e0c031005011407080f07020a12080301060c020a05121b010c051b180c27090402090601050408010c09030c0914040f080702 75
    0x4042d504900e101d40055128540c210191000a070b11010001184203441101521040401c0006038029000e107000700070115420060755050081e00200c0c581800c245c3d00100c0001b501d8000401c0074003400c6010940040140784c0391411032030050105440e030741040c850b441c108070035040e40384443d0707020310121442150066034840e50348580c0c59640c1c215034440e82c0c0c1240544914140042e00000040b1050521a48020402e2a40e441c021081301c5034080500181c2e80300c240e1070800109662500800d51000524401a108814401354294216040344600f02d06002005507204006000461142030400c1c0e5a00a03c21890400000c00c05000301d40030741c021904d20744420300c080d4500842c05403e031b0070f609050301c088032003246007501c0c501c0568403a2207030003000503008680140381003214a60b2240061400c00c0c00d1a554040341d5081d9404902d100700810850801441808001d400c1600a0300c80800140002085c1258541c07408000410142140300003120800030048a1001c8030007154005 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 494911672 1250 494910422 494910439
    0x6010c170706021305090106081306060905180c061c18120203030906010b0f0403030f03090b01170f0111040e0901090807030906030e0a0b0c0a02010f1d070b04050a06050f09 76
    0x20b280c410b00070362103450a6800400316030400101c62030f2003620a41a034000c0c2d600c00c0d902c0d0f21070310030036510f0507500390b07080347c0307513901c071345010030529401c0c071071644a084007001404e084031070b0390601803c0003506082140600400c002c00400d42e481024644401c0000f5900066901040c240320710500720070800040220840312060484c150340080514080c40001090b41d040b0b99071005001482e00c90240382d803c3c2824140000c00c08a80109001c812030340c06400c01180c110780c7c0341d54509807003a09070014083c0d80e104658424020408100384220501c0c03101c001c0000e000605c6844003640950710401514620b10b900050824100703401500c5140d5110801c16221001481c018080c1031070740c000c06002918188a0310803408000540c40754282d040f1003030140680780d11414a40d2039020320ba00c4800d41d0740765103000358580490321900b200014040ca442044094641d074441c00c00c0895032100840b1042031205100680e604100c020443e0030900b0311b81e5955003d44ca80300150300070040c0d15603011448 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 494912922 1250 494911672 494911687
    0x6180b1e180a06031b0f061d0a03060516030e071e08010f1407031a13060e0c0711030a05060f04031e020a0512040303090506130312120518030306010c17 67
    0xb150440820740b4070988a00c00d040d0b034880c0200003901807510441207603504600080203058020075030400b0603c4000715090315054000042081c0c088a42c0c41156126620310801c1011440c1c14440c1406008515052000d548801141c990f1040ca1380281c050911900e01041d0544038880401002441034400a11280c0c00040841d001000410360030001c890000001844151080c0b1650b0200312a1649000c038182c0e002d01403210060001000c4041e446d0740c0c0c10045061420f0301000b0b403140d0b0b5080c100c00c0d40c4a5061510007640c1860102c000d009501640c40c02c000680003007006940142d01804107140c03580e50b030400700e40320849500c00c00702805c0c103908111482c590100704030725064000e2040303030600c0070300e540503040500c01d038030002d400900509414031140c0341001c018004c0504100000d411203869407290030f42c800c501c0b249940070401d91a06000c0840301030007053340c40201010080c0b180c4607200d466a07100c1c07000a04c0e0038104034014130340204100050340c00194041d10400d246880c2c805c03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 494914172 1250 494912922 494912941
    0xd03050901050c09130c050c0a05160f08060703020c0111071b0b1309020d0b041407030e0d050901051b0d090320010e0111070b070606180b1e18 63
    0x81500c22500c01e508202c00204088100c00403030381c0b440b1001c1c01134a0000074000500004181c00b80d56501000820403000403c10810051003210034011000b40001c100b005122429861680e0300440f800c007100d41040220950205605912540302e003009030390340e0f42d550202401003098840c0030341c000401140b10b03000e02403081250070740d890b080c100502d207060301c541441c861401003940420074901804c0045c080000150007504080c0341414002c24806a403d0016094901d0341000c50f841d41c00441c200703c0a20340c9401405900e503006005480b69120f40800101544201244107061000018020354884003441d007905080d440725050f40e088d1440c01c0340c010701c8203815110a40700e04812a0742e543c4d28054481a1903600c240584030b441440062030019900041030186023102e0f4080c203580050304140c403800501d44940f04420001d18035040c490001d9043c00c000700d4000146107001c4545440d41c45070703038000c7c580d800b42c41700004061421340000340f103100318502c60300c0d805103c0c1d100f800000007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 494915422 1250 494914172 494914181
    0x10060e0909030909131b05040b0909100903140c0105061903020109050f190b04170c0a0509040201090305100c12090507030b1503011a1212030106080c041e030201110a03050f0a110d03 80
    0x15021203003406070071540c5c80ac10662010681e036010761500000c052190300d6110303501103031070f40e4480e0a02201c00300340b0f40102007540c0c00c210380c144003d94454040003640d143c8000c2600b00356680101c4e04e5495070850b000285100a6400307600d026081401c1550b035180e46100d03407201d28040c20b2044542031515890300a0b03c0b5003051003103000c0c9200c0341012203c01440802c0c000c15440004c0d05100f402c0d45800c00b0080c02040140050781440307141540440441c0051125410042c0000800f00e42207112200081c4141c4450128102e02ca140282500000d14049502000c40c0d41056200d4030700d40b230310480d90001c003e03149241d82c1d0540c030303110013480c0c80b05100f40707009078104003155800c1e910030079032039460f41342c00510b032003540790071002c000502000e80144041500200c0900c807007814252a01d0380b118105001c040d00c6010f21400c4c040400c115a4030a0100c0e079411244805000e403920107a070064001c1c02f9011442a44000c00b04005020510070300e690501001c001013241d500d0b5060020140040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 494916672 1250 494915422 494915429
    0x22b060801050a0209150f0f03010e10060306030809010f0e0a23090c0421020405091507030b100e03010e01090b0901050609040209130f0b10060e0909030909131b 71
    0x1d500700400191444000e2007038954403200545510134000e103c5040c1320302c0e40d0043c981c50741007100911111045030b8522010394007a1840041d46011401d0000701000d02000b0780d0b2000b0304060505105000080005003a504605028245011316100514050b02c4501c203100300c46030000070030480001d222400d1004101306d02ea451010b0280140c981080c4800810308550030282c0341e104002c104103054a4150130310b01f011220b03a00c0c0c03405c2659070340010203603241602c050402c0e40c000e4500c0a00741503074120745500200241420009900180c000c80d01c0401480c1040c418043c941c846070005403001e400c15642c0c150381800030058100c007440c1c106200319040e076402c1500d600c0c09001490604010380e20900603030700280190b0650b40ea6041d216040070b10504111258070090109000103440403c55a015414041c90300c00c1007810200020701c4201024035113441600b0b031400340040c3e4840881101c3c2e4691064516166513541d001da105400448140018030280300035004810411a850140094 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 494917922 1250 494916672 494916689
    0x60e130f1a1501030501080f0601030f0305070b13150606020c0607081312170306010c060203060d06050a02032215270515130c0e150d0b010303030e0f030706022b06 72
    0x1750342c80b06e0000b46e6030540c064512445510040c0144086403001661fa4040d51003841c1c254600520356942040d0713400103403422000e1000280c4404200652191400a407043c001c07810040c00e440c1440080d580ca0744030342c01134003908d000903080c0180040031007101e02d6030041040000c50b05c0d940d0f81c1313086040d02000e4003d803164498051080e0f424203140381100d01444059503588a4503045441e004001e510140206900c091800c00300030016603070b03000e260f2140c00e030b20b540184c907450545031001f00500004a2860756840300140d5200081c840c0240e143d8044403481c0000f805110554990400171445510b203c1c0002e8015035001000000100214501005c00b4880b87c06e440b801c0030324210120020000b0302002681074284084410724030703c1e56003c003001d0300100985140318049490511060030075142040081c00600c181a0540140310242142e40e00500d42c0c4051040440e07240e002d1020020300c01134000070a03051500030441c0185541d907040c4d448540196040f200c2e1380040c10b0741e2091595 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 494919172 1250 494917922 494917931
    0xe130609120216030c0506130905040b3c0703060515190302090306070e130f06080606060702060d0509071505120f012313020403080d060e130f1a150103 67
    0x3180610f400d4038800c1300c0e44109204600c605000401556400000030343d103401420490001d82200386004460140d809a180b0035406d003413190341c1001061450703200403041c0003121007005211012000b250039036091031034650f41c1911991403c0f8042c0c40643c1c88240d010002030000854000c03440f0042a00174401c0c40325840850600206030305030f00950f0141d59160700424008de000034060241d03508400c000402c5104401c403800003030310443d000e20b00b82c000709956402c41800b60003820040d030b58001e03000715503003070401401d40e0008100c0e200d202403c3e060780391181c0105001810401400025150703031200d188190302000001462078200f8200c8000c540c0382a00442c1c141e0220218040c141e815202104000821584804240322828080c05030403100c452007a160401c040c6c070290024510883c0016911384c02d607050b103010742d403140d001010200c804106209880c00f0000c41c030400b941d8011400f0880e00d021b800c0041800001c001240741e2580d0803810071510055165042c1d41d40082601c0810 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 494920422 1250 494919172 494919193
    0xb0c0c0d0b04020d0c03080301090b010210140402060d0204091416030c0504060522030c0e0714040905071115100e063001020d1b05030609010e1306091202 68
    0x5618006610080d01d03003030754000440c016040402244030524007680c1c4007100140d5a660300500d50740240d120801ca5036460014407074540e4107001440640d8000c6006026603201280160908500034000a108200008100e541030580c0d8054038024062000200038800340c000d5041d558200498a628001201460400702d0742e000b8401c006011000d5940c4a007440d0910205480c0383d44480e0103100c030380034034a0360144c08081c032920030781c0a1841000c001e02e000d45030483c21840c3c0900076040000340100c06044904407020352041da000c95040389800700d01c076129a40251003901042003504441d01508012030048081e0302ea000f80143c8840c0091101162344078411003442074103568183d80324000303020050104841401d4440050101c40c103681011181600c00350880c0e000c10441c81c0c403981c91324009918680302c007881002e9500241401403135846d04400182c03400c003050069528419903c808103110321000d4900c041d00a0742f0000c2001005c1e442c1c00d00324030803200748004100503c241b02511 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 494921672 1250 494920422 494920429
    0x2220b040f0e060a050c07242313030302040302041503020f0102120d09060e0a1b05010e18040809180123010f030e0c0d0303050702010b06040b0d02220b0c0c 69
    0x4810804000d05a80d460711131400d00940400b41000c0c40c9a003044c00480081034440e0359a429180007d14882c101e03002d0242c1c0b10055030050501103a0800c0040b01040c1c90560f0440d00692180c41c60405508401851074203600901640d000a5005845c103000c0003103480c0540f48040503a8021145100341c1d1039804012696170400350610a15004188490410203905420941401d0700c1030001090900e000b40c0300c2d0345040c2485000741c4200301d10100c1d4074400703854605494003a00003032824520303a07281c0401080319134a1842440108106d0321300000c05200d2810240c0761241402131882200d02c9244840404483c0c00f8000c0760b044007061102844019404c00360768a4078041a15241c01105184d00280e0080c85000300d006181d000d807880099a99840005803c0c03034074840d0f00c0001c1e0b507041040001f421113161303200c154080d0104010501c42050300d1401d40d2003907200f14a000d0383d684001c0764189041c4694581e640100030440001081d0440c2e520040c00f400602ca40859001c8020304041 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 494922922 1250 494921672 494921681
    0x3006050307061b150207030210061202090613060b0f0901030506090f040b07020708060a0621020109140f040c0507050613110d030507020315070908060907060c02220b040f 75
    0x804011900400c0d450038001036071051011194041e043c1404001e21003842c16007603a020060480050700222009d4251080c03921442c0050480ca266a0b0702c0400c8641c04128101d80180c02c07644a09001d000f68142100c9940007500504101c00425440360110140c200702508001c02e641d02207820140010118103082ca8042c1c8a0b64008507502580d4031207403290b014a0300081d007000214040c504002c960b90008114550250300b8160001401c1850618003000394280c030444000031012481d115070250b030344094080d0603180400c070040101c05c01e84000614a880c5591840c0e04a403d1010258070103070000041c1004a000c0c2040c3c80555881086819912600701c100a1030011300a00d4000281019110808101d1003400e200e0715000041d00080d00d800c0e51159414010404a42003102c5030340d120300c010005243d46002041141080c03a6059241c0718140214010401964070303440c25542c45c440c0c441e00d643e0b5002e69070070b80b468000c01c04d40054039650503100d000b1802c1ca500c200001e04980304 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 494924172 1250 494922922 494922929
    0x1b070204060f0512030313080901170112021203090d140a0c03050a0516060207031e0b040b01030c05010c08090405040c0e10051906170612010212160903050d0509013006050307 77
    0x41100c03841000ea0342c0d140c60b602700300d245a0404c04d180d420740046401c19000310317000e02a80190400306448610411200c00c0d0140d104041a0300103020151454445e140038200d00d1342d101c00410341882519001c940b52030342c84c94024011000042c3c00000340180412500d50203801130f07040e00c80c0394030340f40c5519101c040c1c80c2c416000140d01070b24042001c00c1015410100c4154484058003115009854030076480b40b058030151045004840100b027040444074490f0002c050a08040055000c03548070311844d4040c43c2e00f018000c544031b200003000c004c007a2900c54050848404122042c3c00c1070100c4500c100c0950045500401d00c143c9510407035582c00094900700d950301d0761042000176903a04a00b0304131201400c019004498451160032101f8280050710307142450b00c800c0d1606260007581c0584a84002c0d03a04400c0c084001410300218402144800c020081c0b41080c543c0e540a29004840c01640e01d8418007071031700c1d01d500030b103141c4505c10300c003e00c0300741102000d01120352144100341d1944078510 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 494925422 1250 494924172 494924191
    0x40f0b060304060e0309060f0a3e0102070807050a1412191101020d0b0108010e040c03030c03050910080717090606012003032e0e1b070204060f05120303 67
    0x10020300011200d0b00840c1303c2d15072010641c1d040c050b100d8040f581a07000800f4240400d440828090101030b8002d4402030040c2c60065504407000c40800600a42e003c00441c045044034001204845000300350119900300d5401a4075a590f4841d50030240d4544403448000c4900307440c02440008074980c00140790f1442407003030f95080c1ca060700f01c0f46140240c0300c2c10918401404494401004019400c1c805040d06c045801ca0109910906000050981c04141c1017440e5040341c60702031101082181800170240e96041c00d01c09540d1540d8102a5030501078031410359800444528400c102d564062840340c01010103844818151094020b503a04051007115a0707041940160001080c56208006d10754400b98141c120407028010150080e08680c002c4610585520000304000c044000d424040c0e032105600b0780d05007a001e403c10300010401d050140525482909642d48902d680b000781c1c1c1240c5110f50700500812641d9075a04042071800140d00c00d0b14440c0d41c515030801046031010048032f10451800 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 494926672 1250 494925422 494925427
    0x230d020c15180a0303050c0f030c0304031b170a1e032f01020c06010e01320109050409061b0e090c0a0203070b010e0910020406230913020306040f0b06 66
    0x2407401e00801d41002440310716000300408261102d440d02c21010002d513000f0707903030302d5034810f460400e444c074102000403210310552003007010600e050004403ea0b01660b41c081d81000300019100494000c07030ba2143c008004041c4074141ca00d04040300010068240c910a0108070305805156401140000c0820405008038041d0162000540c4000403031060300c9604114100c0c2485425070807070b0072a00443c002a0f4190f101d800107002c4d00301c00310300450045c8031141031080091080c0c1031105040d00c03072460f2840d0f40da0348003814503981e03805820701001034000644104034100b4a4140780024049085520058240480c00c1c0d00c1e1491103080e41d5010611f01411800703054403880300510031a401904050704602040c08000c000030481c20956000700304400400c901c07030034403140045c01c100401d007103445810700c10002046060b8010000c100340d0710b03441000e0500e009821604031038610410701440ea100d4400d070440580c0b06600c0d409940075060507242000305060489020040380c400c04071140e40041c00307 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 494927922 1250 494926672 494926699
    0x918030309010e15070e24130e06060a05390a120503100303050906190906120c1d03010e0f01062408062107030b04020414010501050301120609230d020c 67
    0x7c11f0a0399000e100500521150f41207010311f4005504009010040b0317401078103042080010354900315070007620403035040d407a00700c0540b03018080e8490340a40104000c1380403600da040d0840940e12881005c1c1c0c01081c0b07202c0011030500c00e919814190003c0300d030070341106041c41e130152080064a11801188100802c0e0070b003191425200b40e0082004550301000c1040206110001c00f120b440b00d09140fa05d618400c60b040c914041c01d1264074030b160f80e028616081071212465800300c1c40403130740c02980d651142c04903100d2011a026002e1b4805984140c403890003d144a241c05510100c221111490040801c98104012044c0c0303c4a40b1217581c00130700140c0c041010341ca021107510b0040f50703203481d80584200444000342c0c20002d8030350054840794601801c11082d400c1c0340c0070b07401c6032041031180c0664643c18030001030120301060207411506e00c0ca0314980410444103622034502c1c25002861103a20840070340b07020342184182c0013546001c2c01802c00001900b400000c941c544800e00604610400d0700 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 494929172 1250 494927922 494927929
    0x2070317041d070906120f02070f15021c0507110f07141c0314040e09280b01060809030f0d05061009080d031a040f0c020601120f020918030309010e15070e 68
    0xd0460b200706203a0703440d00410301ca029503100404980c0d1280d0f080b480d07840700c182001c00bc0481d04011f0015124010019045404105001c0c900600c1460303100007403544030f1010072100388003281b801e44030030300c586900000c2082c40080c00608a80881c0001e441d00d105c0d01003400503048101031003444216046944000080c0504100c0305080c5d40800d01d1810030b9911005401c4a000988260440b5040455a00103030481d02920009482080070311342c24103841c0c3e030343c1c030007201105220b100204220100031030060310060040354504154030540c1a1140c2074070701c1560007000150769992140585100703090f4014040c1500202321006c920291032401080c0100350041d11905c03030303090300700781201034001d185940c1c038454000240343c0040005496412280060703c0d088040c0c01c1600b101c120b09696000044a50118aa25540c1500c0c0b0014644500000055604416021911318007011003004450b030015402a640c601d0128100c403540c6429000b58910010183c07000340024026200d05011405c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 494930422 1250 494929172 494929187
    0xf050301030b0711071404110c0a030c02030c180907090c02060a05041b15090b04080d030216021c0303061a09010f09030b0a0b0f0307210302070317041d070906 70
    0x10312400c100c02240c941c0c081060409040340c00c2500c1c400c00380310700003015041c2807217400c42d100700d040310b21803900f43e180270f1070742d600c03094072030b0045c1001183c00b1400210344042c0003e0900550281a11039801d240204502c290b40d011141102948940c607400103200c40c190080d0742c86411a900501802e0b1100c00380c0c0e5000d0880108117448440000030603030307330000440d90428000c0c150440b0489030581595001000140103902005444505100501004c0c5002c07480381200ea207103040047c0c3c0d0b00e50240750005800e200c901c010b9840040d40f0082054406402e40440219109039001c020490b11103815000800030715201c904118014031001b212540209246181800e250812412041d40d0366201c4030010700c110744e4081216255045041e40d814802604911a88124081d100141c00c1002c8100c0040c214a81048041c5503841d2071010701d07009015801c083d40c4c000340c003a040c4d02d5015144200540c80740c0b04081c0a22101c4540042080c1e48a00d402e006000b103982d171104851030300608541c01c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 494931672 1250 494930422 494930431
    0x212070f0b1b040b1b0c0901060e0112020f0702031c1b03120f061a0f03040204021c1112010501180306110f2a06010e06040c0905040207060614010f050301030b 70
    0x2101812010844001c1c0d0018100500c40c4201d80c07075582a2080c403100310171592044a25450307100941c031240c41d64030303070140c03506443c107515000390301c00381840049410742c445420012803a403001540b9811401c1c180e006226082c02a401c56200c00c0d450102c02003858203914070640081e140a004682000c3e441200403500f500916040300c0c0460329050641c111116900d281c0240755440204010510000308981c1c0d1112180e60000c0c100780e4074040e907641500c0018002840b440d400034104c134182d9250f00c0640e00d1044056010460a45500d4001c007082d805590310540382c400c0600005000e611410300b0408a0342038010317003445240b85503594805400c1804210321301c0c00b8240440440900e04202811180340c1002e40003003c4400c80d002c840d1a40d029025002c0c99400100060080c090f4000c007050300b004056a00145116400b50308179021011a0030103544540002040ca0a010b1183c003c0c200b5601c6a0f03e05215102d060384c01520040c03c17881c5170f0b20101d01e0034001000400c1070042d18a600 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 494932922 1250 494931672 494931691
    0x50a0308030a0902040219020106060f03060303050d0504031709030d0f0e0d0c0204020405030d1e080601081f0e0414100e0c09060a1505070506131505070e0a08010b010212070f0b 78
    0xc024180c0003036012075100e00700711390049c0e41d603200402000f680098201c2203c6070358103042000c2030468070000c00500c2a07a4105041980700e00200342014070a5800c003100b211102d10010443c20f041c4509522540000503001160342401e0333840da001d031950301c905015044440b0040034584d44407182602c9800750244140c1e0700540c01d02001542c3d49080c00f42849540044c2d503400b10810518034003080b480c04541241003048090300c01c20480d82d030000320380da801c883d207001c0c10503039200002014900c11800303070015a034160001c400d00c4208500101f40304c0540400000b96200044604a10402c030764008000f5011a0300c244450981e50826003080c42d08440040c108010039a00c41010703414131a02c03040850005000050984180102880119004041c40c0e5214211802e03e03107a01011400891180c1406a56000810202401040c0907112a40050007400b11150384070000341c020008061403c0c050300540e84000da00369040d404558401d41d014440c08000252500d0b818441000240300031034 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 494934172 1250 494932922 494932927
    0x3405130915050108101d0c0d0c030501020d020309100905071404090c030b101a03010e0703140103060f2d050c0f12010609120203060c030a021b0109020a050a0308030a09020402 77
    0x1440c003403a00400d4040e24a5500901d10984170588020485002c20a41c0d004600400084515040003056419030083c0c1147d440048000078101503500113004e030301c000c0407507200007520400350341c00780c0241d80304210703245c2502e001101e502030750425618201030041454010039000c0c01000349001505551003c0078000180d095182d54400c603480200b904203130346141d010004c00101c4c5441c106240701605541301c1202d1040306201440001d0300040c01016500c140307000c0000e2145100358040b41c00410303242c00803103036541d4a06242001782000e00070007002c1401c0c415440e41003807003010200d00442048918000940c81100307954014440038210152800007040798403011030f0b2080c00341480401c0c05d008105554540040540a817601d40d00c035840e410a629141009603401152032640300d8583da02c2507a8980d10780c4101c4000384200d45070360542d50f6003803441942051055100d0b91815200303885100c000c0e030301c4100304044a0150701c401030807040100001018604039800022180344050700150 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 494935422 1250 494934172 494934203
    0x5100c05040b04080c04060b1603030513020306130309210f03091d01090609050c121f090608010b0f210c06040311040c1b14070834051309 61
    0x1c140d030142d40510400c0e44185025400c511b000d105003030080c580c2148031441c1610300c90f202e402c08490348a02405250b074800c0098840e80d2886410740810358002c00752100d070b10300004220442c019500c000d5000600c02d103008500e00f540550035641c104981302c034003911030fc019507800000c0000800d08808200302c0c00c50001d241c0d0040c40343c0350444c00303089012151a6051982d10001c50300c2942c000300c101c0d0b050101380180640524110b5441c1456a50414002c4c2d5414552007101c1808002c5010110903601002500c4e01195201b5401d440525000340040c00c0c1d0901088030f0901409807096004900701e000a140c22510111100b07020810070035a0f20410071340000601d1600b10350300a6940022008030074201e8509442105000c8a01e4100b00004003804000f1340f02042d8003580040c61b1080e9056440c0042004000d8140248081401c50725501566510240003000780c00c1004469865584c030f0b8081c60710001d404000791200078060341d124080c0074407600050480810143c46045803040c280 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 494936672 1250 494935422 494935439
    0x100e03033c0c030a0b0d0b01120c080d020f0105100303210f050a0219031104050d0501020c030c010204030c060801060c030e010e0d060c0e010305041505041a130b0f0405100c0504 78
    0x60b120380700c2001c2c1940c40303142c030036038500640d124502014821851414103000094038200100e0554001411003441b0503002e2405040e490790680019500303200350b06480001c140e000a11b0780503102d20070700904c450b88990340da01d10900902d0100902003004046109030b100b4074584034004209455602007020309a4a03007440c00c440064a41c00a001e400180300104003040c5004045581d10707600d0304003c0300752800740c0164503026030301449110b204051940007c6c40000d4041e07a0525034144192540c1d4003410002a000f94080d00c000c50355042c0141c0006401c40c01031250070304803055512411007081076aa01200c0c51229406414140004100602d24075100c104446402da0310615001031061120300c0d01a01400c1801801c50402d800d0604200001d039901c01078070440c20103090007240507200c0d454844100c000746e10000d50700000c900c0c10000a4a5541000d00300309001390300c40740c11a00c440140820b0380904480141580d48503030700b2401c50340d13090360041080304242d00d4154241520748610 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 494937922 1250 494936672 494936791
    0x30c04030b070507021e010e040209060706050a06050406050d031b140a03170a020f12091911130908070b0402150403032c030d0309030c06060602100e0303 68
    0x602c00280d0040703200e0741103003444c0d5040034000c0c3c40015190340700424140020000d54600701510300030750300800c0070700d090b44505050f580b81e25071002d414009882c1050044000b440d2622410303124608020000545003414124241001d0b003640c0c1e1090006005941d51191a4050904a48081c02c6540884e80c6050500643c00c20b1886540c9901110300301c466041c42d8454003070440202c00740304101c1d032168000500f0498040c3c40704003040c2c01499540e00172040c2850034048c00100c00000050105c01085400400c440350f00e0404c5546041541c6e4101414003210303500380c0010010081001844003084441041a07880740c8010034240c00b592081c40d586540c1e420580c011030115402141c1c174074401080742d1320190100c82079014807040242010000c3d85ea540d0b0041040b062603540c94154003854820b01c8080120390b0484400e2080c0341c0d60300e4000350f031256002c0b9642011841e00301c603048040c901101320f0b4090804088940c402a4842459510306804001000c4d1070f6604e003528004906483c851 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 494939172 1250 494937922 494937931
    0x191b0302130e040b040b10050d0f060f060b0403120203070b010905060f03011104080f0312070f030207060603031106061801060e0f09012d0807121a0109020a030b03011107030302030c04030b 83
    0x1811349190903d803a10740311070305000d082c02d5140d2403080c80c180100d48548203000d24503900a40c2c002c0310304901c1d0a058004040c3d405070100b4850800d000498040c4048004104603441042d84226280e40e00f44200d07100d0050910013080e007d0414010443d10b4603a400140d08041d0081101d01c0d0942814006401c548844405140500d0003081c20446d000c2c0a0203610041e000d0b41015520304650001c580c80d100d84001d01500a220554151607e0903105c0d5041d00da805601203020092151207050241c02c400a1191250407407260200054850810f003001d581402142d10350005541d00b440410795000c2500600079801c002d0198402c007641d540c400d802d50003080c004501e40301280514200e280c0d0f2852120300100201d03c6200b04204031000011060100c406944180c00400494600700d464069101510310f40c0c42094000850500708a500409400d81d040e1420060152500c0030b1509a41e04549009100b0405011a4001c00e020f50003c40e80f01030980c114030f01d0203840b540c07000d0748001300b0384 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 494940422 1250 494939172 494939183
    0x60215010e06060f09040c200f0607081b0c0610090e21071a090708191101050f03040c0501030c0e0a05090c0c060108070e071b030e0316080105191b0302130e04 70
    0x600d200210409180c502c4c0648210002030010427038540c201a6580754050880b13400c000030800010100c1426400ba1111904502055983d505007403812503643c40040d01d041030031201c078400011310040c01e403040b498100c2d00030000e4824402c030541d85200084003512002401034080080c02c000640d0b0502502c08000d17003105407109400c0200c080e52610030140c104511640c80f641d60302c00000200030100100992040710800c000c01d05000417201802038602e962507a0a010040c0804c2200344803400c03003030740c8082e601040803c200d450f0490b04103007800c0d40d26030070043d5280d0610550412210081c1d021003031515040c9040c0b00703000031a107441400d07070040b1000d8000741002c2c041c0c4241c2c001202c0d0001c0c1c0302d19020714030940000001510f00c1d20940c1c0103003805180718440805807030501001c8032510355826002000c1c1d50300d08026028110888204d20141000b00551100050038070910907001c049898521045156940c1503000b94480000303803c080190040001d890b0f03140444d500d12640c85213 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 494941672 1250 494940422 494940437
    0x30e09190905030721090e090a1217060907140906160507030c0504060b2a06010f1703041d0403120207030c03080615030c0d0902030a0b01060215010e06060f09040c 72
    0x5041500700c200c2840d65a180f6102100507081117558004610000d48510548070482c0b43c88001c01186442402440140002d50002c07400d00c200e9042001d12001c042890103400359aa9502c0c01c000020100710740b02c5020070243c425905104800c40c0242030a0800030702140c1c6001002d6001001c820b40540085500340d008020074420425030b07031200d00090001b59814083c142c1000030444180c00361007890401603078031460000c03010070300c11000304424000b0401c2d1481540c552a07400700030749203402184031f9080c01005450300742c400002101c2c11540307070307040c000b9945007840540380b8501c0c4040c200740c04102d800d00c541000d0344914030050910600c6916902d01c003044a180150091000800991164060314880c04803104641c040b0307944503142001880c1d5030020000c80c0e2005040c2c00f40c010703400d4412000300c04104180d040700c0034162641e0f43c003217840075429034803810f80e0340409001d00140818901c0101c1d2007070401001901c020014139005606100000d4003060454041090340300000700310 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 494942922 1250 494941672 494941687
    0x151204050d05070507050d050a0f080d061e05011413060306170a0c09021c0f020405010206060603040c1202130213030c06020d050930010f0f09030e0919090503 70
    0x40052141e0300c0c10034141141070202648950b070300c4200d01c0c07040c036010380549401c44003007180a01608540c140d003e43d0300d00302002c0ca170600d034190340c100c804d6a240d401e10706038000c80d45030308030011803404030004000005614101801181c40c518100c82e49207003214148003401000038842d40480c090070312030303a00083c09443c0811082503400c00305070440301500f00110381c1e00403078021400e0f43d0940b8800200076965241c44624601c49450709540b04a40381d00d060740419241819400a1048500c01d0303080710240d4440300c1c10081c2c58403099600900f80083c00c0810403104002c41d0011080c0c0b40001c00301c00e005001d00d125a000d990101c8000380c1803038042d240a204004001c2c41e403401510f0644010800c814008901418910680080b030b807051800b40042c190141140c00e81c030000d011f8082140b45a0003e0607181406000c0001a0310000d5084c0301d10600320380c03111300c9101720f195015501d140d03c0c4070030380050260350040a45240c1540e0a010403000c190030070f6001d824030203032103640190f070380d030b040c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 494944172 1250 494942922 494942933
    0x11030f07021509031b0f010905060103050105070509180a02131d0a1a0d050123070806030d0f0804030207080118140118140c090a0f050a060e0c09151204 67
    0xc8075240408a60341e03181800b010b140f00005a4420240143c8200345108010080c1c910382480c5651182456007014a80d04c01c224010803428101ca1040c0300034016600c03202015282c0740211101e20b500054a4900102150141c4079240e170401440c4500602e40804c80c00d42410900e150b81048007005500e0704440c040155280c5001e9103c0c842d0b1200300140c0f101261270101c00c40700c1cbd001443c441c503210b4603040c060040c00e41c88210004000000282e9104242510710385110302295601c002c0f80541000410301c0c20082032039006c0841c29a140c8450021080f4142ca56040c0940b054045204001001c0746591003445441c05031200c480102c81401e00078908030075450f00800c00034409034100034001400014059801800c0d5030300c600c1610300000c14261403454070f0760507004503510021840521001c02c089912208001a441c1010b2089550300007504080d107003944a02d26614000c1c00005141c82049400b44c41b290b00000c210252070700c0030407401c10850700581e4018a020181c40305002c200706 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 494945422 1250 494944172 494944183
    0x180509150117070503131b03030e090a020a080604050c130602010b0310060f05010c02060705030f030a0c0806090106030f06030b0114010306120c051905100e090a14061311030f0702 79
    0x74a00401c07103215180c0304400a01501000e00b650003201170004203641000030400e5403030061f100744090b1400d680d60324280104540b90701702119002d00b00030000b10f040003a2074000c45540c003019488001090303c40e5814440240001004414138620130b000409494500114683c010040c80d4000f168440b0040d040506007582d45401d80c0560780303040410401b20500001210896000b420b01d4400e049440c0007042d410b201d0540300500c40e000010704402d03442030020103113001d41e02005040289281d0454152907510050b10515844046d050041200502ca80c01503d140080d80c0b401203501755599a80b4551600c0030f810104540d550000d0303120035543e0600c54071004008050501e80c42022944504030f00340000d000d1076009003229201c83c149c0c4101900040002c0074050b000d00003521030124000c19070383d03070611014402e0801030701080c15031010f030081c0c145944500c5c04681143e205c0400f0000c5030fa12190b80d074040075071204c0e4238040b41403865000e14450b1082205504207482c0040e8000e0500c2c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 494946672 1250 494945422 494945447
    0x3300306080607230706020c070e040b1305150c090604061706040203060d03050c1501030305030609090c01022808210a020415031508070906030302010b0d0809011805091501 76
    0x420400d0805804520300e004c25555034800b601115981d034800d0a00c20040c1c452000c5540c554807500000040566003107101c18440c9000b41203507450764450501c0a850240d400c1d41c0640183e10002480c140042c0381f4040c42e40112050425510785540000810307280d81050381b10038003040400b900f1464684000201503401003040b00c085285150000019101103401400501040000301d107026941100304030888070801c1880121100e5030b907d1400500540c4100d40c124010300300480803803840c40002a008141080580240003042494000c0d81e0306041c440d04007451801e46c200702540854544001020481486d55080481001e1204681406100a00150040c6104000030408548900c81102154140c5c0c0b41c0461031503000c103901040001990007000319405100300010700b0309015031101084074440e4009120640b8802c1c100446500c1520024240e134030204144a030546c4142e811036502ca120b100071800040c3c1795070120b0311804046920070800160034404034410b41e00308103408102c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 494947922 1250 494946672 494946677
    0x2031b0a0305040e0c0705030403061d0105060a06050f040e090f19240209030f0c100908070504020a2007060e0f0d17160b070809060c030103300306080607 68
    0x40501664000c01a105601c41e132401c122150380452008903140003140d210640242c100e07034440e512410100010402140c040c41014280c0703d01c00f0045106000b21071013101b0040c210340026180200c04d50f020750201c00d646040542c108004200070b00706200302c0f401203c10a004115140c45042070f03a281c0703042d85019041e601d209210b4180002c0c89003600030309000c0c2051440308508412204140a40203005006a1500030104400f42c48040011040c1c1e810204031020301f41001d44d007400f620039440d00e010320341903900300c100141312030304080c2c005040003134440c940444401e0005a61940c100030a80c00c0c1103c0e07400c0000308008e140d90040302e004190300101c42602d8001000800030303c1c07a003503035040201000c8425040c81281141501615840e046d1054030389100c44913883c00a5030384408480d00c00c0814401c2001c500c031100000b0f4840e110301c40140c4151303d0742c0d08540702c11100078100201c00d0b502044500d40b505030b09051018000d52540140c40c04541c40303041a0317405060140050410f001c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 494949172 1250 494947922 494947933
    0xb041113060219081e0741030301120515130201141218030c2b020604080a11011d0109050706081506070f0204051e0106051201030b060310060602031b 66
    0x450413060403603844101c400e109804041a400341d0780c016001c1c0300006010b91a103104881107485007030241c9841c13070003141c2c0c01c0d84071154805010100501500800c001d103501c00e00041c080d070203244450405240c010380449a0030a49011079420078181100c0030285151880784035811944c01a00c03812070403207009a8503003048120b12448900320310082c1030240008200b44080107500b0305101301c51034807004509a070100700e040565005000d003025090700340343c01c4440000010f00d1003c11007030b0040d680300c404549001e2109004613038843c405095240c0359540c900003626100100f01e500782c4c4030642c000c00401c400e100380c24001c0c02c00c126030b0320007014040403000b007003030102d010581121400300c202c8446031a040c1c1410515900141c0d07040003074101d45044144030300c1803080a03d13642c914210380f103c102c85a889910444042c040c2e09507180c0614138010060002401c07803a43d240e0f1141f00035088a10b80300d0441c140e40103440d0560300245c0560400a01905c106207481c07021030414102000920 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 494950422 1250 494949172 494949223
    0x6052b060902031312410a050408070e0106080c0c120403031706010201050402100507030905150715020702010e15400521030d23130c090b0411130602 66
    0x10030205445040c604014916061240500e0003081c907403800d04030504406c1e032038110f020006401781c0d01c00e005e1074265106807000001c0c1c10035800688c5050325440e96800b40261200307001d04c07a4580203801046500c0c0a034181c01c52100d401680500700450080d0f0360b50040c1c10711070542040900c00602100d0442e41070000300400342e107d102c012440c00e1030341e2070032503907908007410b0850b0300e080140c002a6100300300c000561701260200e03001d04289801013041e804c0c2005423250310750072441542002400b050300580c50f01014900b1100880d00b030303048101418500320440700924030380b103661440b014050394607401407000310a2010a000580c50366082e820005400c0030002161816003255080c0c9040e40c010b0000c1804800340300b070328480c0cac44a0000340140f11034186103621392801480242130100f0306000084c094100419150800b940085508610342c0c28529040040d20f000004982c01030b0703c42e03407004010a030344002801d4900440801c45200e60500342e0013810009010b0105201051248204 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 494951672 1250 494950422 494950457
    0xd120513030f08090703020301090803100e0106090909060b100804060b06040503120c0106150518010305010315090203251d040206181512090706052b060902031312 72
    0x403002c0701c00742d040a48480d80c6040c0c2e01c0e442d0203240e4100070b4041d4240380d4a5001c03c41048061400f0316a1102c0c12201a921074242c41c0710040e0901c5040002b0380084800c00c10103480340d000c4107160b40608804a1000a040c000c12000e252000c00c50002072070b0501000107001d068420b00352411401c6604038541881e210009540700d04114008020303d1000440c6c614018095000000074108240000300003544844007600c61f030458040036014000201000c94158804d1003500e043c0c035485034410304000c0741e1050382401864a83c03000c0b03070144101c0c09034003415001c3c407440e40c03c000c00c21550700b40c91a0401204100d2450080c10400e901c1d1166018000140eaa0b031041e5012120014000743c92030034a040002c008100c9001d824120100c001a20301421040441c1c141c03158411004a5a40765603608007120303148586005ca00185002100c20440c01103407203440300b80c105942e100854020b45030b425580882c0c2c07041d0703405990b8056425110040000c24001c5024488503414040055413890209 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 494952922 1250 494951672 494951687
    0x30111040611010207021c0b220605150306090f010b04020405090c07050a08031501020c030f030d02090105191116030c030f050a0501060326031b09120d12051303 71
    0x700c100b4000b501d00c61181c100750960594000301d40003808001160200440529a0240580140c406c442507500007111105a650605001c0d40c240b0705030040310a590700c0d02d50041201421260413801c40e01899640c2d503400700081c5004d0070002000d0105910528040c41c07c4882c1d501030140224014032003040b4507034900716507030380c0710740d1605001b07648510f285040b604090010000400b406804018003808584540b90325410a60a80843e031620701400d080559813583c50003021200d03401005030821040700c0da0050011050103041190425002c0d407495511411400020030001300f800f958003080c0f01e404c12031206051040145426003604584a0030520b481a000191000020303200e607030300b00001006246061504000200219510f900d00110862000c0c103550000426440b0740340b03001542c08044a0103881641003004070b07c982550303100c0c042d40020100c0c81e401401040c0000007264148001070f0001c026555081340a50702a031088225580038001510b01c0e60007030200030000b50086403 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 494954172 1250 494952922 494952929
    0x201140906070f210203040b07050711102001090c0f08070b0f07150c0908030901120515030d08071211220f03030206011d06011b080f0301121103011104 67
    0x10b10038040d030080103094134070300403015156400c5100c13007407000361040e80e550265018501c1510300350607940f1440800c480600805402a002d80348040400070b10340303402101c00c0040422400c0c5040d1644d16400e4907020821a1040e001c0d460751900304c81c00c20020220f11060241c021402640e10341e0b03041c6800b0320354504442c0543d5414440020f4104a2460031000f621401940000300c20030100d40b00700100c1c0600341110714603000c50115040070801c207401005840920384103035181602c0d6140007500c200a0300003d400741000e80c9204503030341c0c440d4a05204c0d555442c00ca81d1509000c0b4103241c0d10045c81d203600e0f03e002c00f81c442d140c2018072000403d005c080350000c484a6110f221a48811184c1d40d80300c1f40507500c1101c090745440800010160082600b0b412038400032128070340d9036400e41d003100d8503103400c40b0b400f400210040c140d10254200e410320065058010610309040500d210f2805485601c2a0007004407500e00c80320013801c104101050707050542c000e034000c1c0800f06804403848114041e500 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 494955422 1250 494954172 494954177
    0x190305070b100e01080c0312090d1e02120f0601050d0201170a0f020a0908012313060902041d0d0c05061302030c03160e011703270916020114090607 65
    0x10080303403002e0500800c1070094580c0400d003000c0c2d540e58688559450302e034000854060b005025554107813088540030365442c2c1d607003c0d120b030381d910000d136480c0545001c14030503004180b81411325860242c0c44482298126000840c010041011008521072070040140c3c4000d1040c92503641010050760700c80162402c0c0d41341200141c900d03465418400000d0a014a251032a00c0e2000c00c45255150344200903008441c01c0c50700030049074404084021402c8411404406410381032000704400c0c0b1440090f81c0e689501480f0000b034042200e500290940e180c6004640040a6034040c500c1a01c40501c038007504118103040940c0c9040ba43d6684585640009202c45078940c0b00340ca204055460038045030420510040c240c81c88080c1604000d809141c1900514041d05030341c0b00007282203000d40e0b1000c5451400480210300b0060700070328800d825030101940f2010240c206100e040682c40d112290380c0512242031108007032925012000f42140c2040b44907503c0304030f001e428824503090104440d07030008901c2c07 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 494956672 1250 494955422 494955443
    0x30a0e0105161205032a04030f0c0b0d0c0305010518040611090d0c06020111040b180a0e0a090209070201020a0c151b021f06030218090f010204080a0519030507 70
    0x460400348a4001008060080c58080d083da007481036000004600c02c4c0d0500c21007111761070388060120604242c07000d1400e4590000c00007880030614420040c041c40380300b08110b42e2202d84807032682e007107500800e04c1441e40d46c0e1030f40e011a11303494140c010b25000d01000d0f111841030482039000310881c84000760000e004295a1800a581da41041c0111186100d024000304a0f000d41803501c0007084507944151f40040d442d042e41400100804000c48085a448817044da0070032071403820310380c1420780c3c0704101980306501c1c40c000102d4043c1c06402e41d2180088000004521201d4014040c2d0f051000b8030b04011644100094003109030000502c0c2c01c050b0300700f0301c1110620346512811006111090103c0080148a401104915400101e403c04207034429035440b0048504d0780307078030180d034150b0200070b40c40895030400d400340381c104082459101c42c2d854125040503203180d52090032a0f00c1504094455040b40810700d061020401900c1c80c40d043c0700c01c00c0e400300c1c50140c030024a07134050040000c2869182 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 494957922 1250 494956672 494956687
    0x6030c160201032004080d0801120b2205010203070f26150a150e01090f180603080d1505182404061202010f021b120f070303080414030a0e0105 63
    0x181c0c1c010040c00303080540561314100c0c40890341090f07070401d01c56449280300340110b2100701485000c1c86070403142c02d91030707450b00500d495840380c203146070080080c4d03c2d144c0c0c040c000142c110494106411854002c5d00016500d0404901c0100080c5a01030b4420074448884030844c2885900d40b243c04030815880400c945a860b074405601101c000c0d00341140e400705e004d1a000c00e0500c442c03692000050400c4e19050541c050800054400c00d00d180b040302401c2205000c2080180a0f61038101c2c50703a05211302c00240251265141c641da5007014003031031882d0b541c4549800c0e10715180014a4045c0c0b604444d200c06120700000f81c14071010000703240803138145a2035101002010303a103007000c40010b0014014400e86446117088149071185140580c00154003c0c483c80d9258000301751a540d0702c52020b68915622482c3d000c0c8640c025001208103080e00c100e00c04112000414060903009e50708c01c1c1d480d5800381c1040d05104c421000f100f400011280c008010300c0e003040d03420048031270741c110f070a0905a403140403 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 494959172 1250 494957922 494957927
    0xc250503030423030d1a091b16020607110a060c0c05040e1903270506040b070f0c0305011a01030b0d02061e0d09110907092303240a0b22021c090303060506030c160201 73
    0x25800e09c02508410082160001c01285200700c040381030042e50800c102c00d079509421a2564203004c030182c05450222400e11143c10319070401a010440d5070129056480e030450990001550700a05030b00003503814848141796020305030039039030100150812602a90608000609501c52441900c00070180041c440007041144d80081c0f10003604024141045640d81c140b0b240a0042038400b04140c8124410480d0b40d903000344110504010f000c2c01c0c880c9400c0070790f03017440041e500440800030000680fa005004540344000180180d0241d1580807400b0880386c5080894002c242c1c4400e4403c0788014100300f02d245d40311001c0d01c1261001c102003000b0100c015980c1025000c001002909402406c401c200e50072604541801d40240c518550941940c8145401007242d4030054410b038000c005c0580d9001392000d070300b8440503500c4c2c5a2030041ca0003140c03030f18000501018075884402251034024010a0641500c10a0b000380400d460b001d00d18503021681a000d40f00e041c00180c0c004445070003a031300b56403 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 494960422 1250 494959172 494959207
    0x70902030a0e03040f0918050d0f030b0a06020a0b010510080f061309240203160e180f0f07080c040302040f09020402030c250503030423030d1a091b 65
    0x5182c50981e03585507214858034010304514040d1940f002d04040a65001c9140c606030a443d664000b805032449240c1c12108480085840700714008064483ca0109031320303503444140320000c040759002003240310b04900d410b11012005921282c880da15049080b00c041d074025008552003440649030014907a07a010000341d10004821081c0707602d0380740802103402c0000240380d0f01404840c0200d8803104146914583d0142d2204646900c04000d440800c0052a40101078084d120f84000345000c4c50300e0b80020903400c0710300e421510303c1d00d01d190b54802c0c0000620781012546d0010701a203440b503400d181c801800c1461307110741e00c0300074012a5103800c0c0c4099031056034031210040354001d000b0b66907401c02c181c0190841d04060440c8400d00396a05a001e50204400403111203942e00201039810359a5540343c5070307564000f101d111001d85140c103c0680801c2c20500c01842324801004000406081450f00c805907000000f200c140a0140c65050000b034505401c0f40c0c041c0d0501000d0120399501582c00e00c1200700 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 494961672 1250 494960422 494960441
    0x2090402010828022218020d0e0607170c1206011209061a01020c0402090a061b0b0403051308160e07023309030304030e0402030717100f060e03070902030a 68
    0x43c040b40781480416a40090069804131051180c21001d203415052004465201d0303880b4850510080111904941e005403d080000d906d0004206280b1a4490b003042004c4030000c0010b15188051520150082c0200c1e400c1001699502e04024103605c06103c50000030f000c85050000b2912070803052401a040101c015621440c1886141d04a40d980081c1d105441056400741c0180410202c050405100359070403448014182c01314245003030400c1d01c0c80e18000c440121403c04983c0130740d0105103a012035034041e030720039940d465440d80e0b00590b0386000700003504503981980080d0b681c0d1040361401d000200036503100c14506c135030755107444e4030580c03400f0300c41c1003200c0c035806101c4440c0c000c4840800701d00b180140c0000e510300703442ea1103070291512072008440003000b264400704c10700a42e0900364055a44103010382001c54800589400d45000d140f030440e80340380d100c540b4034418045041040105001090075052144940b038060340001e031199024000c007a04580d01100050251240703401c1032200 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 494962922 1250 494961672 494961721
    0x7150f09030804050f010903090506070204061706010509010504020a41031605190e0a0302041805011d0a110a1203020703030e0f01090e10030206030c091309020904020108 75
    0x4200036490003030091032003120107850310f00850190000244060092514855040c0d43c2c40703c19a04120800429400c00c0ca001e9800a0750340074041520030301d04200451800003240108030540c50801001024101600440c0c011030061001c10380c402c1c1c001711518040c00491001d0125211802c10b19000c031600c06415070704807600d01000c0305036003082000460150408004000c0035200760003094442c0d21a40c40446003204c0003004c24010f4a228107505040d034103006001101c640c0d034940000701500c41d11822100d002c065200c41e102000000d2280700607543c00316000d107410012010b8115200c0041e82000350042181640c004800d690b85403214002e00305a908540c1e035500941802991400c240c002100814134103407400b211443d11a07035400c02588141d55040f040390514030040688400a001d9050301c0003d450084010ba4400d0040c40c40f400b03d240c82c2d281ca40e80c05a0400c00f14007810032002c0410b6160071701250158940d0484154800d40a0900100301e8403000501d401540f4212420b501 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 494964028 1106 494962922 494962931
    0x11d09010501060e0d1b090615022a041e0e150411210d05180a0f050603060a03061401060e03030c07090509070b070c030b071407150f 59
    0x2481c0c0c2c0300706061b8021030348495031910b40c03103010303000100800d8071a03500740481d01d9807815100040c030582c80140600640b040280071500d04401d8030709582a0041e5542481c4d0b115600a449030501c1090210030300d10188518200521540845003064001c24003620007511495600301e002e1034200c500c000d070389850403082103819420349500080c2103c0d0110f510b643d0741c109020080c010032060302e6007650783c505500c0d000c0c001d40f0100c007014071880e6455000c0c0f002e85240c40303001055800a48149a8a4545034001402200a584010304440c01c1000c020004007408080074101c82840e250080d80c01c0c10700c0d0801d0344034018414151215884050100190f01c140d41109030843c1c201002e849806880d11301410259205540580300240040406c1080240d0900040c3d8414014900701901003c4804109210301c201c03100070301200103440303203049025000d6000700003008600b01d0400 = true := by decide +kernel

theorem cover : BRFrame.Cov 494784172 494964028 := by
  have h0 := BRFrame.cov_init 494784172
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 494784172 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 494784172 ≤ n) (h2 : n < 494964028) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
