-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4909
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:07:50.79652+00:00
-- url     : https://prove2.me/submissions/31b5c12d-6105-473c-bf9b-ff750af8fabc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 882733812 ≤ n < 882913669 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 882735062 1250 882733812 882733829
    0xa05060112110712091809020d1202070e10030b0105092e0303030e0a08030708090f0105040c0e09010c0f03020d02041e0312050c1f0e070f1703190f09 66
    0x1054a9500c0e180b001c007600075588903180c009810910340c5410789800e4414011035040040780303103020745440b126411100145001801d42481c001c0191680c1d00c2001c0b586e00c0c0e0304003513400818200301c4048200f902a604c0380406104c030380c10070304583c0d9900c40c00406200d05403080c50381002048080325907605140c0c50a1078506400074000c1403a81070128801240310a030007207454446034010901c0040303403110758198000040c501d1b40e03850120640e50484060810325103031140648403a10600240301d5180100d000d2000c0c0005a8030300325421520f250010403584690341414490840305802c01e403140304000182c2405610f400b990001c11009000d550700440440103d181c00d0b03100b00d05250440010750f80581050400004041019202c81c810341c00442d40355482041c0c1c15810000b0f4203160b601901980002141008801c2c500b03900d004180e421821422041f450204000702050f451600c207060814051030801000001d81e91650300038260b207005001d4031600c807810301c51007032803080301a18861b0b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 882736312 1250 882735062 882735071
    0xf031005040c05010f0315030b10080d0801052e080c0721031113121104090605090601050d020102030405150909070207030c0905010e061002010e010c0806030111030f0a05060112 78
    0x141042c2029203401c0c86040e0114019000001980d0f10030700882ea200b00c481c84500469920b180e0702c601e50702d80014400f1008030016000031a1144084c0002406141a992108059410241009140c0d124680503550700b04800c07007405800c140760b001d50501400c032801d222951365171701e4000041d0740c411294007e04440d01c92101070002c00a080b800500d86a03e40e0b010494180740407003c1d0300d0b0b0b1090400c617181101d206070302080307200102480d080059101d6910300a5040104010600f40c4259800c00c842c002d403035400b0001100001c0208a00426003119070405c10174690300041d440388110b00401c0e00450b074002c03804512400790811a00c95a0015081c1c4002c1c2c84c02d40d1700203448503814007080702c049210107000500e483c46030088a050320000451015583c550341c0c100440c00783d000622030155500c550341100c8002c020302c00c0070b01d80882034440c1042c0d850507404041c02c56401e6602403050b60703002d00070712403540c3e81c5c0c042d4039510401600c2c3c001034039202c680c016034104226141200d01203007030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 882737562 1250 882736312 882736321
    0xf03010f06030b1608040c090905150702030306010e09160509190605070c0f180b04090501180204050c120f150d03050a02010e060c180d0602040906080f1b0f031005 72
    0x101c4050300e1080d50135584d5400605451203084030324900a44d0040e0801c101c510003440b81c07142e50761004034858425800c542402c40c2c03130380500d43c181e1030441d02007015130801b10800460b0350f00032500864580f42101c0001c018540404440d1184482032004420481c003c01c400c1c040b6260218454064010407038005006035481764020440c0d48660411200305084100014514860005400958001e401c100351246061000c4000404044100d583c1c000c1e1030f107040901007a420f07c0703000c181c10445490001025a5401404280c03100030741854a0301504202c0066014114a03003113800c841c0b4580580c200340c48000c04200c081074400b5501c0e910002001e103107410550403400a2804a00a800900001c103141c0c1e15541c84400c00c81d040403440d201044140071240c82030003e49500070000f01261507000c01c1d030702c1301c0d003c98005070003e03061303599030302e50901c20030b241008152404961140100250030454841041a012070106c51b8000c51340c0b000301d01100c1c1c1d0244240c0c050b004541074100150b280 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 882738812 1250 882737562 882737573
    0x7050102040b09030f011a060a021f020414030a05030d0b031509160e090a12020330011e05150906130f141e0307050a0e01030b061e0f03010f0603 64
    0x1207611228030911450404580c50f003410f0092000c15160008147c0d000400c3d034007840069400207440c0411801038100101007620000c2c4d9524040d815035000680b07460800d001034001301f03605072080f48603610810a11001800000c03c6504101c50090046540d000c2c4501092416580e100080105441041002200b40c1d0008003005650b0034541c802c84156528014040408400e88050001350008203000001c6040da0f10f80049034a03451040f42c0c9800003134142002020818001c010304801c02d840c440951200c42202540580100e2025400102e18024802051811131041c01d0040d9a85944118811484001c0d14044140501640c1c2c0e620a882007001c1002c0c030780d000705840c60350303c40404500b1054120f05440000d80c043c2609850700c121441615a4403007001089526102d1198041455201c90b201c180c0200350001c81042d0b55410342c42e1203500c0010040805010304e4442d00c0716205550a41c1c002d03d1030071400c0e17031210350018000020902415001680300d00150a01000004010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 882740062 1250 882738812 882738817
    0x2010506040617031905040f06090e090f060403180905010b07050706080702030a05180d080a02100c090509042f090a0506030309091008073b13060207050102040b 71
    0x122002c0040d55100e600500c1e00d0b0240d03480d0707a40150b00500942c3e00e00620908401d01c11000b5003495820665610500c004155844d0030020026002040401c0125003070f98890f5040311420010340100121408510f41e2180004d0010b820440b03045002c01d00041c9203a8110050301400005104ad503840d21102c0c0610340c440d4104841034410010001107042c81024014003d105a40c095440e0800000003200c254108510a0840440d9610a08866503440842c4240c10b40b1842a042e1150b04100001c3d007049110f00d401c600503030030a502c1550715940301c24400182c850445001101d41c41d40c0c1002400010740000c000d6561000e070b003c40d03228005002d81240d007004101ca415009585075040c01065610958074590541e200b4802c000c490720f030400120342d0000e801030045a50a42e1581c440d0301d09039080c1e015080d1801511543c40d0003011000c000304181d00075400280c582084070316180030410009068048030600c2000c80c90401c015601200c03041a0444001e42d01c40f80c031000760201d540d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 882741312 1250 882740062 882740071
    0x403050610260c0d02130903030e06090c18090c030a03020c0f01020c0a1514160308130f0b07020a02060f09090f010321052215050c030418150303020105 67
    0x19580101d864500d01001d10040070760ba801e078000d02180724220040c0000240c003201c0483e8050501101c0307142101c80c6118401025010340d801240c1b2844400f405802c025002d4540308194200060740e8509071104d08203132044840c036038036400c000c0c4e851050766810200300080305545400740700c07400e00a050340080e41c1140088201e50310382c2c640c41481c6c016a0b54801b40c088203a000402c01004100184050000c0c940708081e03800c200480000c04281140039034402c0001180100c08001280c041c16408441d8940c86400010500180d0180742c59a060040001e0340080c005140000090401442401074040b4039901818498550281c40f4058680340c200c1c5600c0c6004a80c0b440020301c10b240d6485029040725000320078407107006503003515810720b07065001d194810b00c0f0041191040100c070803d80680000c1600d01441c28041c10800b81ca0186805050a4000c00200f40306501c1924404000c079002c541e00d0f60fa480c148125040001390141440c8040c6a880181401000051640641080340315 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 882742562 1250 882741312 882741329
    0x9061409100b090a11040f0b04080715080612010617061812070f02040209060415020d021b040b030705060715050705041a090409020405130b0a022b020403050610 71
    0x400d80c088001c2811240c189100e568408041c401207901075200750301110404c02e9902506203401c1d103031841141041d8140e846540304d4140041c040107000c04c14089400074004880009524101c203000c0101400001b4200c1c6200c0d191b2440724980c942804d41c0840c00078025500c1a805c01240d108c070b00c0d91100c20843d00880c244055244220a0b003802040529200c0c5040c030441d82030039174a840d0146440c1d4201e4040b82c1140e420840e45142d5514400940010a1000c00c08001001071060082c10810f8407441401954002d5044101e032030314424118141c1d4009660000e031200340750300003230b14001403580100d0b00003030300040d90014400c0b18844082045510b460500c466140d0f03600440c0c06104a2107a80e9110254203114031a0f000c0350350041c921071f08010f20225410416400180840d4010707514408041c01c2c94900f17100f04102c908880b03600c441410411406c00c4240c1c10b19031468604a07100d6504180242c2c031001102c005541600d0140d13410004803031140c509142100b8043c4491b0181040c0d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 882743812 1250 882742562 882742573
    0x105070539150f0403051605070e130618110f21030a26010b0a021e0715031a041e05100f0905090c13060302030f03090f0603040c1809061409 62
    0x11203c0c072803880c24000e9505640f49864010000d04407040380300d074150b044032607000f4154006101400004000d004401001c10b218080c82a0b1600c20f04881e42800d42d070295030b9103544490041380d40441040494030341503403003403501c00740d01c4002a5085411284071000000408a0b41e00c1000004058a0071041c10b0311815500c212807030700c41808840c241e02d00380801c05007100500c0703010103807005445016503500488843c03174440395000513003020740485514294400c050800c1000c034420917031010010b640c00c0401c0b0b4807244c070070202c9030038084040403401241c071034028540c13603101d05105442901c1d10f0001000b55042446000040507118810200b004100b804c2c08507061960f440380710700a40301d14004081600041d0240b10f5203000e0641a840015581d00000000da00c041c0100001c1c40c101078007540d40c820700e000c10402004140e01c1040e014042c10300400000a01d1960b1950a42c0d84452200d10400882a1140c0c060580d50500814543c2083c0340c0405082215604901403002501a2074 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 882745062 1250 882743812 882743821
    0x906040f090b090601090e160c140607030b011b08070302070518040302010b0f180402060405120c09010f03050a0f111002010212090610050d1b0b0705010608010507053915 75
    0x54501b043c0b806807403440d0340c108010a031041042c2000b050a2501411308a07107050721510b40c0704601c000818801c0c8150840341c104656198907114504110340c1c24241540b0b400141c0800c07c20131024004010078610000540805041c000c1000000804001780582c2c0048466055108241c406440c11000756083c40300c0d4190394038004908e680300c1500941400c1800d030030030488490812010b4400e03030704107400b040080f42588559902419806690b001415840841c8040c0b1071004030503880407103a022004000e0000031800714910311150f0708006030407820000c50800c04051104102c100d03500140d01100191029010b40203401c00f10440b1040008503600c0b0b5900a0300c4180403985a5001410344400384802c0c507001202c01403140c00f60802d8101c50503558983e001d480f00b2034001d0098920082541002c120b4240101c0c0041c0034248001d002c0c50038510b80107000c034081c10708180c00d410b445501c400343ca0b50614101d10070f80d40500c1000241e005091078219240e00265445c404015507010006 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 882746312 1250 882745062 882745067
    0xd02010b150723060a0c020c0f03060c0d0204120308091e060a0c020c130902120106030c05010e03030c1c090b070b07080415050906010e0a14010b0906040f090b090601 73
    0x6a18180d00488052818090b40d540c0c8105440d002907200c0c842c0140400c1e14004401000403604c00d034201740000846807001c0d01c01902e44a00b0302000c80c481c0c4204010a0a00e032400308540e50424036444c2d1007a00ca000b402142c00c00780c00b582d0004145041c061800006140c0d0112640d406451028103690000181d80041420594091010b1708244d1046000c124114126440303080507192910641e0401c0308060000340701c260315100b50b482d01640790182d5005524082c096048095891402000210300e96a24114907600c2441503a040c00045540300001d9203040c41186c1480721030034155411103005103681a9001403503280400010312801b404030314aa4604100d982240e08040f44c55000d070f8655a00f16012a00100100c0d50049107003450090a542401a00c3c054259640501400c2d810032129042c0490014060a144c6003024180c1c122540388100060640d0b04400640360b5410362170b4003041043c4100c1e0301a059a51442d0000030708000039620542e03900b9070440f804929500d994004 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 882747562 1250 882746312 882746329
    0x3020d0c020316020f01050d05010b04080d08102102040e0f010c090b031501090312020f062d04030311040b2502220603080304030f030c0201060b040b28020d02010b 72
    0x201c141054a4102100985171009000168950501d04103142c0007051440c241a40d200307900c40340e16070501160500c200182131203c6200001c152414010b5841e01c1c0440318118141b0b0300c60501c01201c0d00e880f2000d01030600c0002081c040e0060000e00c219100c020b407881d5603c1c10141880159482d02e41100501441207041c8411031b01c1c2000c0c0320782141c4a169984400c121150415030510010400000006080001d030704000001500a010142510700d00306040000003090b03032010781404215505848081152900c4802c03010004d40d040b40d0b1145010740080c11440d8102a0303000700070034001500e80451006020f03503c7d1a000301c1071884500740e401d44c02118403000007984881c0307282e19223090500303280f8801700150f0310340340200c1c60380c1c3d130303501c07006440e900c1a1825400900e002c80204602a014041c2110980d0680b00800c183c51402da202501400380c0d0065103003a0100040c02441550390b0785c01029103e95200b240796010101360307406583c1e032594224000155003031590070122403401034035 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 882748812 1250 882747562 882747577
    0xf14030c0a1b03121821030809160906050102070e0c2b02040609031a071e1806050909090318041d06010320090103020d0b13080a03020d0c0203 63
    0x50070140080ea99015081080010000c6207100e40403000010034002d400e000c886030b58507220364000502070a0620488105130300184007229252145901d9180c00c0905000d003150103261850043c1c581c5960641004840300c409800d11039003040228485007541e0084048510903001c46003000c0c0e661a217145401c03021035001001510a101c0004181d61040c0800201c411002842d000d0707003014072024040360001d40048001907180d400c180100050b88542c0c101064803041c01111918142000404200344104880140d580700340320117070311034041e1140001c0c4414842810108076180d500c02000d82d00000c0507280b0500045001c124032031008004c031070341417145441000403554420144000340c5103000b00c80001503000d041840014005200c0a0b000e13512544405100c5601d004424002911b5203420511401d4400d00400060391003885120310300741c0c4016504a6607582c940024200c0321080c0707014041c2e01c80050304200043e41a4002c043c10100d10208111185c0c28240407039a9008400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 882750062 1250 882748812 882748837
    0x2030711010905060f1b07030201020910030b030a02190512010c14040e0c0a17090a11011704060b0a03051c0f030e0307035f0d050a020708070f1403 65
    0x10007084611700d45000d0306034810002c0040704040700040c0c03028056035103d8201600140d40c0454404036515041c0b584503c2d510040c5800e010001080740026241e540740318000f403080c18403280c641082d0b2004400c1c04010b03c07000704000c8440429149440c040e00b03550950700002445404025903000350300090381d080d0340c00d116481c1c0c9d4588d155040e043c1d03d40e01004174034080c4620313200d800b4400030b050b0782000d108441200c0542500141c42c54481c0d050202920740505000d40e460084080111f04246980e1054200c08042a017045100100d01451100c0c2c0001d40030b8065031900c85501b4045a401c101308491990301e01902c5080051300301c00321203800c0f031803030420780080000801091080700e88e42910221224081c4402e10b8038402d070024046940000c9680c41c0381100001d03902c56940c1200340401102401d94004655480000800f40c82450b0528030070350f50302c4004c42d5410166030b068605c2075038131200340e036921405818582c0d401074142074211484220146228040c1c1c0c40401500e65082c4a075 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 882751312 1250 882750062 882750073
    0x117091213030c0e0c1603021002180a0b04060e0405040804030b0403080f0604050705030609092a010206150f10020114040809120106150e031f090b0f06030a080903010b0409050102030711010905 85
    0x704031ba0700342e8101004150114816485d00c14808030325480140582c0c40000300c0d02003221000c10501c00103601d00c1d80810000c01e428042040a00d8120410710700200b000c9a0008680d0f440b0b280154260080b500041c0480714454104010035411102090141075100d04400072070355107804110640710304903280740004006002003078880c04c00d51800d6400001c403d0660b503c00d56038042c100b648114209200030702c0c080c50104e1074030658040c0001e40e00b003045505031406401500001c00ca410300d604000900648450340e1340352070303603100f0b500c800c1b050040c2a0164115081608280c1030303035000059181e114101d200e030010b6064070144036500c203d4007401c91140615251440a0303401c50442c0380784a816000d5803002002602040500001044443d00c00244a030b200341080122140014205c0191468900610940755400103d41200303079400f4600550701c00c9140042070260078806c1c10303107030840d0416030707140f00300201900518810700841e541c16a40541240c401c41c20f80e1802c1c1005011504007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 882752562 1250 882751312 882751327
    0x81902030304051512090d031d06040816120f030f200309010908030108100501120c03080f091917010204030305040b0c0f03071b05010903020117091213030c0e0c 71
    0x1880c444c214600b081e0100605081d820110f4103c2403500b22034001c081c3d00b212410b110381a4051141c120343c20340d0402140744070348403012070a603214000340000e030414502040d9030450340c003039000c80340c0d84c2a03001b04202c1d6032105149018006440c40a015800b01e810100c42c07203070721300007403051401190010809888200c2c60807070400a40d4405001c180655484504c00386c08181140c2c0114000c010400040050400d4492110220b60042c0c0156441c041942c10300b401280e01848040142c0e0b4101084076a11402c08041c510b49108079011280c000e80c0a0441d5210425013990200850f0314202e000002c4610840c4141d00300c0c850381c000203001c06c00500c070600030080d4550203004003628034411141484902d00c0158610b030007520085441e10002c00b650488410752000b00c6000344800e081c0382d021541198000703031545010b110768498248510000803030030501000b400107180c0c0c0012400d540c807081c11110440142c039900060300c030310291902c002440407511030601c1c4a10750284c4964246070a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 882753812 1250 882752562 882752569
    0x1a0306010f0e030102040b040e090319050306030c150a1101150308090609030a0c08160302060306010804061416030b0d030e0d080706060e010e0a141b0c030a0908190203030405 77
    0x103144160104100090201904940b03003417000f48080d00b58002c2080d00d8030f14008901200d55002000c40380b0303642060165800f510748498804c0340540702c7d0b0424540700e94489022030f140286c00c0e10241c1d80a80007486941c88a200d4800800302e04230035aa440140c5400e01856138262038480050b0261240f40407003c00201380a00301807d06040014102c1c2d280140502c0024584140e0540642c0c87c0712a8143c1089600420000f051000540c9082d1040e0a4030f141c0011f1780c54000101401d040c443d170300300020104401e030752100340c0c0284859011442d0f81006400794102149a20344440800c1c07a101c0812610300d03003040b8150040d81d06d41c8d100900e00c244601071040c6022a0b900c02c880f0200c05215460000d80ba41c02040d01405254007403004039894003003100c0e007009000e80b1000c959407400c40c842c000244069040c2c0c1c2d00001a00218a2685a283c2200075038403076200b6211b20742c0400f20f10000342541c0700360300f4000c0700d01c40422210b034180244400c00c030f0342c2e4051100940c594000c0000300704030704 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 882755062 1250 882753812 882753827
    0xd0c03020a05010e0d120c080105131e0e07061817030408070923060a0b090a090f050604060503030a080412030216051f112505030a03151a030601 64
    0x61080c81510100009a640d50b401d4420200341e603500b40d004a0038030365003c0d901c8000c5030358044040c1c005110040c40303c034000d4030309a018003504c0e00810f1410340310882441590420f900c0c2400422201c044401100070000c0244141c1c19010800e014070500001c28030321400c02c084000103240f04c5102881d290a0721a9066108600161460b000a00001994807030500c0302c41c005041200c4007103100c0c9280200c402c040e030006203a08052040d03000501080b5111515010107507555030100320745da04608400200034030030507803103051050b09011314070008410030341290307001c0c1100351400e0080c20b88480c03c040d03ca0054503940030001e02d0620000d004100011062041083c0d40e080040c602800103210420401d01080141c82c164009010350404041015000f100300c801c2850400408c0b015030305102207449036401c0034042002d00d1030000e4541c0715601040040e40d034403004682c0da40d803619001602078141101111038101c01001c00041c0724a054410703082c0b940010741c0c16480c59440d580151400c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 882756312 1250 882755062 882755087
    0x5100305060c0918070c1b0b2d0a090f0b07200d020d030c03020d0801120b060414240f0a060c030905040203100f0503120712030b0301050f060103140403020d 69
    0x6000324022400441c18001c2c80c0d003d00340507078803140c100c503141c1862044030250b243e804440c10118841000000c0005003600d0a100581d00c1115000d800d40c04c2710210590070780c001580d4000c00203804001e181e00200080100c03512184a1044250303074290030701c0c40e80a511400b41c81500761041800210941c21002041703400c00400c4007034100d5198000c1351852803690002c0b0080f4038a050540140341c0c040043c2d00b240c42980c5004038056040070420b41c000c13501804010141a11480400c03100c0d0f8654120070b00309010408100030b1482c0c1101c2d4001d00d0380d0500c1203040ca000402074008014141804e49010316035024100f00d100a04d8280b0031106240400b0f0b090b0200410343c000800e1a55442c00114014651a5441141241054608038414031154485480f980c04065800040c520307a0061300c07032031038110b41ca84c440309440040540203032245d40c003410303815460601008641c00c0c0d1101168024142a0790402214119803580d43d204132046c1ca0140169200c0080783d01200e10031403150203071 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 882757562 1250 882756312 882756319
    0x51e0d050a06050103150f050c040b0a0504090f06050a0b09090c0702040e120a09050306090604350711010305251803050c010f0804081e0f030a05040605100305060c09 73
    0x400c110390b100c1c0c00c1100c6080e0003c5a000c044c2400f000c0d6209003d005103141030520040c20011802c1040c0c044090307102d14455070440c06c0c408500001c8941c042c0c8180c500824412030140500c042e91a06103006096601805114012105001c03034003501e03032401c0d258808800b50050020b41c9922040380e009800041c0205d80c802e44508800242c0c1c1428014000b448d80034615a944581c0581c60181a040e500d8011602952044081203410b050009a45401075002444050801000404d076001c5d100c030001164a0700060a08411821402000920700b0350f006805c113542da601e5002c011402c2d50025940c1c0040b0941c6286001c641c808409883e0b2100007050a083d1340d001030b0000d03003030001800c079071080d11590855485910156080100c46884015520f8150803905d130960321041c260007480c1c40543c100305410110f00140040c41c0440342601a20143caa40707900e016440e04003c1c20089604480e00340c01c000100d45220282190320080d258042c0c05884244c2e16031030911071070342042400c41c1d403 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 882758812 1250 882757562 882757573
    0x80a061a03030d05090f19060b15121005040c0f0e012006010302030f12070f11090405010e011d0a021504120c06020f2a0102070806090a020a051e0d05 66
    0x4059400b00024818000030300c0c4041840d160464043d81054407000544295421200b05416107111201a11141c02e901034400a24000f0794404502c0c107406100242c881d00c1070018040009000800000384260212038149211944403400c0c0f005a0752030100c1c0c000443e0158845440031401a4201450a0f01c18034020081060103c0816440c03800b2203904071003500000010301c00d50030142300814103130540700018580c0f00784d440010310052141c004040d0808083e480c10200300013150b00b451420200c000c202c40c40e82d0400c2d0400900030640d9412801c813541c64010400c401c40301c002c440440b02402c80002d0310404680d0340900c5503c5505c0c0380d40d40e40d0300c2d400300804100c102d40490a65405401420b01c00c280301d0600b900685410b5035684102096409032001c08100e4800720031548100124440d4054001d01035070040c0e25060b61504181d50038051042000f4907003100003a80754106000b200c43c8140d040c0e40c0c2041c00030469000046010f4560003a6060304981458102069003501c9501100d4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 882760062 1250 882758812 882758861
    0xa14120111030c07060e0601030c031b05090f22050d032a03150e010510030e0f1c020c0a080312071b0309140f01080601031d060c07021504080a06 64
    0x1615030b40201d91481600c20080b8241e4140a42485100f4031b24103000020700407541903858902003004244402005011030483c0703041d600d03819840b0348008003005030801c0f0850a2210154007040307411070340502036000074403003143c01d000141001c0d55015000800740104092903e41100a4080bc0c140310034898150180031b001c0d441b032000c00d4200b490013540c0000e014040902d08651101c9281d0000400c80c0c04000144120703900c0c034081030101c030405c2c01d00252200081d03641c03030b08200a106c7c090510b4059034011640f1030702c201c0c0401540190307a40c2915080c01d1800100003003c049401811007a07401444818001a40000d00781c0e04001c503820311800c54840d9aa41422580c0e17a614120f001800d0204104410f030042e0003103481040c0c0c12203602c00e1440c80c000c0000c1a02c50000c04041c1007580b00d600400c4514048240100d603009400e042c1d41c3c85290000880c01c43e50b0010204070702030441e103681c4d1440e0b0041c10b000d44058901d1100545a01e1006450304800b51040e103100b07100d0540320752076030f0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 882761312 1250 882760062 882760091
    0x7120e0316030c0303020706082202040906020705011a060c0307020d020102030f18130b01050306102a020907050304020a0e04060f06080c010906030b10050304050c060c0f010b0a141201 81
    0x7000118814821450190304500e402810646c5640c041401d1011a10900c54190310507240000340101c18550700581110a000040c0542102030f0007034445480010000c0c10b114042d04090340d0081c1d400e040f059082180302c207100c2e036440340400031b44003a0400e000d15001071038111404241e2074014411641880314244801015a00c001d07a0007140500c185458511804c10002c5030784404499801004205480c00c00130f0014800180020b10030607588a030003120300c0c01101a810090f42000105200c10326451629940d078017011030a070f10881c064000161000e101d0303402c0340d100740d90140401c42a1490005d29409224002d0411610261512503045210500d84102c0c0010320502e0000c04034081e134880090115445504810100750414000301071035150348865110001051a240f5965581d5003441800c0ca910302c01c940e580003c0025814070300c450000340d020448000b180080001d0120002003010b004454461011001140e1a02c0c192a140a000044107840e24a001041d807001d480d010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 882762562 1250 882761312 882761353
    0x409020306130c0501020c010504140307081002070506100510120e06071d0d03080105100302090d0506010e132102030c0604080a18083a03021c0207120e03 68
    0x102003884441c1c1d090340c0030f0050103001d80000f00f50070700103000c28400c0c10700002d000d44924011020014003091020059032400c200e014010071401041da07503420300c990410000f0b0760211000341c0c0c0e070b4440c0c10042030f008440103503d102150300c000c00c40e4000d00001d02c1e040c0c1d003084101e0702c1c22502d0f40d903035036241402c04030504c6807600c2641213545000f40303000660040404401051007003030050b04420b82e10030010f500f0105540c1542e078111548403030011202c0e001c5020f03101d03503100142c0004c14001d120080000000d0040e06070380514201001c00c0d5100f00c070000c4654120328001c4c21101120801462060704010302c000d25142c9841907a28294902044038078140003903a04075440d800002307038070040c3c41d88061409591126540c40c0c4010500c2c01d10b00d96503560502841031609120000311802c1500c0030101c050601c3d030071028580a03002e040c0300c003400942100d4030036800c0c455281c0c000030034001d8501c201c0d500c3c075a003c1149000f40e0510075080320307103180e098545070701031140e4040003000381c40c0c8a55 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 882763812 1250 882762562 882762571
    0x130507052709091b011b020307031a010501050f0d02130306020a0f030b0f090f060102010608060703050402030d170403080a1d0f0d08010b040b070503090d1527110409020306 76
    0x402a060310311250034466060402883c10265422001d0070007512036801c5148210f58a0918156002411b0145160400c150b2000025030507c6543d0002003000030b1000a860f8540e040510020079a80c0d460066071540b2608481d0103070f008041090000070f80307880c0d02030700344544075080c8040603580380e9980504980c003064602010409a40c80102501d0345400b40d0859284156010094000d5a5003c5040f4810140000703604100c0c410002d600360340300358880c1b80100388072411600c0506000d9005001000203580a87c001e00600144d605458010070b145186036003102c04e58601d83d80c403a04e04941c100000b41040000039113488401e06092041481030136001c0a03500589180c5200c55100c0d46401002080641440403090040052500060548088a0402c2c580b5039550700d251411905503c1241c2c94150303c441010113a00a000c0710341000011002060000c014080d000f40b040c84a07640c030420f400140b80220203007540040d040024641011801034400304800c0b45541c00a0f00b0000110b4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 882765062 1250 882763812 882763867
    0x102090406090b10080a020f0406090f060306030308070f2039060c0a0c0f0503100b031c09050411030610080c250b071808060613050705 60
    0x1166102440d0500c01e60000701441c001c2044032424400c0812078190030400e640301401801300025040000e150111034010850300c5500f41d4440d100d4201410032101c0c1e006a80494202d4100854160f01138810b4009481e059103614415aa60301d0045400b22018030300300d01000740c40783d0703a030800301350034140b10404000030005040c0d900345110082110743c60880614406940b842c200120f0414108200010b00c0400d03913007165514440d80480b0316100020000501d003050801c00041d01d407044000b02e0701556811030076500d456491043d2003056469802c0c1c00395064100b00c9032004a40c0040245c105410341c42d042900001c2d0b61000007400321360440c0c2405c002d0f4503002013008154582a005d60741802890700340f1650034104402140c100e4041e2040ca0300d1004018002c001c020055507010003082d5610614014407450407000c000d0002c990200f9078004071201141c041054180865501d205d85005003c0c411074002c0859980d01500c0007030500421300c60204103070070202200800b0f071942c4030a100c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 882766312 1250 882765062 882765067
    0x60d0203150a0b0d1104022203030503060f030604050c060d141003060c022a0609060d090b01080a0305030a02280c1e1e08091c050615030303011a0403140102 69
    0x8520206940c1c0030490103200d001134441160000d403810b01c4010342800c00356030050f2a840440c0041da030700c07049611141d0350300d47c503818000f0406501c00000c5100b000283d441101141012060647e01c8006407401001e40d000032001540d64140b4101a00d45030b441d076100030407a036076241190300c202c0000392111000700461020900c1407104a004220000040c3d10040ca04005203010111a4490303130311041c0360950f0200314041c5640d40c0c8000743c4807526001000300346e550011290003402080f440070b0071a18111380c8000041c0e100d40c00319490b20480d4040e20703940d1941ea02c1a10040c02944a070180000c281010350302c0c00f10244400f101d46030520700540b1800c195406901300f40791400344200704c040501c42c42c0920100041d40d0f9a031314508000311455007040141c03640c40e01092754001c0444058115114602481d0920700b941c400c2100680120140c4800b41c64194184054968a003121601a4001c000400c10b0150300e1500d40d80e95160400c140d0300309038495032214040100c840d039440340d80e07402 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 882767562 1250 882766312 882766321
    0x90f020f06220f0f080d03020309030f04060f0e0301020a0f030209030f0a0b0712110a0c0f06051e0f01050918010b0310020a02011d0706050f0906070602040f0801180b060d020315 78
    0x110002c100136006001c0c1460880d89402107190351200d080d03100d00101034000c400f103070b4882c1c410001d68005d014402d40064580d07444040041000403c40c144000003a5028451081e5003018400c40e0100f004640c1d0711000c44404860680c00f0b07500040e45a60140300d2030061441511081c458100c90601c01c000c00001d50900b170380010f010180000c1d03116080c3e884c010460014104e407a08440300500c0b207080581c40f0070110304004081d00e03108040648060f041104100c0d44030a11103c03040c51300300601019040e07884411140303140070400d014194002030080d01040d1002c920220700044501d1030b0f000401e1309201c0101003410140e01d4950801041d4002c41c00044c61a0280502c04100754202e80c3c1d00c0d2500c61060761a5070700d02c00d620902003800f500080c4030102d801e800701104c0c0b228901400d9569102e2151801c10020b501c140300d44050140c0c141c0020820003018020010b601c24241070200001d00c60380c0f01c01c80416030241a03580d01000c650340800042c1c40600c4200d03840400c0c1201010715140 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 882768812 1250 882767562 882767579
    0x903050c070914361c0e100c0203030307051303060e06040c0806040b16031d21032401031b120c020708070e0901060815070210090f020f0622 62
    0x207003a00b28a0f040d000402500582d0741c4141034410351380350420400c1c8855840041c1c0c00c05010041d241691680b109103035540f01d801410f020079941041e40c03940d110703242c44c40c0c0c100c81031100024004d506403c10000300c1c0c00b01d4800c8026040d0f0910046004c0a80307503480d502c1d0b038100c803510b5900203019040703401000144070402c4241402072409202030071710b81c9496583e40e00e681100800d5445509040c02d07841c1101842a804040c080c504003150500510000d555250f40e64108200d501d20742034441e203244200c4c04140c00360703401800b40d40500454030964a0010201d8059001c080e8101540c80d90409050751401741d0923002c4c0c05482d1208000c400d156035030b18040c1c031180c2d0f4082c2c040d903010f09402c005580000803100101d540b12480300303042d91191306c01c403409031007540d202140c1c6108864482c120314004120841c05035031030b50210340d14403001c0c840d64825640d031900007504172042050908090f0030141104036425000404070340c80c2c00145202d10301d4091628004101e0b00b850010188624403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 882770062 1250 882768812 882768851
    0xe0d02010b2416031b05060609150a0303030e0114040602090f060408100e190813051009150210060b1b010212071409030706030b040b041505040903050c0709 69
    0x246410b48048400c9400c60061224842d461200d5020b1542141030402d00d40300d604050302c0d11011901020750070705142416643d840c420380c0c1507881100d041010504c1d102041280c030800b03c20203403e00210510b181c90660042440d600844225501c07940030211010000310b1030307446144201401601d800e019428440e482c2e8150881d5406013804100c00d0010380400140e00c23001c01c26040010416402e03640000d410f000e413641e842203410315801d1041c010803403200003a2103201e115001207840d80d44e440701003028400e80f080c040004103240210034010442c3d40c006002982c403040c01115016040360031210103c0c1c0d41e60340480982f20380071803040b00d035510104107070200030031440080d0709100141c05451070190b40a00b002090084d1084402d05400070881580c841e044010240d0b12040d6641402902601003449401d20a61800751410511301c1e19100c0c0081180030303800c80380b5006050a041c440100000001030701400010721640190001c100304000c044c00c500b041c003041c20400d9030012200e48 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 882771312 1250 882770062 882770089
    0x3020315030105060f0621070c1a010f061115040302030910030203060f040504030c1a1815041e081902241506121608130c090f0e0d02010b 61
    0x2e0341000c06000c619078903805540200e0008484080c2d85181201c00780302c1c116003180206000440702e5040010381600200007262041c0284100b0650a0180c0b0801c5201a824050304019601c0d851052003440d110300c0440e01080a11800c03607610122014030f1200644048404800503400040c200b40c180c1000000c2000c0d401c42410194158100302d00000c0e284083e40800c113000c2d03aa43c0f00081d00341031003241900c42542c0c100100c02601c0a0044601007003102c1100c406c280703417070000e21410b000d00740001d030300f18051945844102c26031a0782c0c0c0c5c0c000f82c1c4c0c8448500300440148036480c1c0c10100780900010448036400b1340564840c1040800e0190070114403d800c18210381c6030208004211b44c07180040d6070f014090b5400303a500d03411458001031a80c05412541070040c2802000c1101005080d18003248802e5641c0310000180d03981c40d00c0001500590b64001d04441103110104008a034503002070060310070b000800b250000e11a5181d9140c40400d286030b0300103030f4440702e41c0c84090074030b200d00e030015 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 882772562 1250 882771312 882771319
    0xc04120b060a0f0e062e080126060f090c1302031f15180f0803120a0c020a03140c0d081603090c05010c0f060f0c08150109033003020315 60
    0x120f920f0030382e4544144000408660040914040c064a00c81140c01603080112803c000f10b446060407490040c8200f00034060000c0321002010744070085403c590b0300d0502003480760014800c681d01e0190206010780c01611400c8148201407010700f066030744564211010043c0d038401600c07032800404200c82030500d043c00c1710851500300418407401040304036002030350aa600b000b425003844050b514140115603800320300f881000e100003143e404408001000481c1555160540503146c00c1111012104801045005a40000d061000190150700404042c8419008180c00c00c820043c1660600356100602800601c0d14402c00c018000308100e030130524201842c0400c0b10351100c2e13840c4040d1044038040c46050102c46041300c400c100d007800004c0c64a540c0580244013101e944180403000c0c0c50f035504c0a00109a101d0b000901503100750401900303803c6d050359600d000354070316110069071503504202c880c0115001d2024008504681d072500d050a0490750300140d407403400c866581161040d661f0094070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 882773812 1250 882772562 882772589
    0x803040609050301052827052109060f1c090302010b0103060b0301090c0203090d1101021902010804080309011e0501140f06070b090312071707050307080114030a0507030606050108010815010e0c04120b060a 90
    0x49c5150311050703c588520030b0714525030741e818250002804d406a9075500c492102110004105100140c20041e0381174440c0d0028031081c0116001507003551141d004160240d4001d200402c501c9606800007440b0b10410700580340f8104400c408190f04084280d0242d8000000b05001206541e040008403c0703440c203106200424103e50740001c190103030180000d04011408008a401001d080d8018100e200400b0b4910421424010320000a450b091140802c90440700d0003107441420700301d00016490000030040351404071113030389042d6a0000509004203030300c01807004038171980009040d41d001d0802c1e0b84540407078079903107805224242c070300034104000c114091041c0024160030180c86410b540b4000c18040000310f800d00401c1c54100b900030094418400c0c14400030074402d16901240654400380d032103100503070301d8200b0150758804c00c00301a201240300741e004100262070103240e2030f0800850f031f903503500c3e013942c0c1d40c07a581030015071130300981d020242c84060143d10315100d40164010843d00e0300146 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 882775062 1250 882773812 882773863
    0x1202030c120f0403020d050a110a140705030a030918060506180406270e030904141b070b07030c05070804080d110c0f06071506080304060905030105282705 68
    0xd403201041036246c0b00780080491210b005501900d400e21000c04000e08440f000501400d0080841940400c02c407100e008840001c01d860501064040710706402d0303150030141c50b1804007007482c009501400b500380103507100e001040d150f0311640144140c4d02c42d0540c2d43c6400c0d1500d410003089400d55480501d1103500c403041000705503102c030300c0490740c0841c2c0c900000b90b00680c040c00900b14450390010340d0f8020b280900c15400c200c803011009010700c003541117815421041c203a00580d5442141030280000c0d44010004080d184682c2180080344c41170b00d031450900c1d105998407440383d0000e03000180142c10154400310f005034000c20300d8514134403800007006a50720210105041040306e41e90355005001c0098440c0601c04482c407001d8021250300401c0140076a031341c04d4607450b03400030f00600b00000c0310f07040005050b24050050900510717030301c0450002c0d41c03001085100008d461041d80f00b442600d424844045004000300c405851890001e00c40c401c2d680380c0381c42820955080d40d4440200c08080115 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 882776312 1250 882775062 882775067
    0xd110606090a05042307030308010f060c1704090c030b100309170c0102070206030f04051903050d0216150204060e030609060402090402010908010905030904060b0a020a060c1202030c120f0403 84
    0x8a4002c0e0141c1d40003d00d98840342084c3c45001c60071004003150050720f00303c6600000300058690122400703561921120307621400c03000d0036000c5038420703a00020580ca0390300c0c002c244001100c000e410400f00741a89030540e02e001400c140c138040e91084010940d01c1046843c10304060340c80550780c04461904021a10f415943c4a01d42c15108102e201503440100c3d65041e642d00960451b8080c60b00204029107034541001a1241420200d80072142d501075010038944c0c040701c100803c0c14003030b030640f900b80c2000000e844250080d0881e298864000510203041c5021628031000802d102405190240c0c0d030b1800c2c00000b50000c01c02e8400c1d40d00991104042203001d10b801314420790403560403a148020307520f440c00100c0e0302c0a000e412031210b80d442c0c031450400300700d0004001d0402e200117413010300c4929912001048140200c041c450b01623009614a400046d849a1200030040c03070b5801c10210103035160711408101c1e0421600c5580d581c07000201c041043e0388106182d940309040f544903007031034030300340d90300 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 882777562 1250 882776312 882776329
    0x233012408091005040f020307050303190f12020304050106060905063105132c0d080405010f0f0603110301021309020711180406142205120a020d110606 67
    0x4410800001c012500000741842420080103c1c040248044c3c20a8200301c018110014070032031003441104400142820080281e65800f010000b03140d078001c2151000341d40e86407821200744200b00156a08642c820030510145010300d000c0c100000f000c40c10040007030b25501e090f8004038450081488000c600306a590404041c486111032179084841810b030440744010f215400041e03105240c039812824110b8542d00210000c1c4907005000c180c40f003003550820396468880f4048049800221284901c4c60040e444ca6421620030320000408045011400c012110503d09c521222030300c0740c00030410b0080208031440d030601300b00c008500d04800c0c0752107041c0584081c8102c940349600030a085c030500c5000010302c3d62802c4058054206a14a4400c406000c90200c900b200c505241c01d01c0100f440b0340001c140c603c59030288600410415800c1c894074040d00340315000310307a14410058a2039040c0103000c09420050069001070a5071449504003801040b03001c0c160032500d07880f070f504100d00e41e03845440 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 882778812 1250 882777562 882777629
    0x70e03030414040f0914060c13050d02031f0902030606030706080f1b1903140f190609060e040c06021911061215040c02031606020a023301 61
    0xc0c040090010400b0502824020003503000945c40c00c0207400a00c424403884e5445d1882503c2a54050381d64041300c01e419010303044034180a210500806d2002d401c01450300340c07016000600300c5e489007020084545d02404200c480c00a41511540c0442c03c40c1010066190440d104030007512506040000040c40541b00401070b400c1080140302080300d02103000c0c0041c89000e801e8004982d00c1d1a0015540104450205070b07400183c50545900e22010704602200d005c0d456403c040d2540d40c441d030071014501c942c12202d0240c0103554060004010740c90780b091034010480c1d584402c03900c1ca410300303140d2002107542c0e204109540000780904080e442600241d9400f039800303800c3c1090300e01d80501060160081c4041405842480005d20402c0c94003400b11588903641100d042c820500072401c100e0f124043c600034010780e0002412032000240c850b8002c7d060046042c4119855510400508451a0350101c0302c81641c0d460403034140c01075864000e04501501c0c00804086014411540b030400b04020701a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 882780062 1250 882778812 882778829
    0xf09091c050c010501060801050901120215031b040e01080c0a0f050603100806071d0604063903030b01090f051021020705160515040e040501020409050f0f070e030304 73
    0x35158101402036007600d03810401c1d003008104540c0c4543c0042e14100302806014403418070301c0d000050140341c460a07280c840e0390181c556030900d01c00d5490100240c1028040420742d9410501800ca045e0701c2c4d1018000610002e46210002d5240441131420484044802c2d401007509804c00d120504110306a1011154251199030342d9603140e008111442580b40c1090f03810f8010742087c03024551380041000d030b581c03114001c0118843c0c1c059040000e6445180308080c041034106c02e2101d04a49070109413612800c030841107030b002402c000d03000b880710440400200c000c2940c038000922196402408403000d00514a11010420305140000c0d8560002d0110802000108003183d1800c00141c45c1035401c040364020290740301c805a280281c4c40d5003403050b2088002d9040b00300042c40d8584980d601207550000c0d9001c0d0f113080d003000411800d50388000e205076500c1d9020000014456180c1c864148125000c00a104041c10010004045407102030300f00410025048031418540d600801190704840245 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 882781312 1250 882780062 882780103
    0x16030203060a0614190c170406091703070501020a09140409020f040c0225090e030a050f13080706030506040c0c150903020c030d0f110105070e010f020c040f0b0f0909 73
    0x42d00c05680b44540c1701c0d07090b14020101c41081c0c2c00e940045840165038403c851601c4048040c0041824a000391300c00d84000070221f01c4200715556002c424a441d4100c0042501e1810703440f42c4405003660320280c00e502c0020f001c1d00707007000041160744a101400100300d03002d100c04406034000442c0400c8485e2030701c0c89640e07243c40f0311062078000c10030214081080c1700e00704c4c40c150710050609854851403140c000d10608001c2c58848000c8040304944101090341c58090802000c019081e0050700002c802802c00c260801002c0740301281005010000d04940d5004111440e0640600c03081c1c1c1c60f02d0300302d43c0610a82d8512000001c000301041210001000c400040c0d8084904040b4900510034102d01c0c0c0502078544c5141c0001e0348884010900005500c0d01d50b50003814103419800c0350400c444940c00204040301d00b84466100b004c040910141034812100b0300e00200d000201102c441c1541c513811039541c1d08a60025040001c044900100101c90606243c64002c02d015141c0402210400b00c01100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 882782562 1250 882781312 882781337
    0xf0e10030c06080c07020d0c050312040e010303050f0d0e0106180506221404060e0106080a0b0402040504030e04150f060c0c0b030907030f08072018060a170616030203060a06 76
    0x2500d040d60b07175071600201840741400f55030401500404880c0102030080c015007210f143d144c0c20741c030304803000c41c0d101c0f15140d4440c1c2c0c86d60301c0072152500006901c20080d6002c1140c10b683d00024099128840c1d040b0000048181c40e255101d0340010800e0400511281400100012590b03242c07a1406103141d10500c60302d05402010138900244103070800e10410445000c240300030b00040340d021200314144800200f00082c1c4803000b07183d545010940003800c0c0000c010018005051035003000d6000fa00c642008000038420b403001509440702c00c3c60715800c40171000c01c10040e0708181110240146040c0c07d11307092110160b100c03c0300c1b0440d41d0183c8007000d4000800720301074850030060100110340202010364190301ca46401c61455200c1c2d032050758005071500c018120384104100912004ca401840074009400c0c0c0110f83c024840010501581328800340c03000103209502d06c4d00340b980d81910002800c0c4a01e04004003140000c82c00c1540410944144100070541d121488803509650050a0902c42a941e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 882783812 1250 882782562 882782581
    0xe070609080c102a0219080601030818040501060f02210f0f070624081f0b011710091b09050d1e0807020f040c0e040c180f0e10030c0608 60
    0x241ca580c94036140030004c1c00031603d00c54941c0e01c60414400c80d0081c1380042800300120075805039015051035074000800400c0014481d00c014414007803441d0070003002c03403d03070b038001f40c00c8400c241e00541c08188039104450026a040c050348444000140c607409011100000b04035250068480e8401148400556110164806010703580b80c0c903807000041c460444885480c08001c0e4000480c040007600207207000c508c0d0030022543c482d2940540e200800d074400902039290280c4447d000d900c3c14080d03100200503500142c074080500c6441000d806807030781c900c2d01d0015401ca07040f119000300d070201003c0c2c1042115030300040810480c2e004503003001e1031684905191010356003410045002030380d891002820483d888020749540c0b0300845000d500c2c10014024017040c2e4074440b140800049500c0c0b50040140780c1540450303d0249681343c8200300010480c1c864260070070300e400c032403181e00010070100b200445295085a200d90111504001d052441d034503003514102074011141070117204030000b002e21a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 882785062 1250 882783812 882783827
    0xf0921050f0709270b04021509131b0315030210110d0c020f0603040c180603050102033408041101140a030501030b01050d08120a0905060a0e070609080c10 68
    0x11009815244016038800420300280b00344040480c0e92001240d80007401080c0044c03605141d60071a008a00558443d400c010b460b403218040b14482d81c8080c000c0301c1041d1981240304d40c1c1540c01103000124925840c51a9804490292900c405c140c02e10007460f042c0300d8860501c0045a605940e185a002958801542d00094800c0b4070039151003442e50310f01600b07510030510055907000fa0390790361480b038a40c0140101c038801190060705501110700c003000310502280c80e03090448bd03451ba0000308507403a41e4800342680c0c015125003284118406e401280c2c0000400001640c107007a401040c01409074402c05002e1800040002c0c0c45200003441c0f15010740d015810b00e024404403400819550202410080c00034003081c081650300601410010905007440e40c0a144000c3d08240c2d043d0402400c0400f001201c14001d149100360b58450181100285c0100b1441d801034483e11fa01242081100c40c80780e240601130742c0580100010140c4c100036034080802c0c0c01c00820010ba4807040354907522202600c00a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 882786312 1250 882785062 882785083
    0x120411010816271a070b160806010f0908150f0105040902010804060f06050d03050c12210a06030f0f1101050a27030c0611101a0d0606030b04030f0f092105 68
    0x1925140da05013103054070300004203c0d1620416040081c0e07110405403140c0d4200b14104500032841120104030f0540c09203100e4400618186490031815440d07040540c20f00300d494a1240c65280da80080c8910302e102c1800080c0034081c242d4003042102c1c2160002001c0c0f100c00350011300401d58400e010061408180c01103405401c002d40302c08150031041c03400609943c03000e28020114040c114009101c0040300044425507070b00301c4650021484110303101007445002508401489a46c1c01d00000081d07000e240c003a8013680a04094960341c800d44c00c004181161640205c0d0400a0030406c08a135190401da40200d6941402c3c200803042260a041c0c07145001a038001400c000f0915500040003540400011810309010b030030360b0103050790794401e002901c84400c01d001c0c4a0141480c91034803401d101d9105680f482c000d90010820b2941d948540c140400e0903101030300095030782c1c101c95284580010742c6500b151940e01d40200c01500d0040c50404650300017030391140f0f40e1306107103510041c05010001000300 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 882787562 1250 882786312 882786329
    0xa050a0b0906070f090501030e100608030901140a1d031f0b0a050a0509010608130c031104060b0c0a08030c07020414070816080c070812041101081627 66
    0xaa4818104420321000444009001e4810741002546451148240790b82d244082c3e207030364000e0f40c01e0200540141401d9801c8200902c140340c802c001c15885401114002d150000c090347e9a140400001007601303107200102c0e0a80c0380c0c00c000e25030109074000407000040b43d1600c001c0d030000b480140080d082445c0000c103030091095052a1010700440c9a003d0465900c00b00d92110405644505011412000348205c1d0b6002e00b4080040004a000c1e07506990301c0021045031001a401c2035481110008003a0070580f07483c0e40d140356078001405c15208200140c00c00e083e01c41e04101d48490060f070303038100c407a0b4000c080182c00700c0400c50500060041d40d00c41c13a03000300140f144c0340d00d000c0614400d88048410000085260000c40c3c0e40b80011040c00c00d41c0d0503a0741d505100c642e9044400c1c5d201f41c0c03088500310395000042010003506031480c0112401284100d60f15450703c04102c00041001601605d50080d4000b19120300c03007503c0d0403184444003100c0104e9500c02c248024808080c2d094410f9011100703 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 882788812 1250 882787562 882787573
    0x201200622060c0e04150509060d1a01092003060619052a0706030509190f061e0b0a14090a0603020d05030d0e07050d0b09070b0a0e030f010903140c0a05 67
    0x1115008810400131800030f54081000704c6d40c86c1c0c011442e80c03c1a00c9001d822040c450049455804d058442e1243d85005036445042501404260704901400b6400310400f5a521207660300c8042c140d2034150440b0400c0b04c440c5003107041c0000040c126126000840184400da01c1d10341443d14010400d03035100c0501c900301e142c5000c0412459040300f203600c42c14003240d409007900100d40c05000307110712401030404400800e04002020b8454540402e04802078078601c080c8505c0c24001400c60282076030004c480080012151504420182910000040a440340714020424001440c209680844201c0102c41d40056a10f40c641c8020061205400180d00148010442410700c40c001000b40701d285d000d14010004084d01210790358070366030507006655210321070ba907030980415015070400c0d40108100043c6c603013050b035a01880b080d940c0a652010046134840c2c008060920f820f02c50310810140c81002806004555074001b03040d2003030040c00003003100c00800c0640c3d2400c010804407000c43d500804030b88 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 882790062 1250 882788812 882788831
    0xc050115080c0f04020a090335040e07080402090c130f080114101a0a1101050f07260708040318080309090622181e020120062206 57
    0x1621440b990042c01e00038001401c4455550070248203d502504a903610084054119034a080005411003c1001e00306002615030381d680990081b905140c0010301c0c2034035545c510f03006501ea40590001d010714203220100b000c01015071184001141c0c0000c505600a41c0c039400810b800886103d207400120b001085d48001007071007441588038403034613030b070043c00181d4540e11484008200d4007280603408a481c0700c08002c82481d01240c020303250b905003504116000d9480109041d00311401180c450308015180340901141a800c000b8110891341d02801c04006294449040c245c040006000c0400b08107050b070001c0c040c14400c1ca078001302da407c00007103030340700b1948c80964682c0c0350010700c1d034180304840d5000070a6084c41d04210092849160310401d039034020100c0880c0d00203145414031844060166007000c1c0010f00a810340364071441900c680180c9202c0980001003401203d0082e4007508000043e0140550100151003035100c518078a55241c0444c140710302145441007940002c0c0901d04000204 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 882791312 1250 882790062 882790079
    0x100e01260403020c2403100306021204170703051617030c1305060702130504021c1a0f01050108040b07020a0819020c06030112030305090c03062d10060c050115 70
    0x2280590b01941c2101d010040950400101d020100c1d00381003d022003014039090800740e98003071a40f0940008060306865602c3c2c943c02d003a0b0f4082010110040c18500810042002c22060b008000002070060360410b10541c0d00604584034068400824490071403141d401c2080300300c0880410905070800319120704100b44165003136008514101c6a16005003030101d002e080a10035114070700d07001440c82e40e06861034015600100300280c41070b031700b100003001c460841001c0e4801c070360006407040030729444901307681c003d42280da800034044000245000f40100300580e845201c0d0303074009421000c01c400c1500c8a403021b0b407601c400040d0050512001144d120760320814484803448140664094410300400c0c102048030320f1009001d07003002d2081c2e500990010030311075488980c0c403040c00011941340c1d0611100003883c19000b07c80422501031311454444585198000988401548181030485420117185001503804030380900c000300300c15005108140b00e03094021500c0600d040c80b095180c191100700c1c4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 882792562 1250 882791312 882791387
    0x909180a0c090b0306160318020a1205010614100809161508060a06021c030b03060f1e04151e050709090e0712020f0102030c01060b07060c050306100e01 67
    0x1616800b924040c000c0306541030128485201d40c12520419500c80d8220205900920520940c001c01411950000c0d00503216000c8040c0504081d040003100b052051410b6420740c2c0164010318004000d028050805448121204491800b01d0900310480d03611a100d05142c02c007c0300408010801c00400002d40b91102900301d03500e4140742d41d03056450369414007030250640c801d11585006038840400280c881d42c80c801c0d030341c8108055203000300308041004002880c000d0b00359401c0703003499861024001d403461680c548074840110100b0141c0c00345000c0c1c4401c64400b503201ca65200090300c5110188248001e8402c1800340203029400300700b01d0900d80001003031742c41e01c2d01a02c00007502d4030b80640008280010781d4030449844509125641500b0343c2400b03100d4518940660651005000d00e9a00340390a0050700003901c0a50b40143d02d44610382008800c2d1002c561010b42800020424040b02d0745411312512811201414286135500c0303d0380040f07409161424041c900c00c1c02103c545101402c04402 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 882793812 1250 882792562 882792569
    0x3130605100608160c060b0a0906080313050a0605030601030b01090314010b0306060103060f1401140c0309100804030c0308040c150203090436061103010b070303060b030c0909180a0c 80
    0x555144942c4c4001480d0103114001c2030050210f00f80d060140300099098100520214000d400200e034280d43e0201c2038191703a0181c11541c0140c001040e4100c04e4140702e40d40c0001000e080b0b1789550035600d0210b018003940701c0500341354100745e15401984c207a64020444407000307540c003d4110f02c43c0301d110b55034240200f000700d00191081c010030f408074880350f10074040e110950341c800d0742c010300311440d080c06012845c1c0c1d0104982e040c40a000414003d2401140c0500000003504010b540c0d280c00b42020444803040400c840300900030b49005210220364440c61101180d681801c00940940340c5d8140303421070314010b520154010445004000c01c42d030780840a41144207050310706004a6846c0c1e00c40032810b07101880107924214143e406da104001040707042088550003940000790b041c060601c2000a640b090700f00701d2000c540064044201a8944213880007003208a404e83d0131810a04045c010310720070380354800d00c42e2840b074000c0b070240041c503a164107480310110304503000c102e65407601071f007107010610 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 882795062 1250 882793812 882793817
    0x3190302030903010b0609030d03051b1b071d06090a0f0f23090d0f1701030b0f07020606090a0e030f1210080c01120903180905011a070c0b031306051006 67
    0x6584071a90a01506407185001f004010f4078104000c018220003d120041840d02e40c81c074040c850040802d48100180b0103200a00e10301030b0b10b02c588a032060300d40000355010b4150458000050701e40c2d61b602208040d0010004c85039140d29071039008000e0040e00e40c00c414841d40310300d00f4032030341f07074036403071513110040015628141142c0070070350019500c1c074914116410440d80c0c12200384200124400c1d12001c09205582c1020280c0c542162603d01d0008401d0b001140e0070742504c8207018071b480a80c1c0013550701c005c0d148020101d601d00f4001155040788094109205039403a410001d0a41800b0b00590304001031400100b52200724035140c41c040e04000780c3e00404a1510000302180344c107004190442c06000684501040702c9082c1501d5006004514058081181c0040d0314002440121180b03401030522481c045601c0d4108402c442130b40389039004082810000304000030004101c0e0022508454200c00c4860300c0381c1d183c240d480c0200c280713048014041440d01040008074110266400e065480300d5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 882796312 1250 882795062 882795071
    0xe011b02010e0613020a0f06020106240917031b100608060408070320010e010c0f02070f0302061315021005010e0402091b0c01020d0f0e07180b0319030203090301 71
    0x48005900b01d42c140800d409250b0441000103010000124480154a1029180e0b54070503580b45401c03100ca80d03440d040000141d448403020012012030b10304c65804800d850041600c0c1d101c000c040030700010881d10405c1603880781c060800008050900c19941c41c81003101400c5141c5288255650311448445c03410a2100d2030410040791003100001c0c0311788200e520a9002c0e00c1d164858406580110035820810705003481340c2c0441c881a1000c0c010324600790000c00c004610b4983d002000742c06114035004160442d40440300411005407000e1469084a4066131001d561b005248480c3c41031031066001440080c1e4a2503102a9044d40022408180c80b68204108100d980f914523070b4448440641f000395000280401162030048030f10b110004260840c089d036454000101106820390300020710447c003003a03451000c80c1c043c807420b010300e07100700042c030f0b020740405814810814015002a10404419076844103841c20f107883c03c00200302c070740e904281c01000311042854000d50340e51101c0001406542003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 882797562 1250 882796312 882796361
    0xb1b01020d0204170d0903030f030e1920060f09010e030a0204110714070506030a020c07152601030f0f06091a01180b03030415090e010801050f1b04060c050a060e01 72
    0x240c680007003940c2d17050795900a1032109c0d100032000b44c40c0b540c4140d0060b01030440c800f03202001c564030010925100764034150340180c05000c0c20965003901100903005880401004101e111410211003080100b424601429082800840c0c64401c510030b00a40061410781e03170500c0310780c25001610b101441001070101100340031808a4035050144160fa421a00a202245110800703030090200401e28408071140942e4030940305000d00342c41da44000206580b182e50b006008011235408942c010404540c9001c2d500d1903981001c00f0100403c044c004200145400c2d040103c071380c1000c2001034011540620060000c60b0f00000780000b071094840e00a00342c00d07a940400980d00071903c1041c4010050f5013860302c4d2842c00b0100e559007004080400c8101240071404007880d040d114045c0c4440c0c4000569840d04408d03110380c1c410b024040468480b1070721a0042c2c0105c0d0841150150703403062812080000c0d00d842c0040c500000300300000e100f1420b1403104065a0015403010107101d14142e100750b06c1d43c06 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 882798812 1250 882797562 882797567
    0x1d190204030b010e0702010219030c0906050c06181c170108060f0c030c091e0906061c1d010912030515031b060f120601080a05010b1b01020d0204170d 66
    0x80d5120042510800704010800c2d410190401d5038030181a00000d490714950401c00290340d5800140e04010a94640e004200c29501038070810180c444c2d070400b00e18044400d00c00070741d0748100800c103d49140103099101409902880761050210304219000000058218050a16405000310000d003500d00000042d40d43e0001840390b00880403202803d88648603060028070591004008206600d010082d41c111a02c98a404007d0742c0f5520102010101c800e200300030399904050807491044e4020311040c880300c500d005075941005d03600350001802c0300040c0042c500b84400c01200d0a444c1d440d2508a46c10b001140c003040d0100b00440d0f5080101e596802602410303c0b102c50451501907000315452200810f94210080c4124001070080d0308007004d000e428400e0740d021040f4001c00280120a110042d604403c80a4000701d02c882c041c00f142d07051100b200190301030100038608240c2c880e02250300003242941120803489038a1019556261a01140003c940045000003054403030060701d00096403 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 882800062 1250 882798812 882798817
    0x15010b04051302030f0411030f0d0810080327133216050304110a0807090b01020a0f020d0c031b23060a0c03020705130501061b0309060c0602041d1902 66
    0x41c50417a080c0b41944982d20b51b001c081c1d100c030076250780600c140d50195620f004208100d82d444611951b41098501c0d040c5a1184000c80e80d82c0700301100ea0046c821803148200800c01400718100000c61940c490b403c82c00000c0484240d40540d00e81c641c5450344c56500031040c01042007080c9840480700a0400460b5002103641e03004441d0306e110303100607080c0c00034060b219500554104d4001c0c1c13408001c3c10302060000307251f5105640180b05a41c4000400c02a0300b9a40c003414510003402d0014107200244c03611120100c18000c9002171103620075402c0001041800140c16010396001401ca540d030f0410752a68124a0f0704600408012004081c050039180c3d0f100882400900301c0909030a080c84843c0380140c442010740001102580288400803445171521480d90700808003203980451194075028000d055007100e982c0e07101c0d45259513800207000c01d0f001741c2d8a0003141e00a160402c0385811a05085000307002e15001031520000b00da4a441082011584090040c04082d46d140c1c21a08450110400c82c03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 882801312 1250 882800062 882800071
    0x13090507170610030216140a1b080c010311130303020705040b0303040b0702150d140a0605010c021503090a08070b0f01170709020d0906050a15091e02030915010b0405130203 76
    0x19580e2034284043c0740c032a4003d080f8030603d1011808485d100d07642c411000c1d10701c2c00d030184100c1d480b4103000c100303001d03c0801309a000300d0702c2c207506175400741012841c03600c4001d000c60007410f03d5110b030701e00c03080403d001d0100c0c1c0a05030001c07000440552249802525241c942c843c0d00c1c4903506042c110030403403602104680482d594850800d1900100d0b60038000300405242c40c2c5031074800140000c144504107130142d00c084069007000e4002a02d031400e03540007100e2640d0001c604016018407080016124401446607c1e41304503000e5441e60b440c25181031074000380600c0280f441c00003050240402404103d4140102004580711249a07218510702c81641ca0301000c0011540c01402e040003010400d41c0100f80801e088003008c600c00c0e4058940b9810b44100360b84c0b00da14141c0c0c2c0c0106025030b441d140f0416029200c084800c0c000017541f840380800074102c003a010b00440d0b071f000011601a480411030320403045d9a4141d003400c55a03464003158801c3d0000d10409008050345200a94046458402c0701c2c0304 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 882802562 1250 882801312 882801319
    0x608070e0105040903030902090406050f010b0712300204030c1502100f021303050a170910180306060e0f070212070303023106200d14130905071706 65
    0x8582c0b901c41008043c008524059040c03558032001800981c4030305013060301c1217000b1200412981808592000c2c0d40505130311003082482d080c4540b10000340741040030b804420140c80e040c00403030160901d04007040da03c031041405141c1d560034010646000c0390043d00449002e000407011080d40c80d01d80e032031030001880c2c4c01401608040d480c039841140c1a80b04603803c40c1105030045c244084103200b00384d50116900243d40c1640305104220410105081c00780707000d4008207107a07003000d0a18010400c1107030114001e40034006405500d401540151034104000d5402c108141f141c02e9480c0490b502000c01650f201d900321802400050400340001400303480314000cc58030501e4110b041e24110b0094010031409401c0c0008002c004100e030091803026035039003020742c81d40001d0f18500071001d00b4a030760f1b4100c0c01c245014400c5c0010742c0000042040030540c0040c2c145200d1600c07840310040c600d40300395410302c0d040b0100c00c20003044146c45a440f643c800c09203500d4946070215442e504528040c001c441c072650 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 882803812 1250 882802562 882802589
    0x9020f0405060607030807050c0307210c210e1507140c012c12010b030d08010e0f072a0201260a0c0c08040803030609060d050a020607030905100f03060807 68
    0x71b2003034100729444015441d10f04d0a11482c40307109410740d40709000c1a24005060881d4140601b041c10074024800d425051415402c0c4041c0e44040c1224005904e0f248060700c11800300e00035600940320140360b2200200170500480314103201c000d0b170741c1000310240c8002844848603081500c0010368038510440507121495514041a10094203101446100221300314a1000d10002c0d29021100c4c50f0b008505000807419a03005411305103010991b0800c08104000e6000420590005d2091a46c1000304100c1210490303a5841041d52032110b11070340f0350040100c607000b0075295180c0403d42d40e0128800d03a035403600f10003003040504030113840d504100302d0803082c28045240000d20b64046101d858050500002554007030311901103540241c0e100b86100d80000081140c14905622001d51118045034044220410343d01d0b05a550040040000c1c00340000144120a15002d03d4a440042800a01008041d07891303150090072100705044003004a401c0ca180801d01c0c2070007003080010b90b01580403491 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 882805062 1250 882803812 882803827
    0x130b03040b190e03191d130f150905151f180f080f01050c1e0d110412030206070905181306150305100c050301170705030105070309020f04050606 64
    0x80680042140704202c65920812400307801014000707000e10040d84c400940c1014806500a41011016404560310b901402c3c1c80803011354480406200d50300c41004000749210400c04154014418800d800c407041e03109107000107503601281c1040e48218244c0e10020031b00140541800380041c1951002000c1290144043c510284145181c44080d6680000d200c0c42a54420f00000c01c1a41a0002180c64000034494413080c982401000d811a103581d920901c2c050042d460030b410b10b0240b03000c00c0300c608800199000764281a0f0040854040c040c0040e40e17485036502200c08240005810072030140c010300300040c003050b000716010000c89002800401580c00400b0749182011b40c001d0290502d440303254858800308855104100a0000030300c42003601c0c07819414038901d0840e04258001c0d2040c2400c8900031055072003011360f8112000040440f45c0454103000050800040d500407541540c030300f804101e81030b035041d080b500d0442c0c0241c80d400c4498100005000982c0c00854202d50000030801508 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 882806312 1250 882805062 882805081
    0x319062108070c0b0a020102210405060106180b0a05090102011a0a09090303090b090a0507080f0709090602091e120c0f150706050c0901030f0b0a03060b030120130b03040b 75
    0x60696903c0303100c190070301c035844819210868103c4542c02c00141c1d40031079102260510f05c19881d00d05030f80404101003918060f42c032940d4400d414050306003080100e8a50302200e811504220002e4461103580944480e14954010829000101c20034015030818490140c850783d2001c8480e886000a031003a6042405e000512010b000141000c030b04260380c89031040041485a440070703000f01059805400c1022103800d00e5441c25919400820160304078964000c43d1010000b400d07070498000c42c80116a081007400c001d0001d01801009540040340c3d81407036050085005040f003005503045904410080319112002d55801d040700483d500040b1640d25507220b4909844000c181001c0a20300614144180d0344180a8550590b05281031000101d03110700305607003602440440315a200310411130f04004100082400c001880080d00c0c165035120800f2854a0a42001541510302d83e0300360035010358900c655006070b01c1280588403841200c20003117010306da010200d034011f50704030003001120b84801070f19 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 882807562 1250 882806312 882806317
    0x3061a09042105090d21050a020d030506150327010b010905131d0c03011a010e0f010519050304060e010603022d04110a0e09090a03080415020319062108 67
    0x2c240c18800d0510000702e0658403c2603510207184607100480b4004200001080310f0b00403c010740081c01410700050030026400150740c0d4100509180c00314141c0c89200200d020488100039410344850b002080007018805941c5004400078002c100d1341c10107003c00040d80c200c5500445842c005080381408224501e0841d10710400050508000030f03480c402c3c0581550050342d6440050220782045e0341c0d1420070311b42807142c00705500004810442400034040000e0120b400040c003607108020101701e40040346d00c110180c1d1240d03840c944c0081c850198030351010f05950401c490458a090a11408101c140018003c0d07600b01c1354081c000890b025481d07040b04094840400b0402400c0b00c0b02c03130300411540d03528050442c03080341e052061640e410101c1401800da068000100e4003501ca203034144003140800040110030307260149045141e54031a403400e140d04841c03031100702d0007182c000300500800d5030281c0d22840d000300510b482000560740e11150781c03407503000401c011f02080c1079011b403040c08500e81500 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 882808812 1250 882807562 882807623
    0x60b0a17030409240e010303030612110409051606030b03071211101e0c0204180b0604021c06060504051f020c0d06020910090503070801060510031508030403061a0904 73
    0x70040002c0300000080344504070303030384005c0d42e14054400410074140c0503c80c1c480076200c0c000c0303e40d100c6225510f9061001405400d614041c0c1e0b42c1e0445001404000d004502c212103032500e8810f40c05070386007401005402507494162090040d0380f80000c0103002618609282c03940080100c04403040c413010090410007000800b400d002003c55942c0c83c0f0101c070124034202844640701c14030610814010303c0100c0b0700460090100070480210900410f801019003680410101d1b00580c1e02c04540e603000001601308400044581d041c101c01080031504031000e001a40c40c10740380584400c5104074405860480302c0400000341e00400079521090810500784e0000e18040c3c4000b61034005488003152540c00c1003526600055504041071215140a200307040042c481c00000b4801e090400001a0034034100e08058070616035a010041c0d80d404191400c2c0e0020030b01c40c0c0a4a0301c86a03a03042000180a00700110803000c581907250007410f01d807112074140229081040529400070f00355000303500500266 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 882810062 1250 882808812 882808841
    0xc09090d03110c010f02030130060c0e03060c07030206070906090608070507050f0109020f0a05090f0405070e01080307020a09140f070e0d03110f0d0516020604030807060b0a17030409 80
    0x89043d500710240110250003e00600c0140c3d00e615220000c50f214144480c0c0f0600d48500c840c03035501311b804454115800c0340e0040030004440d4080d181c103480003e00c2e42c0406801d40280d20800a184d00340d580a0400030340a902510300c3c40c0d4421500300da01114a010701404110b560f04103002c0e09104410b180d900641c42c6c00d19501c2d190301516020314200300e010705800c4503911015100114184610201c04148068031000a044e0070100024407503080185101c018050800c0014240304041009070000d00340038000e030034296111858191658080700051380a0040002c00082215a6114803080304928445110715511034050b0b0141074103014261108003e600404566a43e8601c440411f140c2d2080c0c40b4034400304640c021641c2020001040000745401050300254160b170410201c03500074103424921282c03102e180c4000780050080c3e40024011103c08152582084080c0d0700920100c4070071903852550954503011440c00c0013042c04140800d800a1000f084139221980043d1112000740703 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 882811312 1250 882810062 882810067
    0x60b0409060f1a0f07080304060903110d020304090203090a020409030221040f053c041b0e19081b03100507140702010c02060703050a0f140a0503091e030301080c09090d0311 76
    0x6849050990304207440039584183d2b1108075608041d040307c0201c8080a100010b02500000c020019489002c0d42c810110380e00d4000001581402d0b09101c0d900007903074010003c00c00785003c2d0070300a5071400000c0c4d1002d601c01140007035030070b003c840c00c059404584180071042c2000f410b2a060003c1a0000b1b00400400e011070500000c0150080e50741c80381402d000d00a60861820243c00c01040e43c2c50404051800f1400034010580c0c40d60000901c4600c04d000d03100072419800442001c0c4614407582e1010030a401340e0000800134412003d98002c000500b10200c4030f22510072082c40d000c4510640e07030140807807020030258007040c0fa5440904003050050402080c40019a000304070325a1140300c0450025500060103960b564102003055162000d500d40711180d09901c1c0b00c0540c0f144160480042405030100003d04c00b50420000303110352440440344850214000e07882603039a50020b00419000d4040c040c4800d1036800c181554511500c0ca913001002000300640c810b40051801c0c801a84104404 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 882812562 1250 882811312 882811327
    0x60111030726120a05150a08070b0f1b01050103060e0d0e01260a05060405090d0801030b0a0204120c030605160e060a2006040b13080a030f020d060b0409060f1a0f 71
    0x80d5000c0344c401c03101084003091301e00e0204207500a000522802a110340000e035030520802c900012036209451070071045555400b00200301140302c0c010003103001c11013880c0710440d541201042d00050b04a1b071040409000e0310504460098070b0b00190b1804030001001c60401e02c2e469031203a40d9110040031500442c11a208048e11440302c0118101d03030302c0c44102c0e00c1d1380500c8401e092600c00d80d580102d0740c00181048451030940240940410710020300401107400102e050409258111001040a00710901c03003804140781c1200d80310300f180301c02d5603107601e41300008e20644280c10706191840e051740d450600210b10030301088196007040388410100040e0707103510080b401c1c2c11080750320305440d088004d00c010f1500740740541c450034004048032080c458020071400022035003000d4901001840c140030608081c5031260000a001e440c1d1041d00b002e082c2200054443c80450060065079a0081d040c016a030310f0710903000c0c8004081c03003a1080c04041032542604110550060042c0004a070001c6140105 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 882813812 1250 882812562 882812587
    0xd20060f070e0a030f0209010902040302100302071e11011d030c120109022e0201111603032a08010902040f1806030602070c06031d0303010918050304030b060111030726 74
    0x8241c100300c4055031244080801e40c47c0940d41c15006001660040d40b500d81190b02046c182c500c80c03000d0300d090540121b100c00800800d0310341c44160300082e40303260818001d0707810f040600d600703907241c018082a1071000210380c0901d0782c1ca922800c081c0140c02010501c20001c141f154041206402c000155a81d0000500580e103842d141c5103024010201220943c0d080340c8003c404004800d4001d05680c13620818901000c100700079100503e180100000b001040d070f08055018000c041540042d80031003000c4240d602c121342080454403071481c1c1c0c8103111682c2715071001b01280300364052513a2218241c03408004110489100e07019003030322064040789150340d90b940d2409036006040c046507a65011031090054652501c141c0e05052500d81060040c0c00312058200d4507840180a02c0c443c954450740100c03034100d55a020f05c400d859101003242c3e0394079920308014643c1c0c0d0040d5402c03400507107450724815208030000700740c0b049190000c03142407502240d4445100c4200b5400315a03000c2d10002e0169010303804 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 882815062 1250 882813812 882813829
    0x207050d24060501180503340b0c1b0a0b0a140a0512160e060c07050303031602010c0801030b010e07110307110312040e0408070201200d20060f070e 65
    0x1d00c0300041100ca08040c009491070f0801c405100d00c03002c004208100300c0e40d002924044003004d0009440ca601d01042d425000c80c0710002d040c9486000f64000022280340c610300602001101209843c13a03564040d8400c03040040044105a001009800604c45c9a90402c0109455040c504141c90001da03661002c20745030300021402004650089060881040c280c0045c0c0d600600c40044001c85900120024108450540d4100e0051201090a8490702d50401254002d000003c0460f601c2c1e2401c8002c4c1601d141071540c1c401c0040d424102401070310381c040c840c10380c1170300c0d44400700c410207078240204412600401440801040600725080001c114240028140140200e0010650031a908203244ca00345142041403810202040208004030f80d0300e6404c0c3c4c0090380442c105541d03d0203400120f801c1d0701030169800618010000f11691a440000d00c039601d80c1407500c3c1c202c11048d402c40180c80030f216198540c240368000304002401036231150403041d80090142488021550108040f90404 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 882816312 1250 882815062 882815123
    0x110712080403030c031404030e060f04030c05120703051902041e09050d0e0a03110f1c030e030a0f02100c060f063201080c0c0d0302030a0e0106060207050d 68
    0x1034240d205100505605001e042001c1c038941c1000e00907900721048030082540014005402c01a4100400ca01503840004603002201404100d90b1555103a040c002980c0002d489414403a1150005280f000740b0086010070840e42c110300034201401d45040c00c0d50504108000403130b405550382ca400200f010a01400c0800d007601858009a221046d00d020340c071301300c1003204081c28001c01c0e075080c080c01c0d41c410004030300f529844030301c8140069a140110f0f02001c000e49000358030a107500c611604c1d0303103040f1041401d02c42c004d40d00d44249e441d4880900d5219140c0c00c00140c16a10310300c4840c3c0c09800c001c0d00d5400c0c00744980c506618009504d03143c0d20211050503605900d07050300c0305030400c4543d12000030108161000d100c80e400103100b0640007000c2e454a90651410700482c2000101440e4034401910400d07082c500c1038442451034000003e000350300032148556107038034204010145950520605003500d1064000306500c905200400012030408141255240642000c50303d00117002d03183c030b8104 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 882817562 1250 882816312 882816317
    0x4090602030406150f061815020309270a1a09090c010e06131e0911120a05240319060605100c05101116050a060627110712 54
    0x12410185443ca05a588600b80b00320443e02044007446088070500210f0101c07080f9007031250140e210746011140c9841d6985c040540f03400c0840c03035117a05035008801000803000c2111111200304440c0141d0607041001e0f030120342c5040300c00000403900046588000c07485880d012014408203032a0740000c1401008445021080d0420505201c807540c1040c0801a0220115502400c04000426240c0b14010500c2035210001540619001140300900703080064503005405100f40d50b000c520450056001038101c0c1d14003194140014403007000c0c1d1207050f00480380301e00d1004801070304589990700c10740d1345080264180070790706140c20f2103215441040c403028424040402c00c1840d04c42007060f0244d82e24103441c02d220920301301100081d4081207940d1042580302e000285440340a000703130b00e5802150007a02e01d221504818800344140010b4003103503644109010b00003d510380ba040300703d868501030300007078182661103000c810340710541081c4940c2c140010311718244446c0f83c07144a400c05a60418001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 882818812 1250 882817562 882817567
    0x2d04030b1005100c0201080f1506070b0f0106030606021f1e0603020a090908040e1906031a280b1203031e0705090a030206030709030803070f021905030f070f0204090602 74
    0x202d0706000c001443e82d0000390070540c04610003500007800c45c1c40010400107107852144001282800982551803501c00040c08243e10340c0e505150003640780390213982102c2c070b0641120000850303511070b0103008203958803580504103107140302d030000c400000b11210481c0340035168400b0030000d000e40695485081d0404001081c0d03980b45006006001901d600041c51940c00c2040c1100172500010032036003251100156072080780d4500800542c4010281c50400b1a41d042c0480001031265024080c7c03c0038540441000694903034001d20032090f40e2241c030880340c203c0c4020b6000d40d0210185c3c0100340443c0040d0042c0307248500701034010704540c022142c03040141c61000f03145002d1080e1000040e4400d07000d0074894507103161200025046a000e100c0240309200c000005203941c0d01c56010507009591003007481762a4249003030050700600f60316100713400510801d203420040c0c0c1145081c0b4500e264200c4051840c0c0103507200c4024550340280c0d0300707403401c0035070400702001600c69108101030507005120068 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 882820062 1250 882818812 882818819
    0x1c050a030516140f071b05030f06040309090f0b100f0f0905060702150c1c0e061309110f07050d0e03060f06010e010e0d051c052d04030b10 61
    0x102180c4010b840c1c050380809110001d445160000740403402c03204074202d000d4440300c2441400d480c502c03490134024500501e40742201003501d056100003007902c008038242e5202a5041b51542d80e1510201e80c0540007a0340d0807010082207500e503002d2196151590720100e032040c035540116042946602994000070015107090b00d423036a00106030701103003a20745000303d922450000044c50768040c000010b4440c0346200d00c609100100c001c12101c09250110556002c10003442c0c0a032156491210441d02003185028540103500d0a40d04481c0d5800ca0071210301c84243c10984140300502c40c1c1c0041c540c0015040100c0350780d880300100500038513441040180525405c410300104000c1c181030b5070741d02a82c03194051000f00c9420032001a440082881c06e40b4108124000480740c40240c504140c1d000202104050144480400c240e2a007608503508a45070400c03420084030544940b24010704094070b0980312450120344583c0315042074070284501414a912074582c101826015162202606514102003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 882821312 1250 882820062 882820067
    0x9080a0f060c08070c062d09020a06030b3703080406090b19231c0b01020a0f030507210c0512040503070302150d0219020c0f0f121c050a 60
    0x100707034810519010301141400c0c80c0c003170260890300c2ca00400c1151120380b8511421050701894001422401c1d0b0901030100100c1c9500092144200c181d019134101a0040b80c030754001e000e107103101c9901820510b050718030303880445485005150055020140d541e008844074402c00100c101841c001c2d0000c590b075924202c4044c004400c1648000ea016501b0700c03603070500c628504003800070301c101401e113850031103504a00b80e1800c00003880e12802e00400460304101e5000729542c0c8100c0b01c49140401c21500d02101c005a80e0342001e4240200b80721208a10040001d110b04040c100203407103114070910074003100c0c40281e864401e401540000401400103182803200070002e00314000c8001400b44c2c038180c01d0601080d20340000b804007a002c0ca040040c0082d099804108444242205540840d1a080501081c1500e030201d106840c00510403400503040a141c020014544004002e0004668021240501601c8071078465801c140303000f15500c0b540d9a5100a60400c085901036890031360b100c2c50460701 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 882822562 1250 882821312 882821321
    0xd03050a090e0103030c030e030a121d0a032d02090a240b030a0c02031b030306011d030a02010807051204110a0e010b040611071a1c090506070f09080a0f06 68
    0x2c11502e400710300400100381c02540c0c06030040d4041c0380400c4101c00b9070000c21f1410743c80c4030006040c0840c540742c44845035401880c0d03140e0083d880c035800e803900703071310008001c0c03600d00d20302018003d407180151000f0f03004c070001c654807007401c0c0c07902502c10480043c3e0000340c5000b40460740b076042c82e82c680e1002c000300d09082040e1100c5403c0c03682e0526603103003001c0c0c4400300f5000041601403519a00c1030075030b03807180c020400d41e501c10343c0004040329403c404645158483e0030503104d10380440c100d01c00340ca076461500c4048000110340078005020550140d00112145038000d020079081c40b13410041c81100c0c145200c0c1481c429030085420b00003101c2c1c641c080c0106d07104a90306c407105c1140848010301c0b0703616201c2c0c100c0302101c080c0d281c0030340c00340c017410b006504208081d0300070640f0f0406040030161100303200014040c1404d0903079205200100040b801c070155100c0b01002801074221000294001c2d0062041720300710281c1d40741c40308259484030f14407440c11042000a8819080c0b88401008018a5000f0f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 882823812 1250 882822562 882822569
    0x2205090114060306161808100f0516020a031202090319030e0303210c0c0316060c030c050d150b0a0513061e03020f0d0c170105030c011710050d03050a09 67
    0x20100e40c648000d80d00035440c54a01317840100654000c00f00301c4d60360706944003030282000b401650240c128800551004089441e070500c2c540382044c0c0003c80b00310100380c1780120401240c01a00c03100300750303a80441e40c40d02e20714000308040780d09022a440c0d5450800c0043d402054600740100b80041034100a00349215512205110358000c100e8444072440408041048901d0b0070007403815602d80c140000841d00039500d003044c49100200d20081c816032064614199507004a4080105003418807017101602d110310010404640700b041999540300a9070b01a0141c00410a100b80d14180c80f0140302d4803551100d01402c0006038040340390322814000700342100080c01c0c0d5003030640b1601c2096103210149100803402c4028941e011800040c10700b85c00e0200d41c08408801801c00c02e6071006100500070741210703905452840d058000125440c01c0004004200722030507101c5903402e07001300f0080048078100a11403800380b40d10040000301901c03200b041220003840b90300c80540324040e809008201245661 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 882825062 1250 882823812 882823819
    0x60c120117070323070902160f051207030c0b07030c091202040902100f140c0d0807020f06070504081006080606040e0f010203010e01030b07080f04020f030a0b07030c0216080c220509011406 83
    0x5e01c03230190a203002601001da006858040d42095810140c6c1000c0e06140900c0d00001d00141d000c1c10141d1001c01040001e02c200381c026210b803502c4004030121141340d1078003004a40100010701c6250080720b807002c05544002c2c40480d81410399404160380c081001c4c0e101001c100342030040c3d85490b4000c8603680d40c82003070106241c1003950003140341c0d9030341c04c001c0000428014414007041c007403882072240e07035079030b0a0140031036104d0300b040200100301d6842445040700a009840c04070603000410300441e0b00300d0b41444010611070722044200001004041160300c1c5510407200c41100c545000c2c0082c500800c240c0320072000542c598140220015002400707002001003031010002c604050421045e00b0540544420000300d8115004c00e24013601001c01400c007881031010000d00e10740c113411409103441107500f500c1e10b0401e034411843d452051805070b80c2183d00502108086401c01552040050700388000d080c0030143d00d400c103c82110819650607040c0c2e51921540d072540304181c0580ca0b00030406070b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 882826312 1250 882825062 882825067
    0x70c0f0627090203130c0305030913021603050a2007030501140712090f0f060506120703020604150522081b012f150405060c120117070323070902 64
    0x72840500c034000a000740ca80040c0c2c08004901c1c0c407042c2030302c900442540401404019500d17070404564a41103208698032404899000fa0b0721907070303180203490920301c0c2540c840d50180c402c0e0f581902ca03a003180c1c00b803008101c045442460812803000740401c00c811060301519240b425828131609407040681c0d90114429403130280083c5035070080740420200d8030181700007181070301490102e020b184c4034503003d0401c0011a5615081c0100c4e0b5000c140188000c0b200d41146030301290441d52201400e03c0080d500000500041160704806604440c40400303501c0c0042c0303003541805ca4500319503c0c0c00054080c0c5400c010040c0301107601009600f008150707080041d840241510002040c00d0860719a103500c410155601380c80f40740c110b0110582c06140d03c4107031540301c031071a0201c01003508100e45c02e43e5540304110209c0d072401188412603241000d03d50540300d05a080440c40c4203001c6280c005207181d0310501c08000085899031480820780d040d8616540c90120285041d289400d6942d0040d0300c034180304 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 882827562 1250 882826312 882826367
    0xe0d02060c0301060c02010e061911070b0703140d060303090f0806010510051b0d0c020a14090f100b0f1b0f030d0c03110d05060a0605030601021e03070c0f06 69
    0x11100b524111501307441d017000c503e613603480100d414480c400d0075190000000f1495203060060072452203003024040d5110305042500c101001c0d5200c58900c910f4281444c104008404070b80304034005851130b1200015989402582c030010011144541c0c0268001044614144000c210f80303110341c002400040002c20155041c1800284460007030380c40c4c02c0034002c00107152810180c02d04240080080e500f01a00c1500801c500c025000c140056400c03845203248400104501380031004608500c0b0b0054200c0c1d001d81c0c0c8400e084810120098012440240007180c00600a071090b00140303a640c01002450b0303103a01c82900189844140c0600710f13241504400302241c1580000030990785960800d980201381480145401c2d401071120b03a40c40340000d4000580901e00041caa042903000d000d0503070715041a10b81c3c030b01e0100d501d8003007500d61b240140c000c0d1543c070020809041d11100c41140c85815079103440c4403035032103007044002507000305001400c2d9641000b4507a0480c036100140d051f02012500d00042 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 882828812 1250 882827562 882827581
    0x1b0308190f0807120f05091f110301032d0318061b060f06260c0a03151e0903080703110c150c07020316033e01020313090e0d0206 57
    0x1009003e20100040441504c3e070780c2e80550001844542e2240081205050000701c441d1140c4241e40002d2002d110103038000c580100621036040b640b00c520707140701c0c2141d08550342d8006100f5048402c500c0041c8940c1070500011145c070803844054403a8540380312044c040320644076004100d03402203083c07100100e5509603061881801c0c1301c106500400000d041401c9030318000040c00f4075000000328140c8140302082c3d10146c501d0355264444c00c01c08507881c1c2d00c50b8900b00301d20903c80d4003004050040080c140d942401803604000e00903003c030031047d0b64020320300e01004101c8410840c00c1e80021600020b000c012900b500c074084c030840c0300648480c508020324440c80e40e1821020400ba05c00480f010015500424190a59200701d40c001d05448406075900b00c1c0080d1440700b8041954280d45400855564020b03002354001030140c4407080c100c60122851100f440d01c81304038034090640c0810030403281c154141c5c51044015100414000803000f0b4a02c540d245000440d504001c02c0d94088801d200d40d949 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 882830062 1250 882828812 882828827
    0x5040f080105070935010e07030308010503010e030f0a03180f0f020a0e070c0b06210a060c0c2d210908030906031b070b04081803010b0109121b0308190f 67
    0x41c0c025280384175218441c03406004100c1a4420440340c014170601208140c3e10204140c100c4008030024000c0407a02d8031034540343d00c41c18241942d0444100250030b00c00b806030b0012600c68000c10b0103d80c46070308584882910701440c0340100d40c1c0d9402081c1460440c0762489112001e0714002030428418548054054030b410b246600c00f0700b80070003c50000703405940b04004041c845507241c003404000381c030480701a0b50341d4a0200703088841600380248401100d2081c1c02c0011001e03045160001058051910641c091656001c1c1400500720781080c100840c0e141620b07500314190345000c110314070791140401820fa00703030f80c0c008c0101600104006109640c07201c2c2034a80010415120040030b1000c03110307520b82403240342401040040004200002c0c0b140c0d0001030061a5801d506204082890303008242c01c8811003001c19020900641c0140480e44c0c2c00d80004604c24030600c0c2c00a8454078401c10401030759160343c4201c0b0f01c542e0015400088008400c20a4004242810300c84c1c0080b0307642d0300241c540e0307 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 882831312 1250 882830062 882830129
    0xb0a06261207060902041d0d02012c010b040504080a030c0c020d060203060d0b0c0a030e0d02060c0309010221061503130b04080d18020a1e0905060105040f0801050709 73
    0x1c0501280b0041800404d80c04004032a600038000c000e183d8a40010000d040789020340940180512142d00400300e0040c00352100c064401200002140c0d602e03404c800100e80359140c0301d000c4c0d40d621403103034030940c54078440c0d54051401034030116111151068000e0999001c1940c5004000c124465000143c80305003100b040d0b2540508056101d41c1d404021403604440c8032409403004501505204501540c5402030994140d296001c0c081c4188980d081030380c1d42c2101d030080005070f2040001811514504002e1500002c0c0c000015281c03085d01c1200e44802501746a42d003641d442d01c2c0f001c0c01507070714040000036429014100018158a005402c401c0b22183d618809400901d80c50b0000b4204008001100d2408100034410441d00b002480b45030b003c0c1940c2d442c200c6c020070050b68081441460311005079070417402d0300b161200190802c0c0341000600405814503040c82004c1c8030100b8943c1c189100e080242480500010320f901d4403da009201401c01d610074400020170720500070300d0409143c64141203 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 882832562 1250 882831312 882831343
    0xe010302210d110c010302040e1f081e060f1612060b03090c03480306040503180607111c0b072003030112140106030b0a0626 55
    0x14060001001c035000c41040d50644524024040702075011900701c5211400032100c981203411101d0440019000c070705ca24080d040440060800042c16003400f84500552841c49100240e1016501d13840603242c50385d4000fa90f00741c111210801e10001008010190b80f1943d330201c158190700302030004400888009280408008110301d01d14001c01294102c90024202503208591780c1c80c00c54802625146a0310500744a809841e41100141e000600c8180007521968900e800c00080050880c81c0c904080d00307901e210b000b0380c82c1040c03400d43e824407540e84101c0c010009944c4d07443c038400c00706101140060019119640912600d00401e0f014003040550000950b0b9111501140f00310603113001d02c00c0c401c0244100c1400041000070303036002c80d102c841c4500301e10b0072040903581180440d450740400d0040300180003403e4500b2000c0380181201d01075854400303000040707003600d81d2035484040d00111400300c3c840d80c49000410440d2201c00044507050380340a00d9981505a80103900c0c2c6647c441d0078030fa4072 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 882833812 1250 882832562 882832579
    0x1e0f0a020d0803041e080403060e060105090a0b01170c040501020601150518060d0c02010b0f01140d180b1311090702060106030e01062c010f0e011511161e0e010302 72
    0x4201c451900403042603055080c20b90b06042d0f9282205166007d0701007141d02908100010950071030000d40701c0e050303e43c01001d14041e07940d110314003001401203000c258100141c0390307061821103258014590040d110116025950f80c10b2200283c40d04006030b0120049400f02040c01a01c41d41c014242e6030300d03503e01000c440c01425400d0000700c04bc05000f046114240c81c02c3c62801e10b00e901544008507480017071b1850b880b101c4030b070700042d650450442072003140030004001c441c1e140070352580150703120088440d103144601c000c0d480344010858103d48043c10300001404010a001103039010b5000400101c40000e1b0074581400c00a403500810b02c150750915031901d120710313407003c004e41100300a0040f0341c0044528a041c01c501562840d02036a16a0616a0007800130802040740911703041601c0c404968020240d1806001444405000082500b0850001c800d038071019010310050850407a212803100310142010030035040110089412030200170800d1080208211070100d01d81100d070112100d5a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 882835062 1250 882833812 882833821
    0x40b0102060c220b12010e060a0f051002030f0f030f1b0d0b0f18150d0b0408210109020a0f02032109030c0d0f030608010c08150307081e0f0a020d0803 66
    0x145103c03020740104070040c10100b1140c01071110100103d04a0314014086402130325aa41403104c800c1040c0150b1207001b002c010b0600c11802d040b0321b20401003c140c41102e250030303141c008103100c0c0e820500c1180311204000040c401481c0d8043d440d540c02019080501800e03040007001a803c501c10398501d150481e40b11490f680c41590307280e4209068001c0a0100e9074410b03e0700800301c0500c18100c1c1c2e42c84000d0000314004009080683c4c40496140d40041e1034111600c66131100000d03034010600004150000c0045200251500003101d07008003602d66015894020b10305024200da0542e4940c20210352052220401c02044500030040110f01d0b010040403540b50340c80c000d42544205549800740e4411100c40c0c2181c0c2e0390025030b11008503020382d010000181c4509140c0e00740c0d0880c5070000d00094078240410900b00500100701882480102140c09041c1d580040d2410f144511044c031800e08070392071a513040c81d00240250203485007100c02600340840c00e0384c0041c011241516000c1c145040100000c0c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 882836312 1250 882835062 882835117
    0x51204060507020a120203120f060114031b0f030108210a0c06090b0f01080f060108030a050306030c0d12140304020a14061608040609060f0806010f03060b1206040b0102060c 76
    0x20083c0940105e840b458070018010060b43c1c0c1e030301c540361180c204801c1200180c104151908807034082c45059642549180803114204d0b52904080d0069140251139400082490b158078010300022103504021a100d6140c261800c0c1045c03000038000c01c101d296080103054121005007140c0c0da40c1010b040442252145007003900c01020185401041101c1100074028103e1002564a0480d400c15049078a0301c4084e003000b5403180420310940350703964407c3c0f084180d01b0f4001c0b009103030300c400060100c40c0214440e00000d100d1052540d4150381d49110a0000004d80d90300c4a00c101409a400c4403107407840c20941e0104030300c41c0482c0304508683d291042c081846550f1316040f980024140004032404100c0b42c202003001d5070040c8142800316017030090000b54540034041c1540304803030a031a041190340c0c441c80107541c1110b151201104250340c61102060590740d113406004000b0025200c68001d24000040c001100d980880843c1550311000420025040c1070303088401c44000d0b400c810078544a41c0785c10 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 882837562 1250 882836312 882836323
    0xd02070b0a1505030a12300b03071d04021003021c021c09020d1104060b0a020a020a05030a050307240608010902040b0901060210020705070506030c0a0e0105120406050702 75
    0xc0520a0000a014540348160008070007100d0521040301455503034003c242e030b15404010010301e490382a40d458040c2501925090500c122440c0140c020604841703650092441074002e4200095580c1c4c400c0c45090408105890261010000707030035000501c00b030380326031084c80180002c1c81400c3ea0001c9802d4184070390140c0300c1c0c010346a07034814620700341420244003a4014280c1034017084140b01008415603d0341c080d00c2c241d9900909096003500d02a210f9004500320313880281d03002503c4103c00140450894003d003603000c203e0303014044007281441007010b55030980d802315120740e214540d00e00100d08003004640b00c1c00d901442035402c140001c0040b5002e6000d20700e41051540c901600000c0516040d0055844184210303800c101008082e0b00b0030440880078058100144e02c603070309030240d0b202c0a031700a080c16801032003102d10380c1381d640e800107040e60300888480300c510f8004140e9030340641d00f00d03001841d03046090a01c681007451340c01c0b0070020280003c2c40901800d0f22903020810b000c0c001d018 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 882838812 1250 882837562 882837577
    0x30f0b062a01021b0a060c030203010b03060603281d060403020607110f011b0813031e171003030210060e04170d05181e061302120a03020a12030903140d02 68
    0x10070070b0701c803440342d0b02017070f10b9003828841900c415050a11301c00455200b0710031207058a0320382d40c40d80e045403035a9041c0022030704010881c200d1078802d200b198228440f50003c2101751411940e0110b9403004804842c00c0703105040700c1d20411a030000c424040040d40229507207520441500d000d0311400038001e0340c140f810743c4107485107070194078080c07040d2000480115440e82e0f4068a44410145d61248070007035909444599001c0c5c0050040b0381944a01818258244003402091819101d00724031891008ca0030202514014a14150f0700d8081041540501c0701b040512402c503001c01200d45401c4c03005400b40d030000c00040c04458031441aa41c030356100403e881c82d0108a032420040c07498541441039085a0310509601e85114120320000303519030013050303061801604c4000d08060740751100581d0b44a4485941240c0c0b10030400c1102c00d10072020003104000030b020b54000e01e407010a5007070807940c0e8650301d10703010101030510703030311102080e00b00310004119107030f0f482d480307980d00040d0090300000c1c050b004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 882840062 1250 882838812 882838837
    0x60d0602070803180d1e0507051005061801030309060e130f061404020c030702040509031629040203030304140c0402040303030f0c0203130e070e0d03030f0b062a0102 73
    0x2070503400d120000c00554030034407501156102003020800410b6907004d481000300c0005400d8507469030480300e0280311021a10040c10014100b0303520340c0c0c07000d08001c040c640c0c015070243e652007000388a1501031100000b01940304801e15081d41035407001800540e15000d80c0042c02099840b040349a1115481d1410001e8000e000300300c03400360340c100f01019000900c80e90003402c81141c15a0380c13501c0d00c0c0c8216240da034018401949042d4146d400d2001525004050030090700081c0100070b413541440c200c4854640c03140041c0b4105800180051035600c400c5a040304500b07515a04010050300c0c00070803650011f03003001c4948010161504610300d801801d4210903046400454000300705034060300621400c020741d01d401d00c020014010300701c1e613034007840111150021001d0802c20030390003070405c001c3d000f18081c646444206c858001203106050f000740201c4c00a9074807203080010380d1042c4203020360038008603402858003140701015140e880101088208821000f107080445003025412500c81c5500350 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 882841312 1250 882840062 882840067
    0x50103021e18090f181b040b0a08030a09031703060a4109010b0a0207150215010b12061e04181b030b070201092118081c0e0609010305060d0602 63
    0x540c1d000b0f00d0040203881002e980204401c013042420004101808000584c4120403440c1b40090100400b4040c4451100d4000c40307046c1c00801c030800c080c00142000d07105604d070464400e00e141340c0100d009140c04141c241e540024020b1007219529602460116088407101100c0506108a40320071400034940848480c000c03103043c0c01188004031107049000504030303000c284076a65124412200c0c4264903d400041e041380e0401e11010701801c40c603280700b07020342c4115110012110040000c11000fa080882c1501010444104490410510603413007141038132400c0c20484c4e071001000300d8600c9411401e00c60390312144580d00360b200c1024450002c54100c0304001015580031009a5040a5804151080740c90344001581c4e45005001d804d0080f03604c040c840d5020840d1804410602040c48421000c10520b12565202c5003101155507001d00700f00800303805004254802c070028065071311541c409101c1c00c0d10300107c1d655141ca0680b15242c00078200410030f90f0720000000c20240c1c4805008200d940302 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 882842562 1250 882841312 882841321
    0x170304020f030115051c11060717040b0d0e0c090c1806070b040201110703080906071104050a1b020d08040b1008030703080109060b042303071a0702030106050103021e1809 75
    0x5550f14004032981692030500310404254146c1801c800c410001d0031441140c400b40c009030038024020641140a614a02c0224030000e20b03c40305a13026030310880d010900031551441d21009480780b4544040640c0041110360509004078051003001021004c0c024404144c00206c0d84800b04071041c2507000414036541c0c0c01152401054100c01510b0990018440400403800c100000400c0e4007500c3e00100d036241060366036030400811703030711468040b107140038403501c010103544440c040c0078041c1c02c0d151008141c0f00442040310801e0801c03241054119440a1150b80b44107801c4404250842d8000140c01d0b13150b5195082ca43c1c1d01c24007a803250f0ba00340310000b030140515034070090903816124030101c24840241e482e011040280502d000c1c0888020041c0100c4841d0300f20680c500380d003c107000d4284c51505540d181180761a8115006030a82c58100080030f004500e428496200a854242411403c0440f8203c41398040c1d200114001780c404000034000412428100c20068200c0d4010103c02c0c0d940382c07 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 882843812 1250 882842562 882842591
    0x1110f1009111207090b03010b100e03010c0219150908070f0c080615011b0503041205010f02160b13080d0e0d0e280b04060e030f010603170304020f0301 67
    0x514160560761042d010702000c40c00d250041d44844561201e80091000c1d504060f4484002c2200108099042d90385256400f00c44c0c49409080c03501403440d071200300c071880010040c542903030f042c0550700c000c40d0403004803034100c411800c0c3c8400550b0703000418402e40f071480d070b02024000c0c0070741d91020300000c002183c00b10400c40994000344210f4030030103068200554500189654140c15944540c094800905500c5603511400703003540d0181009488090444507070b2125030540c1d000350041e00e851542c0c1d80b40001171200034007480c0524204103c003180343c08044801c0a908030700040780204282c0d445408078a00f052190302c1c82881540040005540e000341d01c50880040c01444a08400790184012003171025010305c0080006079806400586954100c044005c0d10f685001e403182c00401481c2c10101d50802e486001d0000390100c3d80b25222002d02c2c0b442007600e41841d142000348260f0400009100113141c003640c1c2071004520801080e00e94456100144083c1d4040701c00380c1c0c141d841c1c416030703419000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 882845062 1250 882843812 882843821
    0x5090a0803040b310303031814010b0126010909081c0204050103110304170a2c0909030c0a03140912060601080615030c0309011b030c140301080c01110f10 68
    0x2654103d201c0300a030741c40d10320f2000342c03040140c550301540c0001c4c00c1000071070b0103500801c801c5110514003921350941e035510443c1180d250345041c03032075a42d98152400b1550304803105400c0403501c00740c240503c00f104610803100c11814002c0400d06034980894908010b00e8074181c4000c102c0b08145000078240329403040002790003500c591070001c0d06001080c06440c2400080b2801640c0000c070b01c2c5141056001405025480081c0300ca04100c0035852261380011302100c0c8080017040e0405000c81d1921a804200c48803001920308041900208280b07054001c0016a5440306a031605080c900e54002c0307000d0101900502404030b4100c44050500f106d00329004c01c5491045e01c00b600d031401540c88007010f000305241d0b00501145410001c00215129022507406198007201540002c9072070400303800340d180129400d01c404000710740c0b1110080d40568110500903141091900b60504542c54802e10560310020384d001a03040c020350b400107405030201480a4bc1400c51048102c075041c10400c501e01d0000c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 882846312 1250 882845062 882845077
    0x70509150307141e010e0a0902040503160501081914010b03070206160e0d0c1d0f01124107060201061203080601081005100c0201020d09030b0705090a0803040b 70
    0xb4041e1030000310350841c041218203000c03840035010740e0300c0d981080c040407030700d15030b0080c454107100b4410410480c43d030b15580e00001802e2980f2000d6101c030b01c0c2c0024075213080c49200c81d0b020940c9114074140283d99000282d9503001c81c400b80c04c8200c9412001030311000b406104d00d01403240e5000c400120f1801210802580154059800c81d0503990700c044000180c80003010f160400200784000b00070480c03800f140c0301e50606000d41644194183e8030310040041c4440c0003001c1c003840824030108602039134088c501a00501810100c0041082e5a60780c0d009591340a1180c49440c040c0044003080c244018640ea94500f2551220700300f03d0050f8040b01035454501d0300c5404019800d028000c070f964580b060070140056850388580074a61600070054443d09801090320469012800300020b1343d0741c0712050507194602c4ea84a9036900101030000904040c8605210703001d024208400308006440301d4601d0341d02c162507250540d251000d180010f804101c072503100030054400030030f010450448100052030007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 882847562 1250 882846312 882846319
    0x20c01020d0b0f0d050334061416080105040905030d090318060203120408030910020f0901080a140414030c030403140c1206010510030207061b090b04121407050915 72
    0x42403c00401c403018000040c01020f43c0c00c1405402c2c04418103144003185d11401990140c681039050010b1844015480400c1eaa03141d140d0310350001c02c401c01203a954100c2264070700059030030001c0c1001350007840f062040320700403a42c80c0540824030030107006582c0c00020340d00040c07151001c5820000d1180c03c00a546110300c44050500003801400001100c0d0b400e040d00b0f040c420141c0e1303240c40701e1101c1d8000500d400c1c00b9000d90205101b00d003480d88010020b04402d640100c0e21411440300040002c14001d04d010310b810301d0a040340310303d012101d800e04d41c015408020043d1100385104d580d411f500400c410240346100218000c0b04002402048030005ca80103011107000089003030030030200c0703004280003500c10b400090061089050520b0498026503c9081c003610346521a41e0b41e070304440a80b60401e00e81d200b0140070308500e0368040088001440600c2c82c1505040c10080c01c0c8141c56800c0700000e1a10340782c1071089210840c140040002020b0003801d0310560b2400e21411310b0813a0103418018803 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 882848812 1250 882847562 882847579
    0x3040f0b0606041d22060204031b050303070b0c1c061502010506100e0a03020901150815150d06090507020303040311071214120f0409060b030412050d020c01020d0b 72
    0x152410540c00f0340e01124500105000218100103819424100203042c00c5641c201940c40e10402c6502e2a0030800d08500c10980181d48510307504103041100f154202400107045000d101300440e0343c0020079510b4184d0886031003030042c1c490400e080c40e144118901d0f0f4030244e0004544500c403c0300b69000b10b08850303081c68440403c0695040c02c908a0358129085680414015480317112184512181d044400018003640d546546030780014500030826403201a0184414030702e0040c1e141e004001c10707080140c0803640742d4812001d1000612000c40207010841c115400b0545910f8949290080030081c0016202000315041240b0029100d0b4000c0364190301003040c06803904000324000030403a00319200c018510540c250560380b00146e540380b009a1201512566100943ca041c0110040c01445144175086580740d10745815002510380d01d9000358454041402040301190b80e0400c1c0c10842c0c0e400e0b2038015035038040748641100074010000002650341c8041074030002c00803591300c0b020510100302e95020 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 882850062 1250 882848812 882848821
    0xd0504090e011104170f0a060203070f080c3a2301030503030106050f0d1b120207111c050a0605060405060301090f060b04020d050c07230c01140f03040f0b 68
    0x10b007030340c4202c0d40461590100f000100703c141e400c0c1407515050403010040d582c3d141004a0060324150603050142c03500c9a0000c01c2c441d809400514810054800d420705924516091075484880d01031604260001340a00312000b20013542c034402e6104080c0500c94140b1003100d142c810784002c0011417820984050200075030f0314100c0c200c00445040701d6000008518503824102c0446141d00b00c0103400e103880c20140701826101d0320a01036802c26141808641655103810700e40209150304580d088030490f4810070600010491040000d044624203840c02044022a040452114003100001601c140078040c00c1c0810011250859402148125410700c2251181400c01d07089480c2100700400002c03007428014002541ca400c801042c4900401c01410b00a2260046050714002c0760365040030640014400308000c5a116504580300c020290b6844120080720b00c60342d18030310f40c2c4665050041e201d51074440c840252003105e10422076508805e803241041d1420244103480104e0849643c41d01a0010717 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 882851312 1250 882850062 882850091
    0x8071a09070320061b100609020c061f031a072604030e040f0911030607181e15050c0c040b0a03030311210a20030a021b0d050409 57
    0x1070342500e07000041c03030100d6003289000e41d9180e01200c01498020506024600c0703042400900c4403e458001d0010300007904d10324900e041114015008400e0640c030521441e03210350320005000358407101a00114134507410580704074202c90007640c8014407803002e41074030348582e50480343c2c8640a100c241d25030070400c60440c21041040d000c0a0399042d04400380c0f10021780802c1c4241c1d5035086248000c0d04c0000e98042e02c11104c41683c18608059440020032144201942010000554495140e1034900c00481d944900c49549003550320a10341021400f440c0c409680820404890081c5110060102400c1c10440050072581006900c0c010f103000d00c00c49010b15003843d010345140c11000610814010741140d5044d0020581940300300e607160010f0200030a12000203044121074400038441c00340514140c18032a046d2070b1640c04a100448a990401d43c60201da00152a01f18a4109000d603c907015610461b581700c0028400c001309100d440d82103405a9003003001001503a141141c1442010a4102c1c00c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 882852562 1250 882851312 882851323
    0x806010903030c0b1503030c0705010216050916020f031305090a2703021f0b120a0503040b0a0e031605040c02030310090b0310090c0e070c03020606010302030a0908071a09 75
    0x5408220f0b6030709040300180020328416408681d035408900c0b194810310200303245810a00c0102515801094103115030345e010014180700058140e60301c0086410840410401d06002d05244916500c9003500c00302a40240045403d80c2c1c0203a044a4695400a0031041e81e4406440b0740d40c001c81c00400801c2500c0301c01d00400c0c0118040f038100115080d500c54213580410780082c41030b021400b801d214104400b4640b803200b50760311000c1d240440c080080d0810804560350b030300070074407255011105000c00100048159001c40d400b400f1a07940b03a03c1b4031413044d281d031411041d40719414001e42e02d040141074642070020042c0d4005607403c01c0070b44181c1d102640d4078803050301c8240700766030140010003c0c250745400c41c20341444040c054410b50201c000c6100140d079880d040844010500c1d18040c00980b912030a030951183c0f0500e085d408024994901a4582d07002038003071410140c0000000d0480c0344190000140343d035000074810b5072010039003000808501e80e03460040c141241c60000c0349094100092 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 882853812 1250 882852562 882852569
    0x6050d0302060123030102071a010b1305090a0603080309010e0606040209030619150b0d0b060403030f08040c0b0f03061804030807030e01060e010b1c2903010209060c030a08060109 79
    0x82c1420303400d10140c0b00120007001c8560320355000490100046480c07c0c0068076406102c0d07003004841368642c100c075030f03001c08050f040080000002e003c40c00741c1029501104040301d00039540790005132a64010030740503050503000640004000000d025105034150b00484d6001c03000410348501e034591b882004141d100700094103905603c9007000c01c03040f20b24051075196407040d0140001d08a0060344d040b45030541154800d0faa0b402010400340c0c01007006000d8105081000c8418034505400c603034002e400c25160300405020840203000060800c2180c81c24200501003141c0142d4981d89900e440120b80d038012a0303000e0180190f18a241082803100e204c05004540c1a02ea0103c0d960301c07540c08500522144000b10615902c5801c001018007418121a02a01e83c2c1ca10889d40c81200c000c5481c208800c00358154880d514043c045800c000e4550fa00e211039000c0800c074003c42e40c145400181c00390054510582e4003160008000c03600f4a0004004d0078103002a880c1c120440c1e4402c401504c80603414031 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 882855062 1250 882853812 882853817
    0x51206060307210b0a1407090806060d0c0e0601090911040303031803020601030f0521040603050702150a0902030c09181c050706180b160216031110020312150406050d03 74
    0x3001400281c44564a5031780b08030140400501d000080200041c40401551a040402c490010511514005000c0d465200109940a03404038007260381350555400a44664203190b80c160000c65826881622680028001c2c007800744000696034a01100950140c401140880e181000800000c080c000d070008000b40c140d000307013005a00e90380f80d43c010247c201034100c130140101c28009185044006855804c100712900b100d80b15814814041c0403100050700704000e40d400810740c5442d80c005604001d50000500002044e1200303140b020900d0f10100d5000c0d298402c10f40003c000c2103000300303465203103440c01103400c8401022240e085484141d800c110200c0000e0010005880403411a0b0016202d507076010f5560800301400d519201110101544e100b05d2141d041c00140b2045981048582c0788407429005407015286507540d03601c6c0015242d6901401101520302c100c200b68000e2007a915402c8984042ca56640340106900000c2d0f401c4144241c8102c2c60628003103060b0404944070b50341759a054 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 882856312 1250 882855062 882855119
    0xc1b0503071b0801060b0406030e010902031b150c060a0606090e042607050c040c0207050109031407050a0f03060f0203060906150d090305030906010b0f1b0106051206060307 76
    0x540356800c0c0c0d4403a2403a1002c544414820009032503070240f242100504179100900d803150704201380142511710641c060a820b81c1400628400342c0e41c081918100f040c030080d4641c01d00194100443d80002c0c0502034172024a40c0403581404140000c90f41038881d00c401802001015142c5c0410b071030900c95401160000450a800200010745042c03e03020102c1d0080209114003802801010103580103d00c1220380c1c0d004804842e440303042c1801600701c108800d002400466080000013441030745c3ea40710180001e104c00c54100f00c125400d20660026020150448800c9500d0b0040318540303503030520007141c41614000240ea8800c2d070510a8074000d10008102a4582d1100401c01100900e07400030302d141000301304150301400042d8856080924826201d0507182d140c03013580e403410140b05a01442100000b048009000742054044621501230000000740307440c5e09014060040195400203504400e05a250150a850028407148160300403012035a4250321036408100d00e107000c500e9010820303140c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 882857562 1250 882856312 882856327
    0x80105041b061407060b04020c0c042f03130501050f0f0106022d0705031014060301201b030703270303091215090c0e0906090607030504030e130c1b0503 67
    0x2214003c044540c0105c0c070201d5a0950807000a04a81c0220080d91a50340030152074059400e05000d405a4140d90082020b5501c01101210907a040c0c03aa29050384040f000002803000c4209085010405030014000c00c031f949000c044020400c00705481e007160490302003000286071480001d02c0611000c41d241e6003a00040d101c410850b031452a61544400d0740581d210110700ba8400704032000050800d0080420181320442000480038005080907003e42d0400704401c054541c02800e5007605120a11502d540d05540c8120100b900c1104504c03e1841c040040c01505041c2c0c0080b030260400c5a42464514041c140d1111402c08241c0c2d200040106103050010054800d0550000c1626402400c078a01181c0c001f00240c4c00325141030030103c0345404041002d02ca080c00225060b903202d071010b00103100c0c6051080455503141c00c0200620201904ca9000070109441850304148014000c0c1040d0800c01100700b0000103002440902800594000c0c414424070241c0800a240c40341c01001444c544000c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 882858812 1250 882857562 882857597
    0x3080f0a060f05060c1005070806010f0507050a0206030402190305010c2c1e030703060c02160e0a02070305070b090c1c02150c24190b0916030e07080105041b06 70
    0x184170303140107010b8002445a0f02c211401070f9880703001f050761020264580440050f019045c0c0140e81d4080040c06d20881002070350015034a903e00d6011107209459584510001d580d41204030500b001c1703030401d0b00b000020091b0542000e00c5102c440d417169500b001d03203040c19035032580b00c01510304640c01600301c40031a1401c000c0b4a9a94088003100910320345080300022030304c4d202d280d0f4000c8031482e0f03a40b80f69200309030313040c00301c044800c000c2c0180c1036201e0b00c1c0540303460b1482d00150111941c294009115010580904101c03683d45501c104000c4152805c03c0322903894142100301d0a02882892001803003001244804812040e4020310141c4e02c220000c0c0d80c0f2003507402c00e03807940c00688101c0c84e401c115442d6a0390785484151080051400518222220704482c503200100f515072513092170580355080d941c1e48500d95008503170304888445001d85607000c0300a8401145143c00c00e0040b56008070b60f110042d080580f08600a0006803460802018214110046881141c0000700e801c0e102421119 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 882860062 1250 882858812 882858817
    0x1050d200123031b04060221070b0109140106110d0e04091b08190206090409030903020406080d021c0c0b04030e100f020d030e0303070e130903080f0a060f0506 70
    0x200c103141204000d200c01804a1035a401c900c200709020030702004200800104500c0040d580b80002c400c50f040c035150090107907540904903031400d0800840d5107865903c050740710a6601041c3c0120344004656074880c1104010302185501c0f44180403880008034109005601d9404407400c0f00303004120f040e20070350088445517812003246070b10980f00e00035400800e15a040302000d415081c405000b105152045603440e003c100c4001200c00001d00380d41d40007580d035603020b8488910003601c02081400062804407003444168200075030107407408001140f800c10002701062489050b400300d4945440c8074080c410008001402c440015115101c80000590704c051155003092103030400c004c40d44a0030000440d40d50300440d10200242e80c070160840c43c035034104031600d01414a4101042806054400503450b444020108002c2c00a0076501060940704c410a803100c0701a8000b04003e911400d00c0d0081080c0f0040e038540c2c0400c040e45010a01c08080342c13082c841119003400740382c0e40b140d241000340700c42d58 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 882861312 1250 882860062 882860123
    0x1020309040b030a12050903210306060f12040602250b04020f0a0b030c0d0c05030f0f181009020a0501050f030430030504030f0201091a090705030d020703030801050d 73
    0x140504060000041c91000c01150000317216290181c075510808141450241040e8003c8240b2581080f6002c0c45100d42044a0f0006415109150389400c00c00c50314080d8481c00070b001c440d1400c10300030441406240d50250100654480341c42e26510750340708909004001804003e441e110303d0001250062800c59a0303c0031000014110804041d92252400f82541044800d00e40d400400a1a19055111481289080405400e01500310f04240d49100c0c001480204403800380341010000c104c458103d031041030118444242181c590050544040015010032041240240d040c84000f255640c02071050701c007840100b600070b6040d40c0e200c3c0c4801c1c0c030301d081c50320b0300d040720005080709043e1b60a182081e02044510603100400c0a0803d4500108506000f4404c84116450304103c100040c081e05245950794518404035415600e078580e00d20b00b845d0b01c2c0da03c01c0c2d0f40b522031400f07208421a008034407581101d001e5150090b030b982c0c0c0c5034240700c8204010b02c0000c01d5a4102c00e00c11182440100d080440c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 882862562 1250 882861312 882861319
    0xa020d0b060a08100e071b170d140112050a0b130f060e07050916032a0807110d1b0f1502040305060a0603020907050f0d050c0304050c0109030201020309040b 69
    0xc214404020038119402407640c0e81c00104820200320b04494480b0b08600208a000c0700e402071807800d4a0020550107141340ca00d0059121000041c0a00004040700305040c0091010640c0c0c1c0c01c0ca0585800080845615150182d09000e000058020300041c60101d0f03a6040009000703000110380e941c010f4244002c1200c851110444008030216102d00341e150702d8980302c1c180c0054030340005a0300382d291108527800b1a109150410401140480508051810032101d0174007040150a480c483e410180e19959100320301070341d010a100003254003100c02401005161034501d012100c04101c5511091240120b43c04180154410184490481c41c2c01020781c0c012140302d401300c4074a40c0c4203441d05184a90000b00d940d0041420300038482c0c2484130940041510808100340751455010a070700040040c00350b01807080c00319582c4031108620341242e0701200100010003162a1019080005402c00d690030b5441c0e100d5400c00e1550313075000c4c00801e42a00c0e0160021801d126488003000f01070304000b9a0300341c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 882863812 1250 882862562 882862571
    0x40909020301180809060f0d0c050c061b2502030f0123060a0b0903010209191509030c0302040903110d080114030114010b0a0309021203211e0406090b07200d02060a020d 74
    0x7000c15451082784000309090390780c65564035103000694680080030b002504003000308141c01c100d0ba44100120390341500c80318025040c40295074100003891840c0c440103905401494010100c00c00198440c0152003840c01d08040500300c40000d03108907110403144150483c00c0e0f03c1041c4036003240c8201404000500400151402d1a0f400c00320707080c490420041c0c90035148050b414001e81d0601c00b140d8482c241c0c41d240002d00d09240da151101c010a0a11019004603a681460005e1510554283c9400580401140c209103166000104248000d100701c80251440d803c1840031844e06000d440460060317101c9110b0340364200464120a580b00b4680d90301070554440281f401a120b40341c43c810201043c0b0091512807414160899500264103061095607410000304500010035110307850fa1803912000c2c440c2156200d15142c03000704604c4501509540c04a0200308002d82d0240c003040031607000070b540c10b2450451803003065070341a07400346000240e040f001c0041c089200c66405480250007080011070b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 882865062 1250 882863812 882863827
    0x518040605130c020c030a03021e0712050c1305040b0621010c05041a0a02100f060f0e091006050a18060e011503061202181902040909020301180809060f 67
    0xa500b46610b0319050120780d128404a540ca6406000c1485501d00035009480d0740c82c61958001d4552628044d442000c0c00c1c14017024070610340800180300035200d048543d28190045040c250f40c0c0751142c0008a12641010058011034860380c000d19000d95400519440a03440f100200712044040103034180c2c1d210170382140d90b1200f007403d0203141410103035512040c1d5250b08255640c0d4000c82c42c001c41d54101d804c1000000c0c0d4003a0b000a50550410010000250015503400281c024002c60b07171046242d01da88140204001c42d24401081c02404050122140303810310700120303000e9411034031030307281d001c0e58000e81006003200c410b0180d0044030460314006903242c1c0741c4c440500301243c2a00f08141342907600305c4076010642c16104050160660300c6000c1070407a8998002059141c03400c1048440e045560b0200d60000c1a108150311000040c940642d20b81c0e459880c810004c00c2d42d410b081c0d00c0380d800c1007144011010b000c0c05c3d2504a58105c40e80b113150503a05028441183c1c0200c075151000302c020003070f04 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 882866312 1250 882865062 882865069
    0xb0d122106080114070c080f040302031203010501120b0604260322300303140a05100e0f0115020f01061202040e030a0915090515070b0f0103030518040605 68
    0x403050825400c100141c1681042070107421240701e540c50003000440c51080c0124a41c0004201042940c400051582d40900c01e960504c40c1c09039500c025094400e410981b05450700100145042e51001c3c2c0e13810704920440302550040d520109076094002404100910902c407064121107810740604111240240c7e040a90b145160f01102010300000402186401100f00d8090b03500300074600a1006201a0801d08220074107080c0142d0602e80c0d0034180740c0341010140240c1041081500d68001c0840754646410417601420003112408448000050003013100c11040c0d00070742c040c10503441c418105030300307009580c09010340d40c4048506504c03a80c010041c508209001c1c1e60058000c2400415503c6220701c1440305503903c440c035003c083c0c2c005000c00d050107680712003150116916050646a40c140d403100c250b03640e04c00f41e040207810054005c0504c43c1080d41c0700c002c00c000c0d48a107404040070342d14001c0c00000008280030040c001101082400f11880350307a010704c092000010000a0305c1c035940d5000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 882867562 1250 882866312 882866357
    0x2b1a130c1503020f03160f180509100803121501050f12061507080415030501060e010c020114280305010605030103110a090e0a0501050a0506031207110301090515060102010b0d12 78
    0x110000a0b006c80e101041450f8008484000b4041506000001115001545140030060300660b802000800c000034030703400441a41200401100e4103807980c82c1403840c04076030714103000c90b10300c809480d4208228142d54410022540c180320412034460911103e50b030414503148002d0a419407107499452070b510a140340301c00801d2001e00c2003d0031541c540c904203410b10f06003107080b400414145068010004580c00421803801e500c0709181c03440000800d4401030b0f81d018240e803012000c550004c00c02a0060300d400b500780a804010840450040200d49811800d0350424000d00001807003c0c80100001456080c14496460b402040c06a400d5281c0655000703c40e01541540c3c015840500c22400740182803085540049035510700b4051840c0c0b50300481d82d0340404048071403900c20009540024040701a510203101c2d0030040c0248070120845c244565a40403040c094212112500c0c00b1804560051094205610014188040d4003005440b070803800e00a5224150611107280c80460182070611007 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 882868812 1250 882867562 882867571
    0x5070602030c010c090e010e250e010e03030c0d180e040320060c03010b0c0106171f051b09031c11150f062b1a130c1503020f03 56
    0x964072044203102c1c6509403220141c50b1018061180028450300e001c2181c45030550b402d00c2e072102c055440c2c460312510803082c1046001c0305c0d040040251075400341d012428045051013603a4222100c5480c0d0105a1207200d21088070300182d00200341086402c0c000c0b9045011b48400301e0840390855582d444803003101e002141c08400140b40c00540580800520300000420174403507004005915040407142428030060240b06584400802c54030600d50b000d4208a01401c0c0d13600c5400842a508aa484e55500070004200144801e010541d42d84c5100380c03140a1268040c1080748001c0e941c2c200e0110300550100584507018029019904c043c1c0c002c0c5040604040c02d1030342e0340c0c2071454440f44081d0915406000300c0c20161350388030900183e1b041e500581900440e04a035032041d0811800380c01c3c444030400c405842c0d1815001800320f0309110070341142d003107185400c1400da4115918911643c84500c1074070401041c41a0a22081c03141803d061080391040a031418014540940040304417101c1e0400c85 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 882870062 1250 882868812 882868817
    0x70c1506031a01080f071406040503030403060905010506030307170313061b03151d091e0c03011503120c03020f190c0f060815030a060e011a190918050706 68
    0x4203103028002c1c08200c6801001c030744014107220ba1061072507a841300d1081c464481e4030001ca5490300819950642241c000701402012603549664900d8808003400c3c1d4214241c03076a5203040001340c00303400c0c04000c03207400982c440c1c5039a212612031807e1010796000039180b202000454814100003660314840c0c1c81d03411540c003c88101c0042020802800d0340c0a251140f40f480c64007110412600041c40c1d01c5200c626400290f008040e40d43e0f061003464001040901c0006041e901400b0100f84004254a40c07254015030092112501c080c10088403078001d03100003000c184500140c220413074411584088114428819256082e44000c105854161810440703040d8440c0c1d0701081c2c0c01c00c0403140e403200003032000c90000e01500b4580b1030040c00110300109000d0a040019a40340d119070360901a00742c1003680641c0800204c10303100d01076402480d84001840c5000b170740c1c1500d961203242c0380c0141e10207084c3c90020105d0132800c05454401030015004505002004c122803000014800d0042070082c06055 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 882871312 1250 882870062 882870083
    0x105091614040e0f07050406051e0903012d0b010e0907090305061f090c080c0c01020c15042003061501020a02030d030212070c11010c02060d14010603060605030906070c150603 77
    0x784d00c0e01c03509200a058075050100c00c02c810002207820100369506042c03100208190212510480841d5101d01230000f81d040d40380c0702c20094121035482221003003400b01c4100482001d0070030304440888698a003680e001c503c0369070040350107260540c0c031203a00c006245030119103030b6500e40c0d42600d849410390302140b8400c51586038240b80c0340c0ca100d5800040294010901050390000405010400040d01202e04a04001a020401c4034250100c1d40d451036034500b00c50a1041b902030404c040881074804981c1d100700c02c50070800c1120384140d40c600700b200040140209032508410400740e401952415410750282c1911800540ea06010b0312241c0c2e003080d2005656400441030900385100014000b130244440500480d0100d0450300540c0c00d250710130308001e0035561044c0009180390180407945441340d810036101070004003060304440d040350a141c805121817507d60a042e5000d01048035280712544c0141c0025249501c40c070000d8000070302441e81c2008113400100c8904c2600c20a400c1620358000e01c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 882872562 1250 882871312 882871321
    0x1a070c06021c0c0c03141f05151e011214010b0d06060908061f090f0605100f080f0403050405060a0e0907052d0f04080f0111030105091614040e 63
    0x1018012403601e4000e1030032183d0007030150390314014400369000c080d004408508a00005080070030a10f1151010204408038407185030b110740c80681011290f40742c0501418003001c107141807010201e000c000b81e030b01d90580c1d0111150300440744d004444d620740c540c1c192108004880d02888440301c0703011384507007005955111031a03403130b507016151560300c16410800720701820070403210042006904420b88004000c005c08022890b910400419003020103100d25000902c01c200c89294021b030201c59043d034440e40440d000c604e082d00c908207030555600c0421b80540014800c14091840540d0203482070505505050711031000c0383d4a80c00c100c0f0050301103202d1200415403883c1c01081c01d81e0050b403503e00580345c020603020740b203000b641d80520092a0501e0140c0f142e078090002c81950070760401000d00c2a120303aa03070303115940d4130509078010900c20f500e410407040144000e002101c0c141c41c406441c01303001d074840c40007492140017182d0000d0100846c0c41900354000e84d0380001000140070115600245040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 882873812 1250 882872562 882872593
    0xf02130314060405030313080706110a080f160e0406030b040f06111812012a090e13170d060b0406080f07022113030317011406041a070c0602 62
    0xa80d554001c650b00040400c00012000400c5a40c4203120803055181c01c0901e1038444094041c50400030421402e02642d0b465400d040c0c2d02034800d40d421035031b0b0300d4881d885041d03100325a02c00c10340b40c0c0c4520408680992030803d0090390300c1c52004201800019a440d40c0761030b200c040c050b0541d011600c0014031050790003440800e005030108800c40b5804607151a180e081a0180b0141400070b01d40100e400c000d071685101c07400e42c081052900c030181a40078504071110786210302c1c44880c900c4000705000c40b00100341c0f4200354920742d214201210f041402d00700252500e92058800d40d041e00c03105202040429240411030082c0401003024040d00303078480e400c204001e407005a008000c58100f050150410440c0c9500140c41060b001d201c8805100100c06010303080d000d80f14059801d03441c501d00c8200002010380c443c41c050525800e4210105150b41c0341d1030b61042c1c001a42c1e550540c0f2440501c000c4c403c0e07804500300d002e40c0c40c00c0d280525140c950280c1c0c48551f6540560700074000b580200503025880c01 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 882875062 1250 882873812 882873833
    0x10e13020d0c0f02012304021c03050a09090501050901030611041a07020411130b03070201090206070b0603240c03220b04031b0f080c030903030c0a15020c031b010f021303 75
    0x182c44c002444003115100501041c508856200340344c0c800032501240940d2506151705611004582865400c60f6280c10054400d0f0b10404558000641d400b100044001c500d00c41d46050300c0d0010078071072482c0d2075500d40c42c014000e542c420b00e0f004101000002080070903119207141081c445c00302141c407610280108011500340b03410401208000b040640308107040c1102c1c01f41614400200951070b51920780c0105d00609259000940110300040d804060260b500c4007103101d00011411980300d81c44d020402d0300500c06103a115030400406030080741310700803c40003841c1d0143e000d06e07140f46064210400040300c007031800010b5441d000994244800c0c507a114448060381075070b9801100c00c11607690b4036603803610380c0c00382e01820141e400f0494840c030a100f48201d81100c0c40080403240c40d446100a0540c55100710041100d100030781d604481100c018034000d840003c034021001c1c1d424802100d50103080d046224114a00c107541c1c523980c0381c0b1140300500c040c2024440400894030031074114906550b200 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 882876312 1250 882875062 882875087
    0x91d0601171b0f10020309030709140919060b1c080a02010f11040302120109060509030d0b010c081b070e090708060604060b0403021504080304060519080103030806010e13020d0c 78
    0x700b02c00320300d40308039440b40241603100500a5486040107900f1110480c02d40c00b590800c598140036141c2c1c002280a46a08400d10300741c080781d41e81e051a29190f244030790345c7e5480102e02181c40d040c1c01e814004200350b540150740c1403001038035105034124428142c502500b9040c104a5419101180d542d01042e0b0902c0349500b6640300d03800411508030421205080e9001d24880248144803040780107007127200a400186501354000801e100c1340c00c1c4030300801d480b9040354502d804128501104807081d580324660140c12240c1160510707150406403114503800c89175080040c0310301e11074508000340318414030a0f51440340c82070001401b042c43c10901058205400030f0300841c03080b41402c0040c005000540101e40c1200e0341268480c1081c800ca4500765003501451780030102902000c0350001b1100d810030000c000f040450350407480c0611403007800751280002808080c002134036440009000d0350140c0107a9043c00401440f05000762246295481a648408905040540c07104c42e282d044031380056210080 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 882877562 1250 882876312 882876343
    0xf070c0c1802210f01090c020c040207050f060a0908160641060a2928031b032706060312090315050a0b0d0507030b0c070c091d060117 59
    0x1141007503501031309503020600541941329520443e02004c42d008021805280802030000c0d91130380f2140c00d001d6204c2c040e008006c4041c0c02844009021010181b00d20a151507000345000c1c1001048422451144e203600d4007256031036a10140285d40e4900c070181b002d8580c0c051028804061948d4a0303000d0060602c2e4206d161482034001480403641e2100f18101c142d80c04800801c81a01030040c1600440e03481e00d125950048001400d000c0110301c0c42c100c03084c3c2d0a0010b00c0c2488154144604504880758203620a54184900e81c1007001c09119421615400307203050388043ca401118070301415109600325003285c1c0d40c0c0e80e580c0108200314044546100003030b00c07402c215403041d19585400308000c0e02d030b48100401c01e90390030016002003080d40c4105001d02c000350085060003000c2c034003203076200660301040d00d120342035400050365041000c0c101d0300c8070355115008000952070504084060700d01d090f54035030a4110800040e5070020200800341c020001500e010005140c0f00c00b5860424400315004880c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 882878812 1250 882877562 882877627
    0x1706150a0b16021e010c2a060908011d03070219050a0b0910210c1b060c030e0f0d235205100218010e0402030f070c0c1802 54
    0x40d681c204103104007586c7c02c6480b80355600c1e0300c0072a80c46005800d80d402d415090791210003041701c2c0e9001d0071040940f125503008000b401945803e801d098800060724400395401045244014100740110010500380c3c40020200c2e00e440b01d001920b03000b070f680c000d220349103c0440d04c02654030b0702241b50400c2280e141440304016850f9585c1a2504000f00403e0801c0754540601e02c280d94895410ba00d151144104a290707a140f4625101c400750080c2d520040000b030405004280c001000f1a40050401c800b078010054928039a0090350a2160850810700d4200315800c21150100c220b8002c0900d544d0a500072012040d0008805100683c0e00fa00805c44108009030100da00742c0100031a084000349c0010742c400744032280b80c46454110b4070050441e01c2400030501c1c21404080c081140e011040c2621030b039000040301c4042c0f100b00d010840b1a61080d0b600c41020a00c00c41c0280d0200b403055004000148000351190b4840e120071100301000c40c4034617400251042410b083c14008030000c888410f1400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 882880062 1250 882878812 882878869
    0x216121703090a1208060f0a0f170309061303020a2705090c1f0e0102010e0d141207021e0d09091806060308030405071706150a0b1602 59
    0x12100003852a84000c2480008041000c0c864208002c2e82001d41c00842e40701c0300e00308280001d11500c0280c0310a801403a00040c0c0700c0e081d02d00030f01120141c515240812116a1401c0c4400240d0318020b9181d0241d400200304500c0c440d16004010032a91078031010a82c151461032041c40340b0b629465000d040012994a04080ca0701c0e03064002c907041059040300401c683d211002260305165607004550f03444141d600040c0030100c0e508c0440220254035894904611407040010780c2610980d88e48e0f9a550741045124400d92400352075260030712060300207418141420056280064071042d600c60016900c008000007054031503440344280c004205010780707030683d0280d0000d8454000b5028144019440b02c0b95151b44440f600300205141d600901f0520142e680c030f0904298591007660159141d00032800049400e4103a94141e1480309a84030090107503507142408242131181d890200f9500c000310134000108903040a01500d40080030080e0140407951030300c10490450807500d508080c840c400e14841 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 882881312 1250 882880062 882880073
    0x41101020319051804050a09060f1a150417030306030706050c060a0b0f060a03060305010506041503030f05070b090c0109080d020a0201031505060a110c03011a01121b021612 76
    0x440c05075041c819252400c8a0304d80001004024810340c000786081c007040f4188005030485445140907440c1041070100c4580d441c01610704042d600380759a13080e141c3c0d500079410441e17030182031600171101c802d041c5900d503161908031401d40303e00c4001650012051084038541841808010040d6090a9180241c480a05911500c0081c0091a19070790703030b464424a51605043d03000c0c00c01c0f00804403540c0b460300f404080e00a20361800295000d42c41d0500040907400c20b44a040c03896039210704440301c1c42c0d00e10f580455070110140320f01004c01078203004020014040302c8490380500750f0b6030301a1129100c00d034001850001d691340000e5250b80030800852007243c01050701c403019902031130003103900b000c00508800011404e602c01900698005002c11700d46034400c45000702d0300091f4040e9035066001004050903240d04030180510141da611903034016601034850207010300704400000ca68005041c031902c500e03039160070390a000341e00030402c078103801c0361003010140260092080318829101c0360380300c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 882882562 1250 882881312 882881347
    0x5150409052508011805060102070b0d230f060904061112010608090105010312050c0a140102090108090610121506030b060a0806090304120804090c051c0c020c010e0f0a0b030411010203 81
    0x81d1441e04c6e0b03140c000c00d04e903900c2800742d48098440401002c1d582c1c030320b8110120003406102203900350740e410243c9400c0003009100c0703210300034405010340e80c0241c2c440d60708014008201a04c100c1d0703556580c0440035855002c01000d40690314480060024075071508001400c215001090a040c5903d003900501c00500303071910f584080c0c0040d25001d17869000031644549400e50401e0058000040c00c070305003100e02c005400810110303800303a9072121a0b481d51140712356210701c10f070f580b02d0000501c564144560448038110241d540c3c01140c80001c1c540040342000215242c2d41c00544181369203100304a01c030300300328051f540100b0507038004100602d81038403006d440307029902881c6450049a61118188000b490580340500000c0000b000468804074016216900410401d0f14620391138912036903010491280c42c00030226500907107000c1e00e0352001101c1201e1111091340d4441c0c3e11035244400780e00d401d940c100180911580030340d92401d103400e203140c2e54940307404441d045601c1000715031070340d2008400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 882883812 1250 882882562 882882599
    0x50d0c060e011107170d02030a020a020103022104050c04230402130905161401141218010e25121b18020909100f0515040905250801 58
    0x80c25070110440303000484000028a400510500c5041d41c0820180616500041c0e0302501c50111841c031090100c069859004001c0c901001d6000141000050b501980003000105400481800c10a01c82c014044011744107690950b0f09900440300f600386400c1902c9100400303030b4401c2c2011801d00442182415140005000a02601d60b4075000245802c9a800c17180d801c56001303058800f10801c0302e031880b101c150103216490f0f14054a280d0440c084d4001c0d8242040d003200c2407201890108000c489400324034003d0450705180500280c001c2d0700780030a01c03a03440401e0300c0401a02a041603615655881c1c502c11960300a8007488400402540d10380042a41e65030364006081c0200b00d00300410001c0060309640710540b000c060034401081244942e00810710305e4011610a444ea0f159040100e802c52410301a0385194810f41005000614000807090a4400c4070580d092900d41c5600740303001a80c2e810b0711200540c400d05080403000d0030320748031006c02c1d076101490701811940c50640010300b00c840341d00c0c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 882885062 1250 882883812 882883817
    0x307020606300f06040f031403101202030a08040b0d1401060519030207021801031b050f1e100306030b0a02030c030406230708150111100509030d05040b01090501050d0c06 75
    0xa0b94101e0501c402d0103a48850502c040960340945450300b0480402a00d0b0070b812000100c5000c0040114050b01040c1c0c0c0c040d03c4a0110302d05401e04060204042100d8a48180d034184921a00000003030003540040c005403000d80543e680310a500141d400940c2c0280160340f80001766203006206056000065032a072446003141036103100f40d9400c0550003071260420194104100031501042806814034040c101d81c400c94000e400d00c1c2246090b203595000a014055001c8401c1c0c00e100c401d40b514200c04c0c050804a01203c0c4100d1409000141d05510000a0003000c41c1d05e0321000c0041c004000f68403035000d0342300781d400d5245213480641034680d413100901c02031280781da50241030351f03d0301c001c4041c0d60525400080340b00d1074107042101504d040401c40c0d041c1c008241011f0355140b01d511804d03588100d0003249004100c0e0280d642c0800b0060000207140c050a44000d2140b610130720b280b030080d50f00503030142418410650518048000fa0303032051700f082d4011005500c1410000f59903148032011a90b651 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 882886312 1250 882885062 882885139
    0x3060e0609071106010303030b1219240501080a02180103080901030f020409090308090106141c060b0d14010c0905090f0a021e0415090302010921170307020606 70
    0x7070405a52003c006403c000580c070580c4000300c00c164140c0d00c180741c9804d00701d4022900050f00b0718655620044e4103c484240c0039443d40da240004c20070000b45030003207040101568454200b2003e60101c40b400d030f21041c801d81c008245c80c8294240203010700f081ca6081080fa0b0f46540c156240c0442070320540c450340c0e04060380c8403064844a065541983c0282c990b0580070700146002c1e0034000c1c03a0140c00d40f5410500c0d4a00305000400000744500c9407102c1c0300242c0040041030500c883c1c1c0030f440d07004d00c40c00d54206840398503411143e99000b04495200c2c2c41080c00345498982c0304095421207140c08207403400d10a0b80d07241400b003980c0720740030194030580050244480c0e56070000d140d80a0b004100320001c4840a1486414541c80507102074429902d0300c01c650303a000003007070000300c80c10641480301a0100b00c0d00b6a0902c8040c0b115210094841c8544014030380780c200a5036a030004031b50348000980b00041c040140045194180305042d0000011035800ca1020704c180d01103100c003c031a0014001102c04c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 882887562 1250 882886312 882886321
    0x4120e06040e130209060a080a02091806070906030e070e0103020609011710080f0601050609060a030b030d0503070215101707120804150507030c02151e1903060e0609 73
    0xa40341201c0c00340010a038a80080d0800e11001e042d0000b607031000300e2250b0b050307100156083c07d01c54500400c50381140e005110661082e02071252014018140c500c080d0200041038140d48020031030f05010f03c1803030b9626103611f4501500101207544910130700089400c0098204409414440b2031415a03804035000b540c2c0e85520001640d010503120040145400b0308410003442ca0403034182002142d407000152000e1015000360642ca55109004256001805029440b02d5042000180c8010f51050030000b490348450400a0b1501b986450b050b0f00040000080000969040c4640e46d98102407850b50900c0e818021002c0048218600a59080035040003070182210401c200100041c036214148411400032428400c40c11350080c01007008a032446668042c4052050044880c1c058040d5074051411001e40e00304540c4990300d002401171130006000c000d550b550a40c02d46c0079000d0404c80078654034982d01c4640b8940c44400320859007810f2071b090041241541d002e052a81c0040d0468108031583e86 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 882888812 1250 882887562 882887569
    0xf0207081f0212070509030f012c030705010204090b01090e3c24010206010b030109150b18030d0e0d11011e090503070b0f07030e0402160c03020f0904120e 68
    0x1119048010000c00f03405118015401500618100c0c2050342512240d03e4944049401c0e5148107001d0400644030050320346040591616944840041d503041d00d10b088800e440b4107099070495046881c15540d9101c4050346c560700510444000c010320021b401316441c08800702501c0c1940240d0990711b00d511079984080307142000c40a15200030200c004003101d0300b00801c0078058007141000825002180100782d403259030000400604139002146101e107180c0c200581d1101a2901d070403800c280c0c80c42c04001248110450018019003400002d448121006001c20140b80c4030012841e102480030050100303040f5154280c0101c01c00e90007041200d02e6401c2c0c040101e500301010501010a100342c010804420f950202803103044450403422940c140340c440b2080003061050620340345540c1010800040024015a80e0300d007000c000500060424650101c2c0d103032000d480f404212001007a02d2014000c40c5004144920005070030b0381c0420b401e00e082d684080e48482c01c412040e060185c81c2c0d180c0c00b00759a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 882890062 1250 882888812 882888817
    0x60d15091b1205060901020909181207030c0b0114010210020315060c0601080d03020f04030f0336080c0a0509130f150b10080c070804030f030c030f0207081f02 70
    0x11000c1e500c502140c1d41c0800c44800c1c814220200c030540556004202901c8050094900c03d180041900e001c50322a442c1c1c0c518070340400848416035000f228009803015081d400542003060180c0c80c4e40020513420b10704035410040c1600a4250954a166000392690f03001900b44041d4070b400720016544d84443c01240410004598090703801a40082d501303041da8030110b0020304079400f000841d400c40d00c00c0c6000750241c4c050351052a0f44608180020408100380d001c0041c8094020b040c091503060005115070004100362040201c070348070750110a03d801d00b50411010062080d1400303002c0241e05a03000070230403525481003912030b80c85400882d281900701881c882200b075200c04820180b0082d4508400c02240c0d1111414105140c80d00d01d504c0c84c10020840c200142040c1c1d03030030401c0d0707448030700c13580840d00b014406950800052001100244186080d102918020b88411540348840d01d001132a03d0b50050001046400c4400e04004070702000545d1507000d010300455908109540c0000c00090 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 882891312 1250 882890062 882890093
    0x903050f0f25080616090806040b13060f1d0705041104031b1205150f06030a0b18030c0f061e06060706022107080a090b060409050712030806010305060d1509 69
    0x134000c0c4410700240788850801c8180e0101a0707211100910f03078640f81903444e40c50032900585038288001c001160103518982c1c03c03c41d00d1281d0b10001d445520780754100101d8200d807441e0061a0300007441150703003620401c0001c1c000c0c80300322010304c400c1000c005584064061407000400c50b126840d0780d00d20380040242c1e02000303040041101d0040100c00c3c1805940d944603500040b40061409010640d014882d0410382d2282001400a15184c54039a464450b0b00200820102040c0c507180100078000e0ba040c001000d018007182e00510052900308500c0b41411805451440300f41c0000700c010300c00082d84c0741603c0d030003071007220000e88030a4182480006807144401280d5034201c20310310324000030365005d900c901580ea030b40d83c0c1100c05c4e07641e0308505d022a0b40b02d1501910035420f0314002140c0b0300d815000484128407034020750784400c0d51030245107000895984200c0c0403031b0940c0204000c9d5681440b03900d40c425400c444110b0b43e00c210b61034903840003020b16460309046403500502070502041c200140c088 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 882892562 1250 882891312 882891329
    0xf011107122303100504020306280b1c05091c120b060c0a060b030f03071407050a06120b0a1421030a023f280903050f0f25 54
    0x949808203491040c2e68400c030b840c404d4001c0c413140701165508051081d070b44213400c05003640c2008000c80380842d0b45c14900c410340c0074000e503010802003000c1341088080d01c4600e203209400880c00300031039022804e030348004000320b000d03078030180d003000080900940958000c0010304002000c1c00402454401408003610180c0e0031850015088442070781c0001c01548031400307120104401c8904200300341c0c880c401e81c002c2c00c0003584180243c40100348103400d003030054901082240e140c69992004121a4003c581c04500407c0c2c00500078520340b43c03240652207580c2030032902c200c02d05007080740c540c1d80320340c1d004001402076914103c0b200082c828070050310003811314001140d03100e010648009503a5080854016800d40c054501c0820503c0c081801c40048807000c200103242070380990011203542c0006404843c20058100310b8020140074840421600550781e490341200390943c1030003450840d20403802c00745640400e00d501000c1101084007800034030008010807440a40341c100d000707928003c0d0400040e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 882893812 1250 882892562 882892607
    0x5030601030c0302040b030a0312180210090e18030304060f0213080c0102160e0c0f07060905150115140f0904020c01020a090b071703060a030f140f01110712 69
    0x602c054140444122803003224248642e40703031300302419101c0903002802070200b4100e0910040c40e1103690031080c40301040c42d6400504a0a540000c2c5110142c0310b400b8012601c1e0000c10f0215a60f1549459800642d20036030f03510420840b030125540f84001000036000d2641d98217407000101382a0100c403000040444103121440d00c82c12242c2e160b2443d02d501c030b8054450369104142030080700c3c64a0046402110610505a5403421000c0c0260f004109402a0807010000d440c00107501d4840d030502e03d40500d009201580a2420310400c640068000d400e00030b1030000510041070340442c3c04001c013085a46103079140d401c025140801c6008a0a00f16885400800c40c100980e0055002d85840c0c0880d0b0b031031f1907281d03640394500102031180e040e001d8501d060002c0d0814000b07940320001c50308500e0103008209a01d0703517074807803114000307022404848400248180c040c000e0000c01032400c7d04505030307001b0000c094030100f409050b446241c500030400000000000c41040c0200e14809400c4481840c045 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 882895062 1250 882893812 882893819
    0xa0e01031e0e0705040c17070c0b16020c09041e0c0b07080c0d0c0213020703052b050709290d11030403110a0201080f04020307050a0b07020a080604050303060607030905030601 77
    0x1c0c0a000560360701c034a03e1246610024243c6818007582e12000510385030b400321695400403041900c0b03001485901400700c80200c1c2000158425043c0303100318810840346800c2108488000d090007007035140e0740d2082c0c021b041848003180104c00340001040401c400d681d0422454940456400c526a0000c810a08041050400e10100344020202c4642100680305e045203645011b4411902e0400042d40082d188800c20010280f42d03402000c01a019080840c2000e030401e087d2031100c0d1081840c01602d081c0e0b80d50030036440c600703802015002040c500f0921100b905184103044c50b04602803400d00c404541c1000c680c1c80444420480703550300e551010a120100c08085582103c0d80151f41c1140069107201401181c0b41c2c0128110444550580d1404550f44030401d911220186c05403084e6414020542c00044555070214013070b000f05900803100d900c6018034010400780754010b074001d2206800120800c00010008070840b540240100c420742d0300c0b4426410700b00c81814140d0803880d0540311383c00011 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 882896312 1250 882895062 882895121
    0xe0a0605060d02070203062a030709080102040902180904051024170706051207080705121005130605030307140f01061d07030219140c1608010c05030c0a0e0103 70
    0x60154038002c1d022102141c0316681a01a503040c2c281e0080c0801234801c001c008488404001141c121520303281c450f461070340b5801103a08a034019400300080541c00195022500c00c0411a02103c02044a04209614040e1142c0d9211400003005105065a0700e00d02400c0c1304810344550814148032452901550721a003101c034035400580282c08491242c1c4070b00261080c4140d0484659144d0327808c41c00099200e000094403003000c09840071087c80401d122842130400300e01843c0d44a0424248000d419034038100c144001c2c80d0038200c01068803030804605000720780b0000216100f06a1003031008141a000c42e00132820141d0914280480d5400c013030780011840d0f04104984cc0708100c402c41006a40c8540e0420b5003280b1440080e0008900090750162500d80622007011000480003a801d2800b040004010b0405004c0388980703901d0002d0307000c180b000300000d204100c04d904182c2012840c50810503551411402944441c0041003850311480c54264031a0b0040c0c0d21407601d11130556544516001c60 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 882897562 1250 882896312 882896317
    0x13030b010f0b03070f08100923070203431a0c040608070f11120403120c02031b030a02120a02040f23090f07031b1a040e0a0605060d02 59
    0x31003460030086400840c030b040184044a01401d0300c1d44500c0303841c81d8024020740383c0d05001888a2541920980001003983c0c03a401880304801c4a60034812041503d0103401440c04400b0306030004552060011841d52040c0908020116007004280c03200b402c3e00c0000c040c170b01e84503050182c00000030b1240500c00c12149600000c44130980c2c5280c008181c0c6c034070f1340300c5826018038807480c4005042070f401f00360858015103003040c407810369180070060f17040f00848007032600003c00501d04001400007010800d00c1111145c0010500701407800c540c0490050300069900c11307a0131450004001030740754810302c0e95403c004940900b54003401c0300000400c0e074090780c1c1d02c40902690a81c00b560600800780103d984a00c9210722a52804c2c05518142c1c00808521484c0a4002c00c01c603028400c1000a10705d034081000340c04004c0d803080140700da074071006661441e09144290b000704d4011191a40181126541009981c280e501203201c0c0410303940c1e204d0151000c0c1c202c1d44e002c160004c400040742036005e0b015800 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 882898812 1250 882897562 882897569
    0x6011511100905061902030f010b0a0c0b15030c1002070e07030b130b010e0904050727061e060315092301030803270a1112030d0f05060613180213030b01 67
    0x140312100c80c05c01c864200b41d2100316076240f0307400000c000500c010b08050019100013051880c04044050150760743c440d030003105443d14061010500004101842c080042c9401c131441038982e00f4544d40c41c000c007c1d641c0d400d1401000c0d1003c803000f002401840c403940c405001030600030191400300012102e071600604048080c240081c2c1d0580b000002418800803e41c01658000300400324146044900074412550040c2203903400700340e400303940c0c002c480703070050741d020f000a41801882c0403540c003140c0320768900c41e40c810002e25040c1703402e180382894602285800c44000b0a404665a844854009050b004050020f9048080c1c40c001005000100016600c07031003003444520568910350079111101c1e05440c1050400e40e00c01818500010b080301041d0613024801b60845a5101800805a04542241c501503044c0e41c2e0b500c04c0e07848410418080c103034011106641c450310300200b09024030b020700d03030f036000f0074600c449040d518010095055048a803000060040001070b2038403450005100b803428403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 882900062 1250 882898812 882898831
    0x21c0302040f08150403051c050405061806010614030c0c0303131e111203090d03020d0e0f030c0904050708070f1d06060412150c0804140601151110090506 68
    0x11681e00d1000031210003084c0c0c0a004a0415610f56400721010341c0502c1c8517201c51070040c0700008411140b130040c240960f205001800b00b51908904c112803442007181443c03056441840100411904841007201110385440810750741d690710102200d59101d01525240c15210020401c01c40101c80704001100902ca01000e90015189016040b20002010005001004400700c1c200c8945401d1070850b01070544c1b541a681005103082c000b9541d55502201a005a000040344105550384030159502e500c40c01c6564a2810141030042641d1f46201404c460003840700f0401310342403080130032441c1c0080210004441c0c18070349a9050176a240e080d440f4105a82c2208120449825000340304144646006045641403d1901511000002c0340407026102c11003c0c5d1b4040c1c6c07005166016107110800c1d20b440d9001030303080178034280c42d41c03402080007412180c10000052003240c41a81040e508040300e0303e032146402000541440c2842d07904e0b84070840d058034142803030040060105045106010304c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 882901312 1250 882900062 882900089
    0xe0916170f0709091109090612070305030d0b041406010c1b06110f03041a070804030f14100b030c040e011508010501061205090304030b070201090f14100b030d0c03021c030204 77
    0x105204410344801000803414944240103e9005040c204085070323000c640285405244903002a2a50920310650010382d0a80c0001030030000001c0a4010748500d0842500e0400808402081e181c580c03174009480d603810080040b80d03903400e101a03010205035111007514092901559280e0140c960354088590101c1e81c0145490741c90b4040d00030041d90122000003010400f149035001203080c203680461402c8820300380502000c0080303544801c5a40c0c0ba04d100c3c00c03080113100d002c4201710b0f01c3c1c101d110504600441c01d00b079541c400741d00c000c0b40c081c5d44004140c2e40454901d003403c205d580503002d0bc500c82e001388410f110300010701040c150003d5040741e280d40c980d04517081100350f080d81514002c031000e41095204200c2080000c1e10310a5643e070244081c80001079001141d41c807441541d070410400c0c3d440040405000d03500000500811050994022041118400000c042500d444140c0800c2c01407100e41c880d100c0501d4000d10000c29a5400c11411241c0f120150b400034000750040d01130b025010916 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 882902562 1250 882901312 882901319
    0x1060c0602211f080703110a030501020f0a0311070210050c0f010f0f0c141603090b0c010c0239060915030108060711100c0e03030703020604120e0916170f0709 70
    0x142800b6a050f50300718005000000d0075070319513003447d4001502440c0c1181502e0000408280284040e020720050803054a55849c48031000a041e10120030310000e0b140c404010680050f52882d80120303200c4046d091668440400b03580950501c007564105034034035400d100c110060040340d980200c4d4004a4400c0801c54848007030412124aa4003018094a1000821445c42c0700100c0740c1500759070070b12a1600c81c00b069151005056981c1203e002d00d40207039110440c85140540600130080354510385503d4005440a03201801014251030030501c0100100040c4004140c880702c044034078103c2c0181c0301c200c1c1e040c800d082d02000382d4400d02c0303200064080d4102081e00d092081340c0100d40704205c18000c0200301d41c080d40e06001403d1a04a07001805807204d001640b46c2c9041c4041c05005000e45c01401c2c5a28081c00c2c121119500e4090390410010341c034580c080544d5aa40000303403c01038020f40c0448106506505840c001640460070054000110400c00300c41d11660186200d842c40d55540358a080d40c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 882903812 1250 882902562 882902611
    0x7050409091523011e260f1209011b0605130519030e060d06080601120302070e090706050c0a021807121a041a090a06051905060301060c060221 63
    0x401c140d540541e400c0108503440f9080380da1010000174075040e841180d580c85041e500c484032001d03140d141000d009400d940d610018480c3c000d102e0204400340088284180f410001032142d00d00c01070601203420308919a40c0c422400ea0201d09034130040030481d0303051074048100041d0442c0c2c812903881c45040714284010710750040c420303031641e03042d1181c110098080342002416080400d54804843c0da652000a441004001140c021311000038811881c0c3d0807401c3c024282290764002e000d840322451300340162400000b901d402100c0c143c4c58100e4440b401901400c2c2018148071000e91702095401401d20070341c01d4001954040c80c02922030580340440b201c3d601013a1190004000d120411450007080d0504140c1c00c403442c60780740305568600188a03c400508610b10a903401c0c0c0801c8ea80340c00500090030b2000901a06101c214806040c1d2898000010790307a2005000d2401000314095090b02044101d405440000303000303184914040c01d4045030001d40940803103003001d8008940c80c0a080160 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 882905062 1250 882903812 882903851
    0x11e080d08190e0a06020306130506060901230a0203040f080105070804060515030604060b0415122d03121a06030c0f0705072c0c0909070504090915 65
    0x1141078403100365590362020701d121a01c42d6280031402c0b9a490381002114518240800c0100d144295001626401d1400a00207641007000002a1803071500c4248006035440b5025969078900906c0c0c402600340030400422241441c140d01d07080503010204424a1480c0c0110181095136002108030001d070341c6c0c0350400e5090b5413040d6403e902040030a40841d001c84d0064102c2584460b00084d07150703944d6425808a0b02d0181c04507030640706030b50b0b907060003003440c42c05016520140070b103402810381050804035020800c8041c1c070030042c20030015201c4440e042c103480100c40300c20b11200200360905083e904019002d19007200d030043c10f8501d042d4498003600a21003213038070202c5d005008103040d540c1d546c1f20900a42c2c8030552211042c0800d002d1800014820041440a40310002490080300c2c1c0c204030a807180d514000c03403036401208803820801e90b01103807425a80914000c48480e11281c0340d04005031024130950300880b04040c01d1030040400d0008500b007540d901115014104841c080041c222000c11 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 882906312 1250 882905062 882905083
    0x1a0702012009011425170d02041505040803031609030f0317010503010213050d0206040b032404020306010c0f14030408010617030c06060d06022205040b19051314011e08 74
    0x15000c0001c058204016014200d070700380d124101000000c6e940c00d9848500ea04907601d00451340f90001810300403000100c1e101d60302640309080141c00c007401c00c2000b41d01c07400010324040f000b0200300781031914680300d94221402182c02180d4034500d00700600b001800d4400b4004d600714100f291f540006000d040500c02c403690028060101e2070514101810401c1d581145081a648040c0500001c1120308000001b103020b100c510f0601c800b050800c3d0102c0303000e0208914043e100d14030502c10040c150360031004040110382c0c0456000c0c0c48065518203201c817841c51000c100c18510020a0101300c181056000c60103071103048050030620071121004c25a240b05045e010b0403103821103000711f0b41506000b8107031110144501405400e20440c03074841c81c441c000c81c44101c40c03d465418400c1210341424844c0402c903400555400b00c0d4001a0000103d0308075140c070449008020781c3d000c1d28040e11060380500203840104a1501c1956503c0c05001510f113201ea0060f10150003000d40003071142000a02500c41 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 882907562 1250 882906312 882906337
    0x2d110c01110d050a030f0204080f100b010c150e0a080c1203060a06080721090c050108060a0b0a030e01050f06031212010b0a030f090b0f090304031a07020120090114 72
    0x1610410702c030844040c0c01500300f220602d51203121404041000f4006007010303020100c01000680c040c410701d2454200300e00d00c600115464184030500c2a640000500d482a8021440b0700300e001d200d4038100c0c010035140618407480d018004042c410000d80c0070040c800b1010040803202040c4a060f0303034114600c42901c00e81d50010700301600f0031401c3d00490000c2d51040803801c1ca8440076101041d0741c01c003800b4000401003080d075110384100802c000d812140c8042c0100386030682c01494942e005c00c60302c803000d0003003840c203c80120380d1212480c46070700847c10b036503a050001d0080742480b400c0c10308600021364840344a0301031100c0914202620000340c0d2031b0850344074101110390740380c038600d83e50b01d900501400c1e080607112900c0c810001c40300c1c09000481480703141c0e2440503103003000d11a290b210f4090505103d6030020003041012661807003c5c484c2d48c1003150180110b40c1c0700c5d58402e03801045250303050040b26816100c880d020300201130141514860130307200c005a440c0b1090038504148540b80b200300d031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 882908812 1250 882907562 882907573
    0xe01050a0b1209070503061e010e04050a060905160e06040e06070909090302070302060f030a060503120a14091f02150123190f050109050a0303020d2d110c0111 70
    0x2103000d0016609034001c5100d070162500d0a480f000800c1c01c080c011a0540509090b80d0790100040908d071020600401400400c9541340c2055500c442d00d9000e40e4402400d11625405207605028042c400d00a040c03080b0000d440c582035941064426040046902c144140c3c40c4c40011001c0e4600030560368071841040e0381f040c05041c10102c0180c01411006c3c1c0a07400c500c01c140001c0f0050300d03008000d101c1261510310507510b901d85088500b054900302e0b0002030081e04000616071400303000d10280c038074025960500101000141200e111303640100040740d80d0002c0200765035610422000c1480da40c0900c182d0a88582001100a041500b00284560b8064145440100342c0d041c0b000c1c1e54030f800b41d00740203109280c0ca910154048580c11910380140c146012640001c0100d507810101c80c00c0204804c0e40e41c80c454a1450b04d000e500c41c040960214240002208070171505c11021098051600b070f1006105925581070ba002030110301040754541d0750740325003400400958000c036005628400145c00520 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 882910062 1250 882908812 882908827
    0x60106080c0307020309060d020706180209070e03330708060a030b13060f0b13150e0c0d02041d06030f1c0306051804062009060a14030406060e01050a0b 67
    0x74994402401d4404501042c0049030007030380c3d098024110301c00c00f030700003503103400c0141004012140100ca888099071a941e20690050b200d284017260301113010305003c80320740c4000300440d061200f04110000300744001d5500441401c1c03101e080300d004000880075880207170754410050b16004015075403560720101054041001441035207555901c00d080c02c40c030000000080e0750304402d451520a900102c5d680340c801062103410a61140c078900300110509020b502c0180b000c08030440d059010b54458401d00c4400181109044070840340c0130040c403042159a03941c2c410509411100410052040c0003c9202180584c90001a6404400914806003001e0841410b06d001c04221100140c800e1540b07039000011180ea80b5900c1d04101c819444071910145011302e01602202c080303410565411210690540440c816402601c00084040e110310343d6a000c60001616020214070fa00b46401d60000104410400c0c2a0810021111010000d0f4000e0340c950082148218a80c0030310b404843d410f101e2070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 882911312 1250 882910062 882910081
    0x3060e0d0c0210031e0603031e0c1704230406060504050618040b03010e06220c0315060e09100b0108090a1104020702040603140c030703020a0b0a0e06180a0806010608 73
    0xc008418060400190003100820705e04c817222210083c0c0c2e4030041d980c03941001819003100000710041c0905000d08041009008060045502180003416405405200d044d00c001103904036070103042c0b03940ea01c010925100c000d8038180360702540380740d01481c1008400140300740100e080e6000d4440080c011820191140070007008007400210a5610a440b041040803544003880390316a5100c64102622040c50a0230002049000d69612400c000840349a48404034003002c003a8416a40c0c4008c0b064800700f0745004500c003030101e54001281240e008001d100240a0000301c4a120062811051001038101030055540d06030464044c8280e40000b951000000d2840f240c0d100c0c240701c000c20050404451b500030500300c560580044440841050310b001166804200701c01c0b9942c011401000600d081d6404250b070441c00f449080464100428003162640c01460220350030380d8085d01b50b0740c0755036510001e03030908440049407074022001c1d040e01080306900441c46a0584031942c6404070b80e40c50384440b5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 882912562 1250 882911312 882911329
    0x70b0d093017430c0219150503070315060306060f2a1406010801060e0a090f020f012c180f012d060903230c0118180603060e0d0c02 58
    0x10070410708440d08620101401e0b00192070703a901ca05130780e030352860740b640c4c41800301e84140300c00701d28000220420708204640260f0302a20740000399150080d2aa100c0c2d02c2c040d00640404800311450745002c08021411a034150b01c40000c80c0c1a9a4802d103040310320b107806403010240089286010301c00407480300040440c10300c40b5a11607101305004403580b102844858200b0381e0a80020710396075101c00040050030341c46500290020f0b0800c01c20440710540f641c8030581c100d1342c020000d00828000141d403c0c184c3c0586040d1048030301000da900251403103e0041d021504100c400d05111f15116110081c01c02e044001c00c5205005003440703569280d0802c0b03004100038059868840f108054034100044a01030b0011103c000d11030380c0c90b01d50b046400c40c40c1170110224514040708030101603840c1c810030000300080000030400d0a003030118014103891044503000703501d130f0000703180e81c1d00340703c40c3c44d43d0158140d0068041349d0203510100702d0031598482c020b880c1c62418084100090020102c1400761030f04049 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 882913669 1107 882912562 882912631
    0x8030304140c100f0f090b0c070302010f020d1b0204091502030703060b0f0d1104051203070219290d0501031101080108070b0d093017 59
    0x101c000d180300054404d01c2e00700104a000115110f0040760098080d140001207503076540c213014a050382d2000c2c41d02c0107e0008840051069100744080740c10240e80c6840ea44a0841510500c0384034941000040141d0780190b031b6001d000000307104401d6042e001c080b40a40940c60f890701c43c901500b118580ea07c40d1160381d008001c19440c081034003040325928000d5410000313007044041080c14481c001e0360009504a1b51000d290010352034000091304040c3c5c0300f01c40e07004c00000b2642500305400014800d0b0b04070003403409841c141c03c2c0401c2c1c5180381c282414424440c00c000958030782e0000d0b07440a0b0300654054000715003448455038410f07030213409013021200074122a480c200f200103540c8600511200910341d940955001c000f8403603d0f50b00b4486050f60b03200410401c41c4100c1508007125100c1c1000b00789101c21011080d403180300458403584034194241d442c2066250310701050343e400302 = true := by decide +kernel

theorem cover : BRFrame.Cov 882733812 882913669 := by
  have h0 := BRFrame.cov_init 882733812
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 882733812 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 882733812 ≤ n) (h2 : n < 882913669) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
