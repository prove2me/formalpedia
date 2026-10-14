-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3095
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:38:48.396523+00:00
-- url     : https://prove2.me/submissions/bc9093cf-1ffa-4cbd-b109-65ae4209aaa8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 556474820 ≤ n < 556654676 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 556476070 1250 556474820 556474829
    0xb090f040f150e090607182c07020102131202010e0603070c0506071b060b01110307060615050f0319090f120207060f0f0509040b0907051308060601080705030604140709 74
    0x42d0340001c08100c6180c95034242d07100d03066000c02042d02c4d0321405130a655601118071600700b88100c0b00790108091001c0c0c49140f6030460908400c0e00c50810181400710f01040c00b42560045900410009020842c0501000152500011000048031042c40103071f1310400403407c2990030910101c20400030541000d481d41c0f05034080d5041d0381e81a0355420342122070046025007080c11520b0030b5039000100b0305943c0001c10521b41030400410185801c00361074950f410514041b0707a400c0d117510051207510f40c1c0c00313844040304034581013442c2490321a10040b511800000c2186202c4692290182c1e90140e05401401100303800001e01c00a02540f4140a80c00c0044411b101d000341c81041d20020314107118000300b0302c440e2840d0340d13a4040590f60321011a0aa03021888507540180c484014280720b56808860602900264559a41d10907d00d4080c003602082640210702c0c0750403140400c001660040122a40402645042c0340c2d290746403000100100b29032080c044500000e6420021015000400c04007580d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 556477320 1250 556476070 556476101
    0x204050f01090b1c0f021203031815070906081e0a0c170705090f01090305060c130602070501050d0906021303030801050102010f0204080a0305090a1a031905040308010b090f040f 78
    0xe107040024007041c49400e000d600e845125804400e008180f565417219400d51005202c008000e40001c1c80c249507420a0322041154884066541c0101c80d0400a10405845485941034140342c0840c010307021540710b01c241e030f06200242c0d0002e030806c1454000c000c2c05c000035420b45041410031841f40001400051304d8000803a101a0b020305401c150190038910501040e510189490035600c180038650b203248000506100050348007100041c810302c03001e8840e124039000300d600d0380e04c2085042c44640c010703440309055400c1200c05100b6641e12400b110305100701d0321808103810a451400d03100a108510710461942400380b408000c065114400d641211000d900a205005038101c203131040340f290344204001680000b5040c00041c1c00b54000d4807900000400b14a615650307018412115440c0300e00c05480e011000082140c480c540c0d00c3c0d54034038001840c00400c420700c1c1540c0e000d01607031010300415200300c1c1c0204844a89558181c0c041c1c16800000e401403200c3c0307111000d02c001400d000c0310350740c840 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 556478570 1250 556477320 556477331
    0x21005012115021b0105040c0e010b1e04210b0109140615070b0f0f07111b030309040c021b0d02130c0306330905010e0f0d0204050f0109 60
    0xa1141c00c403412141940c58030300e140e910020b0707920004605451104085159028010211109846400c40034072081c41030010405180928004c1c10b06140c3c0e0300220040c1800c9401032220003090016581d481d440360b00c9070414440303c2d400d000524000c1c1e500c80c0080c49400010146800c548521100d2a1846020038044e141d80310380e030314010f66142080c06540c41e03244030001046d038a031500340300c00703075401d046011850021540c03110010060b048500700419000c0c03d003405071000860516907440202031800c02a08400c050307066403242c006098180650304d100030030b080b060381d060085547e005001031082148000000d00603440c1e886000d609050501001040241030a1101c140100c06038028404d00c0381c41c9410704000010003070b00f1010740c1015901c400104001c0618001e16043c041c0740c080c410b10502d110b0b1080c505e01c90101e07104008000d8266010011640c000581440c00801240c00f1070001551902151000b000d885020303502c24205822b00400ba0b00104406050720500c44042c0038 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 556479820 1250 556478570 556478579
    0x10b06070f03080601050c0a020409020a0e100f1401120506010e04021308010f11041a070501110d0c03140705070503130906060f02060c090402030a02090306010314011811150c0a0302100501 83
    0x1c46e8000c020300c18429412005c52a00107282c640d1000384400e200600d00032003175484d83e40d41c02451500311803044032401c10380010b1008800c4242001e001740598403680107044107800c0001c09100900380c403096041c0c2c5072400b00d90702c0e82c06040c01d11404400a0300464950f40f00c106031444040252181c444254640601d100e4924800e02824041a020700200ca2801e0311701081d40001074947e2607580041c003001e011794000a00c0c203006840804014a5034a521180b030013075420100e441168120707080c540780c104600104c41c00d80c0401a400041d80c01c0c002c0c3c03115034a0070028218840c01203404402d8101000c00f00d40b9843c20303403008003950259522a01d00d000034030f90603030b075902c0c2c141c4a000031400c0502001c0301070310b0281c0055a10a01c804009070504550b203011030b1500d0360a8000f02c0382c2e040c040d042d00c811554248164003242002d81d0b500e9040f2041130703c40e405980c0100c0c0308a4007404403c80f072142001c0d4000b046403079640001d012600b8486182c14004c4d241e04c0102400004142401c00000303 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 556481070 1250 556479820 556479827
    0xb0a080c0a03032001141617010b0d0f1d0f070f140a0b0c011a030a0c0302130b0d03050405190806240301020a09030209010b070b041202010b06070f03080601 69
    0x400d54a40034000a00035030035520300b99448607551080d90903100360101d1459000100380902d0601590350401c00f116420410120080880a943c9800c10080e000d855001a510380d2600d0904481c40d11744004c5c0d46840e0415204050540f40c0c1c40c4540c1c0c06d050041810b80e002c0d125150b0140040e03c0c405882e206081c0445c00b94070b64240780300f0069520072081c02444119005a0703546180c620003442c268003d540c8002c0000c1c51b4220304401e105607555083c80302900310408005188098044026203035070151503480c100f040d44c05001c064002c0042852514402c5059440000780c000000d0080d80c40c03d03940d06c0c0c0280960f02078018075000b8071400d103505500f5a031a242045c146d42481010780016a00c4100e20650000c0c0c0c003d5001e0100d07205214065651400c0c0b00400c00b6946c40c0da14080c55034150700611081a0042c1c3c841441c1110800c044404070352140034460b0407039841109403d864101d410704074003402050119980c0441c0c002046400c0040040040c1043c0e4400d0729000c40c0c0c4c0d9502e00064 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 556482320 1250 556481070 556481083
    0xc1e210705010219060b0a05090c0d0509071d0c1308030c0c04180b0613060f030203070b070507170f0715080604151707090e010e1207030507020f0402120a0b0a08 71
    0x10b510381d1806000380001105c6810010341c20030003501c000e0485545900103484c0401c10b40c0c54403a285030001c0e07488030030415401010303480840d90740240100307032070180100c094009046000c000100714801150010341140b04564a04800420b60f5811036140c0421030740f241d01c52000c2c046644590b245182003801c1c9800380d80c0900d110500e020440424a40740c61005600003403400b54814a0f20b80714892007000c41c41094003070a40c41d21941d188a06510515103400081d4105800091003401948000340d0002801002e44802040d902000161031800524081c5010504503107401402c1e0041000380c009281680000d005503103a11103030300e48100b400101c2d1860050b80d5804000d500050008030003140b000100e094502e4100c80300c0c1c96588002000301e0b0a20411800c075a5150f202c0c00d15400c10821000302548840c0711064949115a80d000d0b0240c41040c2c0c009010301d50040d03d002c45540d032039040d22044004249941101d00e8052400b1000300350003419035124203062038012406090000e40c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 556483570 1250 556482320 556482343
    0x1080d0305161103070c1e06170a09020a1503052202010c06050606040503010504080307081f061b05060411120f03162108010608060d03020c1e2107050102 68
    0x4840c1060042c10458076440d54014000e8284010460a000290b1010507070b801002c0c44503a051215004031000d8907801c00503802901000003140084404000e640c00b155003065040304002040c00782840840c42290b81076020f469510a084540d00c2c00c1394054200034894681458000c20200c081d003c25a01c02c0303400303c0041d0019213820b4050001907041c1d80103e410000c010141403c050740c03000001c0c04d49804450032140003002106100440d03411210b0f290304011425610b0b105141c140805504042d8640700b020204a84007000c1e11a83c40c04e070060031152500302d01030b1040d503d000c0c1007114490107502c1c0124011440081009103289000c81c01d1031605c04003e0155103070030f00f400501d80c2c181c0c420341c1c401d0b14450400802072548001a000420700d4400940361061550314082d005040ca8400030516406154039442a00000741c3c0840c460b994000221040c041000c042c2903d5028507800c503403069008400038082030808040c00f80603803c10031043c022103d605459a00480e140c90301d000a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 556484820 1250 556483570 556483591
    0x30603050c210d020312070309170702040204150302090f100905010309080c0105190c020115171609021e070f150b03030a0804020117070203031612060e01080d0305 72
    0x100039a00d8280c600c01e2844101024041682d410309046504010340c0c1c1102c0307005a030002a18450a80703074904a1a80042541020400469075880310000c5000c81e4500c0700c0800b400096000440d504d5905580c0500058001021078014032103018009601c040709807071080c500310910603054a01502407201c1882e1507a40c640d1603902e4100103501401c84404c1c103e8568906001c42500b40e0000d1280ea40700b00e003103040c0070100400b1001f012044400040c038a004590401841d0901c2407016641c03103040300c40e20000e40d18185c0468800343c0c1032071004001c0484e80080c41c1400501020642c0240000c205840c40c003100b400b40d500c15850702c134403442e5001081418001b0225003c82c1001140ca003144035840e001103002014035000a05603030105402d61301013070360b41080c803040d9640620147c2c0e0307100d42051011141c2c10b01d41c0c4d000c1d41d80d01004111000307004d0045180043e042c413a10780e503011010856818070409440d03c002c181d41010034000c4400c02d11400342140c02c05071080c060140030301b0001c030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 556486070 1250 556484820 556484833
    0x30b1b19050702151b01090c0303050d0e1b15041202040e030f04121502030402130506010c0503070606080c010503010f031712090a060b01210b030a020d0b0105010801050103060305 79
    0x4014550a0288001010900805020460150301c4260454013001c0902001c20341e2507078100d01800700d0303500f0004001816031501c6200400250b21901c0c0a05507601070030102d03220032070050300e00c0150007091076803046800f4aa46902c0b483d171140c66a90360140007221031132083d01421100c04901c2c000c0f0300c62810100942030034400541842d50040300094001001c0d24601403c5090049282e0f005900c154480c02c520f6a0400c180000c4030f21480030388904260540c43c0d402d00e900041c05030b03088095030003d502d0390b80c40420445c0e0300418914032015031001c140c9803102054244000140b0680c4a103980394090034a4010741580700783c04480c1680e01c0c6110803401c890440c1c0f02d40e000c541201c0c40c0f02103441000c000307890f050045071140e1817080032008000d000c00341082c43c0c940242c0b804c03180200c5c10b00c03007901d600494803621540c0789008030452090004803407103060002450420003650103500400e0344800001482b01e5580000e051f200283c82d800c620b40d03a070340b004604031007071480040d202d0340150 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 556487320 1250 556486070 556486087
    0x10c1106010b03040f0506070810050405010510080c040909060209130c0f1409090c0c0d1803020927150c120f0a0b060409020901080f01050904030503070c0503030a06030b1b 76
    0x842c00355401a0080c031010701c0483e610360701c0525003c020b88a0f280812003640400c03030496010b04c0b030030002c0c0400752010300c201d51502002c5196085035404c50300510a1041c000f80b0340000010540300140824039080c0485101c0d800c0c600c0c029132101125500503801c00c0006410304040303000d4483c466415945151900409402c2140c00c1e145120500c98211400c110b031404964840707844a009010102e0055a114801903009292605100403074041c0b1484550101c41c01d110a28080c0c21650184c40c006034580d00c01410880054100001071034003124011004002100041e0061000608600c440c000e41c40324a0203070740c10301411841140c04a1642c00107070441100c4405640c100c000382d440814034030404030010390b403a00503030410110341c0e9000c140c0e580b056a121007000e070490703151001c00d1602e50420b40407900e500c0c0c0c0240080d00384040000820343d01845103100c50305503600401a6600d82c18002404805000c10348000d5407000140c41c045084a4894000d1025005000f08aa450543d44 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 556488570 1250 556487320 556487339
    0x60c040e090106050a0e01090e07060801270f02041e0b0a0e190602010f180f060c1206180609050f0126010509100e0a150b0406090e01060305010c110601 67
    0xc01c05000742d5201e10b00000e076915219001c0026140e281c0f81104198100b50150b411186441003480301648510410840b25070131000090554400c490380c546a11031021480c141c00f01c0c0c1000d00c001d00c5103400c8070307060241c0d80c40d07014100b5581112207041c020124800d080c3c07030700410340c0100032a02008200c02d40416004964a62544901a00042c208203046008400c1c0e0301c06607100c803000d42d46900414040c50306078440c0d500b944400060000c5121070700d0b140c03101c1003905458001c000300d070b50ba0b4292504900030f114007440d220000c007080c000c0544820000504c030640600c151030050400f04040f070101b0300303030040307034841c0007560500700142c1e00e01190442c0b1071403030700d0684d54901c0ea0211610300300c031401e0141500c88c4a815001740809404c1e440280119102c03000d410a4036042504601c0024208901d03000e00102e123480d01085004264002400074222a44491001458840802000da506410010849020380e00030010524032010594003101003d412520603007040c4018032580780b5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 556489820 1250 556488570 556488599
    0x7020102010c1404061209240f091110020c092a04060e0436050c12150a18050a021302031003083001030b161b0521090909060c04 57
    0x40c04080820485070313a0710342d441070100a50509280100c0d191a08d0f00941d224011184981800c08081180b4002130711044441c07114011a07a01c5100644400320b01e5910800c50760000032001080318000781446240035884d083c0ca04501407800c0c00034120f6569000c114400c1e1070440c0c64507103801c80c49401100800c001060040c0205a2003c6401b04201030f040c10100e6210040303035000c28080c0405840d0a05514040c5a1501d851003076007500c3e9880a0840c01103010351425170480c00204103620382c1d084010281c0601c84142100d030742c0091012090100c00540c14030700d42e000369074011655001155200503803204a520b202d801240c03100030800a12944010070428910307071160480041d03010440c90240d075542401440c0030b501200140103021910f1002608034083d50620702d22000740c0302000e031000060045289403490244c401c1418041c003400241c40c840a41c26010004454900e60518280c010900140c05141e803000020420140066800d01406903c0f102c0b904203480e1500c081041d11 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 556491070 1250 556489820 556489847
    0x60a03060e0106090f05090103021804051c0507030f031a120a0c0b120f25050705060c0310060507080412030c080a0206040212190209060d0b01080307020102010c140406 74
    0x603030340c140c0060200c07611075a050103401c0e0b954500301c4607480c00c4280031030548182c001501c1181440300400c01680d840b0860040c111b40544981540d41d150700344039090030008a101440c5560201e4441100b580c400012710081e4425107030381c5030b4140410821401c45428170fa40d054501078042d0040c455150004800310301e07030248000c54810310302c0c81d5100701c040410369104039100c134000300d665098001320754440c661045191003144142d02d03001c103036441d03440103041e44000c02d000c01e00501401709105908503000c2513013180480e00b8904180078016180d900032220002d04607101304011414038032540444603d203410060741d90902c2d080c12420861a13001e224101d081c03001c01054600001d0140c0d01828002206402a040785e00d003900510000c14009090700c01c10340c0000092101ca04111601b0f43c0e003141d0183c410a42a41c0d5140210303600c10180b81c80907012512980001500600010062251718800e070f00a002048001d041640d4800c10304161a0324030009000c1480018841c1c1074445212 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 556492320 1250 556491070 556491077
    0x80f0103080c100f0e01051b070f0c0b0705060f010f1a090402040f120213050610030b150409090512040806130507030b01031109090f1902030a14030c0f011505060a 72
    0x4441e2080c40404075000c9071340050340300d62190300307094864900384100347c0e100f0181c4245c0301c22051030015807031aa22482e4001454060200e44400500c0038203d02d1401a0000e150034594402190803e9a43d418049031440d6103100f00c80000b141f46100a20090304840d0803046954040000710400307680ea40000404541144d400d01000980815881460b002031090280000c1103a4a500512200d03040c0726400002c01e0341440c0074040c1c00c0c0c036100d82c202103c00301c0346000100311087e42c0000f0000c40b07980103481d040c40c2c03001c2008211501180d200c00c2155114804542d00b060720a803020a035802a403249203c140c01160000d1f140052080191013035038030035800d40310400d8403076585009005080e04140c07005081d503071003240541000c0c40700507001450a0010510403c1d0000c0c0c645c1e803000340108524041c1c1042c00d4403070454400704541c0000c10b0348800a60000f0440e813420366a20b41140038143e003540724051898207400d1040c490302d440d40c0f1007880e56081a90030b10f42440b440e41e01090014082 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 556493570 1250 556492320 556492333
    0x2409011d030a0f030e040209100509010c0804090606021e0304032907050a02010e0714040903030e0d08061e09040305030430020c1804020910031a06040507080f0103080c 74
    0x241e502400544241072050380302c1d81c048645410001c02164400016074040c0c0c2c8100807d4901e036607020100100000700d403a00c591340f01145401200d1a0b8012103006061450218010a84201c0c6401c10025100507a0031695030008184140303898034140c43e60302042340c00401c404d201094100c00c03010a000280c1001400710094081002260902140e03040c000500201e0a1107840b41d081c0165a502215103009144081c01c204000d4580d82c44060520b00c50b0f95200c0c0e003041018000c6d0406c903000910344c01650302a141c04440506403000481e40e0620800c0b003400130071802440411303014100783c4040c1840702d0a9482ea5010b40e0141e2010f0030644005142c0c04840400b404c004803c21009a0120b2200003d4000000701034903002c040c4034501d100314100c0c20200c00f5206200000c903030054048541840e6910351030110002ca582c00d400107001c1001c0f41c607203030780c5040b0141400d44c003030f04003510100071960f1148401c031092070040d00c0000300c0307000e983c0c010000302d010200900b5080741c3c1001a504c2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 556494820 1250 556493570 556493627
    0xf0a0c0810090f0b091c030902040513020102280609050303060a0e1b071a04050c10050c0c0402090604030b100509010504090809220c11070605031303140f0315240901 73
    0x281d441c1b0b01301c42100040d4444110404506080c001c4c030f0741064180d02005a240c00d035900107900c400e051086070f4900d45000703c1c0c2000e16000d1440342c2c812103801040c100303c2c0071410b0a190392664000c44070203000f480c40301070000d80d8a00d202040d0b4410450b184041d132503c0196100c4590940c8071000c1551a0005d020029107140c03200000344d40503074400d000800103c0c900c3c0d02170100d41c5c070101804c681404010302800124000c0441c00c400720081c204c5006a4413510040056990f01581d04040c01c001c207003c04010320955844040402c0c1d80c003c450b200c2081e0303660400c20055940f18640108800000d105000f124100901c0300e0b1103807568407049000315000c1d0051802100d42490725040000c0c0c1d6005080c007500c90a00014000e0070f11480c203149149440100c50312041c1c8040801010004182100e100d40d4442c3c806841c400401c00120540c0c90070149890410129401074040c442c0708000d080e403108403101c448891440200c0e80b8811b04120380d500054450070441610052141c5100710180e0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 556496070 1250 556494820 556494853
    0x11209020316170c1504030609020604090509030d050603030a0f080a1e020912030c06071107080102030a02090102100902090117070909030201140f071707020f0a0c0810090f0b09 78
    0x24041d0900d01c10303080340c81e0703101d000310341c80c249000a00718000d1101c8101c2485c850503540440e015a5082400481d17840190310106100c0d2245a000c42f0400d4603150500c0000000800100744440e4010810301298540f00300b0141c1b244101484a40852000030440002a02400b0030741ea0103400c0210001c2c2d2448140700348c614402c42041180e0301a41d0000e03020723205281034003a600d10b0f442c03e2070056007003407246080b190761014040c1c800414040c64500446280c02c08009040140600713500070354683c02c3c98030304540a03410881d4000d001d400b828114445200146c800c0c0740365250002c0136165564602904148141103c2c80307901070701c1c021030a0101c3d2510242c00f41c00712851185e400040c9040401c1c901d0a03080c00080c018020701c2c101441400482640f088444d1000700c020007111200f6140e800059103801d0280c101104103010b1140b410081c0030301900b01100300c8800105943d0107452119200088401d4500002c1c01400c3c420515000700315042e003102e42c0040d0803400c94040300c43e40308564 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 556497320 1250 556496070 556496113
    0x30e031e01020c161a0f0f0403030e100f09090b01020c061207140c100f14040b0609090705060417030c071e05010806010813050c101d03030304020112090203 69
    0x2100d55a4000030348040b122400c01c45000600c50603841448020f0400b4001c0303010000744108004d8000c00419482044800d240480711207124200040340c0c0c503030303503858054940c01a80d90481c0c45102c4040121015a004a00c140b000320030503500c004845003460307080c5000304205c2c200181103205801c90003559032141001401c0124031070f19007a04500e0044402030030152104590340541c01e040c4640b018072480050200b000f1510030401042e0036009840c0c0f1001002c1441c0d0400c0f030480c44e0024401400782100100d4006e58064590b00500e40d100c00500381d48030311a116076508800c2c01c100410007125850070301d00e0800c250500380c0c0d1030400c0000410740303050003581003410080900c0681d40100841802c80b8401040d007805d088180c0d107000400030303004020080401b000700d140041e984041040c00e00c4031010303581c2c0040c01803c42000025000b444030704800414440b408001418200700e24000007520300c200c4c3e059441c003100059094141024040f100b030b04030380600c5040303e02e03001c100d00b40110 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 556498570 1250 556497320 556497373
    0x31227030d050702010902060a0507061803080a050c18060d0908040b1312020105030a0e1e0c0108100e0c0724240f05210d0f020d0203120103030e03 65
    0x315100d0101c5500c140440d00d001d40041d09684c50540c2010045e01c07504181e03040c0c0c648504202d6108c10090070b011010301101d105404071401440b002c0c400f00b54000715601d00036100c6103401c002d00c0d5241420991a4816800d03a407488114a115040b01483c00800a00003206015408250691076a0351030045400c07a41208035043d00100e6800800020082d000300184608010320128190070780020b0154800644004450340d2604110803001c0b804100351481d050b100204c4400740d0720003a40d0b0035100c00d4950051800500804089154140e014909506403000701c50078800b80c5e01c580310b0762a02e580c403100d01115507a5200032004500480035070822442050010007103001d0918a0704445400314000c03041c511340c01c00700c109202103100101c0346010f0342c10580d000c281511001c628419400d03038442d4500b040d4401ca08080802c01d5205243e03c40300401502100c240035030b50001079890380034142d5205102c2010000410120f445240302055460700a005c5c1c440400041c5851044098071840 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 556499820 1250 556498570 556498573
    0xc07030c0302090901090b0106050901032d0f0204081002071a01080a06110c10020c0a060603060f0608030f07020f1c0c1e1a070203031210140103050405031227 70
    0x1002981440c3d115a507200c1004402009104203d0361a42201e010601a10b010824081114419640298000407950809102c1d0b0700002001045100030500403504549501d800c1050222602c00c0b24002d032001c1e9281103001d00008a6082660700094114042c1655501c91010340300b5040188540001e0280000c3d1000c0c0c80a1000c034104030090311b041c40b081c0c9011074801c0024140059001c00c5d40082c41000c550003580d182c00701c00d070349854030380c8074500279203d42d151850002c100080b0380c1c4240d840e0032030140240410f03039a5104480d16805012240d2220242c10010540140b51503a0121000e000003040982ca45200000f601446201700301e04803401d0724961360a00a40c08207070b04201000040341c035055041400d11024030055090342c0c84a940580020924000311f66050051301c07800c102c180700b088040c0c41c2410584802050740d11900d030f40304403048007151455109000ea02e20494010005500d0310320300c41007080729004000c040a0303102c460f8001c035074215840c800741d86914560070390 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 556501070 1250 556499820 556499843
    0x302060f25061103010e07080402030106180204080c0f03060103060506030106210203061012140106080f1c081003080901030902061614032a0c03010f05091504051c02030c0703 77
    0x940141203c00d0141d50b407803c070009100401030f0306080109591702900754600407c0310384513407000c01d01403c0306400c040154681c0d4400000392070556809403007200c451808882030b012107881440114000c2c100c000741c02d40c110350014004141c85401413504032001400028050b0360340c44002401c01c00e68500c0300d0014041418000551030304000342508600d204c0c0c0ca9034122850038035000800188201c000780b0b050105075002030a0301f405c0d480308000f410640c0c00c1c0c815500c88400b0150300c0704100c090030b000b007402000c1510402413048100303a100c1d4a010105603001421030702c0f0800d29410003240c03281023544810404005031180c4e0090080d40440640030b4840d9695854016050000840a41016402401a1403410311104c142e48004d1840c440340240c8001c52031000d074204001d150f500f5800d58203101c1c50f00c00506459210a00c545851001d485540c4401402048540c07415039000c1d2040c1d02c4807c440703995035540305030060002c2d45401100d01d00786040c155241031200366841500c6045501 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 556502320 1250 556501070 556501073
    0x103060203011d0907050d02031006060905031522021c061a010206360d050d0605042a051303110f1c061107020909011a060a05040302060f25 62
    0x500000500c1d007922240710410b28284184c15a6208107108080c440e0864500c0781c801c0d03407010b100c0416005051071042c4005900c800010344022094403415000384141840da40b007102030845854095500917102d0314000c140d270340300d5500f00d01c82c0c0442a84d100c41c5c55021018040703c0310801c000721a12484c40810501c41c1003801c071424801301040c1506540044041100017201844c28658500c008032901001c000d0084075085290f50020351704096214500c83c5220300c2c0d800801030100c502004c881400980d850740305200c1078070102d2100e110328501e1002101c1401d078182010500505103031401c14280141100c0c1501200c4007584191882a02031040e40140d0030302041030440d41d5400d42c0c1e80ca80d5106002144500e940701614080c0410f90344d0103207440104070b9942110091900100f0810700c50900c9010035000b40f0072003440180c4060214009401410403100707842001c241612164103080c80c540a101c0168003150801c03922150410070482c0055288021200a0790080704031000030109 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 556503570 1250 556502320 556502339
    0x130e070f020f070806060d06020c0709050a051b0a0f020f0a150507210c020304030b040b06090f131104060f0f09060504020414130e0f1605180606070f0506010306020301 74
    0x840d0740c2d080990403403903040c0003200740010030941012058a00030450141801c2c154024020340c0c1c246221030046200000360144d1a4121a01942400d80100b100d6112444503c0e09801c1d02d04010b8180b205c10b2042070001400341040b5141d4150381e0050b41c06420109020301d080121035030044800081c10000c207603a0304042e00c9100e0307001143e030810000d071001648074640b0310311112040c0205241c8810402d00701ca842801550010f691010418501d4207043c50507038000142101d40e94000c0341c200c00000c0d2202d03603000b640c0b40280014074411080e4000c03611610081c82c903940e4082e80054030303401c0019140c400104100d001b480007510074031000d0b04180d080c0c401e03510980d00c0b13240700d01e0061005001002c001d5200840c651421038034444900c2419800c03002030b0080380d1a40404d40603004134105903041c0420318039850210742d48d4034584143c5840410220f0f21440c01d144600070346100c0082c7e4503042000080500c01e01510907071311400740d10750b50140360000c2600100c4100341c0100040141d034a0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 556504820 1250 556503570 556503583
    0xa0504020109172505030c1210140405010c210c02010b151e09031207050c0a0312020c1801210f061d0c0f04110c0a110f1002070506130e070f02 63
    0x44c04d5100c02503d626100001c0c1c0d48041103d0390a100d105800b91461076120200a0403458050200062103581c1103c00c3c0c014110004581c2941d265007803011107241507201e00005034407400c0703404200c0a2000301d40c236000d00410b02c600c003500a40d0340c0c821700702c059942e4404000e441c0382d00d443c0103944c6c1c1d100380101c24988600c00b49002d01c420303034040c00b42c245d4030766001c94601d41d084120013401c1e41340c4095050a0f0718000b81c88006541140c2141c00100620510500d5840b501406808480c100000321041c009080090b40100c0c400910505c01030102d42c04a86803c000020844007045e0000e40c01d80f03504502a01d15001140c035207540e100000c41c901502144e4031024507400e40134010f99810340020a26000d84171480d82d125030790741c060109071046072109966444000c0401c0700d034851580e203869508210342039295842040b03446e1743c0050518020344100f05110003980602401480e0109125403a002a040300c819486103890205120707008841c95442040d199030b8001e14274a40c0c41000c0d04202c07 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 556506070 1250 556504820 556504873
    0xf0a0f02070e190f0903031a06040317090f030607030e12160b0a0e010e0a060b0a0b0d09060f050702210c0c0d0c090e030406120c080a050402010917 65
    0x42010104001c0d8000b4107051aa01441c039030380312003260140c0d80341c0760700034a4807413845012189410020020f0681c960f100c8081002070f5468810407144050800c8514011880018900c0c0564030655000ca600c60307004e4800410050484900ca4607860f0000c0d04010048800703d0002c1d50b52083c441c0c0394102004030400340d0041660031854040700c61031150329440d000c000500004850408509050019846424a110b41000070044187d90702d40458540804201c1500d81505082c000f0486151048000086512440c101c0c1c0c0b6000c4290898006440b2000044c1c030b004d5500c071600308040190380a483d00c1400309902411145201e01c00500c0078001605450f00c0c1440c3c140407540c0740c0d0f240000c0c2448038600440b0000c04406441ca401e800b81015600b00314003280c10160406400032002005e001564010745410202c0305401c1c0501e0111a20703000d0100009100d00003040d5103420503402160014018501700f601e9549500500c0300303010304111442d0183c0c0c0804000e50803040701004081006 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 556507320 1250 556506070 556506073
    0x6030227070c0809121f0c02011104060905100311030c030430030b0f030115050112020c06150d020a08030307110304050d0803091507020303010504060914010b0d09080f0a0f02 77
    0x22500780d29000284d000700d0480c9401030240c030410010011080002c204c2c60a500e16100855100c18032400c409040744011410141d07080880c04a00c109c054026502594016503e1721310f840c1c82c040420a0001c0e8035541541495a1120640c0004d1003650080d489a81030704192a6070b403c5c18a001c10300b6951050001c841c80f12141c040100f255001d05205000301e40c00c0c0b41c00320b0b034842c40d5400104007074a0050a1a815841c200f140310085a0007840e1400310351090702c13403903c0e104080340e8020591041445407082a001400011950b82d8402401240154064010801c07801903501054a80e4030b80d4000c3c12441c2d20210400c5843d560000500c0780e80e618281c0551b04061500001c01c090007502d890062280001100040c104501045201c04c04800032407152458181140041d490303070f10a004541c090742c2040c00c041703001e45003400740c40703000310700160308011036883d000000415402540740345da01640c4407040403001c030301598060300c04040d51b008482d42d14801540d01520981e410120401503 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 556508570 1250 556507320 556507337
    0x50c0409062903251214160503040c0b0a030b0612011404060806040f0218071d0a0e0601031512050309090109051308130f080f100e0a0f060603022707 66
    0x4a000c02e140440601c0d80300142c2500c0701305015400e54142c04899108890382d4070346401c0411031542c541c400d0b0b00801903400520300b01c0302401012100c0d48800c84020b07000c402c00d01030400400401d48020500901d25140000d840e180c408006252940051205803030142c5000060010150343c2c2c0040103021000c030b50802241c2c0c90190200d4407007500a1010345205c803c132800000759160860040d10304c60154081580038a00140d0203000f0504901400d90110000741c0011001d00341407e11001b52406064412150398643c00110041c0852036401074481d001e914001643e10401c217500a800d5100340c01440d01c400400d000c0c4036011405902c014500c85c2800d05002050388034200c00c184868015120030750350b101440c0e805120450582c4008221210008001000c041c042500c40c411006034003503d20200408640c1c00c00e64030107400343c80e1140c000140d03c0001030034078204059014881d46004c10b505030b1b00d400040081e007030650461125047c8258101c010503401010a6111440e030818485 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 556509820 1250 556508570 556508581
    0x6010b0c0a080c01090804080703051b131802040c02010e19020d030503070504051009080d020703120f1e02010516020607092102031f0b0405040203060703050c0409062903 75
    0x1d44051010000d42200d100242c0e000151000b03400c901007140e040280e040d40c4a0351080141e1750b90b1401d100039296402404070070906240c0c0050007060001c80100185841c00d00580c005008140e1481c01c6040d1301c002008050040e00c0d01c0c000c01045550a800028138084100e98071030a102d84085013180309030744841d034140184c0d200c4c090000350741c1d0945080c42d103035501c0d0703a001c2c0c603581700ba80c1049038004034441c2c10b20a11a0300c5042072003a200d640301510002000b042040e03a4603500e07800300800c402c003450f0001100601c280960000f441c00352400e2640306440c2c503d1000c440ca01c032100c0e0f0006075111300400c074040c42c4105005402c40040d20040800b0701d0304000c001c1c6580020301a202c010b00300306581e0058108210b2450780b00980060543c5c508404806007054441c4d0400004016241401a8001f85181c00d2007190310450f006000752840c0e43c0c0d000c0040740200401803110006a009010100d501e003c24400d00004d80755480082000e10b41c070f005401d41c0c2020342008100810410000c004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 556511070 1250 556509820 556509823
    0x603010b3c0d06050606040b041202010906050316050309010b0405040c082a0d0f05060a060611030a05070b04062003040312020f1602030304090f02030a0b09040305162108070206010b0c 81
    0x40c03589800c0140016243c6488000621b28840c580c003405940c000440c0200c2c131300904580036840d0038801d0700c2c5c1c00101580c41c6001e03110360000311144d808800784000410310440c001d00003594025080000081c840c0003d000003411203409440035190f400a0140c284029036003000342710b41140400a0384120700740050f000000e103141800e80d05000f04007403141c01c4108050504c000d84040d5000064030180d2801c00900d00090081d84140d1000540c403030807000f100c02000c03084504008059980c1440c1442c05d031901500014080d2003210040c0c2ea4900003d0034246c10500c490405c1d1018042c2c0360740e403d190034010030a801000700d80e90b090340704101e026110100c01c011103100d814111152600103a103800002d0a40c051680460121401d01400304800a000d40c000c604c5038151003410000041010240420b2010131540140440d00c2080400d2241049102c1089514800d03184e0140030140c443d04a10b0f08044607a6120201e004c0d4814001c0c110307014030500707000d030010364030751800d10003074040f0b16 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 556512320 1250 556511070 556511089
    0x5041b0c0305121906061103160f020301021c150e060d02031e100f050c04030b18010207120206090105040206040605070c1a0909090c01080c030603010b3c 68
    0x40040c040da020320310342014061070a88082080001d401055490702198441d000f114041c15244e240307143c900007050443c01f90f035802c941031908400030750509603032450007030113019007040c203a07200c0052440300d8006076001d000510f11000f002e0b03411802c11300f03404000c100340c070b030003243d0320320041c03414282404158501219258880e204881d00c120100c03039400031a0a20303255500d009205c0e0700c0188401080600014001040d0300c3c0d96a00700301c0e5080c2c2507100011034000b40d0350345030100400c010400115141101c400c0c0c206031180191105d107001e401c015400ca9114840031200c0c8603081244044098050000b143c5c0402808024029443e05a00003211842140118030500a000c503146050010750000b410180080040d1b24a10130309280d0701c201c0740c0d0403140400b03205191560000380c82e00404541d00c0354600040e1035400d00c0d03403601c03041000260001480c0320340665940c0348061566860300c043c8080c1c81c24040c080c0917040740740c480740c0c0550a091002130003801340f400c8001d40c440c1c9604010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 556513570 1250 556512320 556512371
    0x9020607061119350c09130203010f030b0f100303180e010b0904060f1202060d0f0f05060a090e0c0f1207061119020d020d02040b1e04060504 62
    0x95103204519540c1c0d0b0b40c0c06680c880000410f1452010f10500c1d030059000c80c0581c0c40800c8a5510070b100800b0010900821503488000b01c41c1078001c502e0050300c05000d0210564010900c0781f1035100712015400701c0c0c009030b00101100f00c94000c20410300500d9402c440d0492180504070045182000c02d5807041d00d024800102000182d110b04c1e2403405919040320050010308864842d556075030500c221450f0084860320384074510f01500028441d42219180f411a280410a00740c90b444503020041380c0d0f0807070b240b0b01c2035050310340f20103484c189013604c20404940c1a0b1200041c45040c84001d000c070071104da8210030044e03440c04410248041c0c000488414041d021680c07429801251030200b90000c00040e140b04080c803a80002141043d0051307865810705180758107c1e8045a840d42002500160406001e50452010302c04040541410305950100600181000c2000060000800c23102030030300c000e42418001c2000c26441e1803400b802101c0062074222403d224056024041c4012840341141 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 556514820 1250 556513570 556513583
    0x9010b25060b061b0105090d020a15020d0c0c030e010810030611040b03040506090c09061f03141008060603010c2001060909081209060403080c09030a060603050a120309020607 77
    0x300442005442c0d004000c0070500a021551111090680c11103071840d0207000c505603508110004100307120000b103440300010380d54000c22000c030032138803110003242080e1040e0032219002c00c001c80b04210a405400d1600215030342c1e0a100d054581002044120300d2510a41048a0b2000b07001d0105203280c0c480b000d90f0b41040f40003407141d141c5020821184100e60085401180c08000c110902c080814140c2c0300d000803000740c9251580300301c200302c2c8a820455000d130b031115070700405c180c072201402e82070100c289041c180060307400f680b40007100c040e1300c080b1503800403241c2c080303070a2210f4903061100580003182034000744134005c0d00708000361101c60f0501d03007401044040038500344408025007024009081c003282c20454001d807810422901e0b031100c0d00c20703014010740901080701c14000141d801e22850b055600e94440d81c0715042a400158050b061861b40745c4a074440300400b0500d58071403100110720440c01814100c40d0380c54414100000d8a13001d9003810720b0480018050f80710034003280d80b000d50148 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 556516070 1250 556514820 556514887
    0x30804140f04090c0302130c09180e06040803061203030609040f08070c031a07050c0a06020d1e0204080c031216020120150108030f0409090f0b07030b09010b 69
    0x40200e9040c01e6102a0700781d115092400140a0103401803041c030607a0300035034041042d04017504a01090f01c0304055408009455540300b0882e01150b4030508a90540d040c102041e0a9407444606181030350580341618034110000500c100fa16001150f040000c40000155085150010003d006180000d1016124001c00400c003420404c100d800c462146a00501147c015034490070300d00c603440805421045800c0080010401d01400740302641c00c050b6109000713054404050361480042d420002e00107540315114604d5542183e9403120b00c3d03103a020b0790742c001602c3e28905441c443ca01301094500c507010ba001100d4181d0201c000380100e402c0303940304a01d0701d41011a036200480320001405a0418005020032890f80103140118848003108143c0d981e5420303507621052030540b03d2140395800c40407140200000c10501407540c215000981c001c0005a040c80c0454540c0c500d0064112500400a03075254006052071809113501c81c054403898403c4d0342460b60a031900d00c5c0713080e5060400c1d0404001036 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 556517320 1250 556516070 556516109
    0x90901060311060a0c05062a040305060a11210a0b241c090f0507050108060609090405030d050403050d050c0307120b0a030c08150a0207021008130203010606111501030804 75
    0x10760540d02c40303503441000c560080c17070304002ca04804041003180c00300c234003d0240414043c1da9540c00f52015250050042d000c941c0f140d500310001006d80380c52850300c01000b4048610b80c805554480c0c144040605102050703031a100c01500704503030001042e07078070914030109005071a500c04004140035140010782540d40b486804144003413600300d403680499031814810440d003049404807144a802d8030800172284035a88440041d03600d445c0c115141500701e20706201da1003191408040722504940a9000d0301c0c90200e00e401550142c034012102540803410014060044400f06d110b11a40002034460302c0d07065080010005006550314442c2894071520b40450034010303910044440c0055600c1024656526501d41140b600c4902801100ba43c050350000090b000c010a40202e460044d4002c00ca0806140754210036036081402402e21010f6201469880c00162401d21402011740a0b41d1160403504080100c0c03a403a10714131600d80c9881910b42001040064065400c0d60152042d08040300400b02d0350 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 556518570 1250 556517320 556517327
    0x806070c050f0d090914160315080d0e0a0b18270109060f08010612030513170109020a060521070e060d05010504060f03080f09010516050c090901060311060a 69
    0x18414020b0240302c104110603500000150100c8038022010f00c414800c40308601c0070200d049a98010ba1003450300d5000300d1794801d40c00b0740c1801c0c00200324036012a45410303025140c40240b0307400c0404330b0f43c01e022a41e601d00e007655411004140b0000d500d4a070550a82107400c42074140b04e42c0d24041e80d407a4038a05081101c00c4011005503d02c030680003103a41e0340e1016034024010707522400703100200319800410b8410041c0101c00543e8051190300c2404000d940e012240c960210ba51281d00c230b010281c003c2030f0444640100c08400b070402e00046080c507441c0c010040d0411565010100b40038081003c14003140150f403070b02115100a500d07036142659440e0701580c0706080c4590040c1d1105001907010140841030380720605843c000d4408000a903211607807240c85444e0780c080500100f005200301c1901c0300c2654018111000103161842c100303010b88500c18486070300020100c41c1504480d01481c0b1905003c2c150700d0340543c1200081c80060f113941c94400d000d0800040b054003035880007507901c207490700 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 556519820 1250 556518570 556518583
    0x304030f050d1b0f030506031b0d14030301030302030c12040323010221090f0a020102030d1a120309010314060f0d0206090a12110301140a0f0902060a091406040806070c05 75
    0x3e41511103181031000080180740e00c8200701e10401091801000c0340603410005410003000092817007400d100c4404800304607190022090844072800200c42c600301c1400b040c000303940210b02c00e400458a880c1e002100604081000b080c030240a94203200c1040443e00c410106200001000a0044900c009240d00c41c007901c41c0a100c8801d03070341c0b102c0307801080004c1d01c01024450442d100030b40340100401e40302c003600e6541c080d20290060780184846020000c20394002404403d030950016003185605001c00c8030068102c400003505c0c2c0020a140b052560940100c3d91094005000ca0381c0524110b40004d00e8841188540d50184c000380c0c2c0c0000440d100c5904907140390318010411305043d0742c0e504040d091661000f408a82840340f1207202c2c0c0c6030341814010f1082441e0850304209981e030b5000c0040b0010981c5a9144507450b442d24071041c05a141c0340014826880303940e480b2495641020700c0ea0040b01203003250349001c1d4404100810005401250442d080348440c80c0c5070f081010941021880d014 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 556521070 1250 556519820 556519841
    0x130e01061505070204060f0e0c031509071d0123130b0304050c0a06020307051b1f0906021e060103030503060604032f090702120a050403151d030304030f050d 69
    0x1c0407036540d201058000000e0b1080510890703040c00f5080d00e0746514800c409a900c1404250580032022940a684400180d41d01682c0d11414441030141d20b0005480b800c2c0598084000c10b1003c21801c2c030500020800495232402070070010f1003481e640042c07000c98541800254440e075000b0448d0240300c041e5a84d000020702d207075016607407281404e040554503551180c168921609440030000381071400031040c0c841d20b0380c00c10f0242c044d248001c00da000070304a003c9102907101452405480c015041900039020503070140e80c604809030305100c0003a02c1e240b4500e204603100020b41c140403e4204c0d001400c0d030305584e4503192460f2203031038080c00700313065000705d41001700180705107501822141d850581c03200322900c0300c140c020020550101441002c150330b595000042e0008121079100c030700780000401e680603441c1381c10ba141a540740c8a06080c80007008289600e144c550211b4400c00508100a030b0800400e400554070b141815500a024556185001424001e021131a078a000748591f10412014 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 556522320 1250 556521070 556521089
    0xc35040b150303280815040207080f0d06060305011d1819060902090a11090d0201020c0612060f0429040b060403060902210a0602070f021c140309130e0106 68
    0x21002c1d4610076180103090640d125800441d0380c5151156441007445d1402544003940c60f0178480407440c1130001030340c0b20603010703110070804003c6401c808001a000f45880d44003410001030741410070740018156003041c0c0c081140711403001c94141461440c076251541040001c000c110382e19150280103410f02421900b9900402c029045400c18000c1c2d60f0410851a44202e45411980d61003081e520120f401074030740d1003161203080c001c09101e402c002040005407070050044503c0401210009403b40c0d100c0210f5441541d00741c01403000e0b0b4100036489400b0700200700c42c103014060465440c160070401c86403040551803465000c980381038465900c050f40391070002e0101c0742d40300e459081100107844042c0080b4003600039200615010300140190342c443d80e1400c3c000c0c101074240b03525440c1c0607420031343c4180d070344500c8141c0c5a8011394552620300601455010207400e056030b00c1c1070000c203029041d5044d6000c0c1e0410010003446958550548048070401100000c58600d9085c160340180042d03000070605 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 556523570 1250 556522320 556522327
    0x6040f0342241e08240402010e1c20030316080408070e070e2e0e0915090a020405090f040501020c070f1401021f0902130c35040b150303 60
    0x200c0c80c80c03d5142c442c411228140d0701c00c03181d0702c80440c3c0d41c82120a00000400611404110303140400829460700180145854601007004200040402000005482c000c030401840c00041083c108000d07140f0070020b00ca0030044544120100e40c5a1050a03800442e45080d5581041008910416a0050f1400e90300f16004161100440400f103407041d6500004180d0904003d0f017a0702e0015504815140c000e122001c007034060404e4a42c0c0715014038410014400038a02c03030192600e402c2c905a01c50464039042c2401c50a1141c140b10034140090008a0b2843c0100420310013910360400481d00401d1500c1d200c442070b900c90804500a00a0407a807a1041c01240000030300b00d03c19607952000d46014420070120308001400580e503641c41100c200380c01c680360104540c0000320540c030080c00540080c25005505a40c81050310407a01071762112004503101014428040075500903005074000c00e45920820801c0350142c083c05603100900007811f040800d00028000700440d51821305040e400380840341c4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 556524820 1250 556523570 556523579
    0x702130c090608150a0e0c0c03070f1101050c030708030421030507020c031609090203031c1e020a05030f1915030b0a0b0a06050906040f034224 63
    0x9061002d10400300000c00c80000b1400000707102000014080004001e0390040340380203a000b0102100a002c020440300501141c4040761083c80104140e51207143d007004d011180c0d00d05190360f05040d107155410460207000c5020782e101c00208980c2899000031096440e99078924000016901344020761030300d41204e4800107006030b003603004940140403503000d0b649414048818542d4650340440003044d200d030000000c00841d00d40394000c0d0165070010341543e2401801d0681180a090349030ba0016602d075444c00800440314a01a03000d03c00b0300850300079450852810701c0204076000241a8403c00320711700010803295041c1c110320111188006005006c48145800010b07540d151030710040d181e44100c0b4002443c0e0011234810289805401060a01028240f40c01100e03240c01c20251a500464100004030700518000d050000840c4200c1b0086021407105030010242c1c1c102d2000e00d031500b012581c074101c084030695000b582c0070003a824005a1045a000c1508030389011f1610a1803c14240e038000c00d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 556526070 1250 556524820 556524827
    0x4032a0b0a030b01030b0d02010804080f0f0316090b030708070905100306051f0c2a090b10030b0105030a091509060e06010807050a090e030d0c02030901030c0503010e06060702130c 79
    0x84101e40a40b401c02c48050840d0054090311488444c550380605045449401507000c5c00809400c64010300c041418400a000b8000321030707012103020743c0004c90100c00c1100700710b125401d241e0320100525203400e40f00c0c0342c05c144403400c0c00003034040818130150100040b81c4901c10000342000b408014640d2501014108003d00180310501542c3d0040d03d01100c00d1000040b5803100300544c107900c2c2c2d64072303000340800c0e200e418009032800e00d03040f208100824a895180035106010000e45050100003801e00d150a041150072416015020180740c00c00c002c07428180e0b0841c4c03d0740c1d84400c500d600410640302c14640300a00810000071b0a150030b1030107403c0320030301c02940d10104038035032444110341159882d001c1007a6506010310415502203001801845809415007002e006148041c0071070f410460807080300ea043d5030220a180005034008950461590383c10b006400c800203240c10503074659418440b1441b510080144070300c0c02410001a0301c001c6441d030354045d0401d026003a6081040e1840980c004 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 556527320 1250 556526070 556526077
    0x17091609020904060603060b09090408130602010b09130b18011107050a023c0d060c020a150c092c040b060906060405010f0f14070507030c0b0c0304032a0b 68
    0x210f00684c64040c01051450007031048070241d400c8160440d0800b02800104240c030321000300202c03400c1005100f45440305500201007000341c41541c002041002e41e0805010f80d0704c800030080c5850040c5110701c3d001107004410309a801242403402d40d0b140701ea032102003030b01505d11031a5952503420000303807a03014401d0210312191898070031100d02c4110f00d010b4200b134246500c02070380d0100c0241c640b40f40004046d08000403c0048101130712640200d2559240c4908035207040d4500000350300031082c0d80040188403500407141a11203182003102031010400108100c2e200e0068001405004a180d00182402c0703c0c0002e02200003020345c4458030f402d1512400e8034400b0380d81103000e1091040414001d16080080c2c4042d03c0c4107a41d01491303490844000c49070501080c03a02c40601005500c407001c1145603000410245005800074a0b4607491440d24003800515944003400010f4240480c00d40003102000b12030480343c00460300100d284040703114178109078070902080d812540810000841c102500080c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 556528570 1250 556527320 556527337
    0x180303110c030708120c09010912170c0d1103162a060903030f02031e131802071109090a020d05031c0c0206060d030e041e020c01020c0f0d1709160902 66
    0x5074542c5c1d4440d00d4100096000304100c1030b022404030714041c010b0300000c00300980c4040c007880242d00882a225030220442d400a18480303107a8000000c0312911541140b40c18801004407801903280459000a0b0030035200741c400020003a46420401003d05600c40001c898000d040c00100e6803040c0d03a43c00043d280d076030310303200440100f00409641d0002c0d6001000703480c10640007134000c0d04082c0c1b003403000701c11035840012140288d110190000c03440e90f600034282241941d420740c0050350b43c42e5a041c06404884807405440c403984ca0302c0c0810640381c501040d03c01c04568151000807010195242441c150b010701c5801c1000c00900000700f84c030301c1e0b80035042240030515035000c1e100c1c9034580381c040c044014890742015002c02c00f51002c001490400ea4001111869540307c001f5980a181c9001e2040e40d0005120b002c40d41c1d000301c0e01078a072180c24880d68038a500e113840101a902c2445c40d014117886440e2520383c892620040c002a03210b2000e0140300300080c501300d0b0b80c0c1e8405e500d40451900a4000300107 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 556529820 1250 556528570 556528597
    0x10501030b0c12070c1410240b090f0109080105100512010212041b0905010306060905010509220309050904050f07050102011802060309010b090f01060210180303110c030708 76
    0x2064195002c8403c07141d000c5100c569005065071400015503100d03911005c02c880c183d4114004c5540603109110171000c0da209200c010600c160328403092183c005240054244507292014104841d02c20702d02200c0f9100010740320748080c40c054100603038078001d1a5204543d5942401e0070401c21180085080080d00c06c1100c0301c07580352114030780f03c601301c1c0038010710048440f80c100040b40100b00c4420100071880106500844901c0c0c070788048500b903a900303034400c40304070382c6404050080001074015280541020395402440d4905079002031a201990701800c80f044004210240038544189106405072a01511009081c10545041d42d030340c12500d0a0341099000d005400b01c0d0a44c41070248030301318410300911004510740394003049159032001d0b101880d207642e80c0b042c0010307039103030354806600c5072201d03201c42407041d894401c01a0815102e4101d4003400c1c3d160900042c1c030840740d8585800c0303440d014680060011131420380b0f603806202d007807424403a5120201d2811300b0050300030018020310b0f00545 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 556531070 1250 556529820 556529843
    0xa0207290a050403170a2c12070201020706030207110901080312010f0b0a120e0d1e0e1516080f0a020f03070203071a1315030c090b090d020103021b01050103 69
    0x881d840112103080c0c80040002c1d10b14074100080c07000541e00680c201042800008035901080b08121640e0b68507030100083c00550546001112014800083e10000941c4c0c01440e012850b40000d4554100340620010305a010422509101040810b14000440900584460750f1211f0b109a640e41182d0f682d06852004107001184101080420100b00d03809041c92504000b40d846083e00e10900321804054810303515000340351030603010040f0003008045520b59400d82520a01d10544401d80c010201d000d00c00d1140301400c0c01d8440c4000039000031030030340e140c60704d50403548141070910b1124407000d4030880f00441d00c9064a4404001440c0015090302120341c851410940c03141c03680220b40010b541508440001c0001e080c03c4c00c1050800b02078081480c1c5402e444d0816010b0154890b045240780c1c2004880d01c1500702d4161007011000017036410103402243c0362248100280c410381d041503000b412071850600c2164081d4046e038005144050005805580800c1054000c2109103c01d5854180c3ca1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 556532320 1250 556531070 556531081
    0x20a08070b01230f0105090609030111040f0807050d06020a020c0d030305060a080601030b070c0507080f010903080601030213030204020a09090e0604170307050706050c09060c0c01030f06050603010e0a020729 91
    0x943c403920321000090204a0260818001518039030003810000c0d030070140811100c41e1582c2c1c20b11680c900e00f1000c000070780e2a2824000020407241c181c1d02b202c241648066814407080e03403000e059201c40b03540040302591b5580d081004904041e40c420300a504a00f0920101c4c0c205509500030707a00c901c1c01a62509602640c074102142d8410b401e1201400c0000700801107903070984166540e108003030045003203c215039500d6010500c6e081400865804e2a551403504008242e1310020307543c0c000600b480d040d400e1030500c40750503500000b0307031200911581d0300081d48442d0794010101800208102e42040081150304804c0399140c1500b05c40846440c402240c8403104600c181040d00e019405940d0b4550408400c1d0b540d1500510f4060701500c4000c1e001d1080782e0240d51668020501d040210014104440d810700024040d1032a08480d40020703814844207120a40391740c4140c904548035280100324546640000c0d40c000e204131203000c1c03c40000e103640c04028954a05801000300c4200c0da04500a0381c90 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 556533570 1250 556532320 556532369
    0x5040b0301060b09120705031c033c0615020304170703080d05060d060216060c1b031b021c0c1e2607060f08060907170403020a08070b01 60
    0x1d40298541a14180700e411303e02d0801e080d00c0c03543d00800c0401c0340c0720581c58600103413428036602072071000c10702c80c1d040341203000e64103000b41c41620300d1100903400110003c0c1410401c0703001554082428000303000e000010440700740c11120052039040e082c1c03030792003140c1e5200070b46035803250003000c0080d4503d10a00245050020380740d022650030810890800350983d0340d01010b4000908901e6118203000740c80004155039100030880350800352600801c0680c40c1ca015000d9941841d441014080c104902e0301308000700e00e11440c0c245a1502c0c003442d80e0680c11081e1841030382c1501d0041c1d00000000b0019040f40c074bd0400c0c4400090198010454107980c0710221600410b403c192054644c02c412000c010b54141c0805250114011074000906214414a4603213412080d174404000541c0d020600b84d07641e070300440401c0e01700c003060761264014582080050111035407040b012403070091050000c4c007454424018401c2c2c0300e074040c2c01255100c00c20b083c4201c00001c2801a01101c070461440c03160003455 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 556534820 1250 556533570 556533581
    0xd0609061203200601271815110d18080a0206010f090203010515070f0f080d0608010e0a020f150c010506041b17060f040906064b08031305040b0301 65
    0x200c034001800713240e080001c40ca141c910f104188a014481c2403407081213071811401081c0a984028404240045190a007010700c2c840e02c0b0400700f421803800401c1c4061504490840d0904010018040b8112050764400b502c01100362034054000040400c0c1c01c0300c00380e17002c00ca4504a132103d204a0311141d40781c0340028100d01c828401d8030b030300c000c1030240710142d001e10f040a4035003640130b507020901480103500c0c0e10300e041a048108680f03841c800510000650120b101d94005041840020404488181096551030514610280c4201c1c2403100e01340641c0e4414044206200c40e1010742c0741c40303000e101b0070f0380d010303100c1610181e1103103060404001065504d00d04614803624980e81d444081c07080d6124480240c580a0400b9820903210000c450144c0c1340c5000703071120903120313803c0000c54a2800b1100104d1441501e007200c00310440450407505041551104100c80c02079800f0300a080c0c421004228824046510001c1c1d00c0c0000304030040c41e06021a010008c07100c0c10741d8140007502a59080508991 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 556536070 1250 556534820 556534877
    0xb0102061b031308091309020a08031c02091c0302010204140906240f0c06010f0e010302150a020a020a0806180106080d0804050a0c0315150b0a050d0609061203 70
    0x30303030030b100044450303200340101c076482d5008402c02e038608503000000c00c1c407444810a540c54616114040e0000b1410308000030f42c01002080050350400310600030010206020458401c00300390040360141ea1540c4007034154407131240d44801148040380a18019010350458803414840384009200440319040c41c1a0591044000070614141402d200aa03a540b41013002c032140d038080400d114410204c800c0200030000f02e21150010440c035132406480014210340b0390410450600c00200410041e11450200b040030711070545540e48814509000300e140807250100654819a00c15001a02c080c3c0410118080c0b040c0c00f40c0c1c24000608249140d00340c0c0c0c800c0c443c1b11080c1d40010003031006c0b18452805290464404c40a44854900300c0c0c55840b41440c0a8000340e481d021203508801000303040e48940203605001075445008580303062810000d5000b0012020188600050300d111715111650100b0054118560108241030710341c007002c109800e1000040700411000c03d140000101c21003080c800c0030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 556537320 1250 556536070 556536121
    0x10609080c0301020a140703020c2d0a0503031b010f020f0414010e0a290a03020310120816080c0d09090e06040f02100513060e01030c030506010210022b0b010206 71
    0x10503552521000c00c3d881207d084e03003140540007910345159945044c10400c01e0702030008130420b0510790032003a400c807c1c1d903088620411029004004544000c805e0301c3e120a54410a142c00c2004003560b10701600b04071801c191200d00c00200c60520800b100080c10030f0350800b800d03a02e00b0030121001035822400c15000513900508103d800c104c1110403c00c228488140841860002e12082e00c1008640d00303c2d818503000b05c0d401004110000d240300406000800f050040289551f43c99112507000d4030a02c4d000e0520144a1604103050240480864505800030422110420209000184a0307401401860a40e9007803010007501054009101c40c0999040048507944c454158200051781c0c40e1303000400c0c00d00c00c09000100d0400701880c4407078014001c1c5c0d191800d0029102000504460154032000f061600d081c00344a00c50340e00080070200c00e000c0a800696800d0401400c2a013a4003515610029800e000c00e4140f43c40703040c4d004008607420a80840d40c81e625601844002c40052190481d8074 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 556538570 1250 556537320 556537337
    0x801030215070b0405070e070519080a020f070302010c092c060f03150f06090c0a11030904020705010209180f04030f09030609081c0b0607061104050603010609080c0301020a 76
    0x985454000314955074240d01c180c034034020040d07590360f03841441240d059a25801504040154098821344560701c80c040c0d1030610b15000122007140c86e5001d4007107105003001a40f00006440c140709070b040720540c41c0e00b4070304242c03035107060310f00207000c2d0022080c00700c0040c0c0d11000c00201c00701c1e582410451002d07400045010100320302146038650100505070780d48652244450b0b402c6480c184447c8011a52401c1040d0345464095000e00a0360000780185008030105010080b0016036102912882c111916010610566150010f0300d10f000311144194014800101c103800c0142c154010303d040141a10803107141518a41c012022100031160240007107480800600040d11038042022290303594200703003203416265200e643c02ca07010078504035a6400c000404072000e14400c46008400d000500c8284101020304000c00c10b64003d030280109410340350703c028082100c0c8003040d01c021305400f5081580b25a500c10340209549038601c120000c40c0902c0d41d50484900713041c0210b400302c000c3c64440101 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 556539820 1250 556538570 556538573
    0x15050601020a03030b1503130302010b1005043c1a0405030703030c080f04030b0103210e0f061c0519050705040b0c010e0f06090c01090305060106180f0312031103040201080103 77
    0x40d0603170700010303a4000b0010300b805903440c20f0a0050750107008510f2006001c0d0805150103805c40d07408140851007036210030b0303034050003c6d84041140c1c03e80e004c01400c2810180802e40c28030f100c00c05500c041181e020440000f8404420f41c9085200b2030b0130180400d07103d00d518000c81c10141c4a00c0c0a00b94240d0444d480500c0400c0c003581c0b03001142c901c0780403010700e406805404819107030095001160307103440c0240100184032440b4042190740b140c0b0035a014110350f564002802c11b201070200d541c0201d94100c00340e00309544042c203031043c9002110f0880c12445000c0703170003401848108c1d00800b40882641c18031a800b96188170b25841450390f911032a103840c1c14800c0d42c5050350005281c043c2299201c90ba07041050805000c4080240b0080f00240380354245451b8650405010800c51810081020700400224200180060440d065403c100c1e800078010704481d01c8500c9941c01c5499501c08a00001080105e80c040c1c10560701041d58080002103008540160144419200680000c40441c010f00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 556541070 1250 556539820 556539827
    0xb0409020310090c0804060c1106061c08031e07090e060f150c0625050301050607050a021f081e04020f01030e0a08090909060c1821030715050601020a03 67
    0x10b400c00035100200e840a5603648150b410b4a015814401c0058001001d00040100900525450b0402d5091080c110284000e40c1e03555164000c0045200300300310400f42007007880030b0070414a19608030b00040e581e03190211000e5084032440400c40802919440002c10440c82100c0403801c0d12151104140140c5816003004061138011060321340c84158241841c00b100501c500900960740d010018015615202c2035807014003031010300d014090010f4901001d10198001c0c21641581c1084507115120507250400c1e61601c650440700a401c00440e805070004500410100c00080ca03803566400c09558035240340510320a03080c4410041d4070108008a030043c9001141d03c07451043c1894002a050401201c1c0d5150031801e0b4010760b000c0b04005204800790a0543d0346943c03140c1040010600f82c20700d8508e54260717100d640d6001c0c5001d42e2051900219035a0404101a090900180a030440c60022820341d16503001c40003c540200351500702d1a000c03446801410301c02c02e0140c010305144001620241c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 556542320 1250 556541070 556541077
    0x15090603170705030403141c360e1017030c0f0a02150c010f05180f061501080a09020904060b03010c0807120e0106080109030917061510031805010507180b040902 71
    0x395114014030300b08ea00c110034003124a10071742e40749603031702030140901141a024012200c0300000c8504210144048a1006400c11000302c4041001c0ac100e070787c1c2c581400304000d5113150043d8042202c81d4000c2480c058002002d001c501c0c0d10f46003a100c003583d1250615035220040c0c80002e400280c50000c001c10901d0b140040c202d500d40410011a1a40044100c80b089660440b0506928520700a040800c12030801841c4010b401c42c100038000350030403040034181003188840f468100506c0c0800120b11210b1a0450000140d01414044003801c2030300e821400f61171351101960284d8600322549030380328492000140148055240e4030030700c000f08070020000d8060401e0090066480301400500b0403401d125002006001c0e075140340c401410044008039520a1088609099001c0001d00100b8103150080c154080700c11075100000c0c0c0c1c51045c095010303051040500c0040c8134108c50f01003e02c041074000f0781c0310f80c801d5540d0a080d44100100941d07280c146001d02208a003041c08107000140302507008 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 556543570 1250 556542320 556542353
    0x40204020702040b030105181203012108070c0e0106030e011a10021504080c0d0f0519030b0409060605032a04020d140a090302070b040605070b060415090603170705030403 75
    0x2040102a1300c010031700391034040c2c0c1c3d40440f59100c0390742800c04a034240048100707848400300c0b4a04d9945860400740c41d0820840c2c96100901405090720b007040b9900c0c080380ca007150b0020b00d0905140c2c0c1c4940303160310342e0001d100c0e00d000700c2e05111812500e0103061050b40300309616044c9141201103100309200e4080d0280070800305501c00e200c103880c1c10010001201d40701d1849141fa26583d15805a12541000741c5e0303a1801052201c0b82d03013100d2000350800241d603061040011031045817001c1c008201c000d010000d1342c0c00d40103071401c075410050000580022040d42da040d401c0b034030607140c8441c091800a0710716010942d030f00350b41e0f080c400844c980341e0000c0c07030340c3c1001d1130020480c003440c4200d100500c2c805030350f822000360303480410008154050001800401c840e109950401d1729045001c4e00358403d940c0c0092078000c0b92400202650b445034081540e501ea1509080300c80b83c1c891444034001c00c05408181c904180d1800800c0f015503d00d0100c41d0f0030341c1d100000d0340c20245035544540c410f41c2d11182 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 556544820 1250 556543570 556543579
    0xb04050904110a1d0615130e0a020f0a020a050c060a170c130605030708010806070f031e020324030303040c2913030b060a0321090503030705011401060512040204020702 74
    0x9071014000c1a0190078480d00c4d01c4c2800307282050b504109180107040c1141c009150203102d000c1d0502d50b00e04011702150078844948803103a0322580d001e4002e1152404030040b05901240e00107200758001400f100035842001250b240c080014100000d500401c4241e000042e0100c40318140c80103400e1901c0e0300502c55601460030301105002901124200d0303000100024804810410160341c0400b106004080d50740c0038000e18248240c0013400d015851115409043e222031030924404494501c44211051300003045440e414540b2640f0601c0701c41a82c1008000c0c401409031442c0d140100469019a0b4402d011a000d00e1401c80600c42d000c0d0301003280e00004002c0b1501040c1c24030340800a0400140305d05040440d18210320f0440c1a00601074100d500070031043c1c10500c001003d01a044030f8429000c443d40340280f11034101210b003000540c005581502001c2801020400150403510104000048404807030381c0b81c003811586805070207440103003400c512000c03c000d420654020402c0500280 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 556546070 1250 556544820 556544839
    0xe040501270f0f020322050c0d020d0c0f062d230409090b070e13020c0a14010e06070807120f0906021c1b09090b121203100b0405090411 60
    0x75101403c0302e00392041141c01640020801207408580c44403c0751070003c0b08100e00e459005034035110780c1c881031505058001c0e00160f500780b095680344503440201d154001c240c00e8070503484152420b00d10461348201c6003c200041021440350725042d4581c6001d0310301940c01003000c03010907411070701550030450b0140861071044820000c010400020701c003912a0010225441081d071401412044000700302c00d040240314074000b0319503500c00e004004805c8551101607110b60700300103100d0500b0b041000c001c5c40901d6600701c02c04800810740221104502100545503580c1d64480300b550752400803034490000400714000b02d4601c10080d03202e44580d130b101060018810706a641e800c82260f00106200d1141c00395a00f940402c20054010340c94101d001022264a030441020b0280c007075005ea014806409407102101000b5403200c4404035501d50090f0201c80d14455070301040105513009864000707044031548004180700c466001210304035030000c0d0040c0b80070ba07110b0310f8860010300c40a0768507601a5611 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 556547320 1250 556546070 556546091
    0x60312200304031124030a0915060e13060204080a03020a050127030c170705010b280302090402030c0409030903110319060e120d0b181012030201090f03030b010e04050127 75
    0x340285111f40032500d0005140355043c00c044040d64070309980b40c5a2a400c0603014050a001c1c2e4481d50740203442544264582110387c549074000e4081e82c0c000c02c05074421070041000349030340041c83e410b0341809000208520040d0b40c400b03082500d42c0b00751501d0038503180414500068414410000341d217005201e10310726a40003d460702c805a000320310945107691580c00d4000203160001c1c4a00fa40b511114041c4504008400d139032008074803a100281c0b25408942c0001d080d03460a001d2030b0400c2a004100b001044000d10f4040d00c8070401d170009651016071f03020346407118100083d01a030701100c500042540220390355101d0021345401c0c1c8500c035a50042d602521104103540c006072410002d000d4003c20400811424000650012035020194803a480148400e04026100704030688110403086040d80241c0e08040e400b5005c1c40c400100a11a4490040141641355102d01180b400c240c0c0c66200b040182c10801064a10a014814010442c04550364030703800f00031241d84286a80303000100702041e49 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 556548570 1250 556547320 556547389
    0x609072a0c051002010b0102280204092103090209061e0907123207140309060a0b04050411040c0210090605072604150603122003040311 60
    0xc00101c4410000040500a5180c8444030072100210341c4020040f01045400003507644100c501d0081d4907100040d4980d48010410081002c041c0e00030340207200c4103110b4a05900000001c404800e0140080d1005d441d000d0b1107802015072094006020643c40e4440c0010000800b61500394040840500710b02441a512030380c0802e4440d4105885100d00940d414110f0015103425486880d001c0d8002500c04e4440613010580452642800702d42c2500d41c0d441910546404030050102e114403c03021040245a0b0000200300e032003040d1807042800100003c4083c0300c141c40003520000c2004101101e9403146050590204100c1d50b140e10403a924203030405116412a24421401e0354459120010051855008500f2240d601291000340000c5249a101f10710b42c600f01030320084c0709540003d55540000001d801c4140590341046e02c1c03104c000c0c1102e50180546840509821101101c50740300444110040140c030100c0750005616401d01c10303420700704034001c6203820800d01031410400050461415 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 556549820 1250 556548570 556548647
    0x10210902091807080a1e0311070f08010c14071106160308090c060306030a0809030109020a061215120809030a060606020601081618050a09170405040f05060907 70
    0x24414807400010340155905062240e284c0050510b640210340b540005200503040c80c3c800012152110000d007410301e81100c101d840000490041d00c51854080b4540748162051f0b822140300e42d008101002201805031003803590300d01c04940f004000e00c00303100891000c044901c0c2c40f15009220624003a1440300c2e2b12100c0c820340409074001260403041100c0301a08001c40301c82858126111420b44c50300d0b03800070f940d845400c64010030b110ba0104032a0b4464400350020511b940d8001c0c513800056072245c0c1c0c02000755803094034250b40c040c1880c070415103001503042200f041d06d05844100707010320388070303210203070103600c00040b8540500ca041410341c04101d4500c5007901424240c0c0c05841035500d03084140303280c000909100c84800032100b004100c100700728180041c120400300c1700495644c0d5100001d130700904603280003500d00d0410515500407083e441d070003003054a508560400800c0090040441140c00840b1580d8100c040c060201d400340f400395210028000842608a1172080042100e840c1c040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 556551070 1250 556549820 556549831
    0x20703030f110c0105060a050d021c020d241b050726040f060e030607030e0a020901060915030e060f2802090f060903070303110f011103060f1021090209 67
    0x1c0b0115880241c1c1c81c0030300581d5000841206c0060304c0e43d040c0320001d10b00c0300101c0f400034841c840055aa0b4500380b8001382d05400b981d0000c003044c501c1b20040c1009c000d0411081c010303004001c100309811045660798400c04100c8020040049500b2070000d0080e90164443c00b0140c2d100150040d0f07c0b120701c40500c4000108485901d806600c4a28202418015188a4104074144602003a010400d52000241c2079440f010914000c102a810702502c41d0170445a0340c400307900080540e00105910307410444c2c40301122000c0d070109003402419002101280c0d00c00e8080e82558201c0030100d401082064903039500280781150072a404007203401c2c840c001001c04038112182c103801040d5a603103440d00303442d10b10503010305440903840c00c1c0c0001d0020f41c0b10041400f000301440348840d44007200b0b850400c15a07801c0c415010080101c81d04140c40100e03145c02c120307800f61080c0903c0f060300040c1c0c100723080303038685542c12511810846009079110484180d111480c6a150560b10002c400142c0d403014101070140 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 556552320 1250 556551070 556551101
    0x729071103060105180f06060409050f07110a173f0a0506090a1d030a020a1401360812040303150510050711030115061d060904020703030f 61
    0x441108103142c101801680305902c1282c152008104018250003803541c807240c1065410402d550303030000100b083c0620340141c04071510306000c101446a0039030b003e42c0a0081ca484200d4502b000c082c5050751400300c40740060090842103055802c0790b17401c1c009021401e825042c003001750b900601c2c009055403880f403c0b43c202811a03060540c0c002403040005508995501014000f51030007502040503524003400d401780c551342d0703000f141058450241740000080e814005507036884401080095540b20710040c140c620300281c040c003041001c030510070100c25980001050007203490081080c0031410031002c1000300c01d000c1c41114400280000c1c0107092807014110840350700d007001e040c01000c0319128490301d080d400807407006001541e42c1e40740a002c40302403860048c1c2d82d00301514000c0c03500307814583c1c890b81541c206049010014084001c0c203058420b20347d6400e5200542c01204110648003c104542000b0104141a024100382d00186030680c0a8140803800e4501c0480074000c407086d044048030103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 556553570 1250 556552320 556552343
    0x30f0303040f0b070516080c1006082a0a0608100902120906180c0f0a0807060e100e0a0e04050109120201020d110c060105010e030709020a080f060d05072907 69
    0x1040f1141c050160880b4181c070704076007003601c5041110a4150241c801030b100c00300101d506030700d022081001c690820880e40d018081c25070746030f0680c4c1d80e4101001d400f12044107055410101902111550003881c40001e2052100e1498202c0171b85400c40003600407405580d1406000c14007500c00d0005103103d00080203508541e141005543c0d0801601628170600b050003003400c1c84c1b81481c00501511110000c4038460781d94010a40062041c840e00d40c4030600390302804800080c001c1e0844102c0341c58580580d0008444407011908407000f8141c0c1e40301960008600500340000d0142d1030800f540103204400001d01c800c65506c8480c40301005194004c01030b900065070980e01c056600440d2400b1959015070350428031603084003511550140035490400c160b00c1039140540d0740802c5408002d0011a200b155141d4180c01300500c200c02c200c45040340480c485001c1409814840300c0061102e070410302030408242440100004d00f00c04c4034074031440c07060071f030074080e0840b20100080c6a200c3c81010810310 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 556554820 1250 556553570 556553573
    0x50706020c0d0f451502060f0915040206160b040c090213050411040e0403020d0e060c0303070305062110360515070e040b09011a0306030f0303040f 65
    0xf442c1c4a112210b81006a00a000307003900e420b00030760580855101c03003151400b404038940c4004101010003001d00000b508040001e1013507040400c2404542c09500360b9085543d18030605000c8181030b6015801941721540c2002c0c900740c21800650000c0c0b008041c0c510300000115101120205041c0aa80340c01500b002e11040090a51680e0001c3c04842400c4d8109014404407644c5040a8031440e0701503601d8160030b044080d024801c40b000350100034000501c41c1014100290754071425000c80020403000c06400d21240b4102081c3c0d540504083d0042d032965894440c21405000003400c4160041c621003445449018000b01035404039160000030308280454900c888140c80c98007400d41c01042c049000d4050407101485541e803104d03c201e480d001c10034800c1c5405071800c400f070f50040108481e4401841a207d40c086c1000048020848041c04442d1104007081b81024080c410040303400c1908c00d0801003200124040d540c0503d00034160f41d01c0765150403106c0c0c00c0d503000701c2d421911581070b140d0480 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 556556070 1250 556554820 556554827
    0x204031709011d0d060b0d02040504080309010f06030804030807020112060602030c01050c0304021503070c0c06050a180b03130615030503030402030712080d0e0309031f060501030908090907050706020c0d 89
    0x34420f420200d07102d070800c015000460000b856402c0b0113419541c41d680c140480340c843c0c128a004156000c1d0080000327180c035080100c0150810348000303001d542016220038807044030f402440f058940054556184c940365130307214545540520b40807414824078012a0301900100e10035140240803d4004c0c0d55202854003602e421a88020842145203c0610602c40541c4611448640700782886480e143c0d0b903210000151400008031200900b840036404d070224a140c2d001c00504a0241d4a8071808607507100e0311b0007180000d00c1406200c0428000f4000502c0e00340c102041d98270404d000c2d80300040c8512000729890b511f1043c5410540e01c90b0310000c01c0c002142000c2103000010001c1941c0c035082d040071581e501031940700c5c240d045001c240e00c50741c49840d460014012140224001170803034120710350007455030f00398031514035030212003e00d4440000760a5000307000f0202510f80c8004c03400d1030315100364100206a00e000c0c00000800605110f11303400107125200038480140c4a000601c5516202c49008 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 556557320 1250 556556070 556556087
    0xf03070216060e030c090c04060c0311070305150108060708070e010e0607080901090518060405070306090c120f0e0309040c05041509150906050d0b03120f0309100b0d030305060301020403170901 85
    0x200c2c0200c06c094208004101032006035001e4921a03d000307840321103142801c868148251802e110207004840000080003c00210440950081a5000d505a0ba155412034030b0307400c200c501901041c00d032000600b20610a01040001450505021054582e9800810003079003107c0422920003900240c404115a000340d2402c004060494000b4801c00c030503684010781282c050295409180c49801103208a4020f80144001d001c440c08100104258801c0c020100e0b2110f058000e1018503116204030020560301941040c007600390001c510b49440315042c04020424145054204401848041942c400c0089101c0f40030001c3e96032024020308000c2102c0000d001c200186040c001500340410603181c22405460704403d5903080000c50005110200e0b003000c480d0b45881c138100200044240405051034080d5005031640c80803512002c2e5500341220032030b048807689070b5103d2040b40f00c0b813001911239048154042c3c4054005420103581759036110486244000300070980402264940c07155034044400d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 556558570 1250 556557320 556557343
    0x51801110c0105160c0605192306040e0d051e0415020d1b1b0306020309030a030e011808070305130f05042412080c0d030902030d0203030c0f03070216060e03 69
    0x840c22682c4c864001502c90040b200b001841035440b040003440120102000148240440c5c10130301c44400b210108085a04d800040d1107144000078002c980769007050b1040600c0e01030f4010041907256040c420035105a0000e00c812b600c028001c140400422408502038070080c000561400f1281ea4010b00103401d00001c00c001c0410042078072910340d614981c190b00c1c100940e4010350307008044043c80762101d92014064101400441c00042807058034500000203000d001000c0d42c08001c0c01401f100038a082e1034030760070301050100f0b0b5103e842001c22504002418440d1090511510f08070100030b9031858a440d90303002c06503015102100700311505042c0140080d1800002c007921031b0501c04140c1c860401481d010394180f81c500c1e80b0310b11040000000c200c604880f60380d011942c2c2c10f032030001d00030050070381007508078064010803070079860071400001500d01860850711014204098095096038513040288160218415291090214003032804440d004e000503036611003003260b0b080c0500d498000010030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 556559820 1250 556558570 556558591
    0xb150f21120a050f090112090516050904020a05150d0603050709050c031006050a030b060d0204080106120503091c0b071808030406091811030907080709090510051801110c0105 77
    0x640c100d41503000d0121380007080c92544003a107450301400101d919540c1c1c0c2801c0403610b841d0280c1070082c860001000f040820442c0c0914400300e4450040c044096001d4030029085581d4000501061901303030151100c412a400100d81420f603c22121426070308650710940d039541000390240034200441c01525400355424024070303d1800d04101401030344805100d090100030010454482c003a101c9c1e0044115404000c041f6030701e40021440340d400952061080e0b202c55844c00400007030004400c0b50707000016400c5006142000031100900c07800080c7c09000b01154048501d04400180c2d040d02968040c0101e640e810310810501d80c01144508046c0d0400803840d8000d101c1003001591102d000703020740b00403054803070002c00107652110281295126a5031407510200411410700e08c00100349084070b660400b2102255520602501199104103028004e608061400010100b00e50803040d004805450300714800e580d80200b241c00c40d04681e06546280074000b4412400d10780034002d85800a03010342 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 556561070 1250 556559820 556559827
    0x3090206073c0213152607050105040605092b020109050a1401032708070302070b0a09030f0c0510050901020c090708180c04090809030610030b150f2112 67
    0x29800c0c0360200d03120b009101e1a200982d0025650107500000703800d00c51010141d400a0300c4003410100d06240703d45246c0c1806c07001910000941000600310300715181070710b883d4a45410003d0407a0715a111803085500034070748900095100d10400c1413010b891021060b14003d140c1e191000608202e0740b544071610488025009001c00c140391031000f0030042003400d0000380c421095120b543c1020035802c000d9002c08034200e1807400d01c80098010021144030f5400e5868858843c28004040c3c0500140000019440c03003041c40014281c0418400e0f00d40200344040c48695200300060740504603aa41c0800100c0201e070520141d6010040521503078011190091146040c2400034601c180c000c0c038142d614071959030031500c201c0c1c0c00d000c6581500406007060007003c9107420300c141c55601c603c0a00d406842404001250760604001440c1a6035200302e04000644a0b403c0455550060020040c2c0c4540902001201999450b15a000081c1402c06901c281c940c01e00203613040810400b001040c811080 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 556562320 1250 556561070 556561163
    0x1e040302060a0f0b0a0b03040b01080613120216140a090603021005091801080136021e040f0603050601060c05030a2115090b0f011407030309020607 65
    0x128026601c0303602c04000040300e284540c0e00c2c0000c2c090031054103811549034803010442d031700e00d040203501c0383d0300803500007402c0d076656003449550714411143c549000e05060345240000d0b5044e01c00d42c0d803020061040b80d01c0c42205070411614411240e00c00030381c560941081580038204096158007d20140780b0070800e541ca960045141200c00b030904004000d00040d445404c1c2c1c5d40c003182005c05c6c00c007603001e0085c6503864a600178020b0880c0c24805040c09001c80400c141e01015484030700741c880508a030b07a84002025401d004880c6120390344070b444d490000311400c0003500c8503c21a0010280480041480340c44c5040c034509112041c0c21031070070400302d540b10b4404202c0000c01c075000c601c40c034a4040360340204c3c0007290004800101824070000e042842090785e1102c0341c0302c02410344030324038002c21445013414100004c488281400c01d000c00c5c070b10950502682c042c0009804128020308020a6070815580024000d40c8200e00071100d00005200c01403414881021115120243c00030601c01500103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 556563570 1250 556562320 556562323
    0x11d090a050604200703021902010c0201030e070b0c070f060207031a06030a0f0b1b0415030e070f060203040609060810031112012306030303040b0613020705060406051e040302 77
    0x52010020030307210800b107901074a8a034030070380124840319000a11404c641c3c02c40760f041e510100c000e0740103102c1c800e0f0120b01da200c0325820300042941611a042c00003040c1d4019809414004400c0031280242c12000507451562130040c415410303143d0142409900342801c1d40804c0919030083c20844d0f021b030b1802d0000030340407041c030031441c3d0342a6860051a0380d00c800007841e10318042001000ca40c074420209040002c400c900a0140e006561800c0c40034909050740300c254003440c0300d0001c8064811a50402c0540a42d1100f00d0005680d0150752006488a8038500741c0151584400c005030b0001408001d210b500c401840e02400551900103103a0800e484005180c804d180006007449403041d6100d2101e6883d42801117034010b01c14020301c1501908861a030b007080c0c052840c1100c0c0001400040c2c5c1d907280201c1141c0c4656032116200c0076070303101d040511600355804513102c405aa402c0105030f0119504210441c480c2d4400ca01c080307118900b85910086c0c03500410000c1079030f803c6803018400007940 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 556564820 1250 556563570 556563589
    0x5011d01050f160503070605060414091009021816090801150302060a03020904091101021504050a06050c071b06110a1208060105040b07060f1d190c170c011d 69
    0x350601d8140c3c0300d1543c50f140144501c0c0c0d00708010100e00c000118a01045400c0e04558800c80007150100218441486001c00c021000c8a0ba104660840000381400c480c299100007081400503040c56140e102070104810555420b0b03038132400124107185003940300e40d40301e0301c10700103005110000d02ca1462095242c1c048000d140c00002d00c00d220100e40c1c5500548171303506456017008007c00521455255082142005060361400c50040c0600d4806891188440038141e020f131354014001e095560300d584540c4020030010700b81d080c1445042000001040080d010b00404009600c0310042d81c0b031501c44094a41c075800ba0381111f042d0032a03064500841c070054041e52910300c40381003800703c03607660400482e49440390350040e10154a01080420030b0040300d510141c00000e081c1da0800881c0e000403403801034110786e60481100fa81c02032a2050030320300080c16074044107104000d0109925281c0b24100c0b071910702c0031015000c60f8449a05c91100350f9000b00b0007001800f8001102c3c1014401c000420032110 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 556566070 1250 556564820 556564837
    0x1b0203070308250f0b04030519091401020a08160302010212070e01080f0708070f0216080601050f040603020d121701060c0b06040e031209030d05041b080304050f01030b01020c030f0705011d0105 85
    0x1030307000c0003e0b041c1f6000d40d0031212100d24800c20062080b1010304d004d0b188c1e01841c020707004002000450300501c0d5000003122244aa04001c9250501c4483c50706110000030410045003155024480c6030020420b00c402d06024484a84910f0078441000f400140b8041d002040c1d45400084130040c0301d0490381040420743c01c40c01501e0700e11002000f00400f6490202141c1c0119040c0d01410070000e40045c000c5400c506807802125500e203130031303581c004001c141c0d12280800307036002942025580024100310f11007440c00829013030184080ba5881c0e20710307115000c2640300c0310200d2800d503642420086803202190344420200e60030001c09501c0809655640907031504e85560308070103000720f030540c0010030a40d9450250003005100502e0300b8031700340444c4d00120041400146240324040f554080c04426035040c0d51000d8040c2014403000e20044010b4021007101506500a010031002030352018410b01e0207910565000f0700f46c20340b50800044c400100404042c002500d102101034080c1e070b00a04545846c0c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 556567320 1250 556566070 556566083
    0x30f060f03071e03150207030203040b0c0c0901120201080601020a080d0b12032208070302010206070e0439450f18090b071b0203070308250f 62
    0x405400c02007880c180a60b04546030001080c10103d001c03101100003402500e01c500d0101002004000b210300a074003c03000c000740560400d1006020300d0004002402d4091455411156100003c0011680d802020303084115051849082c0c0303025540c0217070689400c1042071004260703030b90709519a001c0c1801840303a0b82e0880c1c1e03121060300441e03544445800308010500d0042d00d41d03640040c001514201d208011500342811044800580b000340440c80508494041c3c0185c0000e1f071b80d29030704035015426006007a034095130307818018403408200c071404c1020f80ea01c41c2102c5041d030550b0311084074030400900303428208200c440d05030b410388101c4013807002c011a81c4002041c0c3c540e09880e0b8011104014520b01c80d41000000c400601c41c1140c1001070200c41200d540c2000e1a810304805205541c03809001500c000d0301d130300110703c9291251110103201021550f41001e0f000140c1d00080c14a6102d82c0240e6001901083d404407602528540d035072085d81b000d440c140d00200d141e80c0d140b0300c10000e100c003a108 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 556568570 1250 556567320 556567339
    0x40203060402070b100602010b0117150a181406041802060f0c0313050a0905010312080c0903030f090a0b09090403030e030904060b0d051b0d0b0d02040c080405060c030f06 75
    0x903078546405488400b0741c000710b0109a45000303218101341145502c11503005600304000d006082d405102c0c0900c54040444c818044c695030040103844c00580322940c035400010701c00c40061a0081d03598514140c0100308000304100e0480c014181c54401d019206074416031401c132401091565516005d05103590607a40c180e1603120003a20113030640a1629203034094000080c81d501d030300380c6511051080c1c500440f841e0086585031803985045030030074040186012041d11241406900805002c0d5001c560303c50014031b07101004000c07a0440e0000c5801c0d0007100c05c0411000c40314a4144041000740031117501407810010100001480540701034009801d0599030b0b00e111140f02010b00460356030440c040c0c030500503e580d41ca521002e991080071500b484501e80300200e98111280c250620401c16110340e460b00782100060610000c000143c0f950358480d02000b09640142c545010b81c10b440c7d4240d8030368030641c1c40d09080c020300b0000000c00e074806081c030400400a5000e20040c20b19002001510f003da078 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 556569820 1250 556568570 556568581
    0x10e1201090602040b07151a0904021f0908070801090302120a050c0304030b151807110f01060b03011d07020d0309080d0e01020a0210140708070219050a120503040f02040203 76
    0x14075040d0005403181d800042c000c2402c00301880281038a0b07200f01c20034481319100c11000c1003224459141c614500b513450f107241a0700e26003201d071603400c83d000900c071340d203601080b048420840c1d09241d550340114142c00400c202925060000d1801090b645000b8844e8124540d402904d80e0038a040e558200b48011824a04e4a48038006031003441a40000301c5e5915500c1f0708013402d00b1442229140316603862420030030700604203041c006416404016280d0200c2e124200d00fa02c5c05044102c4903400340c41000c40d1084000c4090040e03100629846404942d25410130311055001c00d2880b520700fa48170401c0c014080b00d264006002c005603d0309103000984400b06250510036840b980401e0110a03013848281d045142040d0b004107802c2c0071640071942010060540341043d103091001c5050380d008200e0006030514000c02c4456803043c0d240c815030391400b2000180540e25037190038151840d81c0140004001c02800d50401840b0344080e0801c90b045140550f01c2800001540900a0141d50040049103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 556571070 1250 556569820 556569823
    0x31209130203090a12030b09010b16120c020a0306090512030103030801050409020d080c010b0405060a05030a0b090a1205120f160c0c08150a050f010e0703020703020705060d020310080705010e12 85
    0x80354035074055a000b003007017180e50303005000d0b0040d41c02c3c40b4400c1d4031081c0000740b0610510210b8241e06c00e10f41c1100c4c00e00065072140b003200203c0342003c006008110540d280180d4030f100402020314880c0c40005002110360810a1420701c0411001c0101c84003040180080b80d004160541110400c89000c21040c0340d80c800710300504080700c1c0092090b00007040e0047c2d045010341203098850000e8808021395500c1c0000c100d0248224412140c140d004004104045404120401d41c0403240b0f00032070709003480565500d01c0507040b06400d0000144081201e091015201540c242c00150300c5404405a08020491f11020880c1c6440c00c4144844005a0810440d040010900800503041519501e00346801d5803040e805088503080c3c2600e01e003000151034040c0c0b0444843c140d6088d2a80c80540d0755820105070000c0d84201d40a5096200301707900000c25550b084c2c0100b082d07401e85040983c0700d080081900d0303100e4155070020b0704c0300c0d08104024055a680104800c100380341c00c8424486038002e080303126 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 556572320 1250 556571070 556571083
    0x60a0e0c1807030e1609020f0415110d030c092108040602070906090c0903023309130506031903110601031424060907050c01050f0603120913020309 65
    0x15030441036600590050800d050441da12540c0710351824040307840b03503481540e1903448041407002e6000411106022400c40c0d0f41c050491a8031300c043d164506601c1d0101c1e140800f081307a403034034002521011034840080d411302a101e1641d1241c00c042c0b0a8180c0810098415511406036503100e03010004003030b080500b1310f205464102d401070030b280d41e250744a4200940780c8289015800000307003808000100140d0500c035011041c3d1031030351140149800e5a013007180a4880b12a030500309180d0345020400c2c0d0a0100c055401c0105410185076100030b0002840144840e24001050403450401002002c0e2030100742e0640480c00b205401e42000c11507e002e503143d1500d254668105d06c54074002004022040603c1d070001d101c220100e99451003c070000300040c000a840d8aa41356101d00049a40c5007090994070382c04c20008d0410a0900307400300f04060848038100c8010606140840502090b418280800114407001190003441e200c950740100b4050107100c600c0b0b5018036400400503810b0001031110 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 556573570 1250 556572320 556572343
    0x507060b0901060e1c05120a1416060e03070c0302130e011d0f0f031611060a0c0204060f0b160f0f0506010e1302280f080a110607020102060a0e 63
    0x1a4201e940c542d8001080c000780c0103030300c50081c1201c2e20102c00c01001e54907006070155101c002090441282015a21140c01c80c1c2a10b9080c841c0e1814148105450b0358003400d0401d8542c507400c80300341707800d091034070691b400064040c400350020070422022542c0c039001d42c81a40e806699140403186a603150000400d00c0350042d8050b5482d280905030701d5080c7e181144401c002480440311098094100d0645583d2070344000d180560041110100020000e2041446140503900d0b80e5100032416010442560088580600040d0303c010114114031b0103120354030103030400f10380382ca2415092a0301040e641c8075450040c640c2113039901d5004100415080d1190007280c0c050b13400702000d0b03841d20702580d036134400380604100c00000c1000101290348603019072442640080c81c41418807a000802c074922855154000103020540300701050000d40e201100005101040050180031014200103058062018400703114680412428001d030707a00060385500146145c400140056240310700e80d10740702181c240c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 556574820 1250 556573570 556573579
    0xf0e06090d03030506153c180117070f03090203031e03240d0305030901060f081509071214100f0203060f0a06050d0209030304120605100b0403080301060507060b 71
    0x96603010540c3c1034124038014042a030f10032091103900840e070305c1c5030b0051000800c25074600b000080241c40103c0e0080b250140310103202c4076038000540600c025940154000342c510545910300c00340e039590000e61342d0304048400d0302c44001410b041000400c803102c5951001d041507100c580c10800e548d414012501100240300c0d1484802007041d111008030740007280c250612900380f20302d5100d80d0019840741041d5401c024855111049990f034140c0d496040649108031566a40030007040c0e150741c8100d580040c110000c000c1214544040d042d0035040c03001800103070b03e80c10801042290b0442c5070b0144210503800303e01940002007540c2c015151400d43d00c0140141030410481c4018a4441e03402540526419a81d4200c3d600c940b00c140f2886804501c104000504100720310309031000c441d4098403403403c0050689181582d1350b4000107403502d100c0810f68900d039941c1c0900c03104810340c074047c40003003805003803a070f04180c916100d82800f4041440340380188000001c80408002c4103510010000314000d1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 556576070 1250 556574820 556574839
    0x71a07031b030f0615090303090f08031b03210a060b0f040902071502041206050c0901210e1005090106120c0303030902060708180406411816050a0f0e0609 68
    0x200006c2c0a402d240c40182d010901c1c00e1300100d031641640e107c80c0151100f89009516044036200c0340562100150f0601070607001c24010300842070001160b541000d10038000f221118103203501c1c048200d0b11294010b0418850401444680c0c030440b005480803035451a00041e00c07100716043c001c649c01c201c0305403e60031920001c2c002c5407841003c491402d446005510030089680c0d451500d4046201c2c0190390740c0485d409441454a00d0b5070703130180d01c54030b02d66410085602114803c00510300702410f101d1485103525441040802c0c08248a00c0d40100003c070400c0c10317440c9490300d454035031564901020702015240c81c0c0380800e64031614100c42d031743d07680002c010f075480d4001da512184c1c60b10030045d041e208a04010000400340c90444031440c6007001c8000c40c10b01004841550307510384d20a50240d05800303515813658440ca0f07648642001c000581c0f0001d041c0f00f40303411044601002e400440302401c0c05002d21409400b1644940b11490101c007504000314403040e41000200180521100e0704c1e442007008 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 556577320 1250 556576070 556576109
    0x30b01080109060f0605061204060e010e100513034a030709020a050f03180102160302010b01081608090f070f030510050402030c090406020d02071a07031b030f06 71
    0x1544818070181c0664010413038000c0d010031a1050b60424418154046000d0100c2c003183d0000d1815150003d00c0303408005510108800c40c2c900392054248a80b100e83c00a150019100030f0078001c1a1703001306003803010800441c1e87d07940545505000304241c039605031861841920441c1c544060f10046c08610318815419100d0030b03880340500ba42d00056070103402044800154a0914002d8440e5400305403070b1507041080c03042084a454000804101d0100044608000303d58130a20092140155103c05085a000e103420083d01b503c070001c64090400200074100080241d04011074046100c01d454121050380700d00d00e00301e107403100740362200d00c050141c0703603000400e400740e244601c0071603115100355050200444424011500c003100d000e509a00030790416030141ca040184158030502c82e8500504196051003198200c1c0c01074030f812940078030074001c070f028000801c02c44d00e940941c503840c0c00d00610074004580c5180c0e0720b820390031400b407546442e888021260190420005801207040d000c100d403458 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 556578570 1250 556577320 556577323
    0x41e0812071b0e0106031e02030c300420101d030313030201050702210a0201110a0201020a03110717100c0513031707120206150a0f0b090604030b0108 66
    0x50408407007810900300781000341c0d1564070000c000c60302428030702080341e80f13031405c01d60291400c080d40414501d8800b4114100d0074251010354000d50013009103588912002d10f840c04034102c10311070300d061700d42209210405295203d0040d80d1195120036411001c440d841c0902c0b242c004913008060303200040781c4c024552242e01034488191003c074424000884001c1d04285034a13403160b400b803c1c1003101e50440600c0594023500c010400648040e26440b07040e0080c4c4601c210a494003c051079035a0400e00100c010f40da1b00c460001e5000d080c20b4080d00d0000000c2d0300103981c8506005005040c810180401c0940140a101c16001016094080680c19200c0c502f4035455140c06510312150f1468010b898190300d1159040c0c49040b5508080040e503a130039500c40f00b0806103400520180d000007041048c000651905030110680030b41c6d002441d0504000031103802149600c003110b40200030b42002048148000e840500807070f6044600305550303402e0350001c50201d00c156000940540e44c0d107000040c81510 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 556579820 1250 556578570 556578577
    0xd0f110103051501020304051011061303021c08190209041505090c070b0c031005150a02010501290304050c090103031d010201050c040b0c010f1b1107060203041e0812 73
    0x401d99007000280d0301d800144074011851070780d603801039009000900042c203000010642400d00c41c00e01c7c9203481100c1c03280c0b5250207800c5941480d50300f00c0407000130400d90100410005812410700800d50a03075410390041c4000e40062903c0b62050901c444820364001c03075030403507480c80c0e4050400d000f190010412a00b40c203e0b42c3c800e041c002d0b40e034540021130440325801a5284030741e02ca441d60b159070300d48150382c3d5030039000a0400c7c440e52501c2440000c150b0f96048041f824503a001c0c0e0801e490301110704001c2d00f140c0c0c05a000701c405035001c00c128600310326602410301c06081400406900c2e92150700f081c501d4001c0007003546030001041c01c004014950049136a0144070403011058070040c1c0484012402c2c3c94090300c1405140005210038003040a10304081d00341081c024000027884481c3c1c01c004821b4400c0c2c50501100800044980e100d0f26520162a12002c100f4a0052012518241d0025a40d104a218103101d05640352074204141c615a00084d00500c05401103034400500300131120070301e61 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 556581070 1250 556579820 556579853
    0xa12060f0f0f03120810120609060c080c0f07030207090203041a01090c020303060919060605090a050d150504410607082a04150201110708180d0f 64
    0x240300c0788002069111007a004090340c1e400010803003103c000c002c0a0b41c1c4002c1c09043d400707001c40c1c408404110302c18071101d40500d981c0100707008540d8032540d003403000c21115442c0402c01001020f4081101c2040d00001b11220141d03440b40f00340d521240ba0030201d0600c183d40e0400c400b603900000c1408244000b4181803071200c042801d4509169980e11007503401c4074450030145015810070300000300d551074a40708140e44281442c81005041c06000302807400c90720260420303030208002007101201c41c03d11444040c007a180981310303040388074141d0f100c002c840d50b580c4200070340b169110000201080725181c0b40052030307569006202c1034040c1c02c120000040402e00204010360740395003c103044104000a00c0780c040d0585844040c000d4640c9d00038800c034001c0c01d03402d0065500500603a0448072894000810090488404821840020b08802429109171141c4107a0f100341c24000880494000c50494029200b070305001c03094414510041480c404080d0b0014051608500c0440240803070b86080e281e19a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 556582320 1250 556581070 556581089
    0xa230306040c090c02071215020f030406092a1a070c060302250209190b06070302010510060c0512130e0c0315091306050a020909040c090f0c080601050a12060f 70
    0x80c6884c0700101c0e0380700c92074071600d2107400f01034202c40081560441c00c04107040842c0790245c03802100844804a50b40709440072600250340c0c2c0140380074801a903500110f103a00780d8600d0201510300b450010324140d0640500300000f1100c92610041c0c01c42442250703002580320b842d8082e40d96481e20094002d41142003450b260003030103004030f041041c03403c1000c100540c0c01000b20b0865120800b207007100041e40c014901c861551449a421150f40d10006442058880d90000c10726141c010385000459503158001018081940803030800030780d011642c0030000614040554039542039980b1a0200e6075154861480500b140d01805000f81c0a2030007540306200089006452020b034134140125814101c034000340c03080346a0450b40c0001c010f07070030158205828950140c01c003121100081d111803010740b0308a03041c0780c40315003c02c0401c0c02c0340144076092129100c10070079190540700c0640702060003050207041050028450400c54044c01506064095040c2c08100b040d0700c5081016106889000350b0300003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 556583570 1250 556582320 556582331
    0xc0302010c051c0203071202040b09011209020913080f0d050f0714090f0f091303171b070822080f0304050d06020304050f030c150f060a230306040c09 66
    0x329010310304841c10000c5400c1c0c3c505180c1092001d200094201030a03441c1041a0b00c1c600040000041c00608003610b4034076a540d944030343c0c50b4005071180c1813101c09086d0150030007412030301503902c80c000e0301d41c000680c0740b0a5182d44c1a0303251200580c414803020043c0b481002c40e049400710459370045200d2405069076101c16101e800b429a09280202c0d400f01c2c2c40b200c204000201424241191180040044c2034100141c00b441c00155080348201c881d901c11b25101400b2506040c1e02200b62220403070a21002451420812820b85942d6403a1050f2012a00f00250000800c10800e040740d5000304410402d00e1000017003120118180c0c0c040c4660005031142c00c0c02c114070340308003000f1582200d070014907030800030140d50f56030030280d00000c006451078096081014055201440148007188001d07016202d00351070720048004160014203040e0003ca900000c0041940315441030038141c9404030303a060310341400000003842d521069000c668040c0600014032003003081c698070510560340c0390302e402d004 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 556584820 1250 556583570 556583591
    0xf04090c0e0f04121806031d0a0602030426070b1902070c0806010b0f040e100510020304091803021e070906030b10080609250b071103070b0c030f0d0605030a030c030201 74
    0xc04803ca04801e00d4620441001080081d0007039108c80703100c10741d100c00e905447d1b203404501800e022040f881035030f011350000308201c20030002d640038800000750030003911141c02403020013030054020040004e10b680d5480020550103128816201440314244d01b0a56903145280b03070200e2403038168456900b0f54400c8000204490313510000f52800c0b400f1400e0306508103890300a0b42100401d01600030700458040310b00105d820380b90340c240910441c280da00290754942ca0089080d04881080c4803545038040015103600000768042a40c09008101c200150840303d00c2c0c0307031100d0a20f03450f40e01c035008080c070342072002040001c402c2c08584118034080c2c590242503581e858581d16550119800304007900318841800c1c05d0588100b409034000d40c080c1c1001d610680701c030390a0300d00340c2c0700f000c080d61101c0b05885150342c28074041000001901540003030f00c0c00c214611040d140d5074013a000c3c4d500b038540d8000c15200c00c6070400b0b0b0703c6100100340040480301525168100a011103504c50002d07001542030020402 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 556586070 1250 556584820 556584827
    0x9140105160c1403040f18180209040201210b15120c03040312050a0e0c030a08090103020c030d06060e18090303010504020c16030c08010b010801050f04090c0e0f0412 73
    0x240710780c0c0d1811592010800300e0008071403000104104441c0069a070f40e0300c04881c42c08002801c042d04010000e1545a800c3c03881c07500142c40400f204101080c10000042d1000150040d0403c250380d043e1071103403854846100580e500146210725415500d424010f60603104103d4205081c00c1c1c805490408100508050000280c03042d901250760307909101c0003259015022000031580240207160850800d5510329207841599005c0d180c22820a80fa54030704081c803442030003156240c502c12030040a28441e030382e0b10344040b4061801d40d94140340c1c0c0400c80030700310070041c03080743d182d5000010200405503d640e005440310b0741c0b4011050050600c41440102a880440350030301506c0004000d5055030301e4070302000040c1d4001200f12006006000021565200c0640c499003e188511000800b86080000e41421245180722560402040400402254454000310005440c056030003007584549030908048080d007580c0702010340541c69040001070075010b5100350003680b042003000c414054610044 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 556587320 1250 556586070 556586081
    0xd0506160c0210110a050307051605040c080703230103061d030301060e06070f0b1e15061614061305070e010e15010201200d051f030b070203120109091401 68
    0x9402540c0011414000d070b01640900c0d0580807444c0445207140625550a400c64100580840d01d0b980301145074141076240f5400c2a0240009035030820602f80e044000405004001d843c41050564504018001d598102110700d54500c0343c000103c0c03196942d00d088401412003289400d5051400b0820002e083d902000300ca0403107140e650364103984050a0704000a03070703220101c11034140c40f9002d80c2c40005401080c00d14030030311042c5941c030112600500a8202201d00400c0200c5241c00c451664500f030340c0382010340741d101d40e400c90307007003078244041c40c000070f480c1b82003020760b215031017440c040003007400311443e58911840c442c0054401c1180da40540e080303584420700440140f5441d950011f000c0318074080c0030750740d401e105100103c1c1c0c5039611201e80010b151040f51011800700001a9070308c2485140c05101d81108109000e0011034801c07540d4800e043c07030720380001454035419a0110381514801c006651900c1559101700c0810f50b519507440c001450010421203d204203a030900e51050030601c1803 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 556588570 1250 556587320 556587323
    0x201030e0f01090804050f010504050109090b04090f0b09010b0406050d080318032206080f07121401120b15091b130b0405030f010b0a050d2306040c0e100902180d0506160c 75
    0x38610dc103400e00c111038001d00000c86030035802c40d5942c40100d002c42c0b44c0740c1c0f0311802c0900428002c000c90810340d45035820341d010026518011400d2000c100034a49540884400c1d1a42000c1202d0f242c2d11080c0c01000032030080c90b4503044d41e1102003002005034264408810b103401a031400540312955810064681150403590490015050301c0041c40d482d000300660301c05680d1010340011001c40d040050700d80c0140a8124204c1113240010307030380411000c401c1d200d80003019000c130105000c41000003d0348000d0024180303481036a0b40200f9800407242003080e180f07404111240c038080f981e12000349030401d070810300c42c841c03192040c40c00310701d074100d418403420581000c003034015040d5074100302c00c3c00064441460121041c0204403a010005202c0058190188808401825203400d09007030441c06800c43c0d40104c4c2d10040124244218900c4501850084401d00e80b00035850304c00101a08403e80c3c5245085500000324220841c10080e002c41d80610410400040b40450a20400c04945081c9107590 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 556589820 1250 556588570 556588577
    0x20601081225122604020616120e090106030e0703140705030312012c0f0402150d1d03090a0506090a12050703030314130201030e0f01090804050f0105040501 69
    0x201034818903000c000c0c01a40034151a1502e40d098280766080310010058082d20b603000040c54903e43c0c2544582404004401c0e00c0201c03507824034140701e400d140c0c507029000910541002821180050880015a02c516000350160342c1010b0950006426002c2d1082294403c0002c0400451828000d1140c000c08000c50002041c0c078a0175640c54001c0b94112411403152407081c0d650000c0c0303c0d60100018141081e240d041c4600e6940350580d0220814502d115406103428203104000413802d008098560042282e400d43e0161f03100c4d400403801142c1403004074105000000340c0ba084000b4650000343c01c0c54500401c0d0b20201d034404654545a0080e44022507110000500c04c0106180440207031581c41c400038a411070700c1d0754a030100714848481c1c000031152030304000400c00034190544900c01c80c0b143d002c500143c0619003044100135486441900a05040e6601e01c846100c08080211071202c61000c0d0003000102082e040c100400d41141c4119407041c030100058603841d500c1041610308840060b10f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 556591070 1250 556589820 556589833
    0x915020c0c0f06190309050d05040303050319020702100e012015180708100501050301020a0c02040c0311030702010614030706021c0203070f0309051c0c06050705011d01140702060108 80
    0x20108040704042d40c1046600c03200520070b6800050813200358080300c0d012a200007030001044d180850800e0850000c80007130105c207210410100e60410708032503016800c5110705070440d041c400c0e08070007409500d201940040c6507c140022aa0300612084c85582090b20340d600081121103c21484a09220a039101b9821005200e480c0d0301052030025040440c0300101401c080f200d82c20145008400e60007090941d1280380b4500c03036022140f060710302401c0140e009601e4515000e0001c1c080070b00c500c01c001c0c09246e42d050203400c0d241c42a806001c2c8a100c02c0c41c1643d41c1d0400e010001e010f001940034090f10200c40e6080090640390002e500800c0710ba943d00901300460b44030b01a102a5000780d0648400d5000412195000440300f500011100d0300c640c460701c030f04c0c038145024005120000418440f641070060078a00124050031800400c079201490450354034491494001d01510f0317030004061014940410001c9402c0d03064100701e03505c41920703220300c40941d21030b031040b66250000e1041c43d51035040403 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 556592320 1250 556591070 556591093
    0x42405040506070201020c030d090612060806070c0501090c1806060e0d11030f10020403140628150e0103060b010513060c080f0c07080d0c0b01120615090915020c 71
    0x2000c0c2040a0050043c0c03807d4404a03030104e4241900400036600003030303c3c82d1007072005a420840d002901030708070404016280c148581c0603074a00001c0d01c0c40c428414a40701c0e9804203c1c00350402d210155009284101ca00c3d551003a9129040404002010140c03e101c1c0204000c0e11640e03550a414000420700010054903450b00d0b8000704486200a400d0b0095044c0340390709a8040042d800c0c49540d9010050b03859140d4204030354a501000102d01d02900003c0c00d01c00203104e189005015120304150220f02880000c0c0c6040090140c0c0d11048045610410001030950550302014100e138002e0030b0500208281c0401110f6600c0b031200b8034401c0440d0440c003440144e1040440d504100e10900a043c40c0c14400741d0f020720540c11101510000d0b84c8903080c1844141802e100c5020503440320709003242d40c00030350740c0c0d00060700b45c2c140a1040d90604146141c03060081c50340160429541d420312140049407a401c0480c050702010406a0380c141c001000000c0800b050310882d030040400b5000740c00703107002c0e1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 556593570 1250 556592320 556592329
    0x3080c06152d0a03020603010602030d06170a0b07020c0d030c1104090c1502100516030605090702100209031e03040603140f07030911040e0d080f0103111c080f0424050405 75
    0x4020415400038100f050200040e114000114040c1809400a646a00d0180036540a890180d080700484044211002d15560f200040030810164400100e01c0b00303030398000007285003007100d0301d140783d00914154048090642001b0a400c07290b00507140b110041c11028280026a5081280100a1a8034450402440a44151940c1000194819945010b134209c40d1042174800c1950b41c519400c0804110718603a6401d0703c5510002e10090326241e0051902c0d0304065120300d90b40c40c0c003104071900011500c1285d9001c2c070800ca010030094007490304c44c01c1c004426030359a4000d4014030021030f1070303c40c02e903440840c000070542c450603c8014808060355185001c130064000300b00300f04d0302e003200615030640c0d039925400390500105041000b0090300c50305103001025104080c00b00400c2025250051010407003840045825500944035091402c20000c4060707585139000d03501070310701d080102c2c5c10600070403500014400c555003000c80702d0072000003148628500c0310982034032011410400040115060 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 556594820 1250 556593570 556593649
    0xe01031e02090a020c160501140d09050d0207170105010803310e060406090504020603040303050c040f080304330f030207080d0921020a031803080c0615 67
    0x881000c0e911000030a502042182d80141c407405000d50700840e0303501c0741c3d44040101c40030710040c08041507102880c140c0003804030810503041c1080c3e1440028000880b000d80c0c2c01051811b98002c0c119140c0d140e8601009407150800e0085110140400b160318507402414028035040e9240072002e14640303a45022050002410070300c0c110103950b050f40c3c0c0b851095010307808e07480c01440c4408050242d440c0100c100011503109030003a1980f9858882440096140c010540c0d0b4460b0b8103040001c0c05840341582d0907a00c2c0a16407045504131100e0034003150040000c4003900440e14130004c01d5a640c0d941402000724545650901c07828903c2c580c2280c8810f074440c0010200c140c4103030800500d480c1082d01d1748503669101e20340400d03400751600407400402170030a005040240f140744032040740c0c803440031000351943c50060002e0208200784100c0814003680c00c04c1e03c001580d12a1380141d68484100310a512520115104e03007148405205030186801c0c0902004080c060f0310300340000d811482c3d1018850000c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 556596070 1250 556594820 556594853
    0x1051e100b0d0b06070303090308101a03090705030d0309032327040c1d0411030a020a030f0c0804050723010809031608040f05150d020309160b0904050903040e0103 72
    0x19114640f1911030b40f6031000405d50540070390380c0442e03000301c5410054080c05000d000c110794005050410013a00c0070714034601d02c8481c400101c0b59035a46892092a1411a454000302d51501802c00082103942d0998060000359229441c0e0190200f100c0110381c0b03841d0450014211045010044039402c0243c2d40b079401d0891010203641c100d012202c0004c50300300c2d1403e0045402080c601e9074030f01160a60150f100401c1c0d10115000d0205280100103119a408054502c5a005801203444202c2da4001c1e0009804080500000c1012411004c00100004010742d800c0d102c42c09240c0001c24080c46201700c1488005e4005d000001c0070342c0c0785004581e00e0364000d00d006d20501090080c495881100078600440501400050761250304040f10082080d00075800310b440755110300701140d900c010100c151403405810020040c0c6a5595025032414a44101c00024586500040c045683c0018001801024109039001c22450ba69100303607654a102d01e001e5103815010603001000012101c840640ca40c1d07 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 556597320 1250 556596070 556596097
    0x6070b071103031008060a0603050304181e0c0f020610060c08070c03030305060111030903060a0b0f0310200c2d010507200a02150d1d01051e100b 64
    0x20322140710740d0071604180c0b5000741d0030f060180c0410891808000090b004941c100040100310702e195a40e503505d2086200702c1c10003040c4106070000181e200c0c1c0c0524114981621040066001e003040b01c0c0003040c01054003c08181d040710002c3c00b107480021107510a01440f100340d8040303410b10000f0b46013003035860004c448000040204100240480407507400840c42501c02040c5420414005001c130b5400e01454101648140401d6986650024000e6080000fa000006030b054006001c2001c156180c000290584034400100342003518950241c0444642d2420706103000b020010061210700c20740a546ca00c41d0b00405180000c601217005403003c18480c4000b070402070040c000402d080d80ca00712030a03004201009620004901c500c40700c0900c8039207810141500c161181d00085200c040c82c080d46111720130115811004510f1ba0344240c0040322405c90102c1310b0040c040200380a000111041c08a00d0707424402c001041e052a6100d601800c1c514101070b1110b8105a0020b509800001100140 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 556598570 1250 556597320 556597337
    0xa02090d020402070c0509010605030702070e07030b06120f0a090203151815040c09090515040c080f160e060108070c0201020312041104050f09030403150e010507090e0a090206070b07 80
    0x50b41c030340c030040020510450701da4007414a420b0070040340b004160721420510a04208012840d9400315200c4203a400b07110a0500e00d44078143d00b01c0040134100201504a400060229102c9095005c1c031b40c0708a645c003002e03484e29036401110009449462000a4150b44002c044042054140a5003603100c682258890b00e0340c0c03031040401d0315004c01078441d44540c0b518003040c0802d01103120038100140c03581003018400505981d4400e40d4481c0a01c400d8041045414046030802c0080c2004000800035402110b042c65210111542c6a041d4030a002c40b8900303694000081c80d100880c4007500c29a0161260009555101819105500400f008a0450104100d00680034078012580d502982c06052129903992042082c0001c950024158001080411040002c2e00000100300d609407540b02092290706025906d0000240603144176a01a55080c4403c020010394404038900440d001030344025103d4540d000030000319a8142006034100c5410031003030000c100c400380c01c40d42000d40d41ca0884403 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 556599820 1250 556598570 556598573
    0x13170a021f08060306040c05210715020c1030050a051f030b1f091a0307091a091305060c03100609050a1725051c0b0a02090d 55
    0x48400001c8484480e56072600c4654801c56000792010307400501540100100c0c02c1580f190b000c000f92a1041601c02e4500c00e45141c0300342100000004000008001c80c3c03042915015003a400c58811000b1000504c2280001100f41c03600e26440700c113500e1182c0700d40d0725504030701c41120712108141c40311164820980c21308001200c482d1150601c11351885000003140e051001d511142002402000742200c03a00c00014004515503042e503d8002c460081c1140120315521110701d5510201d600981703403d1729080d1501c42c500b103841d03201120705104500741c51900f5192080d040417584410f50780005d51044074900d006e00c4c1803070f030911900464500e03042d0650f07140c10745d1001c1c64034508542180d01800f0120902468901d0b800c4010301170807030341c20f0100e21103080001249900280748503a502d0080c403080c899841490900c1507600746001030010821074400c4505021b0300200034071406000e07010180c5125015400d08140c00768040d4440240c41460b00d84090450194022240d541c2c3d0009460300b4040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 556601070 1250 556599820 556599829
    0x803040e040b010e0f07110f0f061b041a07022d01030501150804060209040204030b040c03170a021b040b0303040e0a1a1804060615050c0106080313170a02 68
    0x100400300c16416810a01d01403806101c0b80030181d005400c900310b000240000e080d0080c0b213599105009181410545034800051442c04410310140090350207240c4c84c00308201c00104040c3c5c819941840800d881d411414280303402c92050384590300c2950389003031000e01c115600030014170303415000604c40c0301c280c5540c0b00c0543c2002c0300c040c090b00d50589001550101c550305800740718014210140b40d410310751130b4128040c1030305100a0000340104c0d40000e0301007081d6540d506486c00b650b04407010000c5464107107094001c00d851400180d5140c0654805444032480a400300c03221252075a0180814014107101030000050b004061035005440d0041c0103904e031410406040103141500c03110029080c90308180040310f14140d14040910300159614a1548030700c1c8c080c0042c000511a050728075a100d09094004012640210b80300034450340c1d4021550341d002020b03000000403c1e00801038560f8849034190790340303d40011191402141101084007020000a13655446092001d5518503400da60004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 556602320 1250 556601070 556601077
    0x30807020a0c2d05030a082104050304090f02070c12060f02030903130801050c220e0a0b01021e1c18030311120a0e0603060d020301092d081b03040803 66
    0x1001100d000d012440e240250702207001d144042109070f00c65110303003401c01003901d4200802c0094000340002880a4541a541c048254541103003000d03040b00742000c0c40c00c2601c030780c4580b040311036242c00c200046075a00038174401c1340d580c0e03940244140683d510b040112454101041e5003030341c12942d10300d64113030a0000d030f00003140706d4002d150155a645482680840940000e500f094010303a1500080012003001102140c0d4090914402c03070f41e454804e00203a0303c0f940f0b030b0340d00484001031001d030034442c02d0701e0141c1046030100005d8003910468400144001c107001001e45010400b9230222000703c0c052030301054401d84904072442d0004411029819002c0d03c18129403044002a014514030500e01c1000c0c0304d115044c04005001d28949014a180100700c0f103ca400c00038810381c000000303d1025501d1101c0100415405002071144011178140400244410001e104a490740c0850030100f00244003001c6080e1680041e03000d0605408817203800b442003515848800c648410040030807810340800c080c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 556603570 1250 556602320 556602329
    0x1410020c1e010f020a0506060105070212010f0b1c020a17010f0905060103050d2d0c0605070e03010b030a2a050904050303010807090603050c310b100e010c030807020a0c 74
    0xc007000907148030001400c1060003100c8200315000711007903000040340850300b0340c0c0005003407030810340769540c0d8000600c17041b1500c640c0b0541580303001d968800c0301c001900704190258048500b50a51131200110205208614000941c0005006028403059103241c109900f00a014400007448008550488080780c00c900b03401e82d060740c07054004008110302048128101101440c04003800d040c0390b08100c1034004551007114400080039039015046108440040b8400c0d0411024000d07410140d1002d010861318040c1c3da4001e5003010f044980c80c0c180000d01250310f2b03034443c181c280405802940c1d040c030101c80f100c80141c2441c8140c4001078564a50000a0040c1c1c060b201540d501c0d407412108a00d0030104c8d500c81d40b070380d5040260410100d400812121407142054400929003204c803440024205e0300800c4100c4892400c1d0790070504a100c036440034030581d40a07030300540e07448002c03079003540d004440d44242c9000a00008000c40041d21445216070082c000d2f0044a0300e0495a9441c25601c1499070031 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 556604820 1250 556603570 556603609
    0xc11010f02041509062a0803132f2e0f03051506070b041b14090c2b0b03100c020615090109020903100207030504050312041410020c 58
    0x7030600c03c036103011003803104600e060b04000000c02d18211000d450b00c2d102d0314000303030f5443c0f24840044020f400c29030b60b00303106544000b18a036030b40380550000460241850301642c0c2c0540c001c406034011341d07401000d00000e0020100c10020b01c4c00b501d0402c100c2c010b507084501e01d401c9038004811042e05040e0b88010b40320b140e13911140c4070285000002011100c004028890380221a41018110748a480c01c81e1020350f000440c41c4e10307640d2035080032481e00e42400e00e1044008010b403800110000d000000c0d82610008a64500703150f20b88400c6003c0501415407117071180c00390508454007080b42c81420b9015450004d00101d0b241501c0000a0700f010f5251443c40700050f250001c1a19496060000d01c1c0e00400005240c946542144040350850105015902c811517002a1445095a007040840540c0011403c00e55480106180040c50f641103072040c81e0280c843c44a0742034a0125100c20748064980507100c00c1d0a0980c603200308040f80070f0219005d003e601400c69640110303210b401c241031510a41d0903 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 556606070 1250 556604820 556604827
    0x7030504141603020d020619020705100905150715090804150309050a150b0310020c010b060f1207140315030d03020901201e0d0305010b09030607030c11010f02 70
    0x920300411990140901d090350031015a2a030502c0b014a52601a0798050f50078103c8070080b440498900d102c2c088a4a040b080b0580000b01060f500040c40700035210b09451907000030b101480305030f443d00310034081d51358009051120032502007071030009015501c1c05002210418012444036900722901240c050f078407040001000d0141c4814200511003c011901d400c00407041151901515a8003074900200114009055038082c81d00075002045a061300405648880140d05070340c1009501c0044041c805500f002150760b65480c2c0390382511003032000140c4c001d2605000c0000c0419101d0000d000d10700340b0580025800012112001640c0700701e00d070042d40711700200e0306400c140c541204c1074051030030036004002403609641e01c400302140740c40040300c01c0b01521040208190034001180d0a60400d251902c08001da007a0001441800091a51b102003109036200c0810301c0e82d07480340460141d050360000c8007042e6024825480b0041403c0140341c407486010a03500e40d00d080d2074025604506164012 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 556607320 1250 556606070 556606073
    0x80103110d0c150f081e060a0b0c01020d06061e05031f0605090f0618041107050a03050301060801060f0507030509030a051002040608060d0c060c0f080d0c18030507090e0708030307030504 82
    0x200400480d0003d1700b0000401d02e007010300548400a4000702140861100b0049241078640d2800754026000c184c40b90340c2c40d0000d0a0b203450013034111140310000c1504060001401c20b02031003080c560b5500e00001c100020704601801d81d03542d0300c0034081462001d40b0308101540020300f020801d001d13190b140d403160f5480801e00108640c14517840d082511441080000a42407030007002415a05034003643d002c01c910021004c00245401401c401602c140100a00c1d501007541c007200542c1030b55840c1d100c0f0600d40c0d03251f460498084c00c00040c1c82c80420010031884020a003e800a4108030900504588004050740da0316030800c0061030402d650f4a4012030b0500029410055051307102400b9290b400c800502a156140b00359917901c603840c11300c1103c945030818007010089141240360001005035440703898a081400601e101c41160000030344d00043e000c40514a584410200d0343c000e801450703010b0524601134014062b0701d10740406d03031248072000560b03d841440690303c510308940b0002440d191a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 556608570 1250 556607320 556607327
    0x10e060310030f030903200102031c020705061f1211122401140f2b06050c03010302011d0307170a05010f020a02010b18010303030c03021218010b01050a080103110d0c15 74
    0x182d00040c0d4001f04071560700700d0766400001e41e410105001c13040c0d403082ca01003801800a21034804013410300d0154000b04442074003d0414100b285270002100480940e840d08100c9000149880007410100e040311a04454684040c0b509513103e55a0180c03000f810840c502610000c6055060b0000240294010041141ca9852003407200740103550601c00e0611910004125071006450380c03c0c07182294528500c04c0d0714021003206210341c0000c0800c12400e0441443c48250401d101c00c90006461945040204045c4007054190803000340080090703a0410440c1c03c550508045003103004c2c03080000b0400030410034003841003181544807005a1301d03081e5901c001d0030742e40d903d00030501501c03040f05003840b00c0c8440d40120b411a44c05250015014008000880c042e120301070304540d0010100003800050301610b560300303004580742c000070443c2001c101c0045d9a10300403820750700c001c10070850040020422004207000e1f250001040c2ca491a606a078983c80c00b8405900005100b1089461820a0980 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 556609820 1250 556608570 556608593
    0xe0d170711061b0d0f201608010b09070c0f0f02040b210712213f05150913080403050d0806060310090b0409051015050a05010e060310030f030903 64
    0xd480c0a00c2d8001c060030020b0071986ea4103064003107410008030804a5030314248244188404030100d0399200555981105010b886440e07440762007107407100e020490141c011030005a10036400082086507064540f41d18011103240a0705980041d29002c2407003680d650103143c400c001c0a020040000c84680009407860814103421001c8a030406141100c04138903000e660791045401c3e654401e501c200d40f18002c80c1c0c2a000e6145080400071100341079580800e8050004000000d070070300c10b0844c0d0a410340ea0005547c0d007034a01080010380d60080300e0060901c0500164084007000001c0504109951100181d5000394415582d5400185915500b41d81c002d07681074002d001116032600354203081c0503070720140110340310340196280e51300360f54982a240e035040986081e80141c1501c4404160000360f03006030852091800c0441c4940d81c01003420700d052440c0310240e61060390340340700010715403080c02100c4c0c0c400f514081408000010000000707145940c903400013440303030b658240300703c0c0b0f1854460720828 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 556611070 1250 556609820 556609843
    0x180b0313231c0314071116030305091e3006090c01030b031005070201060501030e01020f03060120070902040501030e0a1a18060c0a0e0d170711061b 65
    0x40180300d039484160300008a59005107011402905a001c1d000003d0380180485958200508040001c00c14829080003040c1940000c0c8400d0b0b40441c00d034801f02618041c07403400014017203a802e00054a25091210010810301ca00390810040280144001001d038605200304046030704d100c01c0340c5000800c0b401003524291850000038081400c03c2030109480310441e2001c541056a1a03a103108165003c005940c181c07003410030108003504010300000e0281009020385404282001025510000144204c840c04011050340a00b140c0318400111105c100b00b1804100e0184110710040703035442d00740030541c0207042c200d41c0160740d14901400036065400d0104180200c4d000040a84c0101e10025451299a01524900300ca03e0360b540c0128040800c0416803240c040c4212000c20001c06403d80c020000d9041c02d488040d05002841c08000808480b0500102007161030146082140801005400394074824050311046603214004601c00b0307002106468680710154a9070040303150305000704611407 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 556612320 1250 556611070 556611113
    0x40b190212131e0b1902012d0e0703051b1c02091b0c0d1106010b0408190201170a0f0605030c030c190302030619050703060e0403180b0313 61
    0x840c400c0b29045081509125400b518800d8003181c070b050500000c4030700050010403401c00c1c0ca4090700b8040d0541007007640d1710f50000d5880d102411400b8a00221040f6540030714140710700c1c80e0200f0000402c081c29284034419264441c00b0404000120184070007401a40701810400c0804052000c10201480d6069560a118100388010000d44c031f814060350b074400c0798200f0311201c580c03c07002c07004214420610801900d000300107074604501e03840705000d4040c05055044400d541d0301c4a0b220a103901c00c0d84120b12740343e4862600504110302d0b01c54100c44c07950050401d9541c0703c1109036254482d2004139541d44640e030b912001e0038100c000702d01c0307030001a04054000b070400007000320200760750701d1400c0c218030b1040c028000317a40c240700b0203003080030040d542c0501a51490301300b880e0303204103c1c42131031010020030b400d0400080d0390a10900c180b404544070382645425076200c40c2c4040d41c4c1c22510042c41c0c1c4404080400c08600c2115020045000702800700c02c8010f0102d49050408403060800d0340310810 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 556613570 1250 556612320 556612327
    0x303070e0d081b25050f031b100219060606021615050d02040b0708070b0f060f09040203101a1008060306040219032a1e0b0f040b190212 60
    0x128604009540f14441c0b41d102d29a180c2c1d00d100380c01440c1c015986600604180b95210011115101c01144021508151000c046d84600c140070141c40d404403980c03002140001c511132030f64918000b501e000c031441940c010744449507070004400300504e040c54400d60701152200010405154108000022040030140f5101000e081403200d106008134188800208100030a5800c02506036504035001003062280d025521919072038109150f8000c0501515080326020005010032000381415215403002440c042030b0312a150708004800390081d0082c1d825104010424808990391710510f0101a10b03011020001a444070401c00780d4000d80c01002c04100d0120103010083d00c2c0092115085541292155002d400718100100e0807411540060210050b00681e42d244000b440c0e40d000318503c20100c0149078a480310a80011200301c3c1c9442540600e82090401030a17002c0380140a1281344680343ea441c2c2030f500d0b035031803074181c000a286900c20701e03443d1200c07490607404010701b284182102c0001404d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 556614820 1250 556613570 556613573
    0xa06020408242809080a0e010e150c030c16050a0509090303010509040809030a06060806011e050906041803030903030b092214071e09050f0a0c05091534020103091a01080303070e0d 79
    0xc1049142d04030a2000d40102f8825100c05090059802d1481c1e88070032031306081e0301034030050b20901d618803441b0302960036107801098a0a00360320007841120550000c1d861a40782100788a0441401041502c00810a20400400780e40078481040140e001c0e08000c514503003032450380ea00780001130303000d01804000c940c402444000649440700480b5812107420005986a8000c580071380504032010001c102003850079000c06400d40c0c0600341c3d03030b0301940d4200282d010480601c502c421040e00c1170310002c6102030700802d0480311802d10801543c4500da6458030b003184903040900d4401d040d00400c0000032b4a1444018119100c505a0000c09100005203e02c0c14001072032841e280300504a02d2030f00d80c40d034164049190040045883c1c0000240100590380400c5075001c4258020018407200340081c890b000040815000444824926110003500300e801c00303600640003480c1400046840f000c1c50442c0741070350520096818000c0030709402465407031030521402802003994164641c424920011070310f0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 556616070 1250 556614820 556614829
    0x1060f030b070f021b0f0f04060b190203121f0b031315050f041403130f090f050906130f063b0703120e030a06020408242809080a0e010e 60
    0xe400300d02901e64140100d001008200d1203501d1f0410a600315042c030500241090001005140c0400100d880e0038082c50350b20402c9840344180341c40c00101c0c10949001c909014440b209503840010341032055600035980c0c10481e200c1e0340007240d90720032198070050f1343c0007441410356524203000c0404008005614050b1a19500744101030009000c003501c1d01003a1034500800c200b201c41c0390356102c0e00c401d80580d80e503400b42c48507402c902525100c1c41c18030030602480320346402514000d0134600e020340f00c90b90300d0340804421182500015100d06a034100d01c800843d10503c107140030859810340c0c070000308140180d00781d002001c5003800701d4403c0d0104d103074003002400800c618081d00e0b030120300d4041201213060100d6440c4444625180d040c042c41000c3c4c401c01c41c041d40100119034288041d554100d862000c0a00c82c8847d5280d0280c0c4011010005901003100100c002c1d10000400c0c10182c8400f201c40c04402280c4107400200c1d81e12100213030b4082d840e41c004103041208002460400c0d214155240440c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 556617320 1250 556616070 556616113
    0x3070515070b0c070c1202010f051321020406030b040309080a080409051e090d1d0303030c070611030705040f050616020d170a1e050313120201060f030b070f02 70
    0x904690b085802040c8814044030441d400141c001840015250b00d542a42811100325a000c90119101010010301203002d64280e030803103e2078140c0d00860505d403007440c9105243d11000c0c01036058800c40d0900c011303640da08c6810045c41c0124690f07115840c180c136000d8a203c4443d041a8101e5000c0052080041e513a40d003201c00f968203000f000716194507000444a40810707844c4000701c207085c850381000305543c000104840c129003a03aa54030380c04c1071040388042c140b040c004041d9825420410000300c103192404000d0404510034080003031800d40c00c0048019540042d00c0d6000000c40c000780802c5424800c04000703014204c2144c00c0e9252603c0c0e10840032410609500003401540b0440c280d00c240b013a2410858200fa181000895541c002e0000042008951010340000c403004d11124100d2036115400f5244075540d0140341e00348030200383d25041c00c0307007170400c6404046640316072001c903072000800e003104015482056000490b0070025006828051903104a4046500c1451070030035006a07140071 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 556618570 1250 556617320 556617323
    0x204030c062a050a020102060601030605010f0e0607051507140f0a180f060f092301050304060b030d0906020d0e2b140303010e090604030c0b180a050304050307051507 73
    0x49008050300c0c110b00340c81408807a09009040b040034a14005100020861020180c400d90036180c1e56550180154225503003800b56a00280c1180c22014215000e10803e86503140010112400d00c1181d607240d501d05800380340c0c400108800441400706081d08414840c480e0141021480c0c100700b0040ea903000c081c010450000108000201c0031412030140f8042000640445511100e0517511110080d01d444407900da03070b800003402c980c40080c001880d403190302104035030a104100540902001110190400740081d21507941e0385100480700d0340c1c20010000310350103648075045014541b200c06800d0840c078140020602c0305610801c84644e507901f11282c0c01c0c41120402c0d62000c107405151010310a60202d00826000b0b040350200020003000024504840383c0d421306c0350f0309966141d1300507102c6101780c80c018003017400121400005114030f050b032640f00140c0c00c003d0755940c56060401e03260604040081d10355800c0020b00b44080d0800f8000e082c0074100a0b00d54030031004000c10054050722410a0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 556619820 1250 556618570 556618577
    0x80a05030a051b01050115090801060e040f1b180e030a080109020a1202070c0f2705071b0f0b070c2a1d09070e04020d0f020a17030306090a0204030c06 66
    0x202c60108000316407a0306000b1010000801456847c0c07150b10121082c200c40c4600031a1521100260726a0705000341d8082e1415100101d0140c1c41d42e941305001000b4030542150701a000310092161035510030075500c024a0b1440c100c6150000035000c3e601103503022950107400f6001001480010740e0000e110504545020000694034a00c9030f008641013986001603150b050300015107601400303001c1103440b0a0306e0406115901c1c0556030030113103d040c12307801e10456405100084400b040081c0d980201c1c5d2003641402c001c0380f02c0d040c8107000004d429809070f00320741c003d800c1c1c035840c414000b250790f940342c1c81405070070820000c03030b0903031107000d00030307c0159401d48070301103905042100515209019004080106902c00d00080030703495014102c404407101c41e4948510040003800e6101e24a0700d80c09190068181c061400c802d8030740c201e04030340c03009080c0d800c50500900050080410100d400e2400803402c040c41d1203061a001b0041040c00207811064801d005000c01d001141e400e000d414200c64803803c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 556621070 1250 556619820 556619827
    0x21c0203161806050108070906050f160b0405010f06062c04020a0f0e06070305040311150307020705460b0711031504051b130c030c09080a05030a05 65
    0x1001900e00861101184180c04100758006107103007040c1c40b2004041101042408000d8685004440c488812100303070f40016004502004900d01400080c001d42c10a10b01d61440d200c1d1100722810390f40c14680d01141c940742100100402d0040c2841040c40755005d010041c408145411401007110080f2214210200c908800d80e01c0c1c4c000400b4509090b02d40e001d0021354441c0701482c3c0113004504042000c0c40801c640c0d00383e10703011b868004204c8480592540781c0a0034a030968a600300414514090785800018419284080949840213544100e23415802028000d06110a07c24580d505903480c054100c0c80901500e000240040301d00010450301c0c0d40342c000d80c108200c00c0030a1007240d0f4018201000006002070500c6928007042e040660103500b11101c409090f0035882d41c1050072140588181c1081e2429000c40b01e280d599011001d90041c22140074911003511201140c00e0052900e000c070740d5072240803034681d420a5081008158040c00f40c00401c8454075420b46900c61102e0090401c031001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 556622320 1250 556621070 556621073
    0x20f040b0423030616170907030b0106140d0905011e020903010b030601080607110a0c23031906050705091905010809030c0c0d1a04030909050c130308211005091003021c 74
    0x20a818004200310120901c1d031b5007480245d95842d546107000c00c0d560b10203220700101d40c55003e145401e4000040d44003030740c82c0800c010070410050505403422a40d83d520fa101c0785010142844004029102c5280300699481c600410036007118807107094140241c0022004200c1e503400400c2a41d401445400d01411a6011044079400e001c07001c031009000c61000c0c035020481c40766925401b0f80700940071a503034148095003400c266030364411a20350101418402004030001e40030b40c1081e40c2002582c149242040c86900000f89071390008030f0017072248850b5803400c00c80c03580d1001c107980d0480c1890000d0f40c03400ca00489601c0e201e400074029a400307014158611000c0204a42c030b00d41d04281c25400a604a05251130f000300300042c140705024451f130402c00800c4010b079003001106c941746006079034000941c0c80c56440305101d8000000e11421000004c880103010000501c102c2d00c2006c101218a4115050508225805002908901d10002c0c1c0003011b20050712204131003480c072100d4400142c440c0006 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 556623570 1250 556622320 556622327
    0x240504020903010209030303150a0e0402060702100e030706020a02030105010911030f07050f0c0303040c08121b1009050a0506010b040302060a030b0f0301020412030e030d0f12020f040b0423030616 86
    0x1444000703501441f0003c10040144a20b00642e15001011100e02c1081071343d80d0404038402c0c80c25900650b000c001000390034014030b0641402c10204040c1e080002170032410380e00084c104111540058096000407132400114502845407074050300d090f4004015034481075a600c0d08900004129141d020807420100358114010f005075254204030092035a078421019040c1d0307480e034105881c100d51500441002040d05200481c40380c20301c00c2104403103403c0c00e80304583e0410200580c84203144501a00030000e0700110180a10051940242c00400c8095414503090349007000c140d00040420405000604c0181d40c1c00040b03a6102d000361a010400100600c00156004100480d559041d80300040011345e105160080350780040c040c0d01d4220000300300c54185901d032624040b804001a00c04d41d40340210714000d20160a0648503400e0041c1810061103260704142c0c8540c0100800f03c401241c00c0001d02041054401722940481044203807004d040c000c84d90750138015000100c0000c01c03401252281d8030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 556624820 1250 556623570 556623577
    0x8040f030201090b0c071505070f0e0d02060703051e0c070b0918040b0603012313170a0203121f060302220b07031707091215050f0a2405040209030102 66
    0x4004e2040c209600742000c1c083d07810342c4251070850710729000101840b148170032441a1449800c098885580500c01504c2c215001481c401c1080e0340900e442e080100541c03180e4014196561090300c2e040d55406800881c03884203d00588040810442002803c5141070080f2f101c1d8211090041910703150b03854800000c0c1102c2e500c00045102c0ca00580c2040306009044521a0007004160b0080000d240c1c140800813480100080c140c40412b0514041140b003111909a00c0c0c285000702154044003485210710403269000034002c6005910104401041b2070508424540241200b401c001d030b10010490403600300d40c2d01384107075410f0590206d942c6855016080e003402074420a0f1003c50078103915100c101d1300c9038002d01c10560000f07424011b035488510300007032414003403400340d00d0707400e8070920700302040e1348503489000c044400f0000c502902c1010300403030041500400a20324040c0b06441c080031624129942d00c2d10111030410020746102c440302070a06d0507410707610140c03005a41c031541079011901a21 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 556626070 1250 556624820 556624823
    0x3072f10020705131b020109060b030304051e0102070509070206150d0b280c12050601142508030403021c020610060e041b320a0c0501200a180608040f03020109 70
    0x10030707140340302171001d506500007800c0c1882400d0412101c0d0091080c1540c90145000b1690001e07070701511751030051103010041c0e222810500c11503200b41e8031480441e081c10380c01c1d035401000d80d22134820f0244c001c22400c40b2840a013029a410012049542c42e410450040034242101c0c805d03a20307120000240c0c0d5440d94100e4100d800e8824441001001070091101c95003c0c1403101d094548400310302e072076100714440518619544081400c000b0025000e4040e481e02e00c13807031258440301940080010310004051440345001790042c14507805a440a510b200394904100d500315007100040000e0030b2081428503003512114034090403c11107034030101d401001c0390300b285c03401c510b51004008a001e0303001160303202c0309a00c04008018100784100f4045440081c0190007030640c014401c494016100d4030551141c1405207001080301034070800d17120001103500c82584078003a000100c031903016400c4030b241c80e107058030000700c0d84c12680360a400810900014000030300a142c2c800c550780c1458400d41216038060b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 556627320 1250 556626070 556626101
    0x1020120071a01120c361e02030a0c020f0712050f01090501051b0405011d0612070201061e1a0313060e2415040e03072f1002070513 58
    0x1561503010400201105002c1185d4290014a0101e40c0300303c4000050900240e004003000009120076a10700c00c01c810035801d410f00c0355920034000c0c010051800758025070008010060b40d9042c180040c8041d00c00c08486d4906550241a02180134280042c00c541100c94100d0740003030034002440c0c0740c5c1c1418190b40002181750309203000ba500303228042d03014034050100340003035041d82c5612995408a03030041e481200d0108074051964a50860f02c0704e40c0d240c14020040003285000301d480906241d040703007a01c1140050795989410300a00700354105007c907290440c01c81c950303400d2400d81181c41010074990b851950b4840800403031842c2142c0103540c1040b5a0080c0c007070118803460007981c1d9540401c6501101000096030684554a801c120000d001d8940b25402c40036824900702404090521203c04110920041040c0c0011036000c0321210040500e45c5980e42001d6042a0750030700e003501d01504540304002c402ea40c2c1c40e15540001d017140848000395140d00d040d9803003942000090402c1808802d48 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 556628570 1250 556627320 556627373
    0x605031f0509073b040c09020a030e30040e0c0906160b10060f1d010504050a0e0a0e0f0604030e130c111204140f06190512060102012007 60
    0x70921519a44d11100d002c40480f0000c03460107110850001c242a140682003d0b03a0500031b01c161074840e0010702d240492404c0108480c2c4029514914007000c1c190604a003101030030081c00700e02d07101800c800d5401c003550b400c2c2c1d04013400c00c0718038400e80720046c0080710450b00c0011480f107151210350a482c80e201400c680141e0710a510301f041240040200c0b84040c880458900204449026411480f030703648403a0303104100b0300071082d0a0385c0d11508494209050020600000400317070384901c00c1e000a001840c2e1120000e0400400150561b15902016501c64001c110078030790060b00082c41740d84c029050319102145081c01d8001c24801e2645d041c0c509409400c08040b55015a080842801d064914200b1101402c4a5452085c1540a5801020310058070042c1c102c002e480d002500101800c40180744030700e8501030703d00d07110b0080003811541d0f010075008103201001d1449031000780da2001c1c00380006c0c81400c102000c542c03024200650826211071001c00c041c0700b402030030b60cda01010403006060052 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 556629820 1250 556628570 556628609
    0x6030c0e10090903080a0e1c23181306050301020d0603120207080c21030d0c021c08070302030a18050f0d0c050303010b1b120d0605031f050907 63
    0x910920498075905032464484000a102d58039120b0312054a8255940c10300c81d4031094134000140400390702401e8a441041807407020103880342c00074a09035415444030103050a0f00703551007014441c10b01e040280c0b01c0045c00800850764014a00811100040b6050f0900e070704218240d000078960760304584c0d015071000c18005000d24a40d403001c019203025100e00540c80c1e000c3d0904903920601b500800d1280d401007440603401d400c00130840341e88286032850038401c40d214050000c1c0f5642040001d42011611890300d854007580501c841e410b2007c40f50704100741c2c041e00c084c0180007840b02a0220080560010003c0e030944425409272074038220010101d0190880d83c18000d50f1100d0b2555400413500640000c3d00f01a8081c1500c1c50340c0552100142d03003141c1c80c1c50425000c6401003031500310701c107000310a0520301100503c010030201400b4407207151281281c10b00c039012144c941c2c10441c020351041010004115840302e8069000100c00c80c04916a0340e440340701c1d030428000303a02c50413400260202d00ca6 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 556631070 1250 556629820 556629839
    0x90c1209050d08130507180b18041e12081b0a020705130207020f0906120a031101202704020d091104091e0609080301030506070806150a030203060406030c 68
    0x206030400e030f80e81c4000c2e6200c00c02801040480b00500070807981c40000c0030003582604503c0e0280c651240310340045c076a12840b0101d99400580f0300042c1e02d4064074820081044140d204901d0401c3d91000b00c900d01c0440c59440c100c04034600300d904800d005a1350300140165040761041c2448442220b5030790703117640000c24042e54412071401031078420001c6012460444035540300b038030381242d0010031954881c0d188200b840412a0040c2400f604424240d08409891504103c40d02a941c030039524021b0705600011024211048810900c4000c8464264485004400815038503800700c02c0043c1c9220b43d40090724468100d17245081a03801c07900109007503203207001070345c40a0700542c0603020517000d10781c00c201084211a0f000b00e0003050801070910814590006662136121b40f4440c940010300700c3e2513611407a1080c0c00036801151540d1002040001003a0300c10381203500007500f518100c02c1d00344101003601c80c0c1c2c05100080010164007000060195840307030002c00c011900300079001203a0742c43c2c0c460038 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 556632320 1250 556631070 556631083
    0xa0509030601060f09050603060a050301060e0a110720010324091a010504030b0903160b090c04060602060a020708130f030b070e0604050f130c0e03190507090c120905 73
    0x15120780140800007440600525085003a04829515007245038144010017801d40c0019028580100c5c07058004100e548007489000054661450140f02a242c50b1701344405440c15040d046100c0300701842000c0c0045c4c91911100307280c04043d5160780080007400c004a0051080c00c0084c1c5030380c4410548020b0015201c02400d00303035280c414041c40008014a240c50b04044801e0500d40010303400c10003040071034400440e154020030400300b60781c41c01c1c0520a40c0c200044821409a810000440500040b10380c1084603503500602030b50f09200403464006c001e910f80600a00f50000c0c103400181da02c04215804003100c2d00110203843c110700003611203408100440e03031030004070b900410f410301054005000f01e13840c421611000303001d5840c00d801c020903c406901e0b030030700054000f00700c0041070b4104519401032209281e0940d0701c00040c110408105446c0540300784221004603c03004078100070420200307125050390059980070030484e1512208440018009100c4d0089501d000c400303500300b10300860754 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 556633570 1250 556632320 556632337
    0x10e07020708031e0913050a06050f030c1315030203061015110a0f060209041e060506091c140304091b08060d0b07020712111804080a03090c0b0a05 65
    0x803141c030240c466021a550741308640303140344e1400030480071211210164004080000000e080d40c001c1302005501e0000341c98080e00c219001588502c02070020b420080c94010300002e0480c010104d110350840411144a81c1075511105203031241c004407010300313805484400079070740501154620718001d4106c40c142d500034080c8031500342c2d1030280b4611991154021003e549000c10140240114954900361100c10129003292460307000d0082100a651ba44900c8982008050b440f14800103180c07046000c80ea0160003144c81850300f8410300156440f0f61031072030750041110700902c0c0b80014504183c1d010302d4100b03160040e18400040c011889400c0c1e60420041c94104c0030910045102e104010344d5000822280940c0010841076428040343e40311208a07000380303807070041d541926141d071a520b800d07403403440054852040884081000342004c240342e80341386092080498007404c20b940c4030a031030711810750a1410551606054014000c2e41a420002000d0b80d206159490b81ca02c5805481d540040c450f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 556634820 1250 556633570 556633573
    0x12050307020f01090e011401022a010905270411030d020f071208030604090303140a0204170604030804021009150c030806030703051f090203030424030618110909010e0702 75
    0x5110b5950091000505880701c00f0140c08143c3c0c00c00c2d100500400e14610701c54114070601c8400031a1038081c3c10802e0140220f10160b900700c1414200140142d10a42d01c032500451250729124100309000c008110b0200c2c03405020bc05c1c4c0d8032a420021480008140307c40c0d0325008000050488030340010308110402c183c1d1041d40c4045503507441c00420000c0c1c10102804190080000503020705d00741d485910300794481d040008590b0600c0300d04a001d81d000701ea024060681c00079051001030b806c5400080c0612400300109810324059500030550781002d00024011030b1040d01e80c0071414080c00507500503003680640c403c803561059400520020340c050b001d40c0810003207004140d9504011030340d90281ea0300000207080010701840ca1888661203404095100c0d981d80d1503440c016a42840140002d10345240b0314201041d613860b040a00c8648850004280340c5020810800003024078200702440d0100000001d0010301d910042d00c0b41e200e601002d45c0d01c003280c01c00101d0100c000b00f0b00e090203024590b0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 556636070 1250 556634820 556634839
    0xb091f0905150a020c040e01150608190e100c1b0602070605060d02090606220b030709121115040512070f080d080402120304120507150302120a0906061205030702 71
    0x7850002c0e034810022100016000b450079000a820150484100c90302c44000020b0b2000800381d80360405030441d00400000340c080b0007032243c3d54002170760140034030360001810400c80c1e40c42010035640c0e424252050071060f455200110a041c01003680c020304400c1d17000c3c0155544c0e03452401c00000c0d40105030403580c65280c1004506181048a4800040d642c05804040c454541c0000c200264110002a0100e00e90160305044403040c00d040f80c2e4000c14000d070350709849062814000c5c2018025400c0008104440d41d0000086003510740c58194081050314003242064080482c01058480c1e42c000d1a0045848888240c1c120717400240e5900300c804002c0d912a1103516074400c0c1d9141c8200b0030314440001d00c410046005440d100e40341205031030300d036401c0b24501680c9030542081d05501c0f0200703a400b50000581041141921240a00008100e02c0c0c03c520b0540192161002448060010300340305541345503d8080160035400304000d816001580b1000c1c0305285400382e0303079500490341240034082c84d5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 556637320 1250 556636070 556636099
    0x9061f0c15052a16050f010c0f050a050315120a1101020705060706110c01050c0a021c09061b021e15030f070f0c1209030201020d0908070b091f0905 65
    0x103104850090203d00c1203810308806210007084403580c40d0302c8240c5901810050982d0189100000d445040d201d80050111840313030340041c5085070000030f0005c0500984105029200350b01408035020629681813468a07500d8071410240541c4600350a590824224641002040000508003259510a9102021a0441c903004a1704d90844e4032032260044414400b030000036055400c28203000141321070389404e0082004081d801d40d00c040d90340030b000c6040020502c84081d8180106250707501c08034640c465190001d54000c02045a610654080045884501f003451010b1950140c00f031f90002d2008201e05c0d000300d01d010170441803420346849002c0c1301c1071003190a10010b007601e02c100503101c0480750703507965503000740d60b642e8100400310104454113024400040d2200020701441600d41e80e8100e038942180300182c0707081d910320041400e1200e010000c00010304006a0b0f2815603402c0854035840322043c401103030280381d0b502e506801c400003c0c84602c00707503a40940182c0484400301e0b000002202503 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 556638570 1250 556637320 556637363
    0x60504030b090c0906011101090605040f05071a030f0a0e06160f0c0507050105031e040c0504111303110307050402190801150c0b040f0b070c020103050901020c0c09061f0c 75
    0x7526020313008840c54002545540c0214202c030028510000007041c3c40c48140d0f118021100b044a045401050f992090f90500400b044810080d0a0790b442ca0401d40b103c402e024095408010901c408906200380007801040d031a802103a42ca00145003101c54030300707040d081e0b820601000304d0076000003000c021741d40f903625114032501c400302d0390410054140641401c00448050b400101100e241c5c000c0164966034030b041d1160078910490050602040d05820501080151441c4042e5003004000a1050b003a8450440720700004903640301d50070304403604030300e40403c0c104205540034540c428030118030342440b00c0340c00c0500001c095581c0d846900903a00c404c0540643d6040340150000203da000c2c6400004008070344850b045802121a2500c18200d0340e144448804202c1e00800000c81144403601103507010f0007032642150885009508080d0466a0b9a5480502c100910303c9814036501066150302c5a03040103510b181c061024589020802401610512100c002120002540210150314105 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 556639820 1250 556638570 556638583
    0x20d0f0b271e0702070807153c0315080a03020a03080a0b04020406030f060b03090a06020d0908070b070221030c0a09150309170f0f030403020703020a060504030b09 72
    0x20003040a41c20001003110000d403004020605080d11004049200d182c2d5000140c00b0b108a000398000c08280e410994003606005480d0320192001100c2228684407035003117802c0b450840217040345000c441e0244483c00e00d1850003e0100710001d850140d0070360006a1640288038075102010b6040007465603a058255210403441014005070005401100040e00c142c03030542d0007030404080452040031180c0080d089900c41e82c403940c0442d0f610043d07003a00914a010f58401400c0c911840ca0552034107001141c0c550301c0300100180542d5000030303c0400f45032190300140348640c004040702e8680c440c500e0444180c6500762151000b43c4224036103011454003a1400348a03e221003c5000d08603212011240c005801c65690003003403080d08000480c0c4ea400c1c80c5240e500b0001d00d942c000c24070b41e5207410704600c183c1d40d0440074609005d0410929001000840c04c441042100000c00303940c940c0c072400d040b130030240c950300002d51140c04a6000100780d54444098000d80e801050004480c3c1c960301ca081e980c4030f2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 556641070 1250 556639820 556639849
    0x1805090c03120a0e03060a05150a0f1505070602041e150203160f05010e030901031127010504030804120b070201052503090501020c16060801031a0604020d020d0f0b 72
    0x5001036001d02002d90444054032007150103081c40c2e043d8240c00c400003810600e003124088042c65845041003400040d4035081c00303010800707561130310170181402a0f00040d080320303004a071550355000d20340c00d440b03a1203541154541d580040b0219116a20b03840010891030342100140c3d4401d5600703402242e1820b901000c00c0d20181c40b40c0003145010800e04080705d0494000c4000d0b42c4a80c0c11160402c00300b00b0a01a0f0f80c0c4400c1640040c50f551603a0700c0000d0f04969138281194803030380d018031202c6401a150f45401d031140b00c030125005010310034203004990b14030031600010020803000c600003e14a82c3c2282895807240304500142459543d490204d088450407102c555a0491011050a8a1181070651203200002d40f0300800c01c0e0070b00d40c94071801d9134081c84060901e0b034044410900300024480316100a0880c61030400007551464580031400c040e0025205076800c0088042802962640e0446d0050075100307609644452146000d80000c0c64104280f03048182012004165031801d0703030903058a00c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 556642320 1250 556641070 556641073
    0xf060f060806100c050d0c02100504030203060a0513080705010501090f021207141b060610110d050306010207030b0403021011041508040221070f08010b0d02060d0f0203011805090c03 80
    0x1a51041e0803c00c2000382c0301203a00c10b201300f541410f80400c40c140280800e4003c1d0f9228400041007601c144841070906021a00801c00244824001690080303030803500325203020400b04050302c8000400c82c08804202d0000c04c907010004080080060640146049403210003040204005000d800400c2c0e110f8007141c0890782d40310300d0024a104d03005000c04103058803a86038190a08190071408141100c1c1544d26403655440201041094a0400b1302c0034074018003480c0013801c0305440d5840700e82e0303412483d00c18010704c4030100025603543d100300200c1d0010b50308a00800310508090501a482c1c13041c40d0b80c104800d81c2000c100c0d03442c480c12542160101c50356a2540e404184800c2d10840c5c4181014000b264490a14280980080100038648110b0040c000145c519a407420050070501c1c0d10316800840e150b414000040e03c1a40c3c2c802030003d01540644807c2d40da104c561032000c0c0189034501c1210b0340240b0110002c105030480c10300640c0d1180030034034200010785442808c646d6079125003c1d40760740f5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 556643570 1250 556642320 556642337
    0x10e0609010f03062315031c020307032304090501171b0103110702092e360e010e07060806090a09021201060905100e06210705040e010f060f06 63
    0x44eaa030380b141c03602d1035050100083d00115010040449002a1000354881c4050014440145801e014840040f15010441d01c1c0c0e50008070406900d03401804005000d001c4043c5210307203803001c0c40b482100c61a014040c1255110b03141c0410000905081c010202001078803024104c5010340002c201c2207902c0d968405a40030f40840004401a190314000050004d105010810060b21003000190003241d03681019240c410300f0700c40b1100d0240031609101c0d451418600d04201c940c80d50305000307c04044c80001811140f05100c004403944a0303e01d0910a41444c03c90110214401035006640941a4505481013544d413440101d0314644241c0c1c0c0e60350f000c2081d00c00700b1611583c551041310783e580302030300c1d2300d106104168019007103e20b61791101010035120f008000c0d0f1007000d81129405092051480112402c02c200403e9556901c000c05c8510300c44c40ca003031910440c40c100304100047c0030050050201030000f0360014041c00200720074092250030080c0c0816022400f4480006817002e603a92400d2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 556644820 1250 556643570 556643573
    0x1b061d0309090c0c011e050a0b01080f0609180a050c24160609210e0414041407050d0c0e010905061507030c08030703050f0a050601022d15010e0609010f03 68
    0x80c1e580880c600940b65035071104078150780c5159001b500c480300c6040e600050145030804016090390841800744e4104220385041004003640103800c00c1d0007c0080d07039021308917038035041c6030a030710001090350300e0303841c8507034425681044000100c45c05688420380304440340c900c0802c2401100040c43c803048100d8203003840400319840c1d0100100440ca80140b90106120060f9100e18a24040c08100c846800d10414441d1400399000384140030110000e40f810007680c020105540b08031344014000905030040e05043d12400c8100b0000440a00740080245146107180c0c600700440c00d200f1700c00c03044100c9900c4000540c0c0341451003200d100b280007a046440d01c0b255548000c50035402528120b061011110910740400d180c023000d103110f9042910300041d9420080f001c07024149000f055240443c1c1030104001103641e020901401c40c0031210000c1610b45182c00f04040401d0314910285010300c141418400e42400a00c0400e048550807074412000f0303240c0c03905106a04109000e11680c2c20074044c030400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 556646070 1250 556644820 556644841
    0x1a0a050405150a03031e090b070f110301060909020906040501080d0534050c04060305031b030d0504210305040f0305030a0f0c020c04150e0402060a1b061d030909 71
    0x6902400d145154a00c40b011500081c101c3c084940050380007a40390b181019020b210550b04c1d40320102e0300d04040801702c1c43c20711031041c0d510410f0f50041c0303040450b0750aa01005030a201800000380d004001f0302556854454210007480400c0081e8400c60000001c03c070306007820310816050300d07041e402602100b19071403825035841d48021002c0a00c040041c8543c000001c41829030450581038a00003950301002d401e20524140c4100e0406101c2c40c81c01c00100002400001203414100c01c00650060b820284001c190440c01000b8060882c5402c01007008108540308980c0145504400040c00f4070a05400041f4201c40303040741d00410350200d42d403484001c00e01800255038058891400416440303101c0080d001078500101240c400f5a21451000301c05260502a03880c1000c1c50307004182003e4500382c09035115800c003600c040d028560016400707204612900c83c50601281d2261011864b58036450074078018101c000c01071603404105c180c00603551030044115622148018507044154a4024414 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 556647320 1250 556646070 556646081
    0x20d05070b1605070b13020a0b1201090b010e030105130b0115020723180403091d011401020a0206180f1507150e070303050c1c0c0b0702100f050a1a0a0504 68
    0x100c20b00c80180040400039001d10301683c4541111005424410110720501c2342a642c650000042140c081c8080c1d95148a0044880c1c1191a060300c00f1802c4103071100182d03a00d1946950b86501542003400304640b0103d0b000001e1841c6105440d46001c44c0c1c0d0320140c032000300c049641c0d0000182c008020400071842038103841000841c983c0c07034070380885980800152040340030070001180b0700390b508100800d154001720360100401104c4540360035500401050a0a10f00500a1b88000c0282180442e072592003000100481c80e4044c02c81645c840c101150a02c05081d802180c80c0f148a0f8001202aa0700741503080103682e0b031250020500b06a8541d030f48a01d07900c0c0d42c0040000407680e40303810b900742504c1000204001d40c02a01c5d40c41d9203901c1030341c000b03003082d0550a0303d030400c0040161170580184c1c41229041c1c01c5030071078181d40c2c80752141507041f0b090060481c141c064480c00c1804458038082e03294000d13400390207401410013071041001d0b04084180c0a801150360f000507080c004001d40d0409400a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 556648570 1250 556647320 556647361
    0x280902070314070303050603010f0b010c23010617010b01090b1602040b03030423030a0201090b030a02040e011d0601020c01050d0c050f0304260702220e1c020d05070b 73
    0x1500015006282c0324038a070099882900001e07121824000b841c1020300c1504518052550148040d071a07001c0043d180c1540600002c202e112a5045000c0701d01d104a001400c202102e0000c2c03125507911030036107072000c1403e08210350315440d0041c5010301d17602800c8801d0881d003d02c443c1900f011480c400c0c003850148110320aa81080e168104041d003036a0520050001d003c0d014106038803176581622a0303400da5040d030740141c0a41c2c020814100035031f0704080004121940c0c0e6540507aa90303100c107403410103030040307a010108a8501e02e0010481210f51a041c0b401800c3d9035482c640300390f03100401260350340080d80d500d42c0440e03010032115010b403c03150410070001006061892510f6a070031900d01c19a1b0041318290380980030440c181c2c000d0568100010560000c8409840c00c21400e500026039014541c0c40c0c00150400650021001ca03100d80c0006519000750001e60f0418000c4050f03c481460310351603884018003846840035402802142034440580c1c00243c4000d066640d00c04000d5030410491a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 556649820 1250 556648570 556648577
    0x307060c1a061207060203030117010b06090d0206070f030503010611191b0f03060209041b020309061305060c010c11070b0d2019080f0c09010305100f060801052809020703 75
    0x7010f00007050410082c0001d24142e8002d60390380d85010311441d100f01c0101d803a44c41da41d04211f01002990f40300305c1901c2c01c1c3c0e1000c0321020003200d181e20024100341301d0701e40014510116016101d0501d90400302560482c3c1d4035403a445044003580c0300141e1544200c2c046021440115140031010500f5543c4c000307180c41210405002251710781d01c1e40c2c00790301c5082e8812280c1580000701c100050625014016818211502000b4110f070b109102a450f4040c454a0038050640400c00c0201d90510305027004c014400602480d0f500c58030001503502038a0000b01d2600411202203846145200014054084640c0802560305118000c0803243c05040d00d034001c150300569a4103c4005c509201000b42000240d00502c81965104050043c01d0094000c2010ba05d00d5547d0742007120f5199001c01315540d01100b440c00254541d00c840310001d10f0182ca802080c5502e91496010918540140085042e10800c80d201c81408040100d15564160400c44030000c007842c0103401c00080d00301b0b40181ca2040e20a0a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 556651070 1250 556649820 556649839
    0xc1b0301061e0305100c0906140d0e0d03240302060f0c070f0f060807051c090506090109060b0f0607121b0b0f06041a061809150307060c1a06 62
    0x7042c0d5012400075154600b0381101081c0c0400412800708110380300c000b4885800d0000d95846000542045918810348041c0b140f01c0e070100a0341180001184c00308001824200030442c0b040c00079607034440410820001185c0b50030100b08a107010704540151201148a410400e10704503405d000c9217810080080c04c50720780c188401c0000400a2141401801030954442002c1d0310b084004000403009a01c41010703c0200800d0009050384001160700d003084000e0080402c0d030703108400000400345460054505c1c001c0c601400b540d440190000312440703026030014400c42c9079070701c1044084080303000c14552014042061100180c07901b074816207100501e0800c111158902181e505603045c50013400ca50b4003416808020300e403004044550380101080d24100210b200d80000c001c0d000e2419a04144203450109403e403009109a48000d4181e5001c1e22000d2030b800c003001c07104a00110460750621a0140c01c00200e100c40c401e00c500d414880e04180c204518502100558400c64009071001d900a100d04 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 556652320 1250 556651070 556651079
    0x2030403050d1e1805060f0d1505030111030906130f0c060c0b01090c09140a051905041b05041512050906010602120c06060402030601170a09030f050c1b030106 70
    0x9200303251204655032038840003400d00201d8021803181c6900c2e0704080c00b03180112035201500c03403d107072826a001518902c0d90741c069414031f11014000c1c000540840750603c000710101c00701014407038040303030230641c001d100d00360760381114845a00040300d2100d403036400200090382150450303900401441c01850003441d421780588a40c9241899a086031000c50b0403101407070304101100e04198010403203104100107079140d102000384510038a12489200c0c40b17070301104901507a5006d01e5003008001c005c05242280e40c0f110903610411426101c0e0f40c1c03040b458a1626400713403880127003002e110300b01c90740c0300d034505400c041c50f0f0150a100d07002d1500402a0035090705080c90f06502c61b95025071007040003032400c1d600d462402882d1110501d40380600100902c548284c80100144558000790b0841c1e01503200d9581d940100c03588084040c041c405900d00005001d0210f20b242e121840712802a85c5d00c03a03031040c03407600603681d6200d03401d411415a4025100824842c51500c903c08140e0340040000ca49160345 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 556653570 1250 556652320 556652323
    0x14151c02090a0303050903061012150b060c100e010923070b0c1b03070602210c0706081501051206010305190239070509090a050d26041509030203040305 67
    0x890300f085000c00c0c800100c0042520302013000e90b40c01400000307607615075820a1011001406a144024480e054400f40c40c81035800e203030400c511065000e81080d4403800448007581e601c48150744003510651a0108070300c4490410b0140906203a0442c0840101c2903105030640b0350100c850155940c1030050103800b2a41e107080e4070040400369140d000030108800d440140e0150b4044018549201764080703c410822079801203050a540700f12039021200440701c41495584c00c1c440d42030100301c2e07401488004115107070052001c5019044030004c11380a01344901c015070340b03482035010001800740400c001890075842034100c55403103102400030b020030b01e03070400f1440c0982c3c021201900f00d00141d404000e403412443c8015000c60b6032030440690203034000c0004a41c40d030300725000d1203000740b0719140003441c0d81d081000300f0b00007954488100c440e1100901c2e4001c00210442543c00000380040942c00c008060200c5924051500450114a00d8481c910410300400610000320b081d40428400000072810 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 556654676 1106 556653570 556653589
    0x5090c13091103030f0a021e0a060e01200c1009020609090601021c031401080309030706030203070314040515070503041208040602040e070914151c0209 67
    0x72400c0c1010010070320240e032030f0103201c00206102caa240d908003d1030107001039420394110308510350844140d103c040740c141c480c0e81e1181080d280828944d07441540201d0412000161520082c0c032440c06888606c48403400c1440013140c540070000052001d50b805494510080129100640c005005402201c007882e01803c00c01c00041d82c0703a40200842c8000e04171a004641d41c44c129120010090945224200f603c48400c2000041038503001041e00c049860041c0a401da040c2848001c034000c0d00014820000c058a0b0055a801050103441c464021030156000d040c4280c102c81c20206220005424402000420401c00c00401c540b18102480d50241d4a4209120788442c18140007900842e0003c2180401c150f00b801200d9420070400000c68151314010f00072640f1100030006061041d084d0b0428038041000f43d0009010860180c01310245480c000508005040d000300b00e4402 = true := by decide +kernel

theorem cover : BRFrame.Cov 556474820 556654676 := by
  have h0 := BRFrame.cov_init 556474820
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556474820 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 556474820 ≤ n) (h2 : n < 556654676) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
