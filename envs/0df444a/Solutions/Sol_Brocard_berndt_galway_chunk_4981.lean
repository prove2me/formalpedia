-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4981
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:21:11.233662+00:00
-- url     : https://prove2.me/submissions/fddd3694-3708-427e-9015-e56b51468cd3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 895683453 ≤ n < 895863309 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 895684703 1250 895683453 895683479
    0x30c010e012a060e1b0103141611240a020705070b0f0705030a0e18010b250501020301090212090d0234082107170a02120c061b0c1005090304 62
    0x1900c000d443c0661760a0001050f0982e1101d09034101402c04240c08070075892403640e5904512540c204080d00305500c034007507030102c10341d0342903080c5800f03111042c00e0201109002c8420100c9041c1080c02c03903540e00011242240a07800d1301030031700d60001c00207000e452080030052a1402044401b242007101a0f55210700d1070340034148140c0021710b03d0102c0c085c1800d1541420011030501000b6640075810440b020606018036800c0c4421450000a4030005e902c1020a000c4e103160058000c0d0f65030342c3c41c0c1e035040d0701a60100038003015500541000a5404c1404140795102e180341d85c1c0075000400c40410650341c1d075900303402c08540f0011095086060f5145d030004550080580c00054442c45142071180240d09003103c4181148a00c1004501c0018a02c0c001a1900658444401d9219106060100c1c0340481d004108141c000c40000e00d07410802d80002d1451003854000e8a4004140c104a002c6c080ca0044441c2c03825550b00c600314020b240314440d04600d0707101d40d8900840b81000da86119981c020 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 895685953 1250 895684703 895684721
    0x1e071205100501060e120105041104150506030a05070905030609060c09011b032706050403061505030a061e020a360e150609010504090e10020301030809030c010e012a06 74
    0x119030315801117890790170884002a40e15070a80000c102529041e240c03507210315038a1401c0740c82142c0d10007803402c0e40306107400000060300e800340c40d89850f450145c59100003000180c1e41f020201d10914000600d5207000a442e40c420ad006c1400b030500c2d62140301c902556908074680b8141403080d0200340c0d0400c034851420180c0f03014041e80c0c50884100450444806a0700c0c050f01403c40031191120510010350018215400c5070391200f00091601d82480c203064050817140c0000c0d51500960b02c020040c0301250300303d40300c89040a1844c90790489810001d80c100d1041c0ca4580000c191080316804450362074244a2400d454071580040c1500020b88140002070344c80e81008801d80d5200e0140416800c0c60344401540c1d82091f00e880381751104000c0003038004d02880c800c0c2c13038440751034031711020303000c0820300c0a568141107200303065482c1d50f100d00d082265a04511280d501078442e9041c20390040d842021080c1e40180107031215182d00c151290255120070890314820b0710b004451000800044c036610030301e621 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 895687203 1250 895685953 895685957
    0xf07060f0f0c1403120c03060d080f070c120606090b010e241918051c0c08061303020114010f05040e0712292725081e07120510050106 59
    0x585c1c03825504d03032480f01ca0040c040140107a418405c202468441181d02020150061143d83d160401780318a1100b07485182002400100781000004030801220742103100a44685005d00010f0748841c080001c686403890020f00088d1461007004060038403004510003001d0000005001d080c8102444801303074800d1103125120301d00502061140d90b4025100c28107402468484002c1c01e142400017a01c241003045c00c5002080118212002c004110300c0780c0300242080402c0d50081d16092500c51050311078a242a4055400c2044100e0b00b2042c6044080c10b030340991140e9000d040c149000d1000620a554440c003181c843e040c1c010500d00e0001d0300c8440d402e4890304140c504426000611070013000880f8081e070100d2001814006540b1868000c540e11072a2001d211640124200c415403400000e1000583c041d82100001c000715014110014180c0f01440c2c2240e1a45c902c0381d504840990061540403d6600420302c1030100380340c10020410b02c0c50147c0d0449032003074140e000d1041220070a03802040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 895688453 1250 895687203 895687207
    0xc1b0f0f0525080303070302160b01030b040c1d0403032d06030515041509030e09090706020105100f030b04032f0d0503131b0b0d05090f07060f0f0c1403 67
    0x644004140e004011600503407201c00d40c02c1d850000c04a80d0fa01004d0480800e040d001b0880d01104403050036480c0c40b440d0003406001940d41d490a04091034101a202030340c020711411800300e02941c43d9a00483c840c0b94020300341407140e03629201100140306040c05446000219007000031701c0c1011800800010750342c40d00010b5280d1031403500354075140261801030740070801c040030000440d8402c0341040180c1001d03000452114110700e0b00b00d03007510788400401d9001c142d00003402154440051854140e0384d0a40080003d511144149007007442c1c0c1d0310030340482c2841c4410501c0010a0a403005070000d110781081d844007100044010209201114064000051218030140f600020403a203000d841d12410503a1541c24461505121900a404041c0000801034030101e044521100407030010655150752980b01e0000502c01009440151003115440c4151b400184882e00c01013030000031550207445284070101821800e0301d1080300341c1081018090010b6000703021521744545040c10640070000ba40d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 895689703 1250 895688453 895688473
    0xa120f1722060305040c090b0415031202160f0b070c05061b0d1809020307020a14160b121801271203060312050c0a1b080f010c1b0f0f05 60
    0xd8852941d5034030a0341090f041805200102d03c80401281c20341e80e41601c08134503440c80d0f00200d0054000c01d9685854407103a2070380081803003651a032122107504a82c0c2554520703056009403011104082c00781c5100c0c440080d100304020003901c0010020346202e00329411500f0356610000b800c03a002403411030007140b4144547c001d1610140400c00001110782050345490b0720613580d408400303201e4000d80514540c0000812803050080095101c420703801791141d8102c03088a01c10b5503e070030f02d62084440c000d02d00400821600284002d40d1400454000c075821103503100c2881a84081012030800d54070b55071050400d00b42c0d003400d00f0b20300c00180072103c0c8e8a41c454042c6011010030400c004c50a08051030140c041c00020745c80a00300c400c2c03030168500301d503c8000310358000d410300c001c1e000024a040e00005940910100c0150f40c0c03c111220a13043d150103201c1120440d0a0303d03003105000001a00301d40a201030b0f000d500e00403150305409075040810022036035440c180021410001504c07160b200c16120 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 895690953 1250 895689703 895689757
    0x80f0c030708061b1c0c0e15090306040201030903110a05030733112101240e1504030503031e070e060414060c0303040303020403020f0a120f17 63
    0x203002894008001d010910b0031202404400100c4c181c8104c1c032203c00111010600901e15001104220b03000c000c0001c60940300c00600004020b18a0b00c1c001c200c007601d00040281000c0a4070201500503015002e01d9956030300440c001c0c031001e901101440304440700245440b01c1002011034252080e0011582c0e0703007090410204403090702500c0c0f144400c421413a0f00f01c90300f001e00c1c810640c41d104500402c42034107103019014030b80141480c140e0b8030300c1c4801100b444820408401e9040791400300300c0c3da41d824401c9200d2803101007482070000200e50030503071001c0c0714201448002412448a82c8150406449030340f0a400c42e4010f60342c0c403000441c040085900c50441e00c8080f9005004d5003800140b10402e400818543c0c02148039080b1080c464a412002544400c411104540391000030749039a07143c04c0c580a0000c0d0000e0005074011242c07164013005a061218200d4203655074400d8041002c0341c0360340d074212400203050302240c0b04a509a2500b030208122005003002010700402c13111461041e285c4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 895692203 1250 895690953 895690963
    0x130503040315091a06180a0b040c050403111017060a0e0f0403090510090b090a03022d09060f06030618070f11030a14030414060118140c0301050d0606080f0c03 70
    0x50404404044c02805129600c1844809140c40c490640f00402c1c0d03540b41140c1e0060401c003803003a0b086420200d0440d1926488001441624410380c49802c403400342d041404203d0101c9842500814800c003658040000d500c10625481400209680c01c401d450715842c0b4900c03041554400c41c1d025600c400c2c4400c16400c10081e0019010580b000c2d50762035071800c001421912a4410020020000948500152074111860001d07507005403028a0814154282e685c0d40360555000041c00304c00a1008400c91608030302090003004014621050103100504100c582d41c07024081e01c0c1c2c01901c0c43d03031814078894021100c074072455540d140c03181da0014010340581040003e910340100ca8108005d0400b1568110b0a6043d841100100e019103c0d911f9180024284004074802d040901c11100009100d0b107803002c101c07501c02010f10b010b21000f44c24003485460300100780e42021001d4420f100502443c2860a44070140900842c000324100359214400303410030903808084080e94015996902c0d9074102000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 895693453 1250 895692203 895692233
    0x60306051f0203030c0c1e0601082109100c0b0f100e0c120405030d05042303070507210803090102251e240b19030302030313050304031509 61
    0x548540000700c05402522071000601e4181800720104208040600c10007003c5100134a4441002c0c58144803102c0d40c0d55180240f050ba1a2842a0051030301c0c844000d810f80000341544200d0b00c5d0400810208200d4942c0030b206a0b402044903000c140b1010460017034029010364201c41081c030640c10000b10301e20110105800117807000317660f14140b00312101403100f11281300c03800c0381104010351a10f01d855403c501c01c01c200607902c2418042800103000c1001aa68002890402a1541c0c4c00002141d25200d004002020304a5002003000b00000e55101841ea160907051040c41a21000b0a64660071550002c3da0b681160b69400b00718118a01c1240c10140441c1405a24041114031580c0d103044010040d00e05c81a00c00b8419035000c0101701c88414a00c0d24411010b400202c0c01405030200c100070048151140e00c078040214158003021100140340040d0783d0580e024500c0d550b191149245e95502540c821185e9110400c00000070030b405800011540000c1400450824414106100000344d421 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 895694703 1250 895693453 895693489
    0xd14060414010e0a090503071401060e0903030f15030d050421020d0816200906090702030a0c0807120831062a0c03090e160c080c0706030605 62
    0x1510300c241e100400d880b41102c00d1005058034a90b40e41e082c031000341001140042851001043c0d003410015800c0000c0c20320008403008014681e60741d01641e88000040e11050616041080403591100c0c0800750790780d004414016081007014400c010070305d00450b6103004000124003007070521214402e94606400c80310b0b0341003411041c061540000f0b201c040c3d0003000802c1c103400055405a0350340e44540d049a01038105480c2e41c0410312865101d1006c2c107081650358810014480020311130300d800c0c1402401003034030303500446c00c004c0070000513681c540b4104000da0b01c0c41010f000e03000002c5c4c90b02c1c0740c0042e188415038512619040c03840c203030b0031010700550f8104d0103007910410950041c2c9030b1781014180039400510105040d4002900038041c0420040e000c564400c044140c0e031005908488040c201e903100fa612002059a1911840702070b4000f900c49011444000051f070b18094405c00c0030100c05400ba0384994a4100210509403a03e5401d40c003200220703031940410031552030048070f01041e5180e00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 895695953 1250 895694703 895694711
    0x109050f071d0405070509010b0a02100c0503060d1502030408090a06030b030a0209060118061e030504020901030b04150e07150e0901031b03020307080313080708060f0a110d140604 79
    0x4002d100d11105403030040380b031484410400040a10030104400300c02801c000c3d0800040b56102e01c8104850f510444850000d84240c4881044a41891080449160f1141e40f03603815904c03818204400c2204000303003903c0b140800744808034214907a20085004a20034205581d4840d1404180b0080010b0782e44071009051a100c001600b58070b02203160b02a4550407940c0c105c89950701d00060791821503034041002c00d42009100421000c1e00500ca1210031a0305609220302245141c000310f09640f41124001c1d00510003100400c0011f59900c0300300c0c0c0261159083e060300d61582c1c0314071802c58580521a5100d6400b01c501006403604400080a44200614141040755100c0000c611042ca043c40300802985488a42d01c0c80103910000c00c40141d070b4010159000c51b50744040e6969690054803c01c00458000000042c6022001440c10111621480038080c0f590790350200b601c0c241c17402402d118100341c40b003014052a0301d100e0006c105220074081c000411a400070072242140c00700400c0e0601a03490 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 895697203 1250 895695953 895695959
    0x108030705030a18030f110405010b25060902030610030c121212020d09032601060c060b030313120b0907050f06160f0b0f061e1003060302120109050f07 67
    0xc022a00f1103101d0742071811840613086041000710f04a94405007079807412103481c0d0f040115144038505500c03000c03241444207980383c210400b403510400c00000201000e03004041d200f02041d01c4590051401030000141c10100782c8c0109041c02c0084625000d04140315109004211001d50720b07601514125184107040941d540c4e84203050710700e00b00707940705002c84402c10b011700328000e40407215441c00240c41841003292034580980109020b1ba007400140704680660300c0800a1b08013694100d1341c159a55402d140f01342c0e2035000003040c41042141e014042040004508101180d8038801800c002c00307040d010000c00e040803a69594080c03c0c80c513540d04007907410401995104145031a00008803911a034665110382480c001d4062158000c011050110f0004140070a004603144110000da1700700c441533450b1802c101c803d0b424100840d0100d11810320300c10890600e070309540840e05080c18001941d9449400007124603081c1d13441885640e4494511008019052180201440f0000028407416003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 895698453 1250 895697203 895697213
    0x70207080102070f021c0501060b18040e07031707050105101502010b0a0b1309150503070801050610030b031609020307090603050606160c1806030c140901090b040212180601080307 79
    0x130500e0081d100d450b10303021a0100b0040840c20003081742c0e000c1e00801481799201c0310003200e5044054807090503500002d079694541418001c04107054450b802500c003141c1580d945100011b08440007000d1410140020000901c0910840f40505429000101142d00c1c251009200525000e0410f04590401c1c41c241d000d80c0720340611500303881002c001503854100e4070400303003103810301588090001414130038540e605895503040c54056800940540b600e05455520090a81e8003d03100c841d0031100b80b108510a03184a03501c01c10600340d0040555054080c11181001900d64540260801d40d6001050016403504824001c000740717004d007002d00151a240300001e6850044220b036182050070f0100d02410003500c181500c0140881001c0c090958500e100c228000340070501003100e182c03490300c90100b100c0d0059603002c00c1c483c00081144403681e00300081d07000500914500030750030540a0140014054544060901c00e83d4a400d10080001c404900903141c154107034003140141d002009208041a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 895699703 1250 895698453 895698473
    0x2d041a0711010806191e0609080d050a0e04140a0b0d05251509080607140d0b120a080c210a0f023301060504080307020d082107020708010207 62
    0x207002400d00315290398039440802c1400c03003240c8003001a5004080e000c216000e1801448000c52103800e65100c1080d194101a00c01860900466071940e00c000500d259a038030a0340181454017207842c100758440b6000010174282c8105166000042e0200e07001c1000d003003118403501149000889015480740040d4480d59143d00c042c50018054810300304010342c00700c03901602440101088442c04c0721407205000c000b005e29100e400b81403a50301800000ca0002c0c0d1003010307032a41d00b100d0f01d04001c0c0303020380032080c241c01051070303141c0c0f10303007043d503801428907800c030f090103c100258001e1a98540c0e50003640d0300c8070b003130615811500c0400300c10742c04003a2940c0321050940d09079003000d00300948203000d0f422040c1e2070300e450301f0f0a0202c0e00400403105003010150080c1e05020804003054103039035076200c00b810f4505014a0140b00342a62051000d08050701e04100580300351405880300c14a007003c0e4500810305607880061030403981c028441031009071030741007200314002d00c0024000c500b40411350760f41c16841 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 895700953 1250 895699703 895699733
    0x1006090317071e110105041409041403181302030c1b010207120c1101141917010312020f010203100e06062107020d08060d03052d041a07 60
    0x581c0003031528070124110480307407040e81203002d2011a00c041040c4803403922030007a040f5810001c2d5020341005500410641d800d89a5030306105003410011420f2022400c0020002d0758080010148844440030502c010400010701d00c1003c585a42880288498401ca03d402a20000d20403c10000b02c556040c00b038030142c0004441000b1601c05030307d0910b0281c09404c401600c0390814240480e4804d401940c0341390806d00c00c0450091600003480151241d40ca13540c00340c400c0100802880010702d001010703581610115042901107481d41c4100c044480400343c0086440c1072444600d01c41c0140c04002c0340083c080c08100a51071480c1001c20041200c03100e1003a5207003450408041043d907507540042d210070000c20900c4020102c44040010142c1006480100c098051319000c1d00c816442030b4907261040e00082e00c25004a8525038040350300d42d01c94411800701880410107502c02d0700c0d4643ca00445032000161075034840e8213010040d4003401034010344500f00d480c10400d4000068130300c0c14544e26 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 895702203 1250 895700953 895700963
    0x603070b03011d091f0606110312071b0f080d1d0a080717131503091e0f020303160c0b03070e010c050705042315032a040609021210060903 61
    0x519140c548a0754607201175914503103449450100c898400d103003076502c050121102a96590741c4442030044030364072071080411a540304503080b03001541d202d029a81c41c0040b41d0444000511041554640380c010b0184800112058540001c03815080007060103500e4030a05038120410380c0580086055076103c40c013100040c1703120ba0109850060004204071514524640c5550903620032080d02c182d0100d4106001e0846003201402144925074801e105990a1943c030660046c4a5083d074013a02d84142103006080f00c03805007101e000c1300143c80620251004001085451021085038540b0800d80708140d040a004104140104041180d1200c0c0d4140306030020700340051107002c0350a10a040c4005900076507045410116440c003070068030441d0303103040040c6000514140c1c40e4541c000c05401c10460300b03280d00da40000c3d0008080e124003094004a1001e00f6103100301c0c90240d40100301610120b600400030551301068542c0c8050398422490303808a0100c01821300e60b400d162001d0494074240c00301502c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 895703453 1250 895702203 895702259
    0x5040b0109230117090c030f03130b09060705030c0307050f0d0801230406080c0411030601090e0a0b10030608011b05030a0f0f151d040f020409060b04090b0603070b0301 74
    0x1280340d000350344140641d000303038084012503d007000e201750307403082c0f0148154002d01c51011001c0c100322000c01540c03031081c0e14100b0340344d2840c60020104401d03001440060b03404101000b0100015500300700901c00c0d0041034001c0c41d280c001e10305009040241c50b072100441c6803c0000d0780e061445d44180c85c035066660600401ca000206100141b4400702c0c141c40d815000f614104011038000300009003205080c0e000c85040c481000301d140388401d180403c0e00c0042c04541100010302030100180d0610382d01031540e03031000a0b0100c40c500003074815107848520303002117562240705000c4205e085c080e090803180a0b00f400c1c0340501c000382008082d0310006050402d91943c400d15000401502e8000924402517420140042c0701001c038003030076082947c460340043c0c0c0407103046649001410b00c14203100315004a07088145449a40a11028040a490841e106135440e2903a0905941c1c603c201102c042c01016604920704c1c1c107900389440c0c044036420402c4014401e1004007e81d80449040300f07140c02c412a140a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 895704703 1250 895703453 895703519
    0x2011209080313051624110a02271e180a142b0305070801150c1a0906040203010501120b0a090f0c1508060a120215040f0801020405040b0109 62
    0x74100003a1000c2c0312080781c00721000041045400e0184220f80031020182e46c5400940f40e0191002c610a03025200b40350072080070340f00035142642a0b0004030092071b0021000b6521302e4601444c0d01c5044070440f1349403a03880190b40c1b6080300e004620364001e0002a41c29409080c950303c2c0340e641c91903580002d001c4640401c0441c241d000030301c000200d100c6030f42c414020107903002c400a49003002e12002100003c0c9400e0004412510841c081d504840c442e00c00e21b0f032801842c2d00d040320071010101c4103943e10384010915552900c04114110310650702e0030090241400c1610425007542e0040e40f100000403052111600030850300c0c0512074100440403400103255803545442d4090f51000b80024040003c015000240508a40b8200c04961201d5031068100e80d20042000704a03503041c01941c82081c8034140d03000050410b80e000310840103051521505140e030712509030804503c00d400c9001c0a07500070408200a081500034000152401d080c018201800e10042c00c0c1c07440f0606e824000c000b10604550 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 895705953 1250 895704703 895704713
    0x4180c091a27120f21160302010605060d1d0d0e0915060c100507050325030905010f0204051e06091012090b0403260a0e010605060304060902011209080313 68
    0x41c060380c020241008803c00104901d0b00c2c2c9900c904120200c07503003d034003001d490b058403000c0f03000001c218004400d401c000c00c4040350494403142210441c1559a03411001c900c81c0d4840c0040c2c40010301c485000301c0c0468030303510841c0e0702015a1281c140d065200d20005500701c2e030040b80d00c1041841c155152401999008405050000034040081d009000056488000030011448401140c2169414047d41c4c5940c03004a4680c07000300d42e141c45808641011515000d440c1083c1c000d90354091801090f0700819480e0300d8211008082d5001e1010741c005401c0001d400d0241c00c203271740b840f842c141c65032514240310302094540c85107102d0144204120508c41411600506a051000d42038020801058100d886d04103942c0005032401d5010484034002c00402c00d140c0d03181210507142641840c0306548450340503038068071b82200540030a540b9000f0100b540c1c0c9035a00510701c2a8060040410540345500014149117000380c1000007a5003490221400700f07180b030048903001110140125000c40c080c3c100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 895707203 1250 895705953 895706017
    0x2061510090e01090e1501030308040803090f07080d090b040b1207120f0606030b0d030e010f05040806040b07030c0f020c1e060d0506040b060703021c030204180c091a 73
    0x2030329020502d03800132481001d41c5d030200070084c10400031031b105541c0c06c0c0c0040d118841c091000900050305d8130700140009550001030b503001070b4036404445403c8040409035013010700ca40c110303181030b074003040061120542c842000c00017044400c44047c50282000d41e0712617507100381c01401103000041e40101c0d103135a21030007100c074004021600c00c002e4444e02a00000107010135110f5400000d00f40145c2c054076182c0702512030a001d07419142c1005400c40c0d50010b44101c5c11051140050120501001961000a1203250310030352250708400c0c4189402000901251f0004600008001c06040c1d81000f1540004003c071344110225030121490640c655580d101141007286550000740109091000941d142c02c40c40c00350104682c20b205141e07101062009034041e0010260041e88070340d2a10400c0d01844040051103c50780ca070241c90315440341e0040d061201d4115940c2c44265660311070038917041e803001d1910082e002143c13203181040c1c000d55109100c1c2c0200c452581c0000d442e0410380e5209005442 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 895708453 1250 895707203 895707209
    0x121406041d0a0501020406030c410c010219210b061e0c010525030b15041d101505090a051c0611030603070b0a03091e02100206151009 59
    0x21641d030a141443c00034080d4010740310b90000f081c01c151900141900441c90001c0f40342803100c809007603542e54010007000c280800c0c44840c034040340f211320444500590700100101c4250400150f079560315030308400021029001c041041101c1c1c3c0b48500c690644501c20703074114000f103032408210590880b00098a074440e240c040309064158107016903003c000840941500c80b1400000c0085a949040340a907500900d12001800383c5120950b164180c003c1d0702410002c41c1c082c0c02c1130b5112105181c0c415440c0e0098106011745141c49011401003540000304551144081502400301880d0415809581130500315900c24400081602c10980d155926250010300004000c1b440503a00e60584110006081000740c82c41414030440e098929401c83c05c0720301404000e4000d180c114a03000a1812507045104c0010406071551000b501107665244201500c000c0902d40c1c510020242c8100640e042540700c91005540058040000b400394480e81880781c0780e0103035030300700230020346120803640b214407a0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 895709703 1250 895708453 895708511
    0xc01060e07031d0a11040216140715050a08010312050d090b071209120c020a03060e030a080a05040201170a140a0606020d0203031b0f04050904110112140604 69
    0x10100030050b41c2c9034110300104811079441180740c6030b02c20701294944e015060060541d2a07640d0343e0321404d041680c01040b504414130000307560b09003e541d603040729800505524101f54002c032011701c82c0340f000220700c7c1555036032801d02d50b00e40380400380e01030881c410501c406030441034a032586504880c051011500c50061405003048104807078508000b210300141c6e101400a406240c0d2005010141d104a404251b001344131402084e102035421542d03600c50b02800c907000744294000100284160207081811208100070303544a4520032001418900b0050001c00c1440c1020309200c0540d0700080e9026480640c500300c101c1d16510a45204d001e021400d001d1031800c20f081d020080c801d440b65100b441a260903a00362820723007131803440c200d07501c1c00290f940d088641303c40720040c086046800c0007048683e0600e003083e402c150351480007035041c00c402c0720141e0300c40c6c0b44e84000060382d44e4070411411000c0d9003070008210b00040701c0c0811000c800001c00c00b9008c0c954649500c0f81d083e01006040030058044 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 895710953 1250 895709703 895709729
    0x9100302030d09031103160306020c070b070308040501050726041b12020307050a0b03010e0402011b120e04061d04020607050601030309090c02011b0518100c1104020405060f0c0106 79
    0x2c100001d01400c070303520094540c202603e81c0320b4400d24000c608004071600000b40207000b142185c560000035400408241e986104039070300042c5042c02c0700054000107020340c40da29541d02d80350174031500b550401800e240c100100c80348004030070328a41c1050100c84180a400c421550f486180502079841d6031403078075000d40158000040c030341030006043e0250500c01d034290b0f41015a2441444008241d80c0201640a00180014003410b021251600e0f4001e0051400003481c0864050350103c0c0620700c4001d8411880380e00720f0b06000c41e0007400c40c541e6080c054404002d03603868030303442401c45841030186240c06503814006c9005c1d59211405e41d840160880300352060395945e40380207843c424042c0b103002c04d00c1d41084000b42c8540d0045c41a2442c1d4181a54484121341c0c040c0000c49281d40b01d0002c0c1015001d00d214000b280f034a480340204c820100c25212090031000500b8182c1c00a090f503551984201c0c01004144003e44925040e1584441b079003182c16180c03030f4440491030150290b81c0100700c403ca50 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 895712203 1250 895710953 895710973
    0x101203030b210f0a0203060402120c1306060e1002030f09150c0a03080906090d0c0303140c0306130216060e0307050d030b10180b0c01140a0e010b030d0e0910030203 72
    0xb08190400e046042d2049500740202d82d50b2950f02d80340d521070f01a505800c0b420000f000b505106109044007c09542510340c1000240d0008040030b8051107103008590f55400b060041d02e402c45a10280c2d10303000c485501c158540715030020742c1e078824500015501c820224107041d694a40780b4100144d254001592a100c18070103e000da075401030411300f0380c0058070010104160b1400460818041d0610307070042c1a544c0190a0151180051113000314200b41d900c4507010a10307100b820300d0501a5203040ca03641d65a00f044020060300540000d906c2025910400c50f1252440075244001101540300c00081482c00e9248039090460041e075401070803074040c4c4100241015450fa0000d0a41f040455100f0549052003100326400340c0c000160011440183c0818014a682580608501c1c0745c280000b00e007200d19541c0480708800113807090845103440b000610702c0540d00703000e80d08a51000b50004c1ca030000c5c40d103100900040850328907500503200d001c08542242a518000c0e130113160007404032401e20311 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 895713453 1250 895712203 895712239
    0x4020d0207020907090b03160c0605090f1c09120309030510050a2306010806191413021e0d06050a061706060c15060f0901030b0403030b030105101203030b 68
    0x480010103e101d16a03030310000300014018a032000a454105080c181140e40780c8240c608040074900302c003000e000754440581c1c0096442d0052038883e944402c0500200c9800d04070880c5800047d24481e61b007100c07581d1880d00c01540c00742d042d0381211000c201280e050000c504099401d80441d400c082c100c3e01030018150355400b6282c0026008100305141080154524a010821380303074a44100401d411004020a8041d0311078000242c010b800107000c032924903101d600d01000e0708030039442140b0081610b1500712007407405400300070310320720f00c90380951400b00b890b00e0400501c40c880f035030b40d0700c41c00c03002c514452105030690110780944000340040e5680c41c0c5a1002801c031058048118004400580c002144c0342011020346100e01003c06c01400000c01c5071010400001f0020f207803503041202001103c056681e5204070394003c5000704d2100303009080070700700182035401094400d03007e40c4c104420f20031101550300700d10b070445d01080402c4881240030714089000d0f0043c5c15401742c0c00080e81800c080c6904e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 895714703 1250 895713453 895713457
    0x2408180a05071802120402060d0f0501060e03100b010929131e0510110c0402070b06030f06070504030f1509060b011b2109080d030207061a030a0813030204020d02 71
    0x401d00f40c402032030800c441411005a00c41d184c03000c003280d2075090105006052010245c101c44020050104030140120301c1d03038044030000d9201000007925801c41400505040c05401c0f541088160b041c8141c16400001a05162440c4136214985803a43c50440a812a04442c00504500d66511640d500e014080110740d114083c01068040e1042c001c201650b010749202803400c9940290a01013040e05000d4240c85a810184c1d800c03000e80281c40d000303002c540c4c0b10720013000c07524422000e0603880e040c1103041c0351038009614140c405540c014424010115001016103003242c1c2d01c400340996001d200d140500900894000d0209154100307680c440410210303400103000d00d0342c284d0f95004492081d80d09141024145d840c05403485090040300c3e140ca4041440320045180340c1c2c01c2000d002543c54148601d840f9400214030f00082c0d001c51240e00f04030380d0340038038401c51140140da80504403403000025220464420020282240020480041c01005003517900a41c0c0041085480e81c184545520281d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 895715953 1250 895714703 895714709
    0x3071e0e0111010c200307020603011e082406121501090c0203281103030f090105060603070210050403030627060b03040812040303060f031b2408180a0507 68
    0xc24150500c450512405200304d1001e584503642e960600710f000d03a040c4d06904800e4140ca40e00340003c10030f507070242c0c944a0045008040000350f00350f800c080d402e00318440b254a0340025206401c047c44070038185203582c98210104e5100d80307000c5d50a4907540f0004a801071012079202141c09070008100c3e42c08060407449040f500c8401e000d11001d00741d680101c2e04c9115241d240d40444e0100014103d0351848076002c40060001c2d42401000310240040c62491504111031758007030280140204007110001f0b0003010b03004134043e0390141c07d5040c6010040e4995240d0090880750300d540341d001405051090304150001c2607a02c006180c0007080c0c241044440e00940034940416041030f200141c201074000490380710700e070440340440c10840308080c000b18810015005404154803041c01240e1070785c0d402441e02c0250312960f030800c2c40c0250034491142e40e0768242d12400c4008945020810300301e1601000959002c49450080220f588940030b0842d03111400c80842082e204e0860500100000000c64800fa = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 895717203 1250 895715953 895715957
    0x10803031b250206130b0d06090c0c02010e0a0f15080906040206041806090f090b0a15090c11030304050601170d05070828080a0c0c051203071e0e01 65
    0xd20700a0001c140c41d40300d8507000409644000c449507264911000c4001802840100594a412070140341d1040e00501178010b041c29900018000d1001c801c584254401885545024004450013940c050100c450a10307020381130085140c3d080b032559a907066544040c2601038040050301d074440e003c040f0304441c0310600501184198000c59100080080c44900c81c0d94001c200700c0c0740604001c1c84400c0c0b9200207203ea10502e4603854042921001801000d41800891400040024450820851041300901703032400e032501c1c01ea241c0c00221003040441d0b0a48070b00940110b0b600d01c400c02e00b00c469950740c00c4182050300020041c001003001c04901d1504844d0b5030060f40014140b078490b0b150302c0300055030011011680401454000410090240501c40031a40d8484642202c10b8040901200b5020118000400c41c0c0100708558001d481140e500a00c503241015804406544459a61110f00344e04218907201000103607900d80314802120184050b418480d901c58989000548080b0a412220340 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 895718453 1250 895717203 895717231
    0x220501080d1404080307060b010c120806130b010801090c170f04020415060512041e0c030c154a091311041d010e0c10020d020a0b0c1201080303 63
    0x2d800000c10540d82a42d41440140d40b0b000242d03a2038000408200143c64140300c410038101000c54041d64129500c3d0000341c407000800d00e028801c002d030400714041134140c03092520540d030344d451768001c5886054460507000092101340d0803034107441c1d4440c0c400055030180413903020840c1c1e000c1c000b054203000c1c0e482070f50306000315884403158954102150113503100082c0b091168154600300c0300d001541040c0a180115403448140030030a6020006580a179400d00700c1540400c100b20154004100030190032202040c00b02b03202000520004000c5002190300d80d00a1810150301c41c0442180e001005900d0044d0785940c0ca000d1401c00c00300600c03000c40c4035101d400f0000e01007032200c60080c0841030f440384180504041e076008010046c21610540c0540702d200c10321b4803c400e00240309404d66841100010051983e10301c00700100076204459480464020071058058190001f842102084d40084110703610303542c10304220f074140250386449040b80594400028203550200044d03000c1c52065070765107 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 895719703 1250 895718453 895718477
    0x3020c010e010603030c0f020d060509160f080c19050901080a050d03020403030804080304050120040f240f0c08130602010f06051003180f0501060503060a06080606220501080d 77
    0x6400c0f18014440078021031154801c0b940007903848400c3c0644548010306100518519841d80c0c03080b83c0044902080e164403040604004125102d1207800404c580800744c10040d0419101d00c0d10703200080e554038002c140b000e8903e09198802d121034800b814015141d420a980d41e0108165221030014065400c3d000314800d16280c40d109000312811b40e509500c911000d0744465070355010030f40c00104103540341d540c2e42581f9040703410140074810a4058812403280c80b01d00782484124445440d0380900000100081001c01c80c2048442248192603541010050350401441c10f07180607661100081030000300083c44065041d0100f4540c0c00e4460329402004040848840070084030309038010981d02c05100022000702d18441d070841c1502050300300c00881000916640e0500c001c661060483d1641d4403a8024000ca08040004661081d0080420f1002e1450400480c0d01d668000d014075006000300703c2e1220240702039060781032841c0c0c00120100620b42e550211182c035840345a241d00d0006040403180 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 895720953 1250 895719703 895719731
    0x1230a0c050301140f040c1d04020909040b09070b0a0c060606050c1e1501090501060807080708010905070c08030a15140f040c0e030312010608070306030b070c1b0603020c01 76
    0x889600e000e9211646581d0a00c40c4080d40714108a159542c00407010f03800c03040d140c885004184070602c3c00c0c0c42c0c00e014103042e6080c0080302c00e41000310a00070b03481407014a0080d9200a182a0026002044c410072a2503980c000d90030b046490300302654452000400c4506030b0b600c00d0085007503e000f42010040300ea19a082107131248190500405194082c124481c40302e04811010000e91200400701c0c1c5401c40c5d20602c46075a80002d034040307041d031035440d4010041503401904255012809107054041454410406007031400180501c0d00a03da884000403410b0f40903194041440b074000b0501c541320300d01141707040040c01d5880c0c00c2081c45e02112400090200c218151a000a60002d1003022070400302c0040c080103050001c001c904000c440000149592018801407501c04e4104014908031742c18007001415411002d07000704205440c0400c100040381010450f03d4200c3d06525159119400b40d04104000907904412640044106200000e07913580550060071000c034001300a2051588021a07 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 895722203 1250 895720953 895720961
    0x90106030b0d031413030f0b060105090d0f020307230a170d03020c0313031a0114060f090f030d17160206010b0a0302070c030f021c21020c0301230a 65
    0xd01c03500001d60307204040002c1c0c003c00480f20400e10011005007848001920030800107034a902c251542551040341005011059881ea03500c0b80d800c0c2462858160500082004d440d10700c100a810703542101ca081c01156014400680100001d40c120b1110f1052a0030303020b01e000107200c8003440b42c580d50790000b851190110302402c500031420064203c22a4810042d400780d032181c13910075040d0204111041c002e20444103044040c40c040c0758141065136102066409454060f08080185403004420b0652651410210303209450f4160080341c8030000304002c20790416955041a516006145028007020703400014115100c00c5480710804030b031a00d90844508880c40c1c84000b005802180043c00000448030041110540e0391170018070344030081d110402a450181c004a6024035185131017415407401001d04401b2804160f03003000f5200039940c440c51704000c070a003800004c0f14007208403c1d09034000c0c011001f052201400074402e5188000a0340c013414508402d01710b00b494080c011610002d000d00ca = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 895723453 1250 895722203 895722221
    0xd0f2a030c210e0f1c03061202040b04021201150e09040c050904031412160f021506040906090c0e161b2102060415020a020a1e021e09010603 62
    0x84410201001c5030042d14044820a6100319143d240d00c840c0b82c1040307080080c86002039103680030301540012240250b8500d000c1d5100c41c001c25040090501941c042d0208a4441c2641100e0014015000e840805d01074020700090700b900d101d0a00002400400070342c00040140031550f221294190b0500030801c3c2d034070b4159405040c585030300d070043c055420003041c4140c01078001c1c1042c0610704070351168000f0a500890520010304500018450300010340e04a03503c481b211802c000555141c4030078004d5403800400c1517440e80c140c95401140c45521035a00099126400c8030007845036404030b04120b41c0c3c0d041c0342c0c41280d810542560001d0740c8031410820b40d0002107225904c0b1080310900a2000c030840e0b08591040c1c51290544e9451039141d40501c40807201499a9009130580d0b00d01800c11586046880c41032000a81c0100840342007554003168000c0541d17400054885410004004001c4c4c45081e450003e4016107941c0c460b14808144d0026500554811901d54210f6030329240c0072010b07101426 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 895724703 1250 895723453 895723457
    0x314010b04060905210a050106030308130305030703510312080903120f15011805040e011409161a120405011407121119050d0f2a030c 59
    0x2120904c9140303444c030643c0c00e101017140d88084440000c1280075041c0000c4542c11602030395139450402c10141c010021550143c1d0456101b120a030507604c010303040f40b00003441101011355480c040003180c1304000c20141d000c0030305d00c9000500c0c109200f01070400242064040c0244040c0c00408052460301040c00e000c0c1ea60080340da10350800d0185050b1001c850203040c00c1c0c224001031014420100490031603911a070b4410f000c1040500b401d074506160b11016003880740c1040512443d81e1800c07003c901c982411103009540001c0c14803110020a401000071481455060307642c8800c0c402e80001c00559030500c00101141c0e2801c0c82ea6407140d4410501150200415013141030185043e0080105100c0c4c1d44240100004503443c01e005056524445003100d422010032100e10010f18295118410803009000e41c80c1050b14105d100109c2c4000000b42c403031084100180050400c06c0c0f000d00341c000c041205074000c0140200d418014240d01805d1410500b0300544410b18190507102d4801d00503a51040c41c16 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 895725953 1250 895724703 895724717
    0xf030c110d0f09141c1106160201030b09090303060d110a08010b210d080601031506200102071a06010212030a0603141b0402221203030608150606180904030314010b0406 74
    0x70354591785034410700e403d0b94101d100d01140449500d80000a00c00c0c1d00c030740040601403a04601c0090112605400540e020380901c0c0100440b0f00c01c008105c9801c2001180c1c1d07040119140d140070b034112115103441540003840044001f07940300707054014100e04881100c101a82c1084117400030103090f400da99007110703070380310949100c245405005859080702041c50b010408010014501200541603408840000c0f0782c800d400c0310320022003c444140c808040001d40c076180c0c244d119410160883c5041100304035901c00400d4540c4e00030030400640544e6058001d4683c07a1000b400b50007030a0f48e110613909101c000259a201000104444106040358001c040d6a000d00701c1c140402134211041c8404c00384102000c0119001c010801d40d0000d0500c10380f03a100105c2545401029107000b0b600c44042070344203801c0d0501c2e8510181020741d00c04030039150140c8603840c000304110030b190310442d0260051008002c0c84285941034024841a65845003810166642c9440e010f502e0b00c02c80c444c090020f482 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 895727203 1250 895725953 895725979
    0xc0f0127031404030501150f060c02210a020d050c031c1715040e0c150406020601060f020304030606080309030d21090611120a050f01060f030c110d0f0914 68
    0x48125030301c0c0c4101100b04a042c035071280d448600712040703c0c184400700302907000308101c0c116000005001a050f640b0f007001050741245d000c01c0a044104043c00d02d0142103910008010408000d022a4541c0040081ca5246482d0a049856103603801400380207029001100c04116111811640004d503699602c564013546008001d5000e1409000e1001010780103140c81c4c403aa80d24050b59600019280150180010a20400c08e64284034034000e682c1503403d0204000b01d54003c00c50504440c0b650a0507906028241c600300d08500c1240c200a000500e086004201c40000002034540e0007406e0f000c882050380000303010b46d94644c0e05940c1c000500411903003800d00041d10303000302c24068841d507130100d48404c0e002d510f503070642c0200e0b03410141a90101c0070486600c04900850b500700c43e0040306030303903a9414150010503d040200e0380d4005d1689980f00d6924240c0b143e084540351040407000e542004085401c0103052403807000003c1c00041ca184404035080c0c900340140220103d00403e0040e034220 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 895728453 1250 895727203 895727207
    0x2b1704030f0c020f100203040501030f06050f011407080409020d0b0d0c17030408060c19080103030806040e100e030a0e040e0303010302102102040e091605040f0e030c0f012703 77
    0x21540c0b070480c0c2003089410b035050b003501d500c0600110701d50560003951300d840c184000101203401844091300b107070741840001c01150b12a0340345501c02000c00e1810042580066074625180d108024009002d90341c00500042c10850340c0d405031074000c5030340c0c0041c48001c150794100034000c0366110000c1e12a408071082008480d00c0011007400444100003581e0402c1d0f920280d150030894210b4018034502c200041031a10700000c1c031001070800c2090304265009504548000344100c81c000d000b28011070761440340f4401c0c414100412500c50a80712010f002030700c00e07030244a40301c1d00071100d14030120303482c1d4001854910302402844411603481e0010350642e80b0311303020440c91140b10504881070095241c03038140c040300303126440d00100d00e40740d8001da981ca203040103d45040c3e900402a10580c1c0009860340f003a89200ca08210454400310b80100340d403c0c0d0f1000c2c68000f0110803003840f607288000180310300d18620106103807000e0b40b0085c00800203102c1301c0607129030940b00341807039209203080301c52030400182c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 895729703 1250 895728453 895728467
    0x21090b07080d050c070c091a03030d0911030f0304091a122116060515210706050405011b0206160323070201080a020304050a08041d0901020421052b1704030f 69
    0x5010b06100003023100d00300100b4196486080c0c407104054441404509118800305101421001a0000c1c004001d40c0040c2c02d85070300680c055895510b486040054427240c0d00003848613000300017003e111001c0c986190342e13070f0703142e480940201000e43c1403030500d91041d400c40e0a5890b40700018030130810003440c0c3da60701001020001c0101100f003401e804942e50588038000d42d541459110380440404c0c0b0042d01e5914600042c6901400c20803108002c1030142c1c1e68040b107400c144002401040c80881403510000306940120043c480038084205054028035600c0380ca4580500030702c0000740e00151800f00c2c1061940b080c450081d003c2082d0402003483c0c52015402554031900400c01e464000740e4070755031416590321036400f190080c04800c0280a02055200980340c000088030000c40c5003a1410400c621101b43d005e401d0000810408583c00074058180b040382d4001c121901da14240340400300c500e8064441245031440016002d03128607035039401c0715420f14015030301500c4040101c460700404880c40 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 895730953 1250 895729703 895729721
    0x6100509150409050403050c161a070f06020c01200a050403081c092001020d12020a090b0a051c0204050a0b030403020a050d0e040b060721090b07080d050c070c09 71
    0x1241041000041a42c0c081c49031038003482c030a64403241c2e200c0d20410141e10302031382c2281007270300107600720b90400c11111000c080d082000d5903035080c0392719026542841018100c8906000e040705000150504103c403040d4401070500710241401c0305880c01e00c2102c1c0e400341c06841c2010740410001c01003400801c0d1080054042820041d502003007012007260030341c0c191122000c045413002c210600c51085011200d000c4807484c08288000e24240046100084c0801880004190342560000c1c030305210500c244098400303040c814014655803a1214402001c50384000749541042101502d5141118a90300880d000c41d000140b1400c081410044001c2d0642d00c050021400d611030b81181d4000540280410324180300e440d100c00f1042682c0c0300502c4240d50114030f19600c110000c101103000920041a4160800382c1c81036007207106802d0b600c0540380448260041c006034a0301054074001c0040c00c10040c480c0710150b140900c1140c9500c030194400d8001c40200411800c0059000e2040801e968400640c1c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 895732203 1250 895730953 895730989
    0xf0806150111070b04080303010f0816050418061508060f0c030406020913090f110d080f0a1817100905030703110c04140402041b0801060305060102151e06100509 71
    0xa5107a0f280240244c640c46076101e07403900d400100040100c88150f81c000c42c010001e0102408000d041102245050780301405032520583c2c0d581848664212007a0344118000d9000d02c1c10040202c003850f440c00080014403d9a070302d4480c42002034280740840d00ca00e40681c01416aa909603107807580c07420041c0d08607001c07050f0400300309420744440d1a1503008010b20700b400384146482d1503455040400c8500100c40036940540780f0840c04c4000105c84504030740c10407032052045501c869074034100301d8400803c2c4000d10101c00745031001040a600020040749549070b80d004503000d60301c007030000200351400c4d908060510b400900500c3d02180c041d103c6403250168030002d4a00c68075016000908603408201072012001d404002c2108505080c8510b0030302e11006801840180300307261004040e01c0e014003a4008150325100400c0e6680d0081102c107011840140b241606850070080510700c0c00c904220728002c41205101055160605c1d4412400742442c47c0d0b2100e00c1c02d001c0d00c0520500313075025100300d01 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 895733453 1250 895732203 895732213
    0x32c1503060105070b01120204060e090d18080f030a02010506030a0804090f06090c05070b06060412120302162907120e0f0d0e13110304020f010c0204050406060f0806150111 76
    0x300003170784090190f02807d80c0c18445101803a10340103001c21504160880b100c2954000207001c0c0301d03000002c00c1342000300070b0302e0700100c0300e122103403905c00c850481d5000702c0c0d0728440c0220f070041c82c0d4408009000f280170107034002c00c00e640c1c42d40201a5146407030382c03024110510030407003444118100c6d0802c51408014000101e0002d599180c000100d0304030140c030704001180860031100704888500c0e05078100d041252500e08007420041c01020001140000a01b107a61403165510814080d8040e00c40c5442c00c00311001c81b0542c0e5041c026141a040700d00c3c0303404103800a010400c1007140c83c40e010b00030300299652042d402c0495070300e000100070f8101040114891040f041c0c1c0700c044100481d241a00c0d00c1d960350114040301e8424400c0a800c060b100201c002d00380319603402101003c0c1c0640741d100741c0442d101e9075007040d83c50040e5034908010700080d4000c0c2c2484104820701103260400e0080301c03811841895000c7e6100ba803292103481c107071204000c41d20120391052154cc4030300e502900e10504882564 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 895734703 1250 895733453 895733467
    0x1b090a0b0d09050615030d0311180118060e0f010c0b0a0e0712051e0a0f24090f0506090d051806090613060912020f10030612032c1503060105 62
    0x1d45813160448818030401d01340e00760107080d81414084030803007c50394101440801a400314254050080803280103034020510b6546c40b1700c3e8031806009094055031400c2240542d2510401440c030740c00007014070f0145180704200300d604d51040d600f0324882d9800c41d0550105441d00d010550103880440d110042510132101e000c100c40030041c40c0342d80380621410090006d81001c40b140e4000c00700c4000d1341902c0b40c207e44443c5010031400c04400303500755444000c1745110740c51607041c482d40380c41d006a07000d040c0745811905010420400e0305040c40b140101308960141d0781c3c000940d07545428101401d0001a000d004002c4040480143c1701c01c1c5203002000340e400c0081507804503006400007206400d0750340780340000f000640d1700300e483d000240100380c2800c101510141c01203056200c4d82500d1600442e40c100407440c05d6482584128040c054007285214403035924103000b007881c19580d1410113451801c004420031241c40c0f08002e110881c01901054a1900c41c3c5a0700c04290401000f06050210030031400f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 895735953 1250 895734703 895734713
    0xf0e0115141c0b100e0406080a260f030c12010f12020609030309090403080f090c18060307030203030a0903050111030114100c1e0b180c040213090609051b090a0b0d09 73
    0x10800c4c1c0c4c1035070794691004115810401607848a034004011600440320507404103810850f0300700303c1c25601c110b00106450341c6002007011f1280d02010381c50801c01109008410b040c40d001089510010b81d465511641c035441d040d15450f415215103d5800908401d01d40181005000b4004055006095a05000900c030204104281c1110110700140d080020026004902034510350030100c0304009221480402c00072840c400d084401c20f469260504001800075a010400c400113558094192500c500c1d0018019201c21000d0108a8003035007450541400c015010054078100c0b00d0130068584a00d03c07120a12541440140042d010001440490f10120750140f07000020f090280c108600030f0002070038104a4004d002c0c0c944068842c40107803540c2140400501c074000908101c130700580c3c0e0340050401045d801039a51250140908005001450143c50703440140b00da1503040c0c1c0d200d000360021495100611600009a43c810207041c3d0034820a540d51010700080355100d0400205a0420b8683d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 895737203 1250 895735953 895735969
    0x6040612020d02070c0302030615100302090d020310020a0e010311070f031404081e0a021003050621011b020723010c21140a0206041b0f0e0115141c0b 66
    0x130503180d040c2030041c01c20442c14100001035000324161000f041b01c89407000002da184100c6140c45003015000700703030b6003c0c0d80d560900303206503580e000702140c0c408010051501d010b9041b6198090228526111401595000e80900d00605028140a80c90b00700d490350b8101c00c112002c0010340030012107883d1010408195002080549404001801909024820282108000c11006031f464022002c1350700103842d60702500c680c5403182c0c14040755030740d1900007040303900d052800981d110301040320320b29581d2001944000a801200c4c40344860081c1e00703120a03079452209106000c0050007071307180040014140c2c0010148944149003a001c481031507211855002d29040350070303002d55050301184080e95042407200c00200d0342d441d8400d0402125050180d19401300500c0505000410030400010707004042a903000b4120201c69000b03100d80f54031080c542d820003405031074495803c0342501c203031083c0034100f191003000151031014a0013006115810000c6c0210032819190f0b40c84906241b010340d18246 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 895738453 1250 895737203 895737217
    0x81501170a09060204270f09020906151608090a050a03050703260a0509030c04050c071e1a1803030c1c0e01020307030207110603090304030215040801060f05010f030b06040612020d02 80
    0x1088902588070b45811504940311f110400b00d00a103404041001070f1900004141d010b041180d00a0860044c0314035a285031103480000c3d0125803201000c40100007880001d0019040c00f0307a000c0c1c20490304c8105200780c1c001c0c02d01029180f40c3c4030b07220800004003840c0f07a10341640400e00c00d10501c00194110055150031082000d800b266021a03e40490b0404220012505408640c2402181080024900b0903c10580701420f54141900281010000d4402220105510882546800d0303c1043c1d00c41214809070b5a040207444014130410f01d06600105480c010205d141c0850300e0002c0442810a0038440614180d010507120000740714000800e00c0603520415568030003695402251416410039100030f01420310480082c000e100c2c454900005903025240d05a650401e5510b1004100361207010315403190308250f00707180020a9411440420008441d0281ca0f00c600400d10044140c0c19100211045030b0000c0b4180410840b0030310411030709152400092005150403090880e650a90380a00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 895739703 1250 895738453 895738499
    0x50a020d1a070c110d03050906041706070f120b030f07150212210c1902011d06130209060d050102040e040302120f0306010e0f030d081501170a09060204 67
    0x224580340e00320001107940e0050a82c90300440c100860340d554030345042c0f8a030807580141400002d41c1c080501450840f001100000d041d0b5072140d968401c0281284c1020000810502803c00440c00f81c900808203c180b51026499110603000e13400380700c50017018030b542442d50500c2020f40d4214426814010308001d8000c1d43c0c4003580c0c507012440f0103498a0002007008201c81c00c01c020440e00400461882c06138000c3c98a01144542c0f6500e584456900801340e0303c410080e0681d200c4a015030b015444082c40c0c440c07403903441c104001c030500c01c00d13190721088038400c0c03013207124a034030f0303801480c0000072158420340003050350010320301c0383e107440d401c90b042604416180200d43d8280402d0603010400381e181c0ca900b510303103146020420390900b240c5000107040c3c1c43c14044016203100c100d83d600c1030544280e16024003260701d042c1a401006000002c1658044849031340c40c1c410441d9948503110392a007002582e807650b1041e40381c0c0300c030603c0281266602501c03065801e0001045c1d0b5251a11001030000d050 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 895740953 1250 895739703 895739723
    0x507030225020f101707111c080601140901032c010603020a0806010807090f0908030c0706060b0c1510030215040f0e06150c01090b01170c031513050a020d 68
    0x501c10b000e1207190400d070f854400c1800380c101104c0300d03030b005036515805004090140041d844140c4103651791008040c80b400c00d40a0704010f2020b40020607851901000c2d140c1c0e4150b0140c541c0c50042d5114040c00e000060103ca003040500000c0d402034200e00c60340c012143c03074010446010381f11016070903100d400082c40b99450b484100250300d4688140d80107800c3c0d03480500302d070307516100d1095500c02c51440b501c103140351681c42c1914041101e81c4002c172210381048056549282a0041c0300283e884400308850042c5010ba022800e804082c0942d03241e036043c00000d102800c40301d0030000c044030004080c00000d1048007404401038a5104a510107a42c5141e10719031900e05002c00b09410034210780040d51541103001c10464596101159484102d103104606030b038541c0c11020b854054601c3c4900039200005100000840c2c121552201c1c0003078055005654240c8000f1040544485000182142038410070f00442d92080600d450004258880d00c03c84044000c203901049515089501c01e4a200e401 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 895742203 1250 895740953 895741027
    0x807121a130c1e0e190306050a020307080702070e011a0706020408070e1f050d031e11011a1e0607050d081012051c020c0901030f05120a0e0405070302 66
    0x60749503d4100300c8a41c080f00000c00380c00090212100001c400d10680344034940340b05201c80a0301c4000a1030f00a0f5042c4001e24100010320040e500c2543c983e00001d8032100042d042c41d2011841c441540c441501000241c2d203032100441c0c41881e01c54004059100800c54100002c01c14402440140107071005410901d00c1d00101c4141c080c40207100d07141c2c4158101202d03128121040f0000e050341ca0440d9070001c000040c0c00d084850314003401c000c5481186e281540340c000b40c4c110001005200142009001300405001c0c0c41000c091690842c03a08130015040005000740a145000c002d1140035062900b0280c0984400b49000121f1901c0c40c04100300006010541e00c001c0c10341e501504be01e0462000c1000269a2681c0d107904030703100c00754000704a00060030b44600c04c1c054100b0140008140302c1c10b0756103c0c00c100000e4070203a402114507200346982c0410000c2d9000940d01544066100d15000c480c04800744009000001e05050805a08100300d032070100720740c00b4501080180c1c603116941062 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 895743453 1250 895742203 895742207
    0x3150a17120c0718180606080606100206010504020a170c0403061802010c0201030506040f1409070e1314210315060910031d030a11010c0807121a130c 66
    0x51040070504600c0780400840c07400c420000342d10000c0301c1218250050903440b040141008207049100744482a0440e0320310700602805800140c02d0f100b2003800d4882a44800c0300300f1184845240b18040907030442d000401070323854190b01070441c0130302e1424101c00780c0b1131204421550b51001c884003c224180410184103008007485810f00282a2504000e0002115000a01481c0311300704020704260304e503030001d15540c995030486040c04032901e200340221005406d0081150b2030884078000306203d0f00c01c001981c1c00c02001e183c0c1c007406122103010308404490b00c0d440170b0344141036541d03005841071251386e456038030308105001d83c1c082c4070b0003c80341c9130708090b18941c40c81c20446030220722801003070148032499034803440009181e0215042c00210500c041c005002140e40d00c80181c40355000100300e15401300d81022106443c3c60007440204241d8109480c241c07591403040d0784071030000f80f00700c450f004d40e00087d500c00515040e05c4041501801c1c40c0c00d0000e040602260445820161902000c0d002c20b0303 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 895744703 1250 895743453 895743463
    0xf0206010503010212010504020304060b13020705011112070f111f0b010e210f0a0b06130608030403030507140d02010608070f031a1306050f011703030405070b03150a17 74
    0x7004030b009515082001d01e0030340983e10b060058500c00e981c000003041c20820307146e100840c0c1d40030160001c1d503c0d0140030403c0703000b50040c04056400354200044400c0c114420300807580c0801d80246580000e442c0c5c4101280d0013502c80380228288212005012210b10080003d1410700340100c3c4001c0c2c1c4032803c2c1d5510b50a0b15803404206050004012582c5400e54941e42441c1032201d074481d9020910010344400b514001d607a800603601d5000e07030081941840300c001348041c4200340940c2c90708101004049441c0442e03040b4411845a0741080c40217200203482200140200d60142810041880b8400001c50808031554100d00250795100c404100380c2505018040050540302505441d140c5144c03a42d541c000b00c01401c80343c0102e10a00020142c8842401540c00b00d500264204083e103000840014440c0c0280920040c40381982c030024501c0000200716482150321101031310116280001891154002500c2c0b0040802840d400420640302c1840440061142114820001c0d481448030760900c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 895745953 1250 895744703 895744709
    0xc0602220b07120513090e2803080a111908060307090b01020a020f01050705070b0408070f0305030d1512060504060f020901051801020a060f020a03050a0b0d140c0604060f020601 78
    0x1c80d001d2000030082034254210300d14101c240c0c01d116039a02c8602d1000d00c00c800881c1c00100c00c0c10701d071040002d003541c0009512004103104001c0424114161403426601000d0108010002001540020600300e000c1d0440014000c0d2249420f0620000620149110130102074040009102800300a054542000316600600788908200842851100000e485443d0040064020079103141d404045134031510866010700e1300f00d01a0703242c644d2184c0400d646540039100d030b01c9540c41102404140c4c0d5500c18640c0c3e08980c1e100d4000d620308089d03407207070740083d180003100b03031542d041d98440000e21120001c0c280c007205481000c0025491505142000c102d0b26040c3e694090399106000020081e42c100c411502314950200c07490690341c8140004038a410313030303440000702202d081620340036002c4045c3e009046800c100b510700740402d54640e61400c08607440341c4000341e4461904201c50000c28502d400c0d40000700311807000d98202ca07034290040341840e03129500c6100010b10210303040c903220350b040c096507000d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 895747203 1250 895745953 895745969
    0x40201080c040f050904050f0102041203020d080613050406060b03070f02151005330d14041e020102240f0708010501090b0f0c07060e0102250e070c060222 68
    0x10039042c0003c0d032001d0752240c09031600a0f00e07510701090607c00c00b0088001c442d03240d84029595103842d848400c0d6580c4030302d034084000d4401e210b42d5801c524040d010007840303600e000d0171008010f40e049541101070140a4011384d001a921800400c0055014000310f1107058503440341e1008142c0003500038604100c010700d02d5040b801e03041c140112100503080002c2140c1044030490380581002d1030460520703034114640d400c081c190390420030000c0e0088000e80142c60303e421341046810b140403590030b00d50408607402090380e40345804c28100014049640100c0030f0043c41144c090749265294044d21161072292403150030003100c100700004c200442c10b140e000e4200c0c907011240d540740c81c0020305555601c0c0540d10a5507000b00d0300d483c144001034192110300345910100d4204035035442005d0712211541e01898010700404880d02c1e484241100303944c039060116003144150600c0d0a14038090040c01500d184100902071134201c001c00d2460025058000c00121a810381204915011038802c40507408480 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 895748453 1250 895747203 895747207
    0x90406091b05011d0904032d0f03110a0206010302191d01081e03030f13230c1c15090b090102090406050409050303150a0503240903091311070204090308040201080c 72
    0x1629403a45141d446d00154941001c1c000400310a107011b50000302c0c91000c100301501404900d040c103070301131580d003155043c41d10200105046030780e060140348591121340d03025034081001040181000010540601980110840c00986030803000b804c0011158054540d0108107005005480341440200c00c0031165034510f24460342e024900b0b075207a0000030240b030710040d40d00001400520000b40701903101980000720079803000069049201c01c49400c41000004d214090711120b1500304034a104810511003240050880c0c07440da80c0b034100c000e09425912005446491210000b00640c00490141070900001740e120442c80050104880381680200d00c218104503081000c43c030044200e80e00604110707a81d44500741c43d0004605540320507800740b5018480c00720301c0c00d80d0807104900e84806010703200007801551200300600d6540d019a20075140e0214003a42e065012030659486002c59880405460b400d00c0707681d030001000c458483c10240d01091000c4100400c40d0380c04080d0340d9200c4110704900d8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 895749703 1250 895748453 895748507
    0xc09040b01060c15020c03070501050a0c050d2c030d290436031b12210f0504151104061b050a1415010b0306090406091b0501 55
    0x14000e4031040c421082800b41074141401400810407005452502d9020150750b19003c04409580d01e9200441c01c2e00c1e15482d0901003a4940c40501814400420640c0d032942001500c01511005080408007079000e00302059090003142c0d50396003040903000700440650340323821010030240c1c107907240c2c03401c4100f80c019224444050080d001c4c0c6140400c1006540015494041e150580c9013102044441d8445002105a10914121151513601031074881e43e2407010011111000000c50240041c0042c185420b00a81a03201c41c419900805083e56501c129403074104541015812500c000d03080309070b256145d200300414004010002044140c10102c104595a074045440c815030181b0300502c810010341c042d40074051160700818a0341c080d0000c040e0350100846103000c0789019110140403c142c042d2980f0b14803602d0414203c1c3d07040310b025000c15841d55480508204001e03d0003030040365503568549098002c5264610782605d40d84050003002512402c1c800007520390342001e0040086880a94410 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 895750953 1250 895749703 895749713
    0xb0c0703030e0f090a020301050f060f0708090315040f2d11150301180c1b021009091b03110a020a0219080d120506010f020a03080c0d02040803030105030c0904 70
    0xa41140d806140440001000d00d0014030303480703030701c0300e800c0d5000801c8414808161401d6005504841c03040703070b0346462440340d10144111405a0901c04600d06401c0c400400400c180308018410f030603004040d229905010603d6900e01c10702981e0a55104480d40c880d1003c0081100b00341c44072840840301103100c1e00b8075945c030260603100345d04010b050032050303080c4403240d8440f654110200004101015101d61312055042c44030010361200c2c5484904016044803000e010b07005152500004040c4210624500d400b803202641201015030f003002104070000a0500d6a481001c3c00f0b012514900020259000001015214640000c204520080103004482e640006003a20261740c191903002c20111411a048a11701d00d6a00100060040c4101070480d141d0100d403030f9029011070304081040342c640c880115400d4280b11510009a0302040154020901504403030b0340c40070040e90601c2c0b5011500c410740301a13800c02d51120640703600101c01800301d031074140301c2e1107030002c000d481c50485850f01d0303112 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 895752203 1250 895750953 895750963
    0x7030506100c110a03050c040c2c030c040509060a0c09060c060f11070b040c1d0705160606081605030f1f09063204050d0f17010e0708010b0c 62
    0xc060038000d0802c144803c0001401049440b90801442012180d40c0c2c0d0424580382d11900010f030b44201d107412215090580a10070f4840d4965141d040d1f001c4c00051000242941c2c031a81c6c04550781841030140021550703841d030194911441140c809425607050080000c81940ea501d4044020b1080d07642050004941c030841d25035010740c03c04c401080300141e25000c42c00402003020351401e200c2000984600b4010850650380c010b81c400d45103001200ea07160070b00c1031040c0d02422407034000c02c8014042064544180040c00c081011442c100e9030895280d0796500032030305c03941d0002c4001e0b0040d2400c0382d904508104014020b00b4240c0c0500a8803400481281d20344401030b1480030042240700702c0d01400c131019842940840c1c3c0c0b1480401076140364a401d000d021440d54082c6244401075094444610302c280702c0a8010ac0d030250007040300c2c0158407420b43e80784030304911250821650380320107441c418408075143d0092010780c81940c21410003020080000074140c015001c064000c005517074610800241c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 895753453 1250 895752203 895752229
    0x1020d18051903020d030c1e050705060108010b0a0506032d01050a1703030a0903020a0c18050a0207030c081602061b0d11060705030c04030b071e14040e04060b03060106080a0507030506 81
    0x1800040c1f28a2a00040c0c0740b0901c0c140740b0049442e41c040f0014841c40d0000300401915000d00101c80c81030303a0f01c0038002d00340c2c0c165189494211041110410050424a001c0c50b007041401c00b0400e030800b4100c000d0701140d118007102e400e14010040c010000c90511100c1d210150120a1801c4210121074403000c3d034034071018003c0742543c0e9039210181c0030b1520038131910304070960050088061aa64031070200b6490010040302034131740d18080110754041124422170300025490385503180301c65800d0300d030306d0295085260040d4440110f000c1d80b0006a59600041c162580c0d80c040d2104041c2c449140c00b4031f41149030001d54180720603c509a0b5140b01c00040071980700c1781030b21b000c50b81e80c2d60790100c88005001e564401837813114580c0501c5079007a00020b180044e001404c081c0c480c10007e0b14030454403d60030180d040c8444804000504c09031200d414025803280c043c130008a012500c030400b0030300e4030100364010400140320500344511001c180c01901c0d0006550f01e414040340c10000c000841001441c8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 895754703 1250 895753453 895753457
    0x30c0804080901030603080f0406031505031f020f0c1b120a0f03050d020c0c03120319111303030f11010504031b0201020a02040c17102601020d18051903020d 69
    0x700d4441020f038400d8200c13401031640195150385400344100c2025451300300c2e00403503012a003044e50080030b420440801d0411a48024011b0178034080c8064450154a4801e2603c10065020400b028601e00f4090045c0081000d040081030703088008006144000b40403c001032003962a080c0500300700900003142120544c0000c010000d0554615040d01c035449860b0300007403024004504000310507808242c0680a04080d016030341c04043c1900808000c2c80115000001d0380c203038040c8030600c56000d83c091000040075125040c5484000c1020601400a550080300020824900920340c0c079807004003140c0c8015280d00074000303070401d42e501400d007025078a03048111214458490b0190381c400c001500700e0a8015100304070b00460701d1001080301011541c480245591100820203d2143d0120700080f900390107d01000c40c1800044003140c86001a24480c0c1c544d02404000c1502082d4403d00b110310707403400160155040f051034000d00300f42100c090b0310b404035804a1207001294020803903602e042614 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 895755953 1250 895754703 895754707
    0xc090f0f030c120807080a0504031a0a0c0c052109040501080c030f0a0302120a210b0328110a08060109060314011e021b1903030e06010b12040c0b0c0d0906030c080408 73
    0x4903c108c0f91030103154005451750500092010555840c405485c0c000c030840c40c01400311242c6804140c60384d0b400910000c180394010320700d80074441001d200001580c1901d0807042d2501030b0700c9000405580c000c0e0440c43d29078100b003101888624080110305003800904000e020300d038003241c40c080c0d2181c3c1503040b82001c0e036034006409000280304d001003c15001d41e18641911004150004030020721071b400c3c0340e034020f1103400881d5070030506038682010030740c1e18540d00c06650205950707002d042580100740540c02851b9044082003004080c0702a50103058106000221240b03503041052040604a8002042e64541940302c1e40020f0f415000c40c0070540382107005130713a965010072010741251055000368254020020002d101300d40c0c0c040b8462038607010350780c00c0c03200002c0b01072a603413125020b11400110407410041000d6114040e424294807601451490801d2566805881130680c0a4130401805800008034051a1500000c10401800040c42d0400070182030a0b000b4122510107400a0131036800 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 895757203 1250 895755953 895755967
    0x30712110a06051005222d1e0207030503150a0504090c05090f220213050103030509030d0201180f02030102190c110f090a0c090f0f030c12080708 64
    0x38900c40c5540d11205044a90340001d904107000180402c1d41c010503040d01d804800145440c00744100180700407803030b814000d61016031034044000c24004c41c034040c2c2d014200c1c4040c0c021040e600c10024145c14400f0001c104203642030030b0152829100b04c51418590710511011300801e0340002941e80c0020400c0c030200c0030480d150001138001c0419484035a0180c14080c02a0400c8140107491040394000da0318070605403115015019503880885013800702005421141d02130f850103803a206000707400581080c1250130304008100030f9820980050700400c20000398020541800c0202c400c08403d9072000b0000d00d003504025041c418500c540c090034081c60a0000e03029503400b9030444072512456800320300030394100c103000780501c0d24001c011346041d204d6000400c1e8508242d0341020b4400c07002000e0080356942c82c41050010519051000c0420008040114048580769030140203481c032030007003030b02040c035610701042d403003103650002082203d03c036520300d000a546600380e42082d584004590b4807995 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 895758453 1250 895757203 895757207
    0x150c0f14071a090406090603080f16081306020c0108150d0309080d030509100204031a1510110714100c05160303170601030b0a231509090f010305030712 67
    0x60035030400100120540e09000c00b40e1224001045100d4041c0d60a000465480c8800821034a06c0d10014103c4001004651107400101008012603110780070384001c00744543c0c0b5074280a801c141c441d400f1043c800c09080c40b01030380400052601540910b850455490808155821408170fa080d440c0a10504141c0d10304040c052101a030190440030203c4141d42c1910034020f014140c1a5142442400f40d03403a200d481c00304a00840c0c060300d4002d0b400c81140c0c816030185211700712000b800c7c4011002501000307040343d510480c101142240603030340c1d00554503c0c0c241b46401c045560740909a44440b5504103075050b1a04100204802c00d10b0400d0030302c03014a410207d08000f080c0308140703009070b14a01b000c41095048406e1039854060148020340725a01d15005404803403070020b07640e0b4000d006007020400041044400050040b1003959412210300e520045800d1180c00319000507140c0002c1240b00032400e0070800580e201d040004508c00c2e075450341e00e64170748074411882c014140c00e040c0b0500e070f00214 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 895759703 1250 895758453 895758463
    0x3060102010f1a09011203090605070309081b0f060702010e0f0301152d0803031801060f0603020c0f0c1c0c0509090102031e31080c030301150c0f14 65
    0x7240d220703820f0041c40e680c4220142e07a0034400441500c40d0215800100e00d58040303d2251000d1a0306480b0b00000e10b081c0041075580f82c000000c11001c00c60350001c0803441070b0302808131001c20400f07409080308548001007002090900f40c1c02e9039010f2142440f405015030390001c0c452144903420388401800d400703040c001c00e02402503414106002d84040c44005a900980d0000440318840d1040b444000e8079600001104148035100d42001d0394030a2000c0341900c554141c070741c4550b038814000050040e07661029038040074140d600485c0440da02044c44c4000c040207000003060800c0300c0028142506641001071401808204000030741e03200580900c1c10003011840080c050400100000d840780361100c40b042c041c0d8000c5407403005d10140c40604a004be01850107441c09290f03580c00b201c0d036880007000b088441c01d5103507070640340c55103024820f030f80400c02e9a802440c1d44081140a143d0340d6040c40a00c1c5650b11001c0c40070410402104103c2021400c0d412400085980c090250095900b01c0109a13141c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 895760953 1250 895759703 895759721
    0x1090608100509070503090c060412020105210a0905070e070c0b04060e0303040f1b0e012304020d02070c0b12010302062d03060f0a05030d08190f02030f2a0306010201 73
    0xa40c3c04040c0f01ca0381e60072070042c0d846a40104100d40c80440401c1c01d0120714042c0b480342040821403054040700541c001c8000d031201040c90301c92000c014607c0f450303414020f10142c49101909036030f248424140002400410090225050500e00c107040c488230007004180301c040c0140002d120080071904016a6411208440030200c040b2500c03400c190034420007070b0520000440f010360342c5600d0400c12011000fa441300720303842645400c00c49e03032030181c04002d0205d41c00e100518480d040383c2c4d89061581d444c409404802010240180c49180615000385028425000080c16200504c4081c0c00d101c40300d509541504da0603108684c6502c203040400091074203c1380d14501066118500e0030091032070b0301c09988110001ca502c0b6095803982818400501098016141c054112800602c10350703000d040126040040032100d07000070014007030141c080750b00f000c0c41c0c0050300d60000144441e154000060f04d821440d1440703021102c0c5d50b1091a1006010306d2180d11501c2280800007955a038001e500c15541 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 895762203 1250 895760953 895760959
    0x14040e0708010e0c040501050d030f0e01050d05040c0e01080303010b07172109060a02042102010e030303070302040e06012c0103021b0a05010515101805300c010906081005 75
    0xc0c208101e20f002c2e0712030025100f001e0007036103000000aa6031921648070415160141c844500a0100c400b044415029404580341446010071050124880b54810b007807045028649180340390341401140101e042e070680c88180a544180010b002143c402006c40d004240d100202440724804070700300d2450f0f8010903e1218203c07140580f1800020680021107100b00303102d41c186d818966984040c03404900a50042c00840c8000765901400380b048003641c01201801410805c00345204000040e28591044400c440080d030042400c001e440440303604150031050900381110310701c0d81821540400c00034448e0340211501c00d400c0b01850b0b039010b54111500350800790007996403582801b003caaa5130031402012903580d03103070000043c94241003c04d031004142e8024412921801035202c03c880d60101c9940d50394500c450301400040966030000c070440750041044541001e41d07240d2066440a44481d00d0341012a004202c00c054140c0e8009034200660350a41408140c0ea00c8007440d104214030241c0240ba0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 895763453 1250 895762203 895762211
    0xb0a0e0105090d08191a03010f06080a030e0a03060501120b0603010b1c11060d1a0910030f060b060d0b01030c020d0917101a030610030c14010516031d03060114040e070801 75
    0xe90810f83d010030055140540080c00130703046a90184080b034982d2f00c1140c03400d804c50f210010000303206243e406108007000701a1000d82340c4945450007100d000782d0044000c032010b121950b003080303400c0910a85c8044101c0007044108444408240390303040c0b000f5400704003114605004104901104071800c00e0f180500041c0d11581406007002c010049140400c01c50201350220108500d001c0f400c1ca8841c0c11b6038205004003030b00d182d41c0d40c0510349c0c40d00c8040b150709440c0c8004034501d8035040042d00c401100400c000c1150414040094101c0d0014040d0000f10f41002000f14041e030b4005120301c003121002000410743c01c60350403103d07040c6540704040d90592800e000c4072075003417110b02409101e100c00407000c0d1003260f251591206d1286140c0e100042060341b40403030400c2002e038501c00c180b64400040c14003c1c90031190094a0480c810801c804074003007802041030050300d10310b0301d1040d000094184d00902c22941400341e1100550107002105204607203d4500110764042400400c00400d03088000b40 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 895764703 1250 895763453 895763471
    0x105030a110c2d0102031b09030f012301050603090c01081e0f071407050c131103040c0303030e190212120a0e010e01090b07200d0b0a0e0105090d0819 66
    0x3d0400190380035811943c01d580c20350141044040c802c9034090340704a0600d901e00080b40301c41690941245940d254140101d040060480e40c0a0042519103280c204541e030007035000890310010410306800650217440280b081210000c40001c245513080ea007420032541c1a07032034510304509200445d000c2d81c15600c000701130040c908242003a42d405501e00d03460300d02d000c601495040a41e801925405401c541c042c0000300001e080809074252450090071000c034080160140403606036000f074808a41420340d440c02042070544c0340c840c09802d01d00401c0600740301c983c550301a08228040c03250191080034a165203c01ea0502001100400406242d0903134036001c1c911409029051994043c034040f0b62010400232a540c821104c0f2416900c204801a08000d00c9032642500c12a0001060341007102aa078105115952441000c0001d403154030b140700c0c81c0c68080c00007002d441940446500036030400b018010804004130f842425901c5500c1c0446051384c610303034149021086032496604042c6400e0140c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 895765953 1250 895764703 895764733
    0x9031005040501061a0a0503040819050703030501090b0d1b091515020c0109090c03110c0d18140108040524180a1e0c0f121506050105030a110c 63
    0xc40c8124041d0001300900345e0f4408040260341040c506001c3c80c80c10401042aa15015501840c0c0040c040d0101d242040910300c21062200082072090b80415400300f01031040661502440d8050a62601c080c040d16100c800415143c00c4d8611004110040144d010900040902202d000030035240005002820440302440c0100090f03000d21107600c4000415500054000501e00545002c1a520329143d2441c01c5030b200020200540708a0805880d8007000c01c0b104031820243c5500e007058000b0340008900d48c0d00142201e82604150b480211515008000c20000c8039002e4000c8032080c2846035441c1d1b40ca14180d410520b003810855480c1c0c4801450002000c87d80d02090f11800024440c02d12414580705020365941024100908044074455104900c81c0030100c1c207941c41e442a000450001d8640d60706d40b1098016410400d142003480d1412408d000d058400615040341c220f101f082518148170000b007592000503c0011020345404800e001403540350108c8250643e00420340b2148240e402c1c00c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 895767203 1250 895765953 895765961
    0x60f0108060c0406080a0203090a021302041502160501050f041806151107051e0306090114010b070b01060c02060721030c020708061f0317090415050123090310 70
    0x102006441014000740c04001e900044405031341e0651602c01e61a13641e0051007002c2e601c010050051405090741e0940181c44d00001c44408521415026840340c1c10040e601c1aa08500c4a80200311342c044c014407582500c1045510003513600a18040f980d515a801c203106041c4590b5000d24a160000759072150240000d42c48031013601c04048903031100000180b401c4074070890201000d13805410020080000c0e20b044640000703d0040c260304503489004400c0024180001218401c5050351294107086810390740c809168050010111940c1c2030000303988444039069414040c100c01c6c480442c1403001599206415500c6407648101603403850f00d200c0e81c0240a103400102c680303003c6818860282d00241c00030440c14261001100245581c3e03440307100d40e0300c809402d01c2e0302246459240c040440801d0350300341c0048000e401140c100b41d844400000340012140441030341350060141c80c10a001c56a400040c04980415101c4854001d03922145404114410044003543c907108400a5200442403900 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 895768453 1250 895767203 895767209
    0x13150917180f040b01120c02011b020c150708040e15060703180b03090a1104020c06070f090501090e0f060f0402040821070804030318080d110115060509150c060f01 72
    0x141125900072000144030944860813a51800708044050100c10803c00e030b44100c84450f81440041440000158100200880107004c0310060300000b8028250741050106540442c1c400c00d00c1034a00340300c80d00ca10500b070245001e000c00d80c580c007070302055003100c0e070314813003141d540c00107008035640c0b12070340f40c00707004202014140c0301c85640f418070028200c0748207000c0e41d10441c000809490400519590701c0d949090b5460700c03640c0560309002e0414a43ca0822040d07200b110306842d0f10a80400e4610003401c00707081540020704011420344c0901442591041131354000072050140441c5444640000e10070540589225030000d01c01700b03002401d0310000580084050f00c41d003900f40da5420b20b000d16801031081000141203000100b008200080c07068030003502040c1104003100324a500c8458090800c00b1051705400041e414468a442c1c2c04028401d0311040c19200307184c110b0062401202030928021288624030895100008002c00f403a01d00032a0039240c80201511403904e4101a03003a003200e000c0c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 895769703 1250 895768453 895768459
    0x1c0302060f010605040504020d021b0a020310050c0a03051510050310140306040b07050c010906271205090a08060c0d060e0f040b1905040f020102061315091718 70
    0x38046401001c0101c0040d040e9880ca5464918242c04c007030900021750311000b500088141e0030072090b104101e000c9140c10494030b450010b01403141607801014a01040340425007060b6140c5020310040d080c0c1c010484a501c066400c0114031903035134034040c6000114800801c3d80160342d001c80405203036800b00095100d10140f403c000b215584414150920280c0c02004941680c0b0040c00314000c01d80e80000250b2112092130200d1801c01084516400c0d29104501100c0840d240e031100c60124140d41010f144081411218000c0d41d0843d1721407200e4010b61000b100288140014041120307160342c43c0c0c90740548040001c076491030800141100c4140d02110040e51a00e00d1708101140b03400030151654040c04130045407100a8841c3e8031a803075810805003d4201100c401031600c0c204040c00c4c0102c1c0d02c43c2c0c0c0200901101e00e0070718000a030822070300510a500c403007031040c2c00d040040c0d0300500b40e6a80340c2d2880b00023b9610083d00d88240d601000c11020148004080b070820004040c0141511b4220380c19 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 895770953 1250 895769703 895769713
    0x70b060406121208100b07060203130f050604111804020108090c06070c03020f15040603020f0d0c0c030e090603030f0c030c010e07150f090612060308131d0c0a050c0a021c0302 77
    0x5200c0040c440511400380e146c00050412140340403440a401031904001c00c100d01d18100811a66480c010f0fa4004030201d610350441003c100601104541d1030302d00b820300340d40d41c07a004140f00300300c4070487c0c0008000906100701400428807508080104022501c00034020a640714800c0c01d080407001e20303511040344503040c4100c100e41d0b1828030b80000c84140c50340c0c9905c41e0405003020310550103500722041e040a50801800480800061402450911420354950b0f600a0110b4240108019510a603450113100040140002c1d41c80000841e8403041520030ba107922020f0281100d4210310030f28804032010340c02d085202c001c580011030303020b00311164500d11020707000c0e41c0c0300140e030809501481c010105034042010842140546560500c0c01c442e0000040c0082e141e03038615010b5000b4024014980b2041201031042d41d40c90b0b2285803440d102452003d0051030200c0d8110394910a80741290104034000c01c407010104402c10000d101140c0c01404110190014804000c01c8428400180c1c018403031 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 895772203 1250 895770953 895770961
    0xe160503030f040312020a02090109020c0f1c030207061e0b12061312230409060602280206040f08241e09030d060306060504150b070b060406121208 65
    0x702ca40c6090b107412440e00b000e145441d00e103041c3c1c05142c643d8082d801181101401651b0b01451a40640300310380b0016180c422400e06140344c990400c00c0c401195003c290000d007000410806d081a040b86c624015070364400030300e42000034010340303608441081c5004001e50180c2c40c45030044d4100105c1503a5158003c0000c55601c0c2c1d0340c4c03806850110042c1c180d1100c0c01c000c542c0710303c1c0d00e07d40101181020070f4520a8036081c0400188020300c43c408280e804503040c8000c0c0624064080103025900c0109107118600011501222031100d141b102c03640c180008808548582d001e07107008082d1000d00c03d250694400d4201d468040402c440080004c42c0d28000c0350703244021500b907008501c8181c01c120b5024080d080d0000d00000900441071510041c814101c54000313074040d41d40034511803a00402c0162420303042c8004e45400e03d00e05e2548002000050101442180a0320041500400b040b859601d070140460010081034202c0d4142c044802c2da4041070255070003001c0c8404c4c4d183e696030003490303031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 895773453 1250 895772203 895772209
    0x60a0b0a181403010c05130b2109010e251404060b030408091323041e05031b0102030115030b01030906061e1a09281205010605060f040306050a0f0e1605 67
    0x8102c443c0b04840c0c141f11103061001c160040c5c09840317903c04440410100701280000e180900404981201280e9140c0d50304507007102080c401c00700c8100d110b035002c03000e4090001298812550b03601038402c2d03000c1d426821003015561031300f0071030041403e00300465590034641410083e5612900f58107020b07801c1c0880c900c100300c0d80d912445040780d64a24000944655a42e9000e1090201030019140c1c820925001d425844a6840307032046948110000d40e51034400300d0300d00301908481440203299074030610041058840210755601d141a203440c000400e500d0307140042c2e0050400e03150141420b85098404140b5610702810140c02c00d00011003960f05950711038078003135440e0041c088001c0d401c500388654081030800d800107406012000c0d038820401002003002c03044090150f44001c9030412002c10440500c8020302c1040e001d04025160f40b03181205046107042280720380c3c40002e0116583d0400200c0490141c3e01845030031004040500250201c52000b03540e4a00301310354010116106034000505103 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 895774703 1250 895773453 895773457
    0x81e0c031b040e01030609060b030313051c0506011203110607080403110a0206041202060403080a081906031121060703020c0f070f030611120a14010b03060a0b0a181403010c05 77
    0x380f01041003000680c2160b42e084040c14840c3c0c800c40b0225250520f10300c00e55010b0000e417031280c1116501c4c001c001c0ca01000c102286210040100e1034007903401c0d84501090010a1042c151446598030b01c540c0042482c084072503c1c404039101040d40103900c1801542c4c1d600a144601540c000d654000809004018480e1507410328680298464003c20040244800ca07014600a4070f0004025901f45552030715054600e9002010900c0000c41303001c1000715008500e4510031611110110402030b080c11561001800010322010500c40c40b601000d0f13401007405440014080d242d10415120f4a0810f0b40000d00039400ca14544545801090244103406400190080c201d45c000001012454a1516084005d142e524003038038110f0f40c10842849042d22050311507005000044000544210061020341025010780081c820740d402002445804da03500700c00c0c0015904004080c0350b86003001101070310b08034401c02641d090030380d9007000051544000d11035000d188200782c1c001c0c007515402440484542c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 895775953 1250 895774703 895774709
    0x82206081005150915032205061b2502090a0e19080903070609051804021807030b0d060e120922020f19020d020c030a03081e0c031b04 59
    0x18074100c00c100315510b45480302010300c000d591110f0b85031002c00030110b0a00081071410030401e040000902c442d1202007104c106522140001d8446000b8407582c038691204d0b4081c03c03950314944400d1400940c0c8248078111400f02d00000300350080328210109400c5c40595207034059220b40003000020b404811a1302400b00c3c101c1d4800060503859401600004c01d003a10440180c0f250700341400652481e031020081d880180c901515280400340c54034040141d0380c034486045956402c80310060000584a039402c500004003007803040c500c3d070368402808034002c003d1100b00c2035002800e802d075007050081c035034098106081d092040d540124800741804010b84030303120645802c40601d54000c41c0859803079144440081c40d21802503c0c00001502d540c0c2c4982010421100391001c04003440723407454042050505608190000e05000d0500c400000c3d2520004103005e81889002e000203514048031819124000078041d03541051420084165805908202c2d241042e0310540c00c8500b0145004006a07022 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 895777203 1250 895775953 895775971
    0x3120406020703080304051e0f073f05190201030e1908180a090c0f21150801110a0212030609150607050709021306030e0613030c08220608 61
    0x1031490f65540260f0b560004106491a014208254410751200360880b054040e01c10b00900d0b281191044280c189502c03603003d011441c0806419120311100480c07094140b5a042c0d04a610507614125440c092003070b0107600400600628000313140c64010610f24016450003a64104881071902c20b181d503845014208403c0c842c0100c1d840c010029014200800e1b02404003d801d6000310f1164000c01c6160000d034224965031a11402081406a4059280b8203040c0385407401408055111061180003402074181000711030300d4024280e0b503001d03071540c914018800213008201c0200d40308010300050300805090700042c001c04e03031959079810194060701d00601d002050071640307071620300d80300101c100e086200e642c0101e4144407410125000703010304001041d03041c03005640d071003002c03030604d40c03000080d0040014117185c4007060441c00000900264405002c1c003214820f01c1b05414183e40748601408020300001c0001006040c0901d011804101e4081404004130300c940c541030b083c0c1d8460130880e81410 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 895778453 1250 895777203 895777213
    0x204140603010315090312060b0702040e0c010e060a0203040803070813080a030f081018090302120f0d1505190801050105181b0d02040314071403060103080703031d06060312040602 79
    0x2081301005d030700261344d59100e401c1c0100501200039940c400d0f07518030f40c00070006c0c203004110082503051600403103659010680c0546500000e4800107480c0001a000c118000c1d000031815101c01030081084030064100b0000b1a5226900c1d8905170945501c090040100030181030000a24613000082d940305281c0c1c15220043c11440f5070100300e901c03850051911101c548001000185a11000c425040420000a000c10648420700300a0b152883d04101ca02e4103041c01c011000d60700702c1d0792040c0c55540c2440280441d0900d241c1240074800d10040d00842d50201d14070041d40c0d02c210840c02e1040c02c03141514024001c5aa840301084142d20a02c104400f070518940d0019204a003860315400440e01503100d06400c01a40180c004226007184d00215020509650181c0e19150108581030007002552004a609240e200109450b600180700042c9615004540242058041d401104110389804400140841221541540c881041c0c0c0c5039406402034507804a11482501c5c00c8074150f441e0303500144 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 895779703 1250 895778453 895778483
    0x5040e0c011b0f020909030a0f08012106020c1e010e12040306050601020f0102180301110c2a030a03121802031c0203090907030902150c070b0a12050a02041406030103 73
    0x340369181c512012140c9425010340e503c016a01d031020329019402840c000c5072908205c08018181240d0302d130728071060002020040060703027040108030301c03e2400300903d0386070358032503207400c2001e4054a1000807040c00340208445081035555070300b14450b82018001d00508c44405040380c1c40f01c8030694040c801e110200028800300c3c2e520f8100300d411500610442d80300c0300d0000101da007260058103500c4a09101e10602460a04d02401200d0300440302901c16841e0403001001107945a44242c409070301ca40c01e40c24450040000c607031001904010240549201d40028a0010400050198940c001502d00726128442c503814000c07100d0380d0703540038004110310303050705c0c5180f07200b0110000d150045100c00c00c0f845100f40c8038909094001c44480c1c501182860041c03040000c09510581801034140040c8850200c23818005185011640b020710300e140c0d5507140500c1107c042554040d580890742c14a801d00c009914aa0f0041c400c49000344014032540c0c01810402040b0310080c407001c0c12650407038480c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 895780953 1250 895779703 895779737
    0x30601260c0a020c04062702040b1602010903140601060f020a020a0509100902041509050618041d0f060121030509041a0a290c1914011505040e0c01 65
    0xb0041d5144038011140c0030840d50001030251201a0000480819808003016444081d0304002881c01c0c0640b00950915041c0400300c101da0260040703803a08441c0c2840e040c1c095900488100e405150040139050024880c1d01c0029602c01007841058001182d10300d94458080c40410020481a03000b042c101c84c5501e040100008444060800d00c0c00005000001800b0b80041c40108020030300c1c86902081c881035104040c101d807219600160091404205014418054000603840080100d400058002c00d126080c2c0c819040c4042004080c85803482482c10100006086030407a002c2a1a1881c03000f01218190040805007200401240d400c0c480500749103015040502040111070424092210382800103103440a5640491030003050000300044618010075140c4c00c40c0c143c0c0707541c9071500059150321545c61800c0e151540c05400c564900d0b03010840d181250000d1201d500c0000d000c0a010b070283c9203034025207403081521a61a082102c09024000b0602d0305900c00d05860345482c3d14115940 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 895782203 1250 895780953 895780957
    0x3030c02120f031804051608040f1a04080304330e0c0402070c09050c030c07020103020c0c040615020c03161e050904060b12070f05060a030e060903030601260c 70
    0x20100d200d0040c55106240071200304040c01c82c4007454190341600f803244c44107000840b2005071030444503039458543e8460407030f0041004c03600240d001c0e600400d01581c41c202441e8100c0b030304000c501d400744003001740030502c02d02001850056004150b401d001300d0f1a000c01000c40203083c1f095502400320015801c00e9943c07254003500a4140010560b0900400e500c0098101d9014540c12280f5020500c1d00780a0808030b032144550120580b0300f01c0b851030078204e8001485024601000f810103030009040450507905001102800b07201420520030191101c4a041080131030901d400010320440000020629000a040d890120b482c81d01490850412444a0800c20000d42041015900c0d4a00081e95107810851900c02c07400b580c00000c02d0380361042049400000000c21f20000c1d880b4160501c13540202090070012184200e5a070740c2d55040821050f4050030318880120020b000348010054034881c080011441140c01340d03030752007030701d40402150484a1a20f081d4020800c6000c000076241200c1c00c80 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 895783453 1250 895782203 895782229
    0x50105070207260f1912030c050910052a0f0610060c08040e0901051506070b010e060a0302060705010c110d080f0604060b0a0207181116060e0616020c040603030c02 72
    0x10a90301200c01c0c42c1c84c0f032031410340140303601d0600c0c02c0740c52040c1083c0890007804040d01d0095203000d02c8485002e020044c0140124000b8074802d040883d40758550034058000c0745c0c40b0008003030f2062510402c0211070303824051441208841030186017a1550380314030104506201d811700380701c002c602e00e080841c11140540c0e003031001c482c0100200008140c00800702c0c41244510348050002c9803602d841c09038046140d444822041c004e01c428025980014010711005041d40d480c039000c041d403651a04001004c0402ca944007a4001c40000f40d554103100040d003040c44250070580710981800c4c071310034855507520a09000000017035043c1010420030951094115040032000304041007150321002041c103158000d180840240c0d0000381c0400c400407120300c103544012140300e820800c80340d2400340766405104106014503000306c2040b400c1c0070816290f220040c0c02c0c00100884445140414100713142c3c20b42c030541d003400340c0714030440c0c12814640b50068006403940342d0f4030381491a11039801d01c02c0a03aa055 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 895784703 1250 895783453 895783529
    0x90901090b010b09210106051008061011070f120618080d0507020109120816020d05040501050309120703050a0801050d020607110a0302100e01120e03091909060f03050105070207 78
    0x8603201c034150761759001c1111440046000010070030f18000400c1296515050b00d84c00380040d42c402c00156aa0f100038204101400d0f08003141120b00001c001424030380c2d5908124410310007214007060030740082c0402245030303201c0c807810440342d1108240e04012400c0d190008255040c201300e281414403554205a40200f500d000104164865507207001c4180d10216400c00001c04003000c00c064050082c0048011614500142510860800d002041807080740505418031000002044840703a00300254103000188407409030300c4050901d0010441d500c46080b40700091074600c0041011f2808610310055558018a058a44445591000303050180c5241c016030001e02110000096103903210440107200c01582c5100c0540c150900140803042d1040c600341c1140d25100c1d10028100001044400d1080e00f2108081c5010700320075401c6440031560071080720f15081100002e803100380d10480005903845400240b20645da42c8004980d923181c10320401c4035820b0102808188104281c07007000e0101960 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 895785953 1250 895784703 895784719
    0x3110c120c16032004110a030e03040e07092309010320040e0606040e010524060c01060608180d0206390a1b1a1005090405010b090901090b010b09 64
    0x40b1207441807a080e980d10590358461010450a455122403207100c030b0724041114200456145800080d00901688101205040e66648030f40b900140810551b00140078141c42c2030b00d01d10301000c00030b241414902c40d41c01e02e4507901d14505070000041500b030800500c090089070482e13185403251944110300c0000219401d403019140515070300da074028411681030010042c40507051510a1004540701d8104000d15a4074100a1113494541c1c3c50140c80900385441d0b1081c82100500001001889030315801a030941c82e00e000003c615810040c0709100b0408142c846c8007003030700e2082007034035255111311580040e007064000405d6100c500c0404400c010703a29200d100460710003115182c1c000e07885054031641d40c1d03000c1a0407490701da2020042d00764055010b50b00004904035503c3c200c04d0180102011f0b0307000d401600080030f2030784035030101c0c00070700c0000e02601e8281468104a8001c00b02100c03468040c001100014a0010301400343c0c0410719804440d6590a0f03107028a4003580340c1102180540c03156071 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 895787203 1250 895785953 895785973
    0x20d1e110a0f02190b1215091e0c0705060703090303020904110304060617030403062f12070806030c0613120c0807081f0903021c030c03110c120c 64
    0x200115200540301c0c44681000c2d603074500412908210703a5504a541c10090b5505002c070711140000e9030484a410460350f03420342c0343d0711880ca1900140307040c0e10390400701500c00c000c1c091030b40c489011015240004000c0ba20f48596803a120944502100901700e1707803103e40812407a911917405445110302914005003030005100000d41540c03840b08809994030b40100c180810700907e8410003006124048030880780700703144101c00d038032401a0700c400f60030951b0303400055440b0704031288041d0050401c1c140c0001f0300c0d03400e4501c518103604081c00c007070300c250303001e100040e040c13030044000c0d500038a00200280b103145680810405254003840f009010440005030000c3d80c200208820606203210700b15900080e0304100c03803186410b803a03a101c004a030388a6000100b10403103514003c0c90301410111f0100350b0700c0c26420142e240c400040d0306441c81242c0b02051717120311030b41035116420862a80e0f50038860500c0e4003106500c1d234003901c8140d00c180c1d0828500702d680160500e0040039400f001c1c400359000d003c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 895788453 1250 895787203 895787237
    0xc020a0e0106020c01200c09130501020a052109120d090c06050408120301030f03301e06080c0603041e06020904060501171b12131101020d1e 62
    0xd00b81d1006016a1040c0048010342d03800010344075404401e600724841148070030000c165190b031950040d070301806aa0703001c600d10f070b00d00207001e07402590440d0080d5502c00c01040010f10300d41c46003c4507525001c480c1026100711031031140c40b030b02588808004025080c1528800c440660000480001c000d0b510342000340000d0f0b141c100c400040c10349460385500c85280424260900d004441c0c0c6400f4000200f00520001d03c102480781c0c82c20343c15103000302c1800b03032003125000d4440401001302141c00110f0f045145018a5411802d5019056501c034002010240e88100540d20340340a02049a0480d01c654940c81c20000013840d07104d405001c0c1401030220044401da8840074903481520f030b503074002483e50fa0700e041601840005110a207032030600701800d0b9038000c0c00703100302030510342900070000c0408202d101c0040c15541140c52105640442e8103040360f8501340e01c4900c9104568035000e07005000055030001c28144841041c940714949080e040700140b00d60181c0040e009424000c40800d40e1010b02 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 895789703 1250 895788453 895788479
    0xe100e0f16060930060b0301050a0c0e0f06180105040f080f0105070e011209260409060503032106041e02031801050c090f1804051507030515010c020a 66
    0x4815060400c403440e08058004100c0710080d00b0880c0c40d034400c2d200013140e0b00c450603070409001e00c0c0c445071010110346030b1a11401804030409065410740c01c0c003041c890540000d6100100f03002c850f4540d44031106100c0d00b4012100030743e8040c554000414041c01840ca40340000c0010a40b10516249180c2615460f1003031090005801022050b031001b50140d11501091103203542060f81d508200c00081c0310180004d2004006003200c4c20340c9900e03400d0650821562010381c074250180141c0e10406000030790385002c070a400a200d000300143c00c1440c00191400c0100840300201410412199070801d4482c076540507280142c00f590f00540d841030041c22001c0d00d00c41300b9100c1c1c0c040340000359032400c004c0c40002035580d82100c080c14591500e000d0040b00d001700c2c421501c450383c00f80c52603490703508218009151124036082c60070001051000b04020003001003051001050090894081925124011401c0300d0007148c004aa1081c026410425980180c0043c0341081c0300410500784107449001c596400e03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 895790953 1250 895789703 895789723
    0xf1201050906010311030703170a1701270203010503060c130b19030b180711011b05071203021201051e040903020303060a06080610030e030d2a030e100e0f 68
    0x10b41005005008100e400c800c3c44000341411030003484a076046884601e950000700d6100000741d2000145441524080e40740c0603100719080da0b4403402903946090241101038145600721001d04024004034001000d072082d02e0503200c01400601150780c1e1911188004d038084480b40c02116942000000e11040040081c19100e00901206007001e01404020b801c3d55140c2034614482c5011030622560101d041d000a58010040d240088608050b030b20400d0040c004903000c1c4084556200074010795030741220007030054178401c925490130500c40b07410440c1280070b88100c207960f10392104010802c5280c90300c0c010003180c003a540c81d54840304c1e0342c4000070100c4007c808210056000401003004030b1820040140050541c2c1c1089541c0d4a000c00000302d82e0102d4403030300c40505907500000040d2100800588039140004e000c200071020301c3c6209540c500c040e0320000151080b990711080c04981c405d0042e42d105005078001403101c00d880c11107481c0600494032803125a846500104000650204040390300 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 895792203 1250 895790953 895790971
    0x90f060c120b090f060927070806010f0806070f031b0c02030d020f0307060203070e0a090917190c060b0402040306021207030c2a0b181e0c0f120105 65
    0x502100225410350b40c454034803d10500c40c4904110501d0900300a85030711440c101c8003811141d40310202000500034000041141c401001d542c10104c0318002004010b032a80700007190b045aa80d0401400401c50754014070030b01d6040100403600090044805103116159401c1c0443c03901d8400d402049442d80380d48504000513070701c024070000d6050a12074614011a07600c040c01255003007030041e903a2031044e04001042e1035030000005445500c030304440c00e5009002804440c100756540e60b0070024011030300b01541e58512402300c2e40d8426032050104da82410410a481155101201040d1450115180d01b554081d849030460242a5214030050001d513200344001602d51003040e1804408400080910040c1494400c06042480c0c010400380c03c070101c501030684c81c0c090900005803040341d800c81c008040c00320752401c0c03002d00e110007069200300e603e00341c046681403404528008120004041000c02d0382e0480c5031010325078144102c80c1d910040780940303013001c02515045083e08460702203c8101d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 895793453 1250 895792203 895792217
    0x3050a03121103150a08010c05071502040302090f070305072105041419050601050303070c0b0f04081002090108090a020108010b1608040305030c1207020901061b050f2815090f060c 79
    0xf02c91174440c01d50b1700641034001c0200f1809810ba00c0183c07592081c41e00260041c8400c01e21003052540580480d0701441d070107041c560050809120490307a001080c3c5014004c01e0504002030451440781142e40c1c1011590300c00c03d00f0f200300e80030801c002043c0240050395452007600181400c00e004011142c0d503915900045a03100403d41002814984180c01c668441d030004c11100c4046801110948140d94012401550796000d480d00e80100c0e108a40c020f4090340102081610144401d6014281c500c000303032211520780d564845d01d40d441d0142644000e0100b800f00c4014030904008801078a0140610500900c03041110b894810150f081a40119201c0e44002510000128140112109058540030090400080741d00140f26128140242400c204801038280300040000340102c1c16031b50000c060342c01c4404000380e03594035011001180c1c104400281d20501607405444904180e103038100e2078003100c0c00403260411001d01200070060380c1c2d00940085080110b1150304c02d0010006142d21004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 895794703 1250 895793453 895793491
    0x106170906150f090f180c130b010c0b0f041a06090a020a0309080408030c19082502130c090b1204061a220f09030c06050403120c0203040302031603050a03121103 71
    0x511504418102006e50050801e503000c503100d0540c801034511943c0d2001c00c1480851004032008000c1d00409803001101d00144840b0754442c00100303008501881d1440c0d1140c00c0714199a07010312082e2915038020002e8000100203504590141100c02020b24000c24182110744a141040c1c00c0307600901540d400014440c035484400300949a102c1c1400e07500010403a203a502c81c50760b20f000341c000c1f0b2240e18401030010040c1200c0c03400c040442d298010b2003240b5010386410514004c020101c010001300b0030405010502d0304600007510301201174051a0700c9542d90790b0b41c880c0d002e06002540d84907610b4021070b0100702599442498401e84440740074040e5107610303602240069540388a000113129241c03090300008a507000510713261080c0c1040012405072a289000c442e14405981c101040900d03054655158a50120080c42200d0013101100d0740c01410914080759010075207c000c0003903001882034000640110074202c44502d0320400015043c207034440140d040d5004540c50740c00307075841c0710b03000f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 895795953 1250 895794703 895794721
    0x9081b07081014011d280c0201020903010b0f0607140705060c100b060a090e130602040602070509150a051014130302091303020d03110d140106170906150f090f 70
    0x100c1c1c01450170040d403010341041d0000340174501201034402a1480100482e10200016043c44031080da042117204002003411180002d00075000801968400d5080030074900c1e6074503210000d840d41410040103039150400d15542e41401c803601c500d0010f868015614005003d940b07940291080c140c010010b4501380301403001038001c030b40394034001501c1444d0900400c951194404c2c80711003030f128054008031041c0c640e64075005103456511f030700400c003900000b4040ba03495404940a0100c400542e105007035500d03140070404202d40220801504200b0b800020440b40c13a0814240b804010355083c0903045414407001501e00e58400341c4d40c40c61a0b04e040d101007086003082c0c06502c0d441059048508600141650000d440700c0301c541d840410582c03184c103548814203101040b2000c081d031405080124201d44104034503003071400d10402001c103040100840c500c44580941d00d00c030300b80030301c007805490b61350414603410f614240690b6030b044503044149408a481d070320400c40c024482c0070f605100c5450100302c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 895797203 1250 895795953 895795991
    0x10050a060305130809030a0506181605030d08070c0c0806070906080f06010f110318030d09030c29030403030b030d050a1704030203130b0a1209081b070810 68
    0x1034401c051800d410000b4012010a81005155010361078559440100b40040e01d41094040064510f000300414040c0c0500996501e400600c0e8210955a1400e000c100180c11141c00744151a0550040d6041c0200e03144120b030f203154400401e041003e450070003901c4a03041c0051036048010194420800d202c40c04d9000340641c4000e01c03207450b010710b90746460003490f001260042e0000e41071082043c8030080381c0e40a481d810f5025504801102e8480b8503000415100342560000140030b1700030958043c44e46403080c002d00302605d4110103400c0c4094903180300400d000300c02011000201c181d0320223091070760070b08000a40c001c501955020030984514010113043c54100580c820a000702004443c200640101200c40d841000d5603182d050759945050036401e622a12200d1140d00154003c0404c10044c01806030000007055600d410507640c1284551040fa160007801400f00c0c1414080d41203120820344030710500e040041c0550b0001e582d0380c2d01d4107282010302080690a2030721801403040154100320f03 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 895798453 1250 895797203 895797209
    0x8040210090e07020f21090f0102010f0e0a060606020a0206040b0306190602030a0905010810060c05012a0e101b02010e03030301090204060305090d05070f051525020d02031c0b0910050a 81
    0x6440342c0840c0d9400091006c0344200000c80c2d0084010800c0c0701540e86c002c3d80204030981030040180300c10400c007100103440d00040103080318041d2521001080c62403002460500301ca41c0600410300d003e04201c008643d48d00000e0003690b0141c0d00e031861200c07822000407540000d208a070000d44d1117000c0080c0162140259410090401c0042c0d003c000700c40300c009006c80201c0c0c003541002200308030b150070014050b1054180551080e10400c240418038003035200c0030315140e030340d99941040b1044c00c40200090340307401c481014009140708179020b062003034480740c0340340355441414000f540611400200c0d04580090b445004455408501000f6044e007600a00d5480300001020304147c030586507001d4000d014208015018074504107483c41085020000b0075210f001c0d0f5101c0c2025443c0275011a85441a00d0301109001d949070340440c1410b5000140710307103581016030055030500c055168150403400c803c00803004140d8441c1c1c41c08a181d10352150a502070040031a00d28055401d143c00c2c441040380d154 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 895799703 1250 895798453 895798483
    0x206190e031b0d0201051e070c080105040c170a020301060b04080f120a030506060f040305060a0b01031401050906032107030207050a031502070f060c030912090608040210090e07020f 80
    0x20038920051601d4100610014103c952a0044440c1d0004a4186c0508000e244101480c09480101801110050180140b0801e010307640952165052420f03a9420340d03005002d0340f048001449072280303159194001510030022101c280707001d50002425103130f00b540b05079021580010148030052080c0030074807112a04000900039429000c56112041c0f1030109641d08056071080420066500c2e0000c640310710708405119a1a80d8a9040040c1c0b01e290542c0c1d19080d1510b4130350b2101040d4000d0154503001d03c2e0300704000d110f5030310780750501105203001003000340e1500481c03e07852142012607100102e5100c01d40140c1c0c6d1961540c2ca4082d140060941100388200c0c4030710401c0000034136920f1103145290400c2d1016071900110300d0602c10740180000020081c50a002c1034503c265403552006c1e0505005183c1009c6100e1140d0b41a901c0d0340441c00b034200003038214030010307015050646211102da030300c524160b1001c5640f036003080801c100584030318005170003040d04100b03600300810154a500c1010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 895800953 1250 895799703 895799713
    0x2a1905120c030d11041a0a080a050f2a04031a010611071a0906160b0a0209010903140a06091a070f0e040c0e0a0f05090c0301120b090a0206190e03 64
    0x40c20490b690b405510041c98081e601c40c8040c000000b0342c002507070003c16290412a44c004465002c01c202900060404400209150700042d010f9403140105405055880c0c544055520707107144183e005c880109590400341c0c80c016481541e0841c08001348000e500510700c40500340f203036101c005452401a8001010030a12200c036080d1540003261010858091030440c0101c00000950381074a4020405100e60251003c9010071840352040d900b210b101c3e00c280c0c2860354a940d5500b0b08400c034003802c0c0c80e40e800140113000601c00102c0c1980c3c484c1c0c1070405541220180041551028242c030010001160900010303881f185c601c100e110340c0303142c0103c0c060a240c01d06a048540041000405151a0780320700c0d11098154005800b8950003c5218800383c2021600350f02c5074501c250313003c5503118240c0100b81f500002889881001c060b030f410390b0320317041c003c14500c9074540fa40e0381c0b40180034251184600072000c081c001a0341c2c80004041d843c3c2a41a2820070031b1440501804480301201c030300d07001e6000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 895802203 1250 895800953 895800967
    0xa0920130c021510080115050424050d032c0114091c020d0c260304080c0103091403070b040209150102060a1a03030c0703060e122a190512 61
    0x2250030b00100340c12280d00c52481e42e60080d41c84c40e1410540c416402546031840822000c0d410680d40816100d00b61824030491a00f002026501050b00391480c0d0000700f1540c003880140791503040340307140e24040e151411522079002805100d0004104180c1403090300c44220010700d580181c030f00003c20040500380d50401c800030300810001242a00303289810460003040c201107542d07214101403441c0d000400004000c4c0c4684000e46414015400200a408070440382041c0c2c000010071141540d100c00c028160806031000190302a082d482000c45080409a5021000d440100081c00440d401684180401d040c01e005200c0111405040042d0300071921030f001403141d0300014104e07003140304c2817400558000700003201c13240d09150300e00071941400700103042c488114001506d0f02c00c3d0b138041c4c7c908001000101644596420482c03480340c0c00076509000c05049100c4002507810040c800c09201d004025624000e242071840c20003031085021005004101404001c002c140c0002c6810f84020740742c159 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 895803453 1250 895802203 895802207
    0x70e06070b0c030c0d09060501031104020f09090912070c03020910030f110303040909050303010320211002030112060e0f0c090a2c2b080a0920130c 65
    0x78024010002d002000000c1146003a00303c0403100a90030b2804204605100e903c3d044015140a10040c2c0e5031280810740400705280601c00c55005000864070384d45070824100501001c0031004091074107900520900c0040c07100100700801140e48075441e82e070800382c210300c10840c83d45005480c110f00305500280c103000080d0f9080c140b03441c4c2600440002e4141c071034000002c4c80c522481d086001001d040c01070303090800c40c0020185042c0d80c880d42c5489a09000804610b083c121804d401c642c6c028071003004407014551400c8030110384038189003611148400104d40d102a40c0c001c0e400070512600c2c0c14022010b02c04544600d214482c5108041e042d0400801ca50643d240030144180348140702820100d500801541c0c03008104542440721140d6040204c50340c200d002c0c101000701031490060300030b81034510200d07640d00d42843c1c1a50443e50441ca804540885031000d0040c020b111056540e02050003107004015068211540310144000385200f20051201c200031240d6101841805e04100e60780c140e17 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 895804703 1250 895803453 895803473
    0x40b0f0106021609021303080a030911040c020706110703060507050d0b03073501090812070813080d1425031e0207080d0c08040303270303020a03110d05070e0607 71
    0xd013050801584501c088000003140c01c000f41d10041290750005100404c09415400042607940a03881c4114800f0040c0c0900068940c010a0340005801250060000a004910300c02100401100b116072150701c903954081100e034260f038040c004c100c004c80da1642680480c007400780c034003c00340d02a008603440c2800d0440780010070a866884249200b8451003000e83c1d42064103030030701043d8002d000d603e40900380300100394070a21020a01604200c0003c240a0003003600500079666112201c000500548401429801c10a0051800394640e03041503042d075241c50380540109829888002c58200c4102d00e025034161940048040c1410000c8075401444000d0103050981031030400580c0d64441841c0005d490300c28924942c00071407829500d45c2d140f960120f1118859403094508200803083c0b22280b0186003100000c6491040030600c400e40040d100b60058844000c0c039007404a44015012500c404540280605541c2c3c1680c51041001c0264031030b80b1102d00c0e000a54040d85842c015455100030b0b1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 895805953 1250 895804703 895804709
    0x70c1406060f100e040f0b030102030a021206120d14071209320d03030e031b0d1719060803071b0f0305070b250b060123090d050f06040b0f01060216 65
    0x646d41c0c0380c900c0d41440c41280c1000c404000300a000f1596440d00e131385004002e40107079075034803184c01800e00040c145040007500f04009205150042007004100f40701280d00085240d14244000014072500c0c00280c0c07c07081907508015291280310405040c40c1c00e42c41010300c3e0b580b81c08042d60079402200310a0150080072210400282c1d809040782c0203d0a0507400f5101411104869120000c1d038000c5404044004c841d600c3c0c0c28005071404044040303401c40e500b45031280303807140000e00c5401080288880c0c03d0f40c00c1104000c01804241e880e41e4112460842e00040c00580341484039041c0500644c0700d4803141e00141000c0352401c0e0450341180c0b2841d50b5010b00b0b00032003900b00400222032904040c49035500200030fa071150705c200070b82039500c0d000510743c006031480d41c003084904c0701c03694014295510301c1c0c1e80581101c2c1510304049413602041544c05d001003080c1c4243c00307541d40d0f4803003500c400d2010600c035901400c400b15160809004031032202c081648244215000b1500010880d514245241e040b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 895807203 1250 895805953 895805959
    0x121a0a140301020c030a021c0206010f090b030a05011d0c18011a040807060e01030b0117060d030e041d0d0903030206010303050d022b0f061a03070c1406060f100e 71
    0x1400c0c0c10500464020712882c40340300f580e0b20000c034010800a5000884145044e200c03801d0b610082051102aaa1407200703009048080070081d4003070141c5442913201c070030400401012541840c003180c9480f400c4528040d0f1968070b0fa8a40400b042540780d04000c4401469010795514000110f405544006001c0600440c402c0d040c20303039440740b204508881900e002d00826000c1c4d4020541c1c5003800f81c040e584e00358074140030a041001e0b4400940c01402c0c03400202c042c101144c555607540200b0407682000f8084c0032814492071009492094845218a0480c50840381010800c039060000551178280d10300500d8041020034001400080d90115599044a13414140251070707040d608103010203801041d80202c07001d01d031701c1a000c120240d04c1078030300500000c0040070404403e03415000740654505000d61b4800811204501c0c000d04814001950300c02e001c1e207484400940d16a482418020307001c1e0848115500140900c0024907002d181c40c41c6241e8100c500300030340c4c040c9100140003000784500040c8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 895808453 1250 895807203 895807229
    0x203031210030605010b0a11010209100f0c080f030109050108061e100b03160f140909090304030c150305070e030d0f0509060408010f050619140109050d03121a0a 71
    0x10642081c2041d401a580c001c405115540c0c40340a8403409030003081c0b010340040c0e0344640384c02c40070750184212802803d005d0500e405588944c0300581c2e02c002040c42203020802ca802807440820000c00c05030092111002400b42e903549401103050075034006030420741c0d081d0004000d1000310345860308051010300910859040f95550f01c43c80721001d9405d68040e81c07481c0000402c002d080380301d80a46118840c3c0a456250710061071340411140400601600c0965036420484d006007441c10825055115180d102203a24048d200d50740c0c3c2003000c0d055070008030009032041701d2180c41038045c059a5400b02c2c0c1803a10b00751103100b410000b075440320f8014040050000c000c07100141d1a01c140e04454801c036000d03001d04d545e20b40c0d580c1020700070000c0031280741d00c40c1d141001042d082d280052202c17903440407080541528034285902c0503502401e000070320b41031080c0c40000107460f03251a01c460000c940661600a04058110030301d03800c1e42c1e09541c00064500c21b107690081c040d5034001141080e0760b80b40e40100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 895809703 1250 895808453 895808461
    0x1a0a1527030b01090212011401120923210f07060f0e01020a110105010b0a0c03080a091709031b0306220605090d0207061403060111031b1e0a02030312 66
    0x1034410314580e0000342407940c0c0040040751020302500185251008601c405102c0e0380e031400d41c3c03c8049807400b0b82d40d0000c2c503424007400c5071041c0f03500400311050060038040954040d0002281c071100f107070540350505400c2604244041956a5400d00301001051011813428070b111496080750701c91a07100400700d0b41d03203101004d446100b0791300401150441c000210740c0d800c0b41c05000f0b00106030043e03400c5025800c040021500116010580304402e50b161200d02e12040103603415185808010005a06259101d07003140200704003140224a0200c50b2288030307504c203252000d150500c65010000c100c005003c01c4054029100011980d0b0b2142c3c620720210445800340b604151050000c460182402d410071052100d44c050101e0440706100c11038089410407030355100151682107009003000d030b010205000142855000d0640d805985000c2070a503803070071060384c160009604001020450580c03200600442415500f89140700410408000f000d4042640d400285c3da4071400400383c640d921014049 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 895810953 1250 895809703 895809767
    0x30f0e01200f0601030b011e0b091215010f0906060f02120306010309020603090601060e09040f11120f07050108070207080703020607140f010507031a010206070806060d1a0a15 77
    0x180c09107400c00540d40d0f9943d407410502c00e00c81003801546c5415001440441c51440c500109204480c918100f10381054000d8041100200e4221901041402220ba459191500c543d908a0107070074885060000070b82454111401c40e012504500d092100700d00d00d4104658000980c408040003c060a5590f580c40c440104c001e04511080203400c04408030901030201004200c55041c1c80490b51035441c00c050711020130281c5c0e80f00341c1d40038080c030044c0c1101a001c2059944903001e003d2000d490444d552811020316460706030b2107492007400744c00c1141c05012540c1c1c044003d503000700321880140752036400d008865454030160702c8001d00c02c9000082e0882004024100442402410001d8802038000348507503c0c0a800221015000246071401000001a001032540000103060380181240d03500c208068825040c0a0720041c0c1c400c0041c440c403281e60703080d4000c51491024140c032000394440c0c400280a100c0c403850b00013590001a00c098454100d40c09181c00315401300c0344040145521a801803 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 895812203 1250 895810953 895810963
    0x60c030c16181d0d1706010206040b0c21090604231e0111040b04063009050c1201090203100207052a040c1d1203180f0a080a030f0e0120 60
    0x60309940c0c000c4000c52141e031504450b000c205e054007030041038402c0d0303100401261204421900104a00b5205001c00e0242c05e049000d01607405146000c503142465103500d501003a802161014041c0e40100100030400070500414400c4023042c02101c118602092103080c0c40c2e000390743c3c04100d0158910440c90704131000350459981d504041082503981c03030312501c160803143d001e8001c100c00b06946003401c06282182a0007802e120340400808070f02c030100d41c08640064809284140c1c0d00e44030304100d002040e40c2d11f0609090402010b40002084c040c54418941494010b01c1c11420300d0f071051040303002050001c1250400d400f4407241007481d480c00c401c0d4625800240b12801c0381c000c0d140c1003501c40c605030000d805c503c0b00d400060b00103604410744810410503580ea0744e40390409820030302c0350b000d02c0b00c0410049a00414020440800b41c00210041402c8403c5036120f0b150552041c4416400d254001b000d0720303100005031034400c2c100007000001070480881103550000420194140342489001402 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 895813453 1250 895812203 895812251
    0x30604200a08010608010b0a0c03141309020c0d030b030d080408070f0615140109050130020915030f04030c030c05030c06060307050a0303090302060d0b060c030c1618 73
    0x88151075203031015004009070300c240103190108030058000710340045800251050481965103080703c4a130b4030b94007240e0f0f2141040100e0358040040c418401000001c03891440600794825005032100c9450f6030f141d151103103039100700f0280351070b260309582140c5001c21a6200c0c800107080c49801c0c0e46840c54a500707188903106c0c0140102d1303003041e03850040014a41000304801d04400211480c152140018040e04840390100c502080700030f4402c010039400750040b812084500046100300c2c4190b07205900e40460404070f46c01e09240c2c0000c035a03040d807409442d000300050004800c00c1c25854906841c11900e40090000740c00c1c0b0050114000c1003601c03801c0e603148055488010b40303851300e114200300f80e620403003a20a18840d001e030001c041002d00b44200c600c000c44e80c065440040841c51b540a00400da1f128110a4090a4030b8002e6001030340c03034810081c03816404035001981e80700d07010f8200c0790900c3e2844840b000d00d4070401d0020400f41e00710600c030a04540c00b000001410701041040300d041040f00c0701c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 895814703 1250 895813453 895813511
    0x50606040e07030e240a0b01030608120306031b0637080601020f0303070e060304080d09080d060902040f0b0a020709060b0c061006091e030c0e0103060f0c05030604 72
    0xc020451880c0d0b01d034001d0548015048100c1d00300d07016085d400c1a07a8500c10403072442c650220300000b01d243e861900803404013041070400040d0f03541c841000c6414203121621a4100c00301c0042805a1410308211400b408040d00141240801e8510300041d40d9108891040d0400c1d050940b105510200b26021000c0040c2c5c41e4501019100300c2d054081c1410000316030729030250148686206072454040210381c800c201c0313541c82d003003180b030b0b200100155604003500c2600d403001c040c040f1101c040c03010310604c943c83d8020074a040d241d03407225101900b600d1036a080b40e0502801030004000500210000000341c0b030554130050f4561140c4c5408918150303179035020024481c1411000600c6600301001440300e5a003105c16204070356104038004c8001d0b0f00310702c00c080000d699003004001c2003510110343c05034110003a60035110b103552900e65011260550b04111010f888010040003008141e10030640341c0011504140003001088a0150945c000208000d0041e134690801e5816a0b41c00481c0c0c00c4200701384 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 895815953 1250 895814703 895814729
    0x140703030b0607141e1c090b030c03010e09010603030e06250b06040b060309070302010e010203070602030907090c18030201081504050a1d060c090d0c0b1617120a05060604 75
    0x38204a038105040000141050241d403c1c4292004e82155401a030600c5050080c10500c0c0800c4103080000100c0040100b00908050041a17a143c0b00e0002d6010300b000ad042140c40e541403171000080039002600104031360b03150810800002e9042900006503000c1110501e40b038203042d0345044a540c0fa246800c400c2c11144462000401201400b124040d01d403d4800b0440d0480c03206c02d120280c8016038180c0f25035806801300300010740c81070720304120254043c0f040d2030a186595485200313980060300c0b010090782005806006c500740b54070814100880d0b510f40030f6401580b0643d40002c02c0c55601000c0d040092100c00115a50813402011740308201c054030812003880c02e802040c0052540d8407600050001111070100645000a12140140c0c0c6100c0094901058a01003050620790b101c00ac698116104000149003000d450240c020508101c03112105c2c80681d15110b4040c00c45c60200c0613440005100c0c40d10242d0244100303d5000800c181c000410380c89810001304680501d42c401c81545802e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 895817203 1250 895815953 895815967
    0x50a0e040c2a1104050a09081206010e06040b0a0f02011d0610050a0b180d0c06021f05010609060302090d0215040806010b160201081512010c08010b0703140703030b06 73
    0x120426505402503100640b1156401c0950b00341418075203801c01a00a41031046640d0710b51920340d0005070800019940064403940d181d644a459030404028030030b40011f1307042040071558000000c0c07503164070100d410a2515040c030790420a14003403c03200108000c3d9640c900c00d038241c001d40c0b024060038000181c8003080e82e0741101c40d0780d40f13810480ea40402d04041d00000103d50901d0441c500549501140f41070070840740301e00c0200b0b07039141003000d640d00c88550a4420040740720f4068420203084176502030500c410700c80300c3c071000b4607403008481a0400d01e020010407039103911807034100c1903400030300c1c0141c1c1c1d4115541c005042038200340381c069482500001e030041003001c46001041141c0100c0c0a607029030b82e0310364441006010f860425441c44180642c1d00300190700c51000c0c5640f107540441509074070074030b200128081040003101c80105a540700300030082d950708003103000d006090740080e55180c20000e5070003c001c662500c8426001c008041001c4080500036080000005070107481c164035011 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 895818453 1250 895817203 895817207
    0x1061a12060a170d0e040219080a1404032a021f0201091704210201020d0e220b18060a15020f0303091e060f0c0a09091406012a03050a0e040c 62
    0xe13201d00c000300480d00c80310784104141414001d070f032842030114040d4101886642019100b402c802042082c01c2580d40845030460341144101d0703805175000303a40b91691403003614610040a04013601044041c1e1001e01c8603030040c0d4514103036890808000d689040804a101c20a83c0035245002008014890b401c6581ca401d298070070151041b030310081c142100005012001c20307003112444501a0058020700c21700c201060240c90481c90728003011b04207003541648420520b00c00885000010030340350300d61412141c40c3c54408038030440b0140180290741d581c01e01c4400264000740e244191091b550351003c0001c03280b030003407040d007203240040010340f542d903c0c11003501c41d1200b0440b4000e45108000c010002c0702d40c4d00014909126084444003c0107903110090440c00c40c0c0c016076111820801c80890105440095020310301030f00f8103a420440d0142010340014141102c40c0e198400f4071800c0140030307007008401c03005c4a5004d9400d810030b1540c5000c6810111034400b0088119030300030f801c00030b2034241c0903 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 895819703 1250 895818453 895818463
    0x30816060e010b010e0109083a02010506212a03120c0601170d0e04020c07030b041101170c090307030b090a0507050a060e01031e0e060901061a12060a17 67
    0x10f400d0340e130034020414050056038540303128041d40420340d0240b440074050028103030f43d000e001a80964440c03407101488142951181104690380c1c01070351288248032980c1003000782003403880100e80300d80c1907a80c40b10f50710f0307507445000200e03c8043c0052400220101c04c01c02400c0003000780e01800b034400e211900f00139820300b0341c442d03005040d041c8600030000800020780400c0c410b40c10b080b28081c02804101c80411242507402d08000e55000d80d0801004076100750410448005520440c55042c040c6402d050010310000035182c258180100d112200700102400404103078050a40180b15840b91000e0340885c1c60040aa000105101400740a0029800380001e214440d41d11a1003120300d0140c948003441400113440c4180000b00b80c1400c10001a50301a8100c81e255901b041405021644507078081d40c20b513441e14030307100d146400040c10304c11546000e008d008003400b4110702c64240e2400901401e11a403260f240351040400201d0f000c10303150350300d4140c8000200b0200301e9544120000154442c1c843c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 895820953 1250 895819703 895819721
    0x130b060f03040b0c070c12052b0e030307030f0503090c0d0308060f010207030203030307142a060907031a090a050d0203031005090609160908030a121107020a030816060e01 75
    0x20b038200000d054040c0c44c0d012543c43d141c3c0840c084445600d46203101030050b0041070100d03698010742c8824414801880e00b501010202e1840b4070703a0f1030b40c0f00d58000d400d2240d11140c40d40079410800086000c290010100700d1540c40600d4841d94030381d41c8002c1c8070f061507540201540e00c2203581040c0028140d000c07030303c01d02a00e4201c0380a90303a003008000682e50b4054510000f5059082840001c00c030b90b0107012624000034242e0b800c2031070700c443d840303c03106001309003240c00d4402039035101c0c10543c44200f04030840e40074601000602540d0305503182d4415009800c1041c032208410100010072008052280c19030700c982c41400c45001e03002e0140c0281d200d400485140a08512084000545181c0707240480d005d00d20103443c600c4213403600b2080d400403400c800c070a81d0910405c20b00001d10300c0000c0006115208540e5103001e0f85c0f00141c00c40600fa104000341030400301009010074000b60f030316109160101d80d80501c0c12942e4101103044844190700b01140600514a4070440000814040d00071000f1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 895822203 1250 895820953 895820963
    0x910080d08010302040e030c0606090a02090a15090e07080408181003060509060d03051b0a080d0204031e08090f0301111b0f060421181403070b090f130b060f0304 71
    0x20b480c03998611594074003c0c40c002e000c23690700031400b0032050b0416440c65904620707041c0c005440c059042004c284042c0c400d9010841800c01e084500ca1000d82c0104818041c01c2c5081c0c0b900e9560501d40f2006000b03102c040c0005e082000c000445940000c0c01d440141c000003400340c259100e6010200e80038000704054031890303000d140a40700080003450704d030284c82c08041e41a12500d060525190102c4942c0340001c0d032011140c03040e1a11900404c0240010f00102c09403c5005641c49041d071420910000c811042c0f0303250752002890309000180c401c1c05842d8024000d0740e907800c0c40140c40c0000707805080c0460405c03c0751940041c640007440000700386051101c080808640303800a01c02940c55552200f26006030500c6081c1200e00c059481e20544c00d400c90800d498501c6004544020034a00a401e981c0704405000b62074490704200e0509000c89401091031030103140c140014040850b10425406a581d8851182c071102210710580e903a00132084804050107007600c0f901c00302c000a0803540203403010f5132 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 895823453 1250 895822203 895822211
    0x11030102040e090c0a15050f070507080a0f060f06050d020603070915020c0f0307060504050d0809101106090a0b150102010e0313030c090510030609020315071d0603010b0301050910080d0801030204 86
    0x2600f60f542c6c203c003402968840e0740e000c0c031f043c0c1080b5a2003a0b41d0445081207805001d0070500103800801040038143c01030007009200e400c98901d1608108a54400401510b0b0608204003048956114180400b00d00d4040c4e403e41d6503640d070a03104039a401d01c1781e00581c1c00d601d409294008119030004402940000c151104403480880c030b0205665419203100d01c00025200704014003071814140f00d401241d51040c4207050030003140500081c1c01d0b118181c0c1910014103040c500c03039400c2100b000b00d250808001e50281560004070344440305525001410034981c01d034540d0301007206910035031140007280036a01c10349482c0c21410320003180d001d2a91005581c622442500403440305000d00c00c00d40543c14004208408500d0b40d51524080e0200c02c1043e41e140c02001542a4141d401340c0c1c219100e0015680c13000f14a6031112110003510003030b040729500a040520060100d41c0c00441224107544084070258601d0752a80d165481841003600681caa602a010011000ca500b058075a0306807803003280d00344 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 895824703 1250 895823453 895823459
    0x1050f0601032406030903110d0c150e1005090f071205010507020d2a0204020c0601060f0c053403050312072604020f03030f07061a030a11030102040e090c0a 69
    0x102458800c410f100c0941e04800c1420040343e030096100d0308245101e4140359454141c100141030401d00c03250300200200391071707940c204c4c1000480c41c030282c0390310320000003041402c0004944a41e80d41e84082280c4800e80e40302d0201d0343c00f00013048040880c404103002c075511152902650204981c01c1c5000301d90642c01d000220b07611600116041c2c80302c10b01d41e41c40001a0940d40b00184c1110440c01131a40300c000158803910140c0c03500d00007810f0140002e80240081d5240c104002d001e0b030801c1410408102c2c0c907080520000d00c000c59811130041c0000000380140258101c15100c04142e0f000d10542c00c000f41d600003040100200c064114484031541590040e5074a0005841c43d01c0b2201a14a1001c402d86078031481c4078030706000c25000ba001a00d803484804076840420f00d10f42c4141c59440b8800c3c070101c0e0000400c01d06d802141c581090a0a25a610340100130210380d940070b401c01d009254140c5203403880c4807030318254103640080102603040705490800d84444d40d00c42813080e1809010721300c0c01c0d0000c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 895825953 1250 895824703 895824731
    0x602011e0b1807030b0904060b12160e0c190c06230a1508031b071707210f0c03021c0809040c140409060608100f060f020f01050f060103 60
    0x1480d00d030003402d8080703000b0580c0080d56503088001c00482c14140d603800b464241c2e84400c0714061081d80308030000500603074100700308541d0451843d0341c006654846107503d4106c01c50540d2140403100b4280f0b0b452419151300581154500422840c008030086902c2d207001e20f40c0c1c1c031040b038400c810700a040401c406150161030605c8441e1542080c4280f1a100c40411422441070b4406401c00070600482c000c07071512642001d042d80c1c02003059421003c0009030103070750104140120002400f80074458440c2c044603601103a00d8001c079114481c002000c0b84035103c5c412005000051440346d020401400b112054030340b08051200c503000c140d0254890304c955206402c051550a44240c0e0000c0145041002c1c10701008054403000b80c408080040450155842401c200c0240c00030380302a45004c0317400c60038008000d00280c4010b0100184035100e42c3d00b00700c000c07a920388040542e600c51400c40c030005452030081c0d1030320206107a00c5840350300c0d110420000303120030056030f802404243d03010311601c1c086c0312074 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 895827203 1250 895825953 895825961
    0x302130b030c10020a0213061a18090910050a0504030305090309012a020406080c120d050d05040c05090f0108010b0a06080c031f080c13020a0e120c0a0602011e 70
    0x550140c0c0b120148406614140b103946020400902c101c5091074055070100b41804107003500550308544440040c440001c5e000c820301d0707401100d80059400d040f04040e0b4042141c1d04058054000c01481001c103401000501c401911b41c44551410720250404200e4040107020488051300040e00c0d010201b8001b92012049130300a6405a64041c03009036901035440206990b4001000030101902c07500c2c00580b00c901a0740c004106041c044c00c840003503181440400101e1a1744010260443c00200803098ac2040940e210040907000010305d070351301e928061400721866089039902003101c0301048030b001c19440040b070588004100903c8040c1c014014404820105d0081c5c0022556103000516000c400d1005191301100c0804940c00c2d0707011500040f160644a90030003030796600100010a450309002c3d440001c000302d182001c600d0069400d400600050094074590b21a809010503142e0310001080b214415010007085120810303580c001c0a8003c02c0c1031004440f488a41042800c811005481 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 895828453 1250 895827203 895827221
    0x501090b030f040b190c110c0303040b03070e2407060b09100603050903090a030c0e06090f06040203060d060f0f06120f080d0615080601080f0c16051c0801030213 71
    0xc2070b00c0c151500c0d030390b441580300300030826003c43c4200d55400384581898081d02c24200701949031100b0325800c842d101410050710b07042650082e4000c202c01c100d103001181c2101e40c40104e41c03910742501283c2000050001e49510002060304074200d202c501503070030240080c503100d48217020802030640c0800a001c041c0d0012500041307519400082000340e10700070340000394050035070030589180c0803030400010324090190f041a00d07080015541800108854162070b03801c50301c215802103191900d00840030000b000100918003598012001c01e0413511b506185420442d40118248800c0b5041c68036003000300091120140d00608140c40003a001c446007024600683e00111f00c0c0b4803a90007620ba480150780003c0d51042d4803682e50034002503080860900d00e520552540c3c0380c02850511300001041c5d8140502000340450f090341c00d1011001c4041c04075821107003501100c00500351030f418100e05003c4002c22a00310781e03440c02d0320004266408807800d81607038070031a5503007108148080d5040480d45050 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 895829703 1250 895828453 895828471
    0x1302060d2a0f0507020a1a130e0c04062a0615060302070503030a02070c080106030804051810150201110d0516050c12030a0608010c030c020708160b030c0903030703090501090b03 78
    0x9285071800c40e100f40002d12009002030304000c0d54503600d01e039001000121340441981c03101c000c20388400c606070100a0740002c00c0c0400304c51049040a1743c1000041c4101e20940041c0300700c0024404501030507182e03034032182e442c103040d0f10942400341c18040054502d8403400c02d01140c3c4540040707180d0f40a0f2080c0d0341c003d50848001c40c01c50742d49611500003903000510030b42c2c0c03ea16020300040d05031001d010340c00181d40300e04c2d01203494510707100902402e0102c071600e40e9001c2503481e0400820312045404541145d100b14000040d400401c0740c00d80c010207403d525101c80c80d00000311140012442d8010314003d0301c440705904a1902c80c10070480b601d02881e107100c10176030032244001642045030406541c01404541d00014020360321102142160108050301020940700c820300d00c241034043c41080f00611264004d0f0415425540e90000c2c0181903005500620101201184024204109440c42c2e114050b00701da96803007540c18040c1131508a4800c6500291007580041008000c107000da030301a010b05 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 895830953 1250 895829703 895829717
    0x5120a030909150812070c0b0910030902150409061701020c030307050a02010b040c0f09050f0f210618070807051c050109061a0a0e06010f081302060d2a 67
    0x105074000d019082e01000c240c0c90f0200003002068803803050080840142e0380c84601940c0303a0441c81d0480c69150207034841080c091041c0b2840741c01d5110445c083c2c02d145603524000400c49010b100098114241c21110940b03036070045400305415003164071400030360f119840520038440c00540e61030300b40d200d071030083c4000c1c0c0c0044c404540210700030409440041100d00000c102d180c40200403c0480d80300c1c02215000614425107440c1903034001c3e0038030340980360958072030300305030070f45008541100100c1d241c05025080300c0204c41e04200300c00303030311200e0a202c1c40182c41007800d091a441e440b0b00d007181d0b443c0c08103006000340080c6003400003c0036812a90041d2041e0651407240d100d914554a500000303440b00d54a8130720707500008917a8400d160003e00381c4807505a071110389405200900c0c1054100c8108100c1c1d5005001440ea005840c085140304240f0745681103507103880c0e82c0c610805a03410000d41004002c030b942880808590452501103400304004810030000110071800e2070820450031b8041034017 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 895832203 1250 895830953 895830959
    0xa0503010b010507020d1119050f010207150f0320040501110a020a03020f062b0f090510020304020d0b0c030f130c171501090b03010e2b1b0c05120a0309 67
    0x10071b88603c078000340618200e548202070100403e50f0030101090040900303c03003c07000d021a14201c0d240030a00c403020710003030000d58180108192906402c0c00e01d0028059851100b41165109420407a5018464091110b2103190f1103c501001d402c036001e071601003813a000d12140803540008400d98a280c00130880c0c000c9a20350f8003480190b080350000c80740c004c0d40401ca038003c0d0a00ca840d041e19008601d8852954580b44881c491048070b01c1c090065501c18102081d80c0702141c80098403c60381c0648080060b5240c4030f51000034102c2c41c1100004150b04c040302c04014071545030001031403280c40301e5030f03000000d07a0f07650010341100086841d00030b000d070180300b100303110f821400c1220f1028070a0034400c4900e41c00800020070105202603005002594072500c118600b07007420b00481e00c402440d4401454020010203070704518070b01c0c1e444a035846041424003030700100d00c18508100000031580405400c03e1490034904071105042c0a824040c010410040440d01c03c0000c1000b07503d60155210b5111a003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 895833453 1250 895832203 895832209
    0x230f04170d02091c0308071409060a09030b0a0f060906050d0f140a240b060307050d0f0603030e0414011a1b15090606012307061e02090a0503010b01050702 68
    0x10034550361120542c24001070803961074003402443d9414122091151052013440c0040881c20700901c1503080000c217500d003002541244c3c05860744960102c91030fa4417408884070860f03004201da4030180c02c1d10303c0e0200f40108229980d121810000c004941131104907141c41115043c0e0b811449000e401048681e80200030820b401c1070a000e5511405680300120040800d103464180d031020117840f60020000301c2e03d041100c43c00f90051000741c0c280c040c45032010705000101d0300e010083c08001441400902e03280e001da0980d015100070742c00c43d01c2c20003e494803400c004001492110020307015900d0080f82c6103a40803400d43c1d641c12191051202522586c8029401c03000350802841000348101140c40394101c0007090015001e00d0000723480d02007851030070300103582c0f806001900450520221688a50007a0142c1040c900b40e140b9140c02550744607407510b403100090261041c02c180d0000700e110448440403c07a0001d09001404480c0401c05640300c100b0107080b10440d11800340817800803c0740c100142 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 895834703 1250 895833453 895833457
    0x103020a03110408030a021c0807080403090819060c030e100f140405031216020307081b2a0406120b040c080303040b010302100819020309030904230f0417 68
    0x4142881c0204100709034412007140782d081500400f6a43d0400b040400c81103504116030045104c25210754905c401040c072014251106c040c0c0040b00b004003201c0000c0034503029103082e10007444c01c9000c1780d401c2d00f90034200c500400c480300781c200c5500b4180350500e40c800e4883d02401c5000d401e020040d115116400403400c00506410020450306904c171010700719420008800c0d20711643c022400707556101c4410303400704200c02c4c004150038081c50200440102c12036000003640d0166521400703195540c6e0010352034143c03c6504034490030840c4950401400d0070404461941701d009452624214a00c8a02040006455050041042c50ac030001100800315200b030035480d0300107005038460301c401340c2c032200300d81d0030342c2d0044809440c51a1404c00404c11410548070042860081c0e14281c400d81c00c00c1c015600306070001001e0400c100d40c012002c242421014000c4030060a40180104080802c044801c1c400d015000880b000288048000941c0240482446403242d907101c411000b00c0d00d0804404420390f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 895835953 1250 895834703 895834717
    0x402070b18070b0f04050117092505040507090602240411010c0f030503093a020c0604081b061908090a0c0306050a0c050a020a020d11270c040311010302 67
    0x5206101e0000380c11403403200100760502d030482016517101d081c9000501000c511080b6240c10360b0b0b016040062101c0d000c100041c0001d02100c2216401804003010354003681c3e6130b0803059106190106000c0c145800071000002c0703c40c0c5800b46e85400074190b0740e18004045800c0b6425807040a40e00040001d0303060000104805014100030007617403007c0d201c0030000d5981c10000c50220b40700106010141c403003000948054020031203040c1d420100034224614101d8050908a0207411041003080700038004e01c1102038040c006011302c0d031555a125a41c07940c400e440580d1403825003804200c40340c54141130b0101d51004207188541000380700000011124a60000c00388006400b440801c1b1002444800c0080001c600903c00410300b0b0500c401c0030421510041000424414200603202a2030b4020449803106038044135216008019824641c0c0c03441205003549920a044400003182400c5103414042d0b12078641780030440568410040b0303801c40c4611f00018048092802d8140c0340396200780c0044c280c0c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 895837203 1250 895835953 895836001
    0xc09101a070b070f02012703180306050c07030e040614100519050c0624150d090f0c080303011d090c030f010b040b1801031101110a050604020f0402070b 67
    0x90510141c490401201040d41d1800003d01d10102d0256419824001c00b8541a504003030b070a012022107c400319480d00ca0803001302440f12444e140d40100641d10500c000564000105202c1890040320140003540500c800310b0101300345003185205400d0500c290b1003540d4440003620791a40901041116007254600c0c0001001810884101001d401b02c00400d0f91016035111385444440115030581881c0000703240a00500020480804591104001025402c0d0646842c0060303034117040a50b00912400c0d05401d003950601c1518820040c0211502c0d1095020302e04040c091b544400c0341c103480b40700c20f100300d04143c2c03c00c111840c41c0c4605004c082d0f80100c7c1c005c0c100c0710390b90807440209092209580311840c05035500c02c80d641c843c0c00c0600480300b050400302c440404e00130428204d42516403042c00041e24015508601c05040e0740500c011b96055408034003100d15400041c03034110359800301280c00300d008180c2601e00c1c5035942440d000380c980c0954465000700c1255580201060070480c0c045034191 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 895838453 1250 895837203 895837207
    0x1110304050a300b010e0718030318091812021b040b120a061a0d0c0e0903161101030c0806010206181e010e120405031c05040b0307050901020c09101a 66
    0x1400303c1d0640c4140b60b0355100c0c407800c40480d032500180e5507800d54000c004030144900c00f90803080422507980c803441903980c503042c1030000c401c04030040d840c00c1401e500480086480c00c54030610842c2d120201c0700129100340f4020460195040f0101d85598482d03003e9146002d800300500d03850310b800d810401c1002070181035040da45291a22251401500c8042603803020340d42d4084000c045848001c0740601c40c01603404882014241c1d07a4034403501210f22810828100c040c01082c00c480382481210303940e4080d00c11100d8581000d0500700101e80780307450ba0a0121785001803400382c050040516512990341600500303200d030340c5d030100b0310414000318122841d1401501c0085180e001202c0c0c1c8005c18144c428000110144691042441c1400403e485c1c0d0009130280070800650b50002829040102800205580414900d02c183d80700d000c2d0383c1000c540e001c404420460707550b03442406044061402d90840b036503910444184220945c0c250359030608041d0a0f40240700e400c8002800c1c1580341080b000280c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 895839703 1250 895838453 895838519
    0x3040807200f04050c0702060721110f01061220190e060303130b1b10050901150b0a050f130806010807060206010f060f0c0c0902040501110304050a 65
    0x1a116640031140411071a081c460484501d041594200004010507070381003080d810301704801d010a014101780288038910004d584401c01100300880d00c0e40701d140400ba648070783c0051201400c060143d02c0c1d11080f41c42040e0300d0b07210a0b04140101000c44e0000c2c0346902c0e84103060b4640c00010395101c2c00c0c040e11000d1320a584070f0b00d034540301c4a8503508541312085241c0b041c240007556000080141c4200e110754800d02c941c20004058421100c1218140d0f2403803036451b40c05005024501140c0190035449000e9130340240701101c007035000702c0c0c4034a007044003c00041609905440032500f050103009030f400c00074041d84602500801c000c21103030081e000c0b440d05054014964070441d0b401130308500c0c030980045004001d404410054000030b4007850014041a40c1402c084107004640c91090000b044004800410118058000a5007403904005950046030b141c02201020750301610409000650700e1203107151115010040c0c0781990780040000c5412483d040c1c0c1b0200c0110505520744034011603400309 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 895840953 1250 895839703 895839713
    0x503150f0915030c0102070e27120706050105010503160e0616051b030f0a020d021206091e01020c1023040b07080f06090610090b0a050408100608070b03040807 70
    0x3041c42102c0101d240c1000426610601d0306040380f440c55103056500038402070207501d000b000c1040c0d0200826030104007040c000021003c0b2841440003031602c0e80202012009505601c0000340307000b501822044c007641c2d0b42c4500440700351004803441048040f00c0c3d008085001c4c031640001c800c20200411042c14050810841003007a003d02204880c2d50307111004106034141c0112803803112000440182c086044c010084c075450751580b0900a104007a8074400000b15a41c06031080c0c40040d07d042200d1036882c000c258150b43c2c03002900700114140783c44e078024a28100500803100f01d40101c0b0301801001e450f10003880d014000003200c0403c9003880041500280c295004014032480c000c003000c0f26141017515000e003107504003901203044440380c0410000587c07034040c1030503040740081d1401c1e41c1d20401091304031105155504044105040000c403c501b06a000001d0000d8a805c5001d6601c618410b08414080b45c0c01403244010540260400704000c0032010090750380580101d95092400d003013a900c03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 895842203 1250 895840953 895840969
    0x101107060c0b0906061309080f0d020903120c07032d2103062102030c040c030e0c1905060c120a081e0903031909060c05070b090d0503150f 61
    0x140c00040c900060100500c05044415500142520084c08950810001150f070b05a0710001d81c55400c0c1c0c582d003407881081228000c84690900c000e11041d190711030070300c440b4007071350099542621901ca1140d40282c150340003001c61744a00d84801c0100b50710361440d03680000c00c404a40c2180c41001e48150b40321a80c00f4500e050511503407060f0004290044641d900b0145d07089900d001000701403034180240000b226500b190500c007110001c4909024595100092034182803070501c0c0e1300a41400344c0141415019000721742440900e00c107a90400d03186805100c02d803a00d42c901c0c6103034080c810008100a00f0428014600541d110b01075a230304135000c100300100e035400040d0000001c1c00d600100328543c8046000d1000c40035113815039008604104802940c1c0f0f00000e0050b54204a0020507001000150360116294543c84001400107400c0c00d100500580c001d1001520b003081c07014006681003802007076500c42e101792519140d080d51110244c01c0c1e11914910b401d20b410041200c840b20842d600c42d03003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 895843453 1250 895842203 895842209
    0x92a0a03060f06050a0507030c050a150608010c0e0f010305130c030b0114010302090d02090a0f090b0f1614030703111204030306050a050f06030405070510081006090e0402101107 78
    0x2004620030340b610025045412507588084204801400f041840503404000c4804e00c42e0945401c20b1451240d040c1b49081441c0700e0030050802c1e00b1070400b0b2508031580c2c0c00404c1200d40150080000110b081804d9504248013018503a00c5446401d6042440d8020740c08550055090001048001c0103076a0390750a20f0125081520303040386100041010030305034807201c042c504081ca000c1d81003100300c40c085042c4843c004402407048505a000030003944407540300807000d03141e21230240b01248290610340c8540000f1b841070401c00901c10b00040b030711118081010f488031115919a40b01d00e01d943d03080c0d6040e4001a00b00e10030035490360310b15684400d428018041072201c40f18191054200b9250140843d04ca40c1c0c040c60003104120000c00441d600e400007220500c00a8480030f60b00d0360395140c000d041281da40c00442e0300080c610b031000d50b4a079000b100540304501040c000e840c555140c043c2550036500500c03c4283c2d50305598001001400c001c05480b942d52091309005041c03d403d01a01410301c02160 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 895844703 1250 895843453 895843457
    0x1050c0a080f090c100c05010b0a0b0d110c10020304051b0a0e1504060312020c1512040f020d050a03170103150c0c35040f060c1106030c19020606092a0a 67
    0xb0f0000701846009c4c1302c3d03150218401c82d500e4286904e0041d111480d8019143e00c0c0c813a9903906c8000c015a001d41c2400c403005440080141c0700071003000c1c414800250410741d000d0754507124140c4c1c2c9110006614520000c158002000803802d80d00d40088005262002802502e03e4828030342d1804440c0c40743c2c01480069480780115501d5007880c414001e01d4003100c08041841160752080c6803860baa86081194100c5881c10b41404141d611070400f14000801100c0083d004004140540306108002c9085200704d480381c1e80d20303c0c049540803000d003525a82800050003192458100800e0031403d40e00000781c05038681000c0f00310382102d444080341d00704901c04c0303001806422000c60036203c040011000780310980700c072843d0900f402d000524850744041d0103240144404401001d0500000350110a510f0304014200c0350340c1e00d0039140c405429080615580004804503125065240c004505a03100e200d000e0000c440c076607200881110503142054000e10310001e40e0781d281401401c240001d280b600034607 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 895845953 1250 895844703 895844717
    0x30207081b0c011812030219060606180e0c090d0c0902040501020c1f11100513030e010206040b04081b06150306070f0806010c030912060b0301050c0a080f090c10 71
    0x155096030030404040003183c10030501403030100d1180038100c22402a10140503245185d6041440d06070316000c0000c42440d920072040c0b85100401c000f03030708524282c03211503070365812500045240c1c509044c032500413030325003200d194002081e038440100505110440205540c405010035140c4021440c495002103e01a170002414407155030104007808101c1790545030b03403a5510500142c0305c002c9481c13503241c508100042a0540441c442085071000d00039103071504100a081c640211180942c0e101d20071804a083da00031071000b5800804c04e9881541c00000312000d50ba42c1d50303514826a8000018440400e0703000580e5051100100b044c40d01c20040408004550408101003510b0582c00601c200c0410a19054071081075034030038509070f0429002e08182e00004114501500c601c2503a4210080061804120300c040c0a09600700d140c0a400580080040d500c1c0c0d1510400d00784100c0c80c0b0b81e00440c1d40340300403408c05408544144c3d80071034608285ca1480c000d4400052002016810900c001192 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 895847203 1250 895845953 895845997
    0x603060f050a0b0111120d09080c0c100302040b03161e0210050903070f060e24060406080102041202130b03030313061a15030402041416090e150d0303020708 69
    0x8610640049030001d0800301c0e4102242048299a046c4038580c5800049000c00d25600d415401c1e081413505550108116444266281c01c82e40c0e2684c280400ba4420861110240c030030034081d100321030540b00d011820605e9039a40101030611040e9a030342500420541c4209030b440000244d0081d607406000794040c00c60100b810b90000243d9001400b091059001001800006820300c180410840e520030004150410b400814034102140c1024403110b5003c1080100c04150511004c03511440c1e00311001c201e059120658113080740154010110000c418000310400340c5060300c010f510801c01800d0221b01c0c848280c002c00e00f550429101400300c0c0345050110410403880d4010000c842c00d00d00c909011100c0c3c10b800181c99200c4000c0c5408003000e00002190554946801200410003102201e0180c1d0074200300801c10114100308082c00555001004100001d0303400059026180c090380030b991101d640d008001841170230b41011424182e007001400d000032141403362202c1d80800d0303541921101 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 895848453 1250 895847203 895847221
    0x201030c09150918140f1e132a050d0602071a04021507050601060507060e07060e04231b040f091d0c090a15030b09060a1b0207030b07030603060f05 65
    0x11484a101c507110708090551040802d044605d82d44004944046481900d900d08180c004115000c800d50f8951404404c00c001c40303440364010300b50a0b214890140050324808210f51450482c0ca400f4403241a40e1141000b8500d0400410a036507400340400500d0143c1540d5440010860241e8400f101c421500401c4203626005900080719410550103510f880044ea4071252640014010302090100100b42c40342448199070010b13070070b1041c2804482001d41c44072009010b8000d88a90a44501c0c102008208214501d0000e0701138485032502c00011500e440403c4081c4a281701124859500184000100c011425010b04010040340100103007001510380c10380c0443d0f400d2007421010303a0146900340306a848000e00540c1c8903100c1300300007501498441c4000c00300751280c0c1c00505161040020b00c002d180e80400c03240c1c041e21082000300442284051502c0a00910100b481c0240e0000d400c02c2004c078102041595000d03101d40340c00290a6243e540e16002c65101449031300c483e0743c2d58001c1024030700f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 895849703 1250 895848453 895848479
    0x60904060e09070f031a040807061806060510020a11120703030915050c1921210605010c060e0a08030c030718050a09020903010b15070620070201030c091509 69
    0x4200b21028984c000d0440e1a00b1041e9442d43c095810030180240c0000e00b4040c011050796441c0b42e01c420305201d421071281032003000c0c801c1040241c5085c0d00d00480000c06141610902040301510303005000c11020701c0e203864512141c400e201d1604080c03030100c003040301c260078014507019503c00d03198003641500305a0950b0080e5402d940640520004100c1b03900703c8100011201c2c0554440100c503851101980350001c145038003510b1580555120042e4001041e801145c00310b440c2907015078550b5006a07800d14141035400d544030302d03408904810180b5021403255048401c4020981e403c0344e01c3c002140da1044900e40c0308403103500d03040502106004100c1d900c005d0781850a00b1b07120011600508040c0022034400c0e00d803060701c04007940001c0c08025032704d007900010001075005007000030f482050301d10000c51760300540080750058604036881c145004145030010241c0e06181209081c024240d006400614046100c0410f011000c0d000180d00c14000c4c4041c015449540d603018800340c0380001b1060a0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 895850953 1250 895849703 895849709
    0x1d070302040f050904020a080102030c0c150606040b070606030f1202012406032c0a020102060c0307140f0705010c0f0306080f03071205040815011406120114060904060e0907 76
    0x26004000801401c0780108459054500c21a10003105803114070000e08803041d0741d803101c03001d54004403c1118907104030000d0700d0322000800a4540040203a20340c006040d50890345140d00c94000e03c0140b1410b500c41019011141c07150a00040003522500c03003c0d20303d2000c10007111030300054400450201e03428040d803c0b4010b0441e00d0103c080b1762040315a441580c160181c00c0415954400000c51920003c41c90441e822030b003102c15808003100c0c101c0b69201e48103000e0580c0940700b40c101081d1100b0355002203030f12840742592a2545d42c2c4e81085031550651001d035800000f55811310070720740803400a1080300156445525072060312040c00b04d0240a65059078008203154101d040181180c1e02c000c0304940420340d0105c03c00c1c040f2003030004190fa05004d250400d101921821000000c0341c02e0b007084050588a84041c1c03144c2e00c071f443d5010080c2c50701c10450f644503129503000040000030440d084200c04031a0051086090011520104003150199800340d250000c001741031104086c401e201d0080030f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 895852203 1250 895850953 895850957
    0x1060504140403020c010305070e18071403010602030901120605090a09050c0103060e0c09042a02010b040603050c10020c150403021f05031b0904110909010605131e08071d07 76
    0x11850b10f600c0194a135a0412443d85c14981c54074001441c590ac9006821103100b0700030b0003441200721000b0303010300a050455038000803c2840c01041400e81d030b0081640e04031000c0703138020742ca840c481100442e500c1d80360080c101200c5840f1840441c080d40c62415451068454140c00200352550f03041041c070384003000464a041c980380190030310801d5603036030019138003002c1c852105940c2c0c170f286c00c00705000708518008500844c0101510395200048a00c0350441130f0310550003840498161000c0004850701032100400c03e6001c802c502d0918109031032a058030b021680140c4442010340c0c404241c00e0b41f20030344500b1309140005000d00462414001c05072552a21a440050a0b20141e101411621010b05030034800703241413071000c208840c0345c011545020750240c814000c0c1d04000b4402c40f072580181c003010f0f229440490001c240707241f1940581c0da06281c0e10645102c500c4c81d181f881c400c415050025180a0b8115240c04510741e03108004840050070a01d4400c16480103811920a45200261200003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 895853453 1250 895852203 895852241
    0x1e0b03090a03031b0e0d020303090405040f0b06100906030c030f1107050106091112150310020403020103200f0d06091b14040f0e1807060e0a17030412020d1401060504 73
    0x1c015078800b82000c9503a05c00c0d2241000d400c0940006071550180340d020b01e5000c0c0c280800c02c001c1040b46e041040c0024400d29400501c0c0c0c07202c500304034005c500100c040d00052160682008447d12a8204040030003142c20005003c1120340c0d8048141c80d90442043c0700000001045006c1000c00d200c1c1d0760003003d03071040070804c20f0240e0602c8841c503c183d01c50800c1c400f1016002c10a0300c2d521080d000b540c001d0060468401c110000f80c454065042840181e0209240042c43c1c1d5041604810010b0200c008003c0185400d9640b414140e00e0782045802c24141c075520303000030403d44803500c14403c5441c81e038143e000c4612500c1e407008005d000d15440c0e00202d00014041001aa00500108829199a5209141c061761038020f010441c440c0c9207094401031094010001e84290003401b00708030351005441a07500d050300c0303040c2085070303c001c150200000e40c030800c81001040c0e100c189040480744014180844a00070351a089284240000300381e001d40d5440707004000311b280a04c140c1100684e0440048 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 895854703 1250 895853453 895853501
    0x3070e04060308031e010b0307141c150b0327010b0d0b011406070c05010f171006080702121801020c030d03060510110c01080a0f1d0c0405101e0b03090a0303 69
    0x40a03000c080c142750240822001e07041c140880e110306840513164a40c10100c501001c108440024148221170f05520aa40540101e000c21140c0210303803091203030940d00c440015955164050510440803002c0d9555690141c100305541e600c1750042c9082c0c05440f55108a50400c4081110341565425140c411182000700c04005043c0c0f000d2003003260824204140c3c03088a11005803071070042d9124600c107540241d0100515440481055015a85c143e070356250150f40d800000e0340d0300c4040180c3c207451820700740a503800340c40b850340115000b4401031040c1c900149102c0003207483c2010b00130304030011039201c04007813086082c050040c1401c40310928100400c085031400e10b5407120b00084500d410070aa0700300182c0001041d808c440ca101c40203072010041d040300b0304c001540b0050402621030340ca01580c07054500e43d00d490300034a802411903014450700940340144004407001000c0710050204c458010000d000000c20000d90300c0380b22400b000d0145072007070f46001001c403020561030801202c1c50390045 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 895855953 1250 895854703 895854719
    0x1204060302180423150604081b15040b0318030a0206010603140403050a2d020a030905190e1f171e030a12110304030c170c030f03070e04060308031e01 66
    0x114001a0003010118590740b2030b5040040168850700800d030b0014000500003400e5140000c2e000700c048003000032645c600c8a003408000b100c242b15800032808034000d1000340a03480d0240011a000711480441ca1070078031f404007200d800c58000c2901040940c10260042124903014003a54400240c0e42001d12401c0c5007039680944140525103600301001a603041e141d60b80c07070020a09842c82d4003a070040141c803400404d4029035821710365100f1000101104400541d9060069203140d9024520f43c0718a110740c2000c6041ca80d49030002d041000c861011000890320840300300d07480703020b400d0204071081d040241041c080c2c94810080070341486000071640c1801106408010303680c42c0107a903e800100c8000050020001e0400c03c00d40010260f4000241701c10550400d42c480b44140c42212084000c1c202000910114011504500f0b060b400410180e880c0d90815002181d100d070507030800100b2500c3c0b1001190442d021504200e0302940c002085c04600c0d50600c0d0001d0801d900803200000d598141104 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 895857203 1250 895855953 895855991
    0x4021203071a1f0810060602030c120a1407110405011202091605040812030a0c02070609030b190c031a0f0a12022206090b0a05060306010e0312040603021804 69
    0x242106074500b040c00b15001070240c60500448003554001c4506590311000c249880307500c25440384200900d4000300007900b03400802516a19410f01c1b02902c21008a401000190340c07140413080200f10301d41c1c255004990710040030303184081c010005070000700c842c142032004517041a08070f00380521201e080800103a50b035492181c0d10985042000c4907100e0040300c00e95450140c2e400040c028042c9034030034500100290042c52017a400d020051083d0443c022040e612070032140180303000a60000b4040c0042124000c4c00c03074008040300010244016803001c208212000d0000180000791500c0524068030044400c2c0780c0b030120201c1c2c00070324192443e0700141c031010451040341e1a45c01001014000d654944240c180c1c400b1140140b00d60207484180c00c90001e01d107602420101c1441c00840261908000034860701b9240040c0c800d0385180c81b103400640d1030305010400e03958036226000343d40e541070705400c0240000300625100541c4600381c4111490700c410740038000a000e54074004446041554041c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 895858453 1250 895857203 895857233
    0x706020c2b052e05060a0b720d050a08210c040e070e03010b130c0809060c030f13120f02100b03030409020a0203040503060c030402120307 61
    0xe5842402480c03440d16a00f8001c2000c2240c200e25200030303295910250500c4918400050507000b0007090b503d4104002d0352034040e014440401c6001c2c01031010b208007107000d05100449038203915010060381803240d00b00038070801800444100300c0b0104010424400c5582a10340c40e00200b17a2020448128114002e283c034440203481444840c1001c0e09122003448071035040c40c0c2292007607070303a20146240882c140480d10020b038a46041b10300000c0320422101d040d50156a070a00780c005c1c0c191030740c51089610300a003030fa4080e41550303a414900f160395100310011400e18030a0782c0103c0d040f10010005480d0000041c07101010750002402c0100d092200300c222035000c1f01c004602111601c0f41c141451184829600c0144664000c2000c040216045118039640300e20070b81c211114810040d890b48141c4015004841d00b44c1d105000034050b215864024020309081e0344101d900700740d60b4400180c0381a00945014100300400000c3c0019410060340e149004110940250302d00801a500c540004074184 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 895859703 1250 895858453 895858519
    0x1306180e0c0f2b08031e010e040201201c0908010c050c0309210102040b0910261b18040b030a1e0c09090302060a0c0e03070513060f06020706020c 64
    0x41c0f103080c0031000040c0d510703080c60f0003200d4261603150880c0340158280a0340f003149620a52030000080b40681038a042d4400d55044e0354058641d00a030565621800341d00c5940390140c003502d016800d07c480098050000384405030f9844101e185041003050840d00c1641522007040340030016004800000821200c007018103a40b49801901d04080312000400e55a090340c556500010340040c81d80561005042030750411070703941c401002c548409840e00094204080201c440080460714580d4145c02c5a0303134032501040340a000b000441d8000e1303881e0341c0120880d007c1d107804450b80701d04600b043d1251a4070100b00b86c1c01050010354a48800c944140d4040441303071045a113451324020441100e16000c02002040000c3c82541c0f107030300d8041e41302c0e5004c90340c0381001343c80d00c9040d60199109250030082d070304e40900030b80342003400c0c03034140034002c100c406e4040ea604da260350000a400e4112141800100000d0380500320703c83c20220000d060a074071884180c0300c1c0b85240c2131101c0d68240304809c466058080 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 895860953 1250 895859703 895859749
    0x140117060117010e0703110102010b12151513140f04031b030201090602030411120102090f01050313170706050c0a120c11071202040e060f04021306180e0c0f 69
    0x80c88142d400340604641c0b481c5180521038000080120310a60381c3c243ca5000d80003400151a81000d2042c1070700b0080c8521400d9000203113100d1030070a242c20701ea8010390685e415170703510400302002c682801c8c4800c040340364044e924a04050200c10401e410341d04140408825401400c150b00e0040c0000070030307088403803c038001103880000c25000f54801225158050010740d181d00c0c02e42032156a101c03003007419600880454502100c00d150600c00c0714040c0c1c0b001050402c180030601d00454071500300902001e0710f001c840c117441020400c8210007031107145007080f1040d5030301c0300c52421a054035030150100b07006960501c240c4407110341120320141e46110161002481a219910444905240f822511614001c1d07000103c2c3c08050703500303035802640c025039060010036200c1502c1035540604843d002c040c0c0745000b01150040c1781c40010900c0f00a8080c00200c0c5098172840540031450220013000c0409545041e22070803100148018002d07018100e400145450000001c01c00c810480c2081400030901 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 895862203 1250 895860953 895860989
    0x140603030a1416030f12091e0606030606260601061e0309060f0c020f030c0d14040b03090a0b090f100e010e0102130e011509090f06080a05011401170601 67
    0x490b0140c4815034030161101c01d0180d041c1c240544080340c1341c8540350001c2d007025904003d100e507038010b60010a0703000c03210005450446c120b6903454145900f04640d0b081c0c440364008007086141c01a00c000e0132006003100c030b030b2402c0503d411140c002080c140441c01c0e000b40d0700420003d60842000c00690300341c400c124409040809045009207038840000b0540e03842d01e0400000c4800d80d0b408510f40041c2602241c01c00d0064041241c0d5a0248920352001c41c0e100c1c17009007501c4c43c80380203800d10b4180c0200455040940714095119146c200700c071034002d940d0105031803006011030115400d40210f40704010b4050b000301d56103103039100c5814601050b1202d440341c40081c6405800d600040c03100d228400215100c1410944004048900e8070403584101c11080000c5101c000048401403000c401d078507191051403526004001420803c889500219610200002c00c100b05102500d0424841c0000103916030366031080382c86d00e45042c2c000f010108501c1f0441110644005525415548182c46144101003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 895863309 1106 895862203 895862237
    0x70b090a031202040b1b0f0303070c020a0e0402031c1e081f0506041401050f070827010c1515032405061e0117130204140603030a 57
    0x3810086c3c100b500020000f0f40100032010301c15903625140c0510f445040d03400490300c00004c6200c3c00035a40440c40d0180040d00907040310003080300c1606181d004a9a1426036011002e4003142c3c600e00d14116a0003407180a0029083c4d5180030345840f107200006154180c1a98031104000c5030440701d01e040220700224000b41d07080606441e0629182c40c4241c0b08005a80440b5414400104881e0200c118404000d1048038000c1e220240d8801d5403d401c1c410200c44001d440803980181e5041c500141e0344008402030301a0400d5602183e058000c50600c0103240f00084940d07400510000001046412005200120102020700c0104100100080141d50045540a9010800c000410fa112041039041c00c20810185001c00328500e401c14111001403050b03450400103000c18003031070708603d00350082e103028840e80d050b03075041e60511a020a90f07030b0042c0d1000d1401c1c48221003140801c94 = true := by decide +kernel

theorem cover : BRFrame.Cov 895683453 895863309 := by
  have h0 := BRFrame.cov_init 895683453
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895683453 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 895683453 ≤ n) (h2 : n < 895863309) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
