-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2420
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:39:55.824214+00:00
-- url     : https://prove2.me/submissions/b432d736-bb5f-4982-8749-f69e0ff09d73

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 435071942 ≤ n < 435251798 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 435073192 1250 435071942 435071953
    0x2060403090501050309100207020d290f0f04020d1506060203090f040b090f101d0402030d08040312020a0908100204050a09140408090f0d061e021e07030908010509 72
    0x2810094544415988030b10704120080042215071000400c041c1046a60070b0b0001d0f990300ba00c5d000042c1017650900d0050302c1c950100160f19114030102000d000071000a041c1507805550320800000d84034400c0703e41100c1251030744d001600502c0c0102602c25524482c0003d003100d560342080d020f085404603002140540d10000d5458210301d40b0100c00303200c00d40c08441c18404100000701003060ba1802808560038407044074049440c5101c8450640c020b0f00158000740c05000721107407406901e00301554140c0c040c0c029440e100403024401e0144c00d1045da01070725181040307444261144000d610000c004020080e10990100f850f0743c0c1402100c0c071281c80c1c40b40168589041c0703400c2048024141d4080012640b800c524810001030302c201290f40903400203002034440c2d50f104085400750b608901c443c0c1c2c0c4105840c02000401610360300000c03403002c1c908035004651030301301c250714100c0c40340100c980b0300c0c03551071051684020350f070388001c055007886860501d030700540c0e610f01d0340c3c20759006982c24050783d00030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 435074442 1250 435073192 435073201
    0x915060d1205041d1909050316060b0f24180d0506041a15011407081c0506270405191401180f03030c0302090604030c080c190b0306041b0206 62
    0x35105100103e00c5244001c4e1396a05081d90100744030008000481c0c0d402d0b48880000d010b01000f4001c2d2080320440400102c14403010f8900b650040151900d4944200302e82c900800c080d04105400c540b00011010100c444000101d0007a4040e0308a00c2c241c5108443e411070070b03800c40d01c555030103c804902c190000d010504241c03401d12843e030018000360082018170b01c10410003401608007941e030241c0a0030140d44035108d90420600e544100035000c2e0600000141c00410a2614194200440705030101042a51140c2c000c21194031942150100d120344010901d00c807503110414200d0b0800e02c50030441d441c420303000440c07100702418144c0584040c40050b000c140d11050a008003000782030f40454042c034402040e6204d006a280499028081542d25458041154003a41c1107031a02303000180450303111541c0e4500041e070f03401c1a0080ea01140904500181c207800c1009420078400345407900c1a881c1400c0c01031042080c0c10060815a0068541c0403c620080c0742c25080c509205403603001d040313586030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 435075692 1250 435074442 435074459
    0x70c062c030324010206011205100603140c0a05011d1c0803090d09030201080a021b160603061706162106150c081c0b03030a0207030b0901050915060d120504 69
    0x144102650f90008107408943d2180e070b03000c1661815141c41003c08044843e05041161405a1902d4a02030140c941742e404814094101c0000d006d41e03001c44110348090307000c0014020101d81078444c20307011908401c0480440354400c4142064040094007800f8049110b0243c102c1c01024900140c1e4031303020010500034420004c2c08480f1901c196410070707100725480e40d80006c0c0003c00c024014a1959030100e102200c10b210311400e103c0814052003101c0e017407520795011040b036070f48921400d80440c0c94140c00007401c0c4060065140042d003041e026080c00c0d907845250384200400c003040241004bc80c0c0d002c18824013194141e039808508120b0700050030382d0410100600c40c9214056003414010760603071140c00200340e1012500c000082503c10569019035486842c06480504110307a4036000c0890b144e08841d03400144403044038051040814945c4407941d03a54200d80c0243c42c41036540d0811390504446440012803181c01800c058040210001c25407a1a4484440340d98943d001560000e410801c250 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 435076942 1250 435075692 435075721
    0x1009061104120b0f0c03040816020d0b070e120c1210050c0913020309062409041b1a030103081c05041a071119081201090603020315070c062c0303 64
    0x14540c80e20801c03d0030171702c203e0800c42c00014001003a42c0c40c00038103505420450000d00c05080d6000d41031100140d468071f041e860408007245c0c040c0c009285c4005564581c40e1140d9000d0400b80010040d1902070000c0051005031208038a10002602c0781b0001d9403c244ca00c1e03c901c81c45420521116529820b0301810070580e444024041052980184107000d80c0420124011342c000384410000e003803112a80c06503902044101d0200c9501c4500c8600300010b0140350700a4800742898000d800740b00c40d031242d1403905400080218800450014030060000800c408014900099441504407a9503080e040c2202950030448084850401d01c88070410103180d00211641c0128039418201003554194002d01d558076602c0d88401114455a043c00307051100050490744907031a40038460903030351b8548102c0b401030700152104074001c0c441e0218040d802c0ea04e0840301801032489a0390325103c17694580300c0401502002c2c0f0415a07802a24405d01103a000314205c5211045d8110040c0d0f40324a0100002203403074 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 435078192 1250 435076942 435076951
    0x2105070501080411120f010207060f0e0613060c0318030e090a05012108071a04030f0807120203180118170a0903080c0c040c0c020316081009061104120b 67
    0x10b03040148000210304580d203441420742502c040900c1c40d80c1030502132602070000d14082d0036504c0041c4080078445c964015000805c0c00c10001d010421003c180c0665428085603840703034100c3d51840f0400014816003040801056a26010410580104d0700031000d13500440100c0110b00744c40f038481103605202000962003407134440100708540c505050f25104a03c0050750210504030803500c90100152039080d90f44da55003042142d4031140f00c20380050044901070f9016030109461a0b220a0b1941c4200201341c804c071050b59403a4248141100c0e0880a900040c0007520500c6480c24558000c0e5000d1068903111042106602209001401c0403489004401000c207840c5500300200240c1d55080f44100782240e60100001c0c1c0d60301035003c100d9080200140c04075070f01a017483d02c0c16170f80543c0301030b1068041d1300882c15580041400104a01f480c22980325841540d0015400b0741170100140d804840341e24000d1401244c8005004441c2030145c0c070640003001c00019403c015002d0024052030705510 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 435079442 1250 435078192 435078197
    0x70c050c03070e151e010f02011d1e030304030c0b0402130c0203091009050a05101107060c1104020a0818010914160b160605060f03010e0a03081308091201062105070501 74
    0x4071100085d00d080410060f044a03040c0281a56800101d038402d41c001c151216030208001c44c158040c140c1581c6072088500303401e1902e2a4032002001042c0e01100301d81c01564942c68401480c4195a10002004e00080040c0c1e4004800000110200c40714000d02d190303030300d07150b01566440b50300408010030280801c03410010001010010320450300d074130040038199001103491041030b04030458116070301e0f191182d5050550207890703c0081c4070390b004800500c46910400b84030280c01e1003c014001240102e900d0300300041c00702004501c0101c0307245501075802d80700c0400850080d00688895001c494103242c061103d0b4818555848400c00000b016005808001d41040c41d2898400036000354a1180130b010b0080d541c1c80d0013154869a61280c445081000640203001440e2403a000f035403501880207007903002c07828020005450912041c0320389070440e8064030003405c0209000031312a4214600074582d401350340c1d5040c0403481344103054a860490441910001e5405060b1415608060700f69002505 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 435080692 1250 435079442 435079459
    0xc0b07050d0f0c020d231906060e040f0b0612070e040c0803040f0b0903070e010e071e0f1218050609070801060f0603020903070f0b220b03070c050c03070e15 69
    0x1a55001ca030b141050340c000c070f0405030749400480460306c0200c14590b8030099105280300040041a401d0002042500440d802c1002543c1d9003414202c0c2c0d20b080303030010014441c0440740800039540460040d0852005020282804010a000c52501c074864000d029040f407002d00704003c0005440c1108060100e0700051801c083c500440d81610500780e0054141001003c19078405a80f4100300340710003040003142c800d403956502c185403034410b03d0540b20140041c0c07a5a030b6072400c81c000b000c0001c003400c0150ba9100d10003828004104d401500341e0980400c555100c64580714103404c00004001141e00483c040c0003d81080d43c5100e03e4060194000e02c1d46034100501040314100368400001115810700f40903984806150010342045525041700e126903111040200d08099907038058090761021a5088006d841d4065401d082101c0340d00c601d0700710f04000c00c000780c5010711034501c20000903c12000c4544d411500b10009081c0708103a084100ea04504400f082200900410603015411003a00c0030f80 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 435081942 1250 435080692 435080717
    0xb0403170901020a0311030d060905070e040b01022a0d0302030a170609010b090111100605040b090c2a100902040f1802090c0f0f07030206060613120c0b07050d0f 71
    0x13500c0396801a40581030180703c0c04449002da000f03000319460786419403000c1102c0e80d20341da01c0500a2409445010008865204030800c070300b07284c0b28010705541c0580007080041610301056440c491007690b03000340c80b0007004c1040400c3d03c912003d907030904c0c8030760040c5485004c0305a00400783c0302c081506204088415043c8812902d8450080f41900d901042059492400d5070040e80d00d0000c0043c410310300e12885404407100c1402d079100e001900d00c120707824041181d889080010400c0700365081c8160080c1080740701184042034440205401ca60180c440e1418021040142030980b541020030403103840713041000861815214034122075400c04c4042101508510807503200a00daa4002801500f8010126070282d08500c159501803566007049a0307201c00d4801840142d40105a08401620459000c2042031801c2c609584204500c82900c1d0320042c64042501ca070180136040948403004503e502160201444004042c1c45000c1d00c0182004d81c51040000c0c60400c0c12255034040014100034071 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 435083192 1250 435081942 435081947
    0xf060302180103080405060d0207080a02011a1801090504030e030303070203090a240f030617100c0219170d0f0504110306010503031c0b0a030b010609090203221109010b0403170901 79
    0x680c25100b0644900ea111023000070520003d21078003001901c01e6001213948aa087d905410404070b0804216400c0c4c1c40160780c60a205c117046c011440c1e2a040b4824038018040d4aa00b54400e40d841070103860316866003c0352001203400d42e40300365072a41c0103800020304481c4a003080384101005114400b152924051410f00c2e000c4e071801a074400c502000040c89400c007026101e0741001d07001c1c0404c00c0d1010100060907a40d555603903412003400c52454107020b040c840d61400851000215102403002070124040d5680745032001c4400e1050080140040c000c1264a101d58891000031070314030070000031942024106068060034410711030b44250320400c018429078038040709613240a00c49000826060107075840d400003502004265640021229000006110f11841c040f41215141d854070611b040c2c072081400c00360321080b503e109aa10310a1408883c018040c0c1420141c540a506034040f614508400505040020303407110308014000f15050081c002428400c00b1440c005210180ca000c1c0b80c507001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 435084442 1250 435083192 435083197
    0x1e101a0f0d021c0e0f06090606090402010c1703070906021504080d090606090f1b110c150c1c02190c050f03031c3204060209060c010f06030218010308 66
    0x45407025802040403012420148800000343c2c006072010301c00d0b07490700040907550300e01455446035203210702c4000c566448404250103020304406000901e290380c0b82e80054411140c45a802c803141078080900162000340d000103140034089070740d10705994503e0b20400074a400791034090001404ca000042c44005070304002210b00000300b500000c660000340c0d007880360040802c0ea00a007409402c0025016000507a544483c0107a901500800014005100222064542e4129948007540702100140041c0b40c0040460416010700140c549040e00f03400c41a400c16580c5090700003000b203810540d401d56038045c0150031902c0c41180e900c4030000c00d151200c4d0108000341c42600d005420341009040b040e10248211542d040c80f01c040c0380701e005480d201d258004d2040c0001003122551003c8040540c02c000c03d035540c402000c404044076681c85503120800250b1120075015407008007000307581c80c841000e004110a0340f101e8440010020310714018041c032250340d0000c40c2c5c1c001448a00500014252105 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 435085692 1250 435084442 435084457
    0x11012010050612120304031106070914040e16090617030304060b03010608030f0301050907030b10181203020a0510050606040b030402031207060519020a12051e101a0f 73
    0x101180d1500d81e00049495183d008111400c0c50081410035500090b156008501541c466a2914955400101001e880e80740680d02500002e00214080003031104620810321500002800011000c2d001d140c039034503208100301c1d1104000c20041c0d0402002943e845620001c006490a03180e2105500b03810a841c0d00c0006c0008000540c0c0d40c00c0420691800d504c980e01501c02e01040702e966407070011010f48960000d100c0e20b48078200c0c0e9030000780c81500ca4002c800e5801c0000d000c5203048e14103943e041d07580703185035900c0c0e400c1d0a600e140002100303008900c0311220f190194010700a1031040e4200582090329800c0380600003403c000a101254952070211800c8a01041c0480d0f12500d40c1e00c0064104106401d1441d94143e0102d601820b001042c1e00c51405000040103090f48100c14801c82816401400107503004218410070350844042290012940f112101c81c4c0120421402c914050100c0000d440c2c02202c00d070750030030904c202e201403039591803654905c003881c0b42071412509070100a03114203030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 435086942 1250 435085692 435085723
    0x2060907081e010219020a11030c0a090e0a0c0b121305060705031b030c0c01050f010302060913061802131707142d03010b0901081018050a110120 64
    0xc05044415420341c1500c1c2c2e031040c1c0e101418445c029a40340295120950201601c40300c05425100c6180c0c03600256042ca140700140c14000e040e494802c800005103002c41d0070318a03d0040105480020b15004e0680014040054282d5151807117040c1031007403d90020800c4c141c144041001802081001235020751150075070cc0c040f030348e9030b6400c0c0c0d201907180d800c803120b900c07290408028850a9511a4050210008018001c0100340d841915052086000303101c0070f07411040400040c0c1b514207045400bc1e034170307040010010a042d50780314a4841060103400c1c000003500e90201d0050144000c100d0040010810883ca03900a490422001501c1d01d844d0b104d26855034a640300d880c40c103911800480c030000a0041c084e44021160703078070750841518900e48014425483c00e8000203c51a00c80b0b03019042c1c4502e07500070526082102d1040008007a4084000c0c14800c4182c0b410000070b03810401c41c0443e038406d11444902c0810003002401200d0b8080600405030500c111880c12003500080415070541d851 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 435088192 1250 435086942 435086983
    0xc23041a04020f0c06070503010603110a0c110a0824090a03020c01030b0411030a05010303020601121109060a030c0b09030c011403040609081626040b0a0507110a090c0206090708 78
    0x30041c1040c0ca1184850390600d9024240411040e142c020008e14102c845545040c03040a00d4298080c0132803155490400220741c24050748404602100d03450001c101010780144006622544454a40034250f48250407007507000760f10030b1295a81e00c040f2030700500c0b1600140007840303455901940780c60420000a0402d5a100c040c102555038a400c1050440d101a204a40d207040a41606018020900017540580b01d090300004a14610034209428540c020741203c0305c01421808001c10f5100113484035a00c8400b05002001060220380120010481031111581e600021024581040200038905040c003c010712492940d0040100300e961040d0311090004074010b591030004010300034101d04141c088001403081e01000070300240358114104ea160754042051540d03140125a108a02810318040302c10301c83c0500346405403002d0060321b4481d017285840d441c0b4500200b107024801d64098460300d070311009850060398040c010b175608105030750042c203c00ea080a9810360340356004654403010b117115 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 435089442 1250 435088192 435088207
    0x5010203040e1f0b0702030f0c06090112060e0c070605010504050c07080706090501021b010b030f150a0603080a0807030b010309020a120614010f0f080715110a0c23041a0402 76
    0x403a04900c3c82010250b000380002912201014420341190900f203020b0b00ca50108011101c0c80028003028500000b44498941b07400e80c001158148919404441060348036080414241d01c001c2d038186c820144c501034640c030380c8043c0c140082500c106a0209014038541402d201c003010f4828209d8942c0d0783c002001c2c590b500780398581200109000384018080303520200c0e0b0751045400707200400844003001c0d0028052000c3d20f10806031923400c111076000941e03000d805480f55020880c03078031035800203850b0390010f895a565201e516655102034070100c0055006010040010342510401c80038400030300c0c0420417075042d5808211700e1030480c001c0d0306685070507620700380810269400120190500f801c1c41515560f64503041c0202d113405018050820174604c40104103000c0c00134510048074072900c24440503416407031081c0d0354807043da0801e49090081d00c03210004101c201049070020079084119014a8042e410b0003480f20701441c0016125508010450710100300d0241d01c0c80104100302c138010b075241d030b6 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 435090692 1250 435089442 435089461
    0x290408030301053304050a06050f0702191a07030801060816030218130b030111030f01030f031e0e040501170c1c021309110604031a1b0f0712020705010203040e 70
    0x10000845020724103002e003200b6420203000c01400855201f81d807031407100c076260f000589032401b8081501c0c1d10054140040c002518000383c2403c50017110040352268203031558804405031706105c616204c16a8002001d1007007641c8440c11030300514080c0740c440241e0900011504054880744080c1041540104400c0f032180d020420880050070000c0603001078050540382540500603401046203e03500c0c0001e813602254018003200d100762000542006a82e0856544080520710450141e00f0048062406d5001d4a8010300f007203c00d840c1d82d01e502e010143d0240411098a40503048001e10328482d0907403118200700062480fa001d1011a05801d21215a00b00628840c5070000065030208100309261464031003603001d59030440c01546491448101103081c07011501c194440104900302c044050035180c003110300079580140c80f20401d41003505e810300301c0801c950021943c08540c2003000a0100c100016481066021817a500140c2513145c907100000c3d4484c0940d00ca42042c0041401c00103071b6010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 435091942 1250 435090692 435090739
    0x408090604060c050714240702060d021201060207051003020c1009031101050106091202060c01110a02071403070e0612122703011406040e0f0729040803030105 70
    0x50015091507140d41e901e84005080e02d030019400d813010b000d01400442c104400b00c0728000712403405081d10741181c0204040050b0f6040e400b68080340342009110341001a91450000e120104030300c0409030f11000c1c032941560110704d044c0d01a60941d441954100129107512885954040301c2d82401601c4030018a00c640c1040c0c0c80480100d2000c2c035100d03524040640003104014480410002000141e80300c440582d10b1001a005d500100b00031307195041c005107010b000900301120404008921511100f00c0041036030820f50350140540c01081c020b120b50300341c84141c0128214110001c0074401c3c640038142a210360060301540c0a0f101e102903001c0c050104201861000540c84407040c0d850085180040c4200010743c6501d04014036002c00c41e14500d8140900301003078840310320042240c0c170341c20b0030000102446001c49019002d614032010303406905100c1000240247c0da0030120444151401600c0b0342aa14112100f1001c00d04c014170220100006032415500705481c10740400b03082c80c0c121034000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 435093192 1250 435091942 435091957
    0xe0d030c08030406020408160302150c03122d0f06150c0a150501140915180a0905010b06040f060c02060d05090703481505070210030c020607080408 65
    0x4000401c3c40308000c1c9950007041110011030660709060070304034110850000320b21002e5030203800307900c103000c4c00140c101c01000482036450460745000014242440003100031101c6401c0400d00c80b046d900c0c096402440c0d00d80c1c8000d000074030400d43c501840c2d10380c103290020303200d540031340364100690740d6002000080710039000f05903044a02040c800c1c64070045042e41520007032103a07810072000041c619030002604080140003400003495035070344c00c1c9500380c20300c020200507840012103e81500740f1852003001c1e4021485001c0101e160074040c10414252142d86002c503028090402042000d9640f001d080400c0c0d070140d1514140c100c0090001503400e009041d981040d191511041c0404048002200c4040f0391007034400c860f0464140c1a000d804111414031040d0020520101844a02007182c00704c501071022408020f125440d6000c2e58400c070001004a0003003036002503240d0551a126080440d00711491506204040c1e0b0210020340301e50015100324140a50030300400c04000c038000a5a801 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 435094442 1250 435093192 435093203
    0x207051509040c0908060a050a06091505090c04030507060f0c0c0e161d010302030606120118180809061b1f1506050f0a03091703250e0d030c 62
    0x500c028045644415400100481d1050340303005003070200c46000e500d02c5800c44011030050a803076622098488090035000f4194440c8a82c2c4681c04100310400741300318030f1004004515450003d0804c414404c07001c02c0038001c1603503144140000c2000650016151003a2041442c0c075048010001030f09441200700544000d1241c01070100200e043d0f03c855084510662a20003901c50070400c00300d040e45d403e0121402c0210781d0380ca8205258440d40640c0045800c014090b00591404a107481c1414a401d42038000801c0305146400120300055180242001e030280c03903400c0305da290300554921005100d41000107001e100c0c00f05001e0b0038421800004018410030750140d445200e2011000c402059801032400c25143c40c0001e00c00340078102e0019103095600c2c6807519460001c0e81c0003580d405c2c0d00005a035504058079000960300141343e070303105400d85030748400c3c0b45a00d03801e1203541480940000c035000f6071020846644400c10507400711980c0c1c400701095405011403442401d01715407107954071402421 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 435095692 1250 435094442 435094459
    0x2120313061d1027050105060a060e0a03020108070507020405040308091006030f2307180b0108090a0209090c0607080d0b09190f0204080d0c0308010f0e011401020705 73
    0x88580282201044140c881c0d0020400301081c580800d02c08082c09901e80c1480d404034154007081c0b40d03103070322681e101074404c1000c2c100c410040769a01d00c02521080e04840c241d451f14241321040c10140c1c41a0080e0155040c66040000d07090045011040140720281c1001030100c049080e0b50b00450840e117075150054000c0c0aa45003904000d0311014041e20180d840e485440e541c1c02081881c0d12868007969880101c00039105116265441c0b01e10a481c0001091403944c9920300c06400b080041400a04021001d0000070a0451440d4200e80180e14a1414000100f0401c110b2060204a0706000d0b40e04544103880c0d511114195890711520007a400d81100d0300081071014000703040003610011008920a108069045c002d205c200b1505444450b0600102c2c441c515401905400c0511100d010840040c28282e40310b60aa00e4085110540b0000c180800c2c40311050581c00726030140989100c0030f0a4075064680000b0440c1880144200e1004550008455a40d60310034829000206402410b00c2c4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 435096942 1250 435095692 435095701
    0x8030c03071b0b0403080114030304050609040216030810170c04050912070320010e03070303020c15040b0714180d0809060f0408010b010f08150406050909070603050a0513080a021203 80
    0x3e000d540640114064100004001c0e0403405504c00384080034004c2d40c00d01c2c0c03601003444100d422020780310358001e409000e40c1e5440100074031100e8205020f5030350080303607040921690202d0101500f1852004002c400040024880000c52511601040d180002d0581c0d480f0000c81c2000c00e02c0504a09600b00041c5000c14035a0ac00da41c1c1130b000d003104212403584591101e00c07070b088034007503002c0644030380003403000304040380c043d9000c1c000d514440d03416605c103100d01c0c44212070900001c9500302c92881c440c205020400360f2000c5000c44401c06050050700d03203082c8542c2e2440d50100070206600c45d005500e401010480000160351054402500d644e444040300e01100030340e0340160060203d55071030041301d08070940c8103494a048003581919054603a40711010984003204038803000300d4116460b81c3d40000c0c1a01c03001401845500f0360b00140c00f10740d041c040c0080903220050000c0444509200501441c4504032b050070100c0d60340552510f55900003400240c0c14901c20b401ca415a6071404001c00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 435098192 1250 435096942 435096953
    0x2a05060f0d0e01021206060f0c0106060504093b0109120207061202040608040b06121015050307050f01030e10060b2808011e09090c0608010e0408030c03071b 69
    0x9000c05a00341c4014019000c1000140d03080b07005954600c2c07034210a110201b040c504204004100d24445040750b51301e0082403070100c1e42900d1440d0b00c0480000d8000400300000e011038842e09203214500d0a1200c40340c460351400891680d010b451810100724030315661070b8608000d601c0040f80a6200c40b42c85800400c10101075259040f0f88241404544100300c0c600c0803001c2031081b83c4c19155991901c51942e1a00d0b240c4189881b0b00501d9141c000340c0c507003080081000100240e00c4c7c400e410f100e02007240700021582142c28903495004ca40a0b030701192090044c0c0d0750f4032000b15680502840d0020b000d82002041d03603d030042c42505090340354500000401e00e440100020040300c50440084413444128a0f80c0c14100284d8605901c0080c001d40018456160000b05d024403404000748101c1501c0d0b140c5002500302c1c0c180c0d1a089640707000100341040029040444580108002c2070041c0040c0b5003515213090510000b04414514100040055000360080710050700c0c0e01081100b40050440501c0e10 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 435099442 1250 435098192 435098197
    0xa0512010e1b190b0d0b04091407170102130306090503270307060807020a141606051206060703020d050d111902010e0304051305090a0b090303040b01080a2a05060f 72
    0x5400f0f6284000792030703c4914a09001d50448040c043d01c41d1501d507080c544000200503800b40203900541712440000441c1c201a03080c000343c02d003075025040c0c00d850700621500c0c1902020070b491311a40148013101c1d2110700b0008050442c1d03004072001c0303990b6002c0d1400e40c3c29032081680c407645d03a140e6050001203023a08a5000c6041810542c215040c5a031900c03020b5503105c004403080360042e0b01c480701e4080000c1da500000c001d004e825500302e03241100d02c4105499001100e801500c0007407270100f030780392104000a00c1542c201c1403e0314207a181207080c3e02c00030340700c0817441d90041c18001e00003500c404203400b0342e1068100c46010101c1a49130b88456a101440031880c100386401503081c604070742c3c0b08100c084111012036600410b0240054a4402804080c00d0014060289400380c404848049442058140d200c1e1016001440ea40d00d02407402440701c01041e00440d140d80c1c4402d000720b0014040c035110088121000444280c802c0792451071004048458200c80e4022002040301904005040301 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 435100692 1250 435099442 435099493
    0xf0405031c2613020415060e040f06030b042003030415170603060a0c03060b04080a020330030423010f0c110d110f0114041e020a0512010e 61
    0x45554926800b01d15442c50352800340307400c552844101c0c002c11484001c0d1030400300301d103101800218201640c4a02c014070341c10f0301d901c65404241c2c100f0160340306190611610404a40b104c5042080c039013151504142240001c00c001c25182010701100c1260081300207040f045a0018200e07a80c0340d407600c40d0303040102c0c4035a4201e400b18100352407100c0384500001c507480c41444041c00500305030b40d940c0c4001c80900b1004040106060b41c41e10080ba00592140041c00540103800060246141900c10b0500e06080401103100400ea502c40281500e00b890741b8403d80c0314030a102e4a030b129221802d010352070310811202940b0f400c5641d650b5408a09064004102112407214100500c1c10b134280180c900001103420b07a449500b180800c3c4041c28003500903c0d1000309410100e41da00e040d01030302242101c95a4880980c0724850b13604110820898030b03030500900d591403d00c02c0080fa030903808610012403d000311440b48021742549516140e095010884011178030f0225005500101c0103503142115209 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 435101942 1250 435100692 435100697
    0x170c0409050c090f2b11190e040314040509040c080d050f091315030f0c090e0d0e27060315060108010e060d080c0c0a1502030706020f0405031c 63
    0x2610b046900341c1643c240303c030080e0a0301400700c00e131801c00c8416085141c50603003c001c20003540c9042100040001141c520512080c102c0c1007200e02000740c1461055803540301c88041c400c0030b205503103440140310b4015a0508240c0c8440c8100095680d0602941d0002034002c00c05d4420801440507400507c8116101c0e10140c03200c000ca07140e800c403014071038a110030210380703010041d035034213030070b024034082c003440c1c040b000c0042d000810320181500c1130580d0b4401e032818028040c20b00180201d0380521001020469810880391411110300e9071200b007040003000c2840500320600207a501c440002d00e001d1002c0c40243d00c05031744104c4440100100c02ea801034041c0c4241110041403114005025009900503114501260f290182900402400901554220580d20703c0e0754001844500a40102c4c0211005005100000e0b4103200c410411544000207010003a9040c00b421a00441218075250f0810720159403421000c0d1800824402c0e80d000603054801d00a002e1500d61034621018004170555 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 435103192 1250 435101942 435101951
    0x1503090105070e06040f03030e130e1e071d04060b09070c0c090612140a02031009060b090610030e0f0304090902010f2a110909010e070617011203170c0409 68
    0x31004d00c10180910b0081c05d070592a22101800400d010307002c010710000d4020a1101c05592012000d0300381e820100d00304149900403041c20010501c80102035100b0945500249102031610084c50b800005c40c50040c3c5c541480c14020034140f0540703401c110a03601c005000b0600f81c1c100813100604200888206540741d8841038808102c45031980521400c644082e400c540380700340aa141c1080c141d01580e078800c2c0d20b110f842543e4005803070a01c8240816451003900040c00d52040c14014280c1e040341004e40e104101c80c8040200603070300e0300a46c02001c04249000141d09000c000a649884030a14010106100204d00000d0050031034100c103031100e10030f07642e200510020840560700720414403292452042c0d40d401fa0181e40c0800303180e02501c01d000314001d00c8004020808039590f04015105501282d448540303011140c001080000001d0400e840c082040304a0200740c541022410b0003842c40d441c905c1390bd128140740c410119110301e41c02e10300c0841e0701e50070100c52145082e0f001e071068108103401d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 435104442 1250 435103192 435103217
    0xb1006030b0d03030209180f0105041a030a151808071101110307020d0804030807050f011d100e070b03100810020a210e070306050a0b0d030c030e150309010507 70
    0x207004010518a000e80245032060035690103030040c0d00300309421508640c0603260070741007030488000d4034091480c0301820000d44d414a01488281c0f8448001107500081074420000c0783d85001842d24803507900000b002d0741d0103500300032020140140400301c1400003158480744044c03200c92303070090405038800c900b10740c0c0c000c03410001510081c07038200e410f407000d401c14400e02016041c104103406025126084c0e0790311702a1240e54400450b08010406d403403035403181401c440e00300c80900c181d40c0480100d0020b40300c081d034680ca6081e980ca41d110300c454196900c4960110081030200001000360803202a00e68aa01e8402d190f4481600c00d44a020058405c4010701140802907100704c44400c200c81e07484020849460171050750254800b41c014254a0381c0d0314001900220074804200a1440350340040340604100118005071604241154400c014404000002a8112040c94406030f81428440c024a020500083e103201002804805515000041096024065109512500440d203c0041d140031 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 435105692 1250 435104442 435104447
    0x5090609070e0117010f020d020a0905151b010603050f0a110603100b09012c0108100f030f0611040608012409090b040609060303030b091f090c12090b1006 68
    0x50078410356900100c1c00b4014001c0300643c1c032440c00742d5000000082496000b90503020201d0f84010000c0f0403a542c04a82d40725195844481040209002c030b0b0503010841009074110081d1046a6600180a403020b0040006190a4008c0001580c0020584803041ca00030b4407207450341e0b01d0401c102c5043d100c51300c7c05001d514007081030f28040d509140030034102508205000c42d050b401035003100d0500c04401c8001d9206540384640084070400410104490068100054004034000c3c205001c442641541800303241840003d03030007200d401c00300c2c0c124205002e092090003001e01c0851307003e8079000002d02041d182e40200c44941202d603c20455490201c0d070f80d00805244012400c0d00700021808002005881d6068004068451000b040050b2680c0d6903414401141c809030b208a002c6526034011110516103070603603a5106e61a81d81c076403035007102e042d181403000c080c5010b10b40c0d085641d204486e20079403290031503451454104d03900300a0f081081c109284403010440b0b950613030101040003c6000c40c07 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 435106942 1250 435105692 435105703
    0x9050a0c15090b07032f011b020102090d1b170c0a0603090510051b0c0c01021e060a02030c1204030c020909030711060a0302130902031009091208150402070605090609 73
    0x4003c420118140310143c2c1d022105008100c900c031201c0e499821309440100010300551800740903202c0001074000368400350001884007088074206592040c03004c080c9507122803411808495012040c4603000030040d68003000c04446801004088820040b50ba90400000410703070050703030085a403081c80c103036038460440a680c100d610080c030903040b000030542110815040140c005020b0012184180444044000340342c100706031500b070a41c41900304078075950301403081c1c08451800d81d40c20503040411a0f50300703540e12000f8017400c5403164000b0015903c0c3c506070003a940100d0030030b01c00112500306424002e10404552505038410300907040803030040c0c0340003c02c85072200c0d0b01c03d00c60500845c4000412000b9002410b4490905400b0004182d1101c0340394040030142c4280381c4016280d003014648035841e01c40390b400c412903d034034285400340801e11040c0000400140ca1501e00710036a2040c0d100c07910f00240d1545035422600100e846000c2051641090703104a0202c0d040310720f10b588000015540c0ca = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 435108192 1250 435106942 435106949
    0x80d122a0e0922020d0302070b0d051501261b0414010f030b150d0e06090d09060306061d010306030c080a03140708040b0703090509010f05030f07051507020409050a0c1509 75
    0x50f01d0b070a43d2080141002e404200c496800390058658a9548280314002c5034084403000c0354045ea41d5003004034055880061100d484400e20f0700c04141c0300948032007102600c140c3c01e051a42003406c40003a0406140d210641220a1002405526266500310710000f4004194070180400c06c3c00c0181c0644038031902c40c40301da40c00000d100080f001c0820750b51414541c045140801115100c11099126000c1004084c2c0140c007114001c060705562401c0003011620b058000104050400708100125548102c1800c84030707000d00010305100c107001d40142d00404240e88002c22510b280600020090000710368200c1581c00303038442e072650400003540f9206905c07031002c000f0820b004c00e2009010030494140640b43c40391083c10f0035540d0a13103450000e01d182c0f400b41d00081401c1404501442907050a01c4560703004500500100038071414480010b8404251000d01d034504180840d8040c2075540b07980016400542250541d90200e1085c10094000451401080f003000404801c03140c0317080c860300188045 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 435109442 1250 435108192 435108241
    0x3051f06030906060b0310050a0b0909042301150f1e091e060f0504110a021c0c20010e0d03020c220203070315080d122a0e09 55
    0x18104030080c0c000341100002070718425038908002c25582d41c0140114024498000c2070341d82d044c680410001c40303150540040303004400c203001c2c42c161078484401c0340340c1040d4001c090a10350a004220260184103d034003072540303582019030380b0044043c00c044010540c0c149000141000f6260341c0030151140600c0c0300c0762b2840c81d401c4003c100c2c40545600414403001d1450119506e504160142820358a09802044c00030860b044200700e00c0c9090b00c07480014128020300b40e0300386a008030b001303074460260800c0481d00301030111600f21401d00c21240040304079400354200b9805042d0485842e807113504159031502040010311a2490351800399100041543e25a005218001c411410b00194030407010142000301080c000e268903a280a002071440794100d80c0d03001660003000020180924010703803086099800c56010030104030750014034200c2d402c105d0900812005070a900741c0c0b2220a2420071717143c3c0c4030744c4001c00c0105194080068800c0e504125000040394451842407290440006214140c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 435110692 1250 435109442 435109501
    0x30e010f140f03090a020316050f040e03090d080c010c09030b060904050d0c020f0d080a0e04020301140f031c020f0d0201020a210902030618010e0607050a0507140a0605070305 77
    0x141c2c821140c01181d0200121040e2044200558042488c0c80c0748810240c00c0840008401d1000c3c2c144800300c3c0026841c21103050200702d8620308466224800c00340b0706406804606419400c3c041d001044591500c0f24034000c111111017080c0c01004001b141c00204d03810f46400700800e610345411150113016903041005080d0f05580a00c00f982c1490014500f00e03003101148040100a80d901080c2840503070042c1030340c0380d440012240c014404800c14450034443d600c11b00060154580d1641d00100c50301e02940c45401c42841000040d1a00f00c3c0d603a94012103035002a4400961036000c80c0e00f20395171001c2e80456440c1030300321100347c2c241e005844007000090007141001403040381816810001214129000a0207a80e0744c001c80c2c10004200c40c850441d0001808814001c4402d1141085640d8010b0180209043c9120010298402c071514202082004141c1800744503030f80c590115801144012242540340c50310705407010308000c854081c00300340751000184044580d861000401021501c016170b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 435111942 1250 435110692 435110707
    0x5060c070e130b07030b01110a03050f07060e030f090310020405031c0521090f0606181b030103120f0804020a0b03180601080a02041b05030a050c1204030e010f14 71
    0x1041c01c20040202c00151400780000003c10f030000c4156010f8a07040ea00030408001180000d001344810400440c05131b405428403001080c2c2c818142c660359168103c2c50340d40e444982c140305005c1c080c100e4085009000000d9007000550440c8020716401c10180c2c1520b402d0748000b42120101c0c041c501c501078041d00400d114040d0101c19078842d005294107403e010342410080701017440c0e4080c0b01c82000005036442030520000707003400c0009800e1413410100074a41450014003144c01c1c1451f60400e0311070002c4400c00304500205009140407116007591403c2e4503507a4030b003410702043c2c04502805011501200049108a10507a91680306a030054215a4400c6c03412107504840d900041404003040d20305441c031551001c050040f01e0081c86001e00900c03250070a40100804c0f500c4d501c8502d0801c0c10150300b04203400d0b411009590b0310070180c441c00500c40c0e546958901c03652041203c4100c1e0545808208000c0542207040183c14800a0b40c88042e00c119511003a00d1185881a003100104400e00001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 435113192 1250 435111942 435111959
    0x1170f16030905030d06080c100e0d0206160f061422050c04060b0d05010b040f0b0a050702060d09050c0111030d021b0703030804060b0a15030e0705090a0209040605060c07 75
    0x22101002036180020390010750340c0303881d4103503044094800e00c001d071214400c01802ca400c02c1504046e0000300d528070714980038118041d02a11030910218004c40106081d4003c1d0b5850b0301c150f074103030400e82c02c0140325169907141c80d103014072502404550503440d124105c001c00b00070a504a10600040d1808000b80030b50b200c41c3c0c13104410508040b0780621990000e403285032100c0c01004010f0000c10307105900e9404000d103201c1a950b0503081448111420700040020308a48409502164800c007180ba03a9449440c00c100e90314881c03034030041c2d08860006150703408010103a00036084640141c2c19117005e248000011110100c490307080003081d41c01030140e001503400d03d500070002240c0c030302342400b01e4441c00d040c0d5600301162a4015004100880208024040a801040040101180c080030346904040301c86000d940f4044220041561f1244c409020140c02c000c41006410f00a14440e079034602841018040c0d4800c221140c016404c0c4040003d681c1890829914061800c030040e15000e400c20160 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 435114442 1250 435113192 435113221
    0x2072d06050315060c0c12010c08070f0203210619080705150c010c1707030c0f030c02031209010b0319020603040602160609060f0b09071409010e0a1401170f 69
    0x3d50200000c207203508655445000a1850210510203803800040150400106606017202c091050341085480360075039a10001c041d034404502d08040202d1104c8450480c81d5002c1d2030004180c4482600c10080f400d0740c0d0348a2030707120b410100c03981041e202c2c07015a48140f50000d4803400e0580cae07224260a02c02071400461410448107502552800c1ca2a00d2400a0a484840b6000030115412a80007081f50003482041030b40301100b81828000c003034021000070302c030352400d0b070610041607038810020b02d5051003841114019040e114811170b031030910034819030080001c1150b042c400d02c2040b10b40c1081c0d04014911030401c0c0c0d0001c01e03040c15a03540c0e458040103540710720800b819040b211b652005c0003900c2da1040640340c5000c0d09002450f2441441c401c000c668080c0798071031140318032604001d4001d502c000d980d000c0501c21498161900031201c01030321429000d000556000a0401d0045504480303403010044c0e4060981c1c2d0b01100b071840e6031060303511000c16a0b503003684030301104c0095609840c0218 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 435115692 1250 435114442 435114451
    0x1050c030909190b120d120f092103360b0103060221010506030411040e07170601060c05191b0b0711010f05040e18030a02072d060503 59
    0x80d2803030458010000745000d40c084071540c028898110304411012454400c00301649002c0c3c401e04e1a0140c41c81c1081e685410602d40c20007008154442d10000280c1030300224081b0074911414000c2c11110f2809400000285100d0f1281b00d200c0383d152400c0500ca405520500b400400f0356a100d120421140422144242554118800c509020b02c000030003048001d802076024603001a00c403400d0b007010120a0201d0484400042c081c0c0c0e00501c49a580c8c042103076085940b1101c18848280b040010070082c08030002c0c030842c02d0161600020b28100c8403000390120038000070540c0c44581c2c1715501610000c02201010700164803141110320011003900c0d13003803c41c5000390102060800460300d0090b008480b504101e048a40110b843c5d400c1046043c0c420b00c0c84c0700c0900f0700e0042c20f200110000c00c11b0003984216520400344d1000b0401010031401c000c1c420070100815259a4082010041d58604883c4103413100e40700002400d90144400c03015080d000d5103c106605021840c0180442d107640001e407 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 435116942 1250 435115692 435115717
    0xb0d0608150103030e040c080105040b0a091b02100507021c02070b030c0901112116021017011d07051c0f1a15030604050c0705010c0801032108060105 66
    0x401040c480c0e820441403003260070140070103885606524004100c4804d49a002d8003680c1002128140380c0d030804184c0e41510019940011040450000140342c01c0b026401403004070b1419802000b8124102d03003e01800b510364080365900158001d140e012190102c40003401a00300d0714160152a0140d001440301100d01d10468501640701c6c0043c210710b610907980000d010b10001341e4010309503000040500740c80c3c640c90281c04140001015419034640541200d14030560024200503000e43c0440040741841d0040c00280c0c010004800240601c0f464070181283c210000c400020448a040c02c1d071640d002003107213421017a03103e8602c1920203400c040f41c11a0141008080065000c0700c40c0f2801d01899030a400c0421054048689020f140c1c041400c03044c00f62100100003910155144100c4c3d41001c400d440018807503888800712003070350089000041c160750038004510300240d0b0046103e8140e0740521310002c01c50901101c7d220f0001c000d1070120b0040341a10b070000d0025070040b0090f000070000d90 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 435118192 1250 435116942 435116951
    0x70905030c030c100512010803130b0a080129120105041d0a0b0a06030b09060f0c09010e0d0804030c0f031a15010309320706090812091f0519030507090b0d 68
    0x11606c401076180980000c1e0180e807010a0000c03114515213240c00040c40001c01180c50108400360050448005004d09031000c40d1f501890214082c00743c4910b901c208044420a8903440c008500ea09030020a00c10f01d032255041a07544040ca80c1c0f030340f0004918484501c0285071503185039680d4031352014020200b4820310768854000010482c5034507401c0c030908510019108529043c142c46e83c007281c000e0001580e040080c0306001079a6000592000031b02011141000c08003407078a040031a500c03554200510010304035200041054006041900303a030300c540192207142498044400340b2078000c07515003066429800c2800c2d05940658003889481c2d004600c00e407009010030084c100e841d98401c0c00d10f034001c0c08403250b01e105a002409810060308107841c00c401214900440c065444014100d48902264005500100c1c1e644144a16420114844008414000540d000f9003a5004901110300404c44440e0603000240300f1b104031841290b00f03403219030006081045151051f003103400800c401540e076 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 435119442 1250 435118192 435118207
    0x503030408060f061c0303020c0f01061202040207050304090c02031b0316020f2b02010e03070303050a08090a060c03020414041401090908070f061d06040804060503090c18070905030c030c1005 84
    0x9003010519030070302030b4401595940727024500518094000580c0e001e40e0745030600034031640c291100305c0901c0c942c0484000da02c88000c2e04100d03085102d60741c0b00c0c43c5032500d0b02c090105155000720181488200320000c00d042d000d00310320f0050b00c0388030b003290b6403920341500c1c0350600040c0340400140700302c1c00c0003400e803854000883c0c0809140403050040d104c03031a08607003051011585d0107401852000400d03406070260030725654010304107001d65100300040c0142d50340010b6214008200022003941c216009121a01ea8004050002c1d440383c0250b115240d40841c08150900b403500804c8100c0080c40c2090a180c3e280c00a40380c0102187e00084410200801c80d42000c00c50400e51000c1450181034001601480803440801c08100d00c1c00c2c45005410090800000c40d400e41e046d90700b191041d007442c6a07a40d40b10b1108504042010711400d50009003d100420010801c1811612071021500d484a0700d0752128105aa40c42e0001a0280d26602490030b48801d41440105d034201c100481c284242003000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 435120692 1250 435119442 435119479
    0x3022209080903160e0c03040302120a0305040b0609190c0e0a09060f081204090b010e21010b0612040f030c02030f0105070219030816051c0504020a0503030408060f06 73
    0x3020000e0380d10a001140544840c0307814002e4103d4910507071040781d100c5291042c04458494001c020401500c8044006810305000380241c480598403900d500307584003c1824007900402082c0d50a8440d540303010005580c908184444601031481000c4a000d0f0160440841000d04010b030b2245003000001c04405106403a20980700c0043c0c1000074003c14160b09100590b41442c0e107071f80c03008800e60300ac07005001240c110321f0200e4068400d960808243c004000340180d8000c40c014000070382080745004c10600340d610801c01c910203400880020702480c048842000401d00802d0500c506118055001c9030000340004000c17009940f00b428001041c41c0c00380c0002c3d0030440d1505010003281d4442c2d04221440350705200d84075840c03a401210905d4454552001811030304018417001c2d1841c00810550b2800e0301900a440341c84440c10150304030000c00960440140c1400d0310200e01929a000c4041050720340402990255800840240000d90312210480d884045c003400282e00b01e04a031112440011 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 435121942 1250 435120692 435120701
    0x70303020a052e0b06070f060506100203090303250609260f03062103040f0f0801020406020d1d0402120708060405090706121b02060912040b0301030222 67
    0x1802900500802280e0703003407050030800552840840042d040d4524a090a5a50188120250960300015400a508000c0360640c490360344060084206001100100039030f9800c180e01c00c50301a14001642d03002c4200c01c2c6d0303490040e250b405c3d5250700700f0300c80c0c11902e680466401c40746121100340481d4503081900c030041100d8100d00140c032400d0300b600a0031120f0403002d2440300360340000c40c0c40d1864285040c05030301640c00081c0070288541d848660042d140b010150200740d81c20208002c0d81c1c0e440769a61110600000729200d804580e80b0f00c00c00004014070188251411201d070f40d000303400402001d80c41180c1800d0080840011046503540484080d200d51001d2701c1064201d225100d014140130402a10f000001040c20384204c0c204801c2001000000c01c01d0302c121481c50a01140d034040d207107410320207410780f0307400c080521400351250a20309a0010340c0034040c2c081381042d100303205411007100b40503202e140102c02c400b0350100b00400042c20000e0044c03100700c2d03030714440954012400403800d0946 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 435123192 1250 435121942 435121949
    0x7170703020a0308070c03090b0c0a060e011a01030203040b010614070f06050a0509031e2b050601080f01031109040602040305030a11160e06090a06050a0303050d05130b0402120c0307 80
    0x680c0800ca50008042d04984d40344d800003030300d0030036510f0305210381d50041c52651280980d070204280426082c0103081d0030400e41e1407aa601820038000c4840780c0507010b00811248082d880f145d94540741c110700550181c401c6a00407a080481424241e090001c00d6541947c4e246050010341010004280032a0542b80004010b0b0311855011a55080c2940c1242c280c55001d0480f40403500100300e4405030081502107813103020b8403400d24503190302910546c146100110301c25075880010490006880403ca030b4440d52041d00241c88021040e2199a04924607034000d010040a490702a4a850058a400780c0fa40e41e0181c46400054603003a16661402d003503030070644806000c0350b0500c001c0d01d00400140f0010440817070b5030a803080000d1802415810403040680000e001e05141c00100710101003540090024210252402440c1d965900d0020150780c481604070300c00074501004102031612071404101e40035000b005048460311181c080088500c200e21050321940715028492003951010f00031407009 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 435124442 1250 435123192 435123197
    0xa051305040c061115060f1011060c03010b030403111c030903020d11100203060a0905010605132408060a0f08490314150f0a0501050d0207170703 64
    0x120700341482c2541c0c81002541043e0240070030b8a8a00d0740d1404000742c1c540b03520310481c003c60641d865440c081040c0480300341c01c80d034002002c00344120400c1d0300300011104480d441d00444866941c2c0c1c3c99800d4090100f0f01585000c0c00f030400106010a01c14007800401004003002d0b00c5158003441071058202407450b000700d01007520342501c1c01c141501480700e880806654107040101d5000c081020351030b202c032400328980b0298044046121901c0701403140019040a47c4100840e5844d0354001c0e2190300420018010065880c42c081208030301c299402c20600042c01c0400010034424500703a800302c40040c40c040e00143c1c1c40c5000a412000141504001c01412000d00301c5036410811800c03207400c000000f090381a10401a40c290701412400728240d881150300c10000da5200314204402404202c00703000790030402c402c28040004490050f0b544c00c032030301700c4040c00900840802e118408215109035408944244006c2401100a400402450748501d080f0451420700120822150f081807005800 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 435125692 1250 435124442 435124451
    0xe062a03221113270c0e091c05070804090209040b030111030114030303100b07142506080402030d0806030a0c030b040c0806040c0b0d0219021c090501080112020a0513 73
    0x3040c200360884200c40141030100b40100f1041c00c132100b04580000da0000055010f8505290078008407029000c0600184241103885047c4004031903552890801c50224400141083c0700c00c0c2d50040c0101c8004681c08150070341014602030301a002908582c0145400c561514400840ea9400f0b101c5c5400f000d081700c00050f16035042015800c0204c0910200900907407040060101200d0240d100d88229015040c0560356442c1c0c40ca082c0100c16615081c1e500907114002c40121001400b00005c406800041070383d826599940d40d08442c0e94106580c003a41580021140c401000c2c451041994045c074040d040342d528103820742c4d4040c2c1040c610b50098850b4039040e4140b004002c00d290081c1c1c01000301200919240c10507489007108015548203415215000064404030702c1002d03010340d0024071150103d19560a0103200103515108660941c50261012014500481c5c1c0a04210b0b0144d440603075440825a09002d40340080c403405081c1607038810681d11002440b07a85076880c400d44604003550109 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 435126942 1250 435125692 435125723
    0x5060f04020d1401090b0f101808070e0f070537030b0f04060b03070e0f04050c091002210d0207060213030b24060d0605130e062a0322 59
    0x812203c010780260007881c1c01c2003c200c90a968004440740030f04800c41c3c000465100303882d010741e0080c4807070a441c01100c28410b800500350f400495140e04460140c070251a01c1e42c0e80710303031031a00031100300d41c1100801c1e824807440481340c07840f5008012440d0101301946102580680154002802003940c8002039203505da509103904042c01842c024810564007400300905001c01003400703000c0180003a04100c9020081203071640c031a0b41108070800003810812407800c048107444210f620854520f8003c07181c20f0842c1b55100e1000485140e08801c2041c82c0ca000843c107400042103074841c000300700e24103401703001d8130000c11003a00c014400080e0f500c20540e0f10600c0c5151010300604001e01c0404060040c80d9118210b14020401100b42c080403a2000d83d40c0720a0a00362004040035040650400c0c0044c42c03001e4501055480041915600400c480456071407a10440d40781c0c105d55107140d000680300e84040300070340d2801b01540d001410a40420707003c110410155a01c400505005d45044078a0742404 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 435128192 1250 435126942 435126971
    0x40609020d0b040b09070f05040b070f0506070e1c06020d02130f0602011806180507150207050f4b010306060503041a061c08030907080a030207030605060f04020d 71
    0xc08030000907034041c00000000000104004402041b0000744600c902d82c0c0c040040c031840449002e460f00d02c440c1520b6100a0810303090658204804480700c0c42100b0124500500596542c664000001c003100d43c0700c41c401c5004486201003043c100d402c0c50f0240110400007040c0c1c00a015225001c04902c031080d46030903200c2c0e60f020203651010f02564504049414500c1c03414292342907050300480c01140c0c50340340780081c212000290002401501030040c020617411556401c007901d40c1801d900f202d080c0340d21002044096002c52080d10707807040802c1404400300380303e00d10041408140300d0a48409031300c2d62180401d0740d6070850240c810812103900041d45503030144a100041c00803440e000b419071034580d079000082855105003210450307034100000c070940c1e514881c081c040221110308844084042c40d0000260b00107a0b40006a4000d00601098100c8006034041607240c15a0043c001240307591105030003800c0161900da04040e0a014042c465180d0340003c000c03466003990000391156504424 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 435129442 1250 435128192 435128201
    0xb040b010611060601050a110f010b0109080321180615011202031909020a0807030809030706080408220521070b03090c1306050d0c030303050a050621070302040609020d 74
    0x104144002c000c03100010341000288107920100a0824642d50301b1a14416034010320a0140012941b02d01d0348640c2d145881900f100030010340a07240c1c94441c945603080551640500d00304640300240c49520308940450040b14550803503000c5100d13080c02d007403890080e400c003101141c0700e403840740021500754481d582c0801c42800e0529022011419410080c2e0403a66003080380348031603c0b0940300c20010301590b64580c501c0c0020b2005104940629a881c0ba1064154112281541c42800341b07000010315540118585407266900c1240d00346050b00044400e0f101540a40d03a101e0007800803040458aa01c40c80b22321f12040c40000b660104240f60019140c0c600b1600e6004440079190074010b1103003501b000a6901001c844c03c81d01c0000d241030036180000181a00c5e800a41d008001103110000d205c0d9803102c0300c0c1070301d0081c0e50511142c1e4400700700105a58084da03c0307507084000480036034292111040c0e102c43c444108001e41d80e00036540d40000741900d0190b0800000c0325030004007140b01c40142d214 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 435130692 1250 435129442 435129449
    0x31014060403020a0302010507140d031d010908040302011101060f1403240a09081306030605011205010e040f061811031b0a03030311070c08012c0c040e0a0f0b040b01 73
    0x10980d00d8a03045070f010884080041c80000d060001c0071501104000503501e009294030546003c481000c00c0c0e000006020304121400c134000c0100078001c1d0010b254041c051078800c2074018200074074113032a550044844030b070b0b44451503115541c1e89202196090001460000522000f280e45804201e101c04150402080b800810809604803080026100c01c89151507400140128001007009050803e607a440c0b059115920b0000c841c0480070422a8065105c981a15400c0c2d07603000407501c60380c407d02e04841c000e02807a09100e960300b0004000843c404100c0c000b030703881544041110603d16001d81402804140e00f1142c0f40440701c0090131900701004031410390718001401e80f0794010311101080c010507070781c00042e04158071402030f410600c0c1120215074030150710100740b50005a507001103500904030b009a078038040418440d881d0140d084100c40f22003118181c4060060200c01d00b04010092000200e950114020000e4200c00f0903008a0301011a9001c0d86100300540f900b45041c40f503100d4140c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 435131942 1250 435130692 435130699
    0x7030204180b07030209060c1204061709100f0908130503010515060d0b1c0302030a020d031e050a0b0604090911100822170901020721030c080906031014 67
    0x540703020842c802d442c0d982050141c180140d6aa40034008680140700d2460b043d8001e01c68541a042041c58003401081202e02c159200100c0d5005900050080002a100c0d080150b001080110301e504056001a5851904010001d5600c201c0da0781c0d1072454025001201040601134000c03c45401c2c00c0c0101940700410342c055104030a9640000740b614054054100c00031541c83c0e5410b19503442d214031184103900860001d180e10002494029501e50002c940341c0d0060240d005440d880900030b00030054402e102c100440420f8800b407a406000f408001c0010146541350400110386407101130091000e800224004240344585050402c442e101f951039860103400c82c10795144680b5403250400e900240c1c4070202ca00d242e802079002000304a0b803014040e11200d051000000e03402c40316002440c503400c01381c00352021280d44040003c050b8540e00e0740c546c80d420100381d5240c00280314031442c40d1440e1240d40120b0030001500e021400a8000b15441c0214051500040c08004200c198906200074102d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 435133192 1250 435131942 435131981
    0xb0a050f0105070303020319090503030a14071b0303060e090d020f03120402100c05010f02090909070609090c0c081207181503020304080c06090706180b0306010c0302070807030507030204 82
    0x1030000070028031a040700601056804000701d400001c0d80f402d40c0391361481485052001e40d00504207140c5a0f4020384903501c070549007039819458502c00300d00c1b451041e841511125480c080c11280d000d000741c4c080c9000c400301640c2e1030000ca0507091100089015803849001400c1c100030220b4082e2030052008038181d8103034028008025441380400565a000303605a039034101c14541e03510b0540d60f1280d0700300b001b44954242100c03041c4a4010354060700042c40100c480f4800c648411101e42d40314002d03800f607100090510070050003072150302d810521417015540340071840c40e800c40d12050182e4011209a0f01a05581c13028040340a501c40b2050070210310142c018990b45241402c01c01d158084a02c0c4c100074541c02100041c1813028040c103564141210005468080c585104125161040b030f0040c1c00108070403240d556156a103410503501034034100b07a0802e155449540040d224403c0c45601241184a00c100102d42d0716800d110070001180b00d00700400d1034504502c10407058403410001c034513120400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 435134442 1250 435133192 435133219
    0x60e13050c070219090203011e0e15040b010219061a09011202090a0b04020706060f0602010207080403060e07050d0b06010807030908270a0b1b0d1e03020d0501090b0a05 74
    0x203002c030360289a040700c40c400c100ea000b11400c00751070708903800b40144602c040300001c0c0d4003240002140848900801080040b074451210500041050b142c800390a9448201c1d4040ea08081d4481d013000001401101c2240f04004900407880c01c07241d808031184c03070b1610004404481c90000242c1000401c17642111590705005075810190007164020b8810107100021503600e91a0341d0060920000182c019036a42d10700e03003420b0020302a90700c54001045000100040c0d040d206100345c0340c01540c07042410b032505103140c49800180c04a40c01e0618180a02000060159582c0701c145103007034820b1845210500d881c5001400c810b42c000c0c10582854104810780c0002420341c0202c820140940d4048075044480c24120407a42c681c4022168201c103a5007008101e004000c80540b0340c450a014101c4008081e20069139141d2494800e4100442e2482001d0a0084040135170a0031a84807403400505041680b51107200340c0d034082e484805003540d50f82d100c20072400c150340503034051b0000b40d0712407113015030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 435135692 1250 435134442 435134461
    0x7060e070503150705040b03010311010906022e1b0f080708040c060809070302060d02040e010b07080306010804050307052b03050f13080c06090601050913022b0b01060e1305 76
    0x6140781c3d89a59003203000001440180118140c90203012603101300d035201d686a00d0700302070b00b6004001d09404178440440000700d0354800210307601d1440d0b0340b410f81d2207541a0707055210750075019030101c00e80d52503c411640b0681802c07048418110a02507691484502c0d600d81d000c0c041c8032001d0650380400208000304804a204101b0400440d0124500313200a680e90340041ea081c0415a007000350b111000007117400d05035641c0c0d0054030a44980c40100c480999842e0900c45003803240036401003040c071042c030000f013156010701080c0354402d000341c05503860300e6104c1d0b455900f01038940b0407080d285c0900303e882d11450200c1d402ca03600c1c2e4882c81d0800b00001e0030a40b00c3d446440340001d000d103010400041d000010818044162840c070309a880032030310181014880c56899080074007449016010300000210084410f190a4107942d40240c51008040f5001c102032a041c84140503c00c40d01180000b500d000505201013540203000c15541c1301c4142c0c56440400003644200c1d144150802d041c201030124130341 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 435136942 1250 435135692 435135703
    0xf0616121d090a1d24130803060a17010212011d012105010609200a09032913021207050915150a020a0203071d1b0409020f07060e070503 60
    0x880c11218180780c1d82d152200f4a000e003c0144501d684003480f45100303a02008006601c02c0c0c40a6864004481d01a02006100c40380004482c41c00d20400e13142441c3e80412040001140c2201000e054040c100c0c0d11450030450400240c2174140d41690300040352403000301d005017041d02410581d40b8140390503141d100d1400366002d043c0034424010f00300c1200c404800d40c06040c0c0c40307032030743d4008000d200c6070b90303100c21840c000c224440070f10200060503417403c249800b112048030041c0039243c494001d1981075403241910000384a006001500480fa01c80396080800007107244034020503107454401010742e2050004c900030a4a60360200e61000600784580c1c1d48483d0651380c003861503903101e90004039103800a400450741421362128020000341c18070200e030b030101741c28010a0003941100d159981d280703001d10800fa01028807440803100342021580c5145a06031080d086e80b200030065003410340703ca503554102d030b11444030403910010005100b010032080e0300415010305004400391200700c0c030b02030100c2e4591 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 435138192 1250 435136942 435136997
    0x4110a060f0305070c2a051306150908031801030b15070c050a12031d06040e071b15020c0a05030a09141c03050c0a0b040309181a0f0f061612 62
    0x301d01610681b03540c500aa00000d00030607000309a0000e0550001401e402030155004d000c003941042108105640d000d418000c00700c0341584021850482010300b81c07421040000071460416482d40b580c404c980da40c140c1030294004185605507564442d905e0b040040301202c0e030100d07014642860f000c01881400d407088031103964060800124003401d0540030b5500d00400358200344d100b01c02040200d0384540300c0071030354030540b2030751103003e0400320000c0c2d0511a500b07460001403100301c034411500c41408194014004c100c0c1300d0340460b520140c040da1041e0031500640319520010320300340300401c401004030700303410600441a40c04903403034500582c12a003c40c411080181c00c0c410700040c032400d41c0300c1c00c004103404d050700410020b00c1800c061070001d1142541d8811104071034624504400e0380c0556110b010700861080400d11028002030051040809200c4540c1d940301c4503100f0440c0d2a5124000200485120585046c04c0d040301803401c1c0000281c04a0100b08003c0005602018a0308690f46008031 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 435139442 1250 435138192 435138233
    0x6150e0108012406183812130524070f050403020d0f17030108010603170a08010501140f03090102071403040308030f0a020403150923120304110a060f0305070c 70
    0xb070350000d43c090032104a09506c40b14522081c41341b480e25401310380041030310324000d088401c4601000403506c6846030141000d01410354400c100460705600e15234881060007441042502c0601c602c0300c1c5001d0498007020018900b4070302d4030302009040d9502a01100240d803407810321070300706070441d00801d111240202000b84604005600c003810302c80c40000f10300c000310907183e14550342e40c0c40e0302d0a9406000584011219a107006d8405aa8105030100303540600364240e030303001896841c01c001190b23403071180c03620000404010041b155284918400842c0f203800c02c078001507031340c1c41da034685600300c1c071803c1e104504c180c0c00600c41400007030700440480e50030180800a03102581c1b40c28050800a00c280e520050202c4203104449113100059000800b1f154003a40600c00718940c40f07040303610310f0400c2c01c0101006070854418045820401405036030000c0c003a40700090b848040d03a020a4281c2110303040040030132500350520354040c0d490301559a10200b10311340080302005980e9105003240748212001300 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 435140692 1250 435139442 435139457
    0x60816020604110f0604140405010f050f010e01050c03070b091905100b18090604060515060f0706060515030a0f0c0507020d060e1e07080303070804020d06150e0108012406 75
    0x22940c0e6000219182110005e007015030711035850460188451444070014000c60500e000040c8054400510008544029120345100c0c3d10310310044075852a0010000e05220041c0414101c0c21020006130143c0d501ca003100300c5540c1815501c0b0707880e0191800b41c007a5805a4113056800282c004266503418602086011070901c0c00c100c00500320a03c020004001d10412904100f00c503200025814000c038043e80e03040002e610341508590380c007030141c0b56030f60b00a1010410107241182c0c8200410b00c1038001c80c40050b295807260002103003c10040c20190041d0b0b0088140031100540348100101a0b001c00307000c0014000c0880003400c1d82c01030840281c400c0300c42e2550310f0140209034021b111900d00b4481034030804038000f081d41c032003d001e000c00c0c8034117442a44400b02d42000300004a034002d0350315491b8050655900c0c0e0030810303500920201241d000d500c038420341d21842404a503202c0a40000e180340304e650740c10000d000f82110414030711040e1480407181603a0202002110103c2034420303901c2d001c0c5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 435141942 1250 435140692 435140723
    0xe0c04080c100525050a031d01140901051c05010f17010605030a08071a0c1803030c0703060e0a0602040305011a030c09063a02091311041806050709060816020604 71
    0x40109a21550280240c01b441468004055100f48071817522400a1000c070752040d0031a00459070b14000040c009015101040949030300d60142010301848035202915100c51000503107000c09984003a4032446044028841c00d0049501281058541040c128000c20402d881c000009507110000000508400ea002075100305001c0301c1c106a0741407041e12901441e6508100c200342d042940603103401881800f00038616811480c0c003004030b6260488076070040440f542035455a000505600216811034480d02d90010001030b5503001400040d8000d400005964501c030b074000605c10b0f41814054403d40110526070900c0da02c4200b180d810920540320428541a846181c9600105a481111042c02c0803500310240e1100412a81c03880c91090f20820950344401c2c035201c9624401c09002845803c00e074500301407904040e80016000d0406c1061a030342c80348140c40d80402c481098500f840081c1682ca030a000c11034000343c84c0c0b0b4100c560b00c0c0d0265030030960550006d48542c03010748002c012900044c07104 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 435143192 1250 435141942 435141997
    0xb01020c1507120c140a02010e0402040e01050625030c0c240305040213090b0402150a0801091a0a0e1008030408030a030e0f1e150c1801090e0c04080c1005 68
    0x22045980402910081030456562581c2e80400306d400b00e00040400701c810308503042500907507044405400035540d407039003407104112468005980000041d075030f03102c100c0d03407070b1071508c00341c0300064040c1d140d03d49440d101e42000e00b06641140c0100c66508440f80c074101e600701d040c1451003450b42c1c3c9443c0005064680d480001e803115848044581d00e06d050a081d033301070180341c000581c003562080b95151101900420071030024041c542d21500070651000040000e0700c440c4d00309014140304089166250050003000404924554004500c05c070f103400d0400940400f02050400603046800003181443d29107002259640f26100c072036410180c50309245d81c10a8803c0040c0500e000050040e920618100d0740c5840007518074012204451250400503480b05c0d8001100781d0040c010748544c0d900e40150400d4012002d5850b40c02c07181000750400e80041d2210819540a0007003c8aa5001e6503952810070880d14210540b0740d040d1081070356000103041a0f07003100888044c0800b92030044004a56500034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 435144442 1250 435143192 435143207
    0x8040605130b011d160f05030c130902220302030c01210204060302031e07080703020f0c010e0309130212040f0f0b250c02030618100f0b01020c150712 66
    0x103008080b03082c00070400c900340403200c2c007020350112004030040e40c0714451710401d0209016100b000c21882403128402a101e0070045600c8131603182c010f40b1304840401c500301000d240b50700540b032096000c5014011085c20501102e41035014101c08421107055030002601e03114000d0f816410b00142c02134180252420040c0c645480f052250219195580c510020f0043c1d0300031074240e00c0c0e20300100843d5254490303074a08217004038805d9842002c00c0e55094401c1c0c0081d8000b90041540c130800780000c0308403850900400042481c8100559150f61104060018128000e40c041c0011801800460244c2c01c80880480d0b10a41007a55020b0341d02180c00c0c0040900141c03900030f07085240d080200407005886000166100c840314544201c4902600000c85002001190095150700f01c0c0c40401c11400445000e448003880c4070080d600c500e1110081901101e0301d1644e030358541500c1d400c01c110b6540e01403105040301c14082d00c12048094042d04090740c0d603c90041c004108460b510300b132200085c8503a24 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 435145692 1250 435144442 435144481
    0x2030411061c15030204050c0a0215040201050405030f16170c1c050a030801081006050d060903020c100306140910060f1205010b1305040218040504050a060c05040e01050105070308040605 82
    0x2420000400c8420800b83d110140e030105a01035030808001c9080042550100c40d41108a58041c000006181540c1421610084c101760b0401c0300903c40461660340034001070f0300404081e0700820001075000c6c5000301c03103141a4000702490741100e07051300c900500410b05004800d41164034005045801c00e0308602c0b640c1a500152140c41408200c40401d900009000c3c180c58500c000c41d0341203074920300303580b05407051405015049131500801000080c09038002c00b003d240b00340180c8002c4064900071070900c1c08a040c200c0000b80e10350004100d015440f40d001441042c050701d4040d1985081201400d00516134484d04042080b40841100420700c251121991407241031014455969940d00301070740f5030880c4000d10034000c281c140005061620b842159030701d00c0740380e12072114041d0210802000344801070040d00c032401150300c0d5500103602441180181d6140b0344032203071200d06000d0b040007201e80580001e1f050040400881d80404e8000b401d0725800f943c000b0303011800707543d50000d25140300b00811 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 435146942 1250 435145692 435145747
    0x5010803271c02131d011b17150405130c1a040b0703020102042c0601020606240702120a0b010e0f160e1002010f0c0507080405240703030b0a06030203041106 69
    0x2000c600300520042903002031294445c000e0000345004038040100f0085900e14802040c059200740c400b0009a8454a9101400170000e032065001c01e8040b90a556007282c1c021585240880d00408110780542a54050000e0304403040c1c540781c1d00c03c0340b002c0d14800e5000300501c19001050280070140b00f501120090044c00f031214525103101d00040e551111400c0d007000c40c001030900000c50760351001a05d107105120081c10100c01201102c41402401d8a44c2145420460300f0085d860158030b40d081c030350301240d644400500c0d03810804c3c1002028010107030442c9020340503010500400c40051022030350071143d003035944544c00300c003071a00341c800e4005034904c15040782943c454162020f130190311034189202040400d01652017842000c645030b104444c00203001c0b0000b0f000c240900e040130243da00000c0340c921118080c18a641328100c465400c560000c03000641c485035600c49034144010b050000340054101541141040e5845c5100d001c0300d54241402958081100d00d003041c440404030b003010b0b0044 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 435148192 1250 435146942 435146951
    0x3070807030c03020a08011401090b0316030c0e061f12090f050d0201180201020a060b010203040b162102062e031407120c120609020405010803271c0213 67
    0x7482d00800314040c920044e0300c00c05200d100044c1d80c007410300070301400d01d03604480d890b0700340c2c00c104041c0e00900b4541107481c2c26108052540800b41c01c1d50003008095030280e09141c4d02e243c40c0541c14405000c0051801f40203404192052a10003900b00c403540030500e0506200e644046201012001000c0c200c1001c4d20b0320a03405076403c00e100c1c0100710301c0b4128980364001d10080b500c00e65103500d80505454000d00503070012540101080a0703601000c0a014144140c0b0b10301586e41081d17412640000ba0300403200c17222000b00d0030070003003004885081441e9566921040c03075016040691544c20080c24034000401141d0242004000c0b040640e00030341706641c0d41d029030ba849080c031b00e406202030070607490248250107010074200349064518011546c8243ca2220140c01d2200d22040d4034042e1200311996034071003a001005a44502901c0e001c0c01d041c800540d02e812846480c2142a0360040b583c80c20ba200c0440f11140503100c130180000c80110310100d180c0f04002c80d10101d0203515034100c41d00c101e0b07480c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 435149442 1250 435148192 435148199
    0x10020307080a0608160308130504050c041518030f0309030b0a090b0609090d110f030a0c050105100b16050f01090b0f09063309070509011b0b011403070807 68
    0x41100703140207540350101040029191034a032642c2d94010380c0c890040741c40e0b0b03070b004000150401c4010444081080f864a52036a42c40000c5002d881003680e420b4148900890148820804460b401da1601043e203000031210410a032914051103140c04007902c4904140901c405040c0100e440c84000d41c1d0107a2420128035011191030300a02c41c1c02c9040369020100c001080c8285403515105000d405004081d14146040000549602d8481e00760041140201958458440e90900c007501071030700c413510b840c0403020706031810b81e007194001003850307060901da03043c1401168240313800c0d41c0307880100d08091005078002e400c110385080301f054889602507080448000c1045090300c0e419009a030307100c0c041005611003100c1d858807544201c5908040d212255807084507580300036014122078661180000c40e030303810300c408240401001c41e0140c020031000030716500d00d075030300040c0044512046092035510261540d01c040311190184100070707244098214280f1a41d40520124004103024000c59042654 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 435150692 1250 435149442 435149447
    0xf07030c081309021902060105030d110f030c0a0309060201150902030604021e040303030c1d04180f050c03060108120f030a0e0307051f06080a12050c010e010f0b04270510020307 78
    0x1c10007045c00810260005ca106007400054024103a85c0010050011030741120701c00c0f50482d440140040b0705108100004000090900084c803000c620780c00078150340384444c100588204120781c400c40031a803602c500742404400300a0203030103481d030103800582d42e80c480f00005400307070140000c0c0d03089000b41c3c420b002410715000d10050084074480d440900030390711020f0003550b0046030010707031038240c4600c490500407500d00b551040e8101000c681e040e1000011a4542c4112800741340c00c11030f50b95000071100740c1c491074100110750040c801c40d001024000c51a4081444038010124080001c550203c0802d181d43c0064202d041e0580c40c82046917162a42c504089a4440b41e48181040c0b0300100c4c149411420954050030f0f054030501d000a0800921035916000a18440d805a00412000f803140040b50030f0300b03001c4e9165105030040086000c55007402c02030115048045850700c100c2c5020700e10480c3c102001c480e800c540c49c48a4040c01800c0c01e40c1450b0342420308814500892620000801401c03d8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 435151942 1250 435150692 435150697
    0x30b0412111204030507082b0302070807050309042a030203151c030e04060302090c03090132100f0e07170112031112090d020a05091e07050f07030c08130902 69
    0x1740140c0c00c80303082c595112207441c0c86590700c1008502c0d40c4142081407034440102c1c4210f0a51078228030300107144c03030501e0b01d9072019078001a01c100d580c0d41002444151600d050b00540c0c10b001c024403e0200e0f010200312182ca10151051060024540c0200c0014004c0092041401c0040000f03402c0b100906241d40c00030448010403c000c82c0456842501c1c200581001d01c00c05041e00c0d4041e050110039240d41400e026030780c10041c03e0326607542d20385407802d2100f04d240d0541013510b0051100c54140700302c44541030680840050212a03450940441005007035071800042045844101008003a81c407410400c407054000b101c1c501d40544090030000440008019180314158060780c0c40510010002018a0300e4a2420200c04600081880030a41d24900f1550031007206100400c803644840e03030b8002042601c4000c84030f0394030300307600c0d00a000004541c4180d141da0080f5286880c40c036052615904107858082c030203000e4108000c41c00c0e0f1804100e5200100c844600c24811a000c045a031015600081e5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 435153192 1250 435151942 435151949
    0xf0303070f020d08070e13090f0606050f0f0901030b070210020304031d0f030604110409050a060507080702060702210d021801020c010201060b0f070c051324030b0412111204 76
    0x18030403c0310f0340f0700d41c6105180c43c9000d20b2040d0303144403100105500f003080c1c090901d09507024160b92103c02340c0000700c900030101415485001c001c40c00e45d10740801c0006026411014900880741c8081c00503140c0c2d82c248060341540d0707010078906050b803500c501c100e14092460306450101480082488103142c5c000d00e80c00c4500940040d1148550311801c14801203020842c081900741d030005000c03400041c082a44032104400140c4005000c80b01c2d13864083c5454401c041c2500c240740c3e01c0c4188003041d5808495158040c0060000f0100d600740300c2c1d0300075a50100c0600098649000d0300303111070610422000c60300321135043c4a05640321285014500501820000d0140c050321615200300d07030320350060007408200e916010300c4a040401c1c045080b00700d540000da0468007014480000b15640c2d48403040150b00010360440096803550031480d1502c0b107a40c1003560100d000d4034080c1040001c084a60f0f0343c7e88282c0c4150865070a03000880103455500c000020349002d40525030003022160707941806030088 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 435154442 1250 435153192 435153197
    0x3090d0813060c02031c030e010609020306130b061602031507020c090f01081b0402090409051b031605130e0715081623090306100321020d0f020f0303070f 68
    0x40356201e0b400c0d01d882880b984000c0d0107411850801c2001249a4240c100000080c1804200003d1702010346003101e88a410106031254040148616400e00c012001c1d140282010200a840100000948d0501031214a030618000d040510003c544061003918000d80c00b03200c000d181e50900c0c0c60081e444223840c6510500403206140041d484a19500d2602d04a90017038000d0540c0740d20015002200009000221b074010341c0030402884c11ba1207074401c2584941c001c0d4040c111286407021201c44682007100d04900c654055040c0d0500c10511204100c11100e007151307101e4944400345c5880015008201c9170741014082c50703e00264200303400c1140c446030000da03500c071080c80e500c1c50344044001920031511000103400c4c1881100000003080c80140081401880d14100082e00001a1601c0403c50721510003c00c02c4d03004108200e04980c1480020104015409081102c00c900a541d0152040c2400c2001200c41d41040909e00030320007110071801c81d07029660b4030b242c001c2014140c0034000d45907100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 435155692 1250 435154442 435154477
    0xb070c05031522050a0b01090606180608070c0204180501050601031103010e1f0f09021801030924150803090102060717070f11010903031e060b071403090d08 69
    0x840101c4989994402ca060003444141e10740942101c0080e5010003c08441501c106920840030440c01e04080c1d0003007100752408075506d42081001000182403080342c0220605d500010b000c22600140c1b82c0741d10128030314000004c00748900025014001e83c09035101183c903c1c000741e0092040640009202e11400e807418009000c20300800c1303040d0300c801d1240d914042440408205000348645018101250b040c1100c0c104507100c500c614091680796021543c0ca542c001382c4034012410040c80c0201607042400d04002002c015201d48500311485035060300401c0c039030b501101d401c03002d80c0e10400c105450407003200610f0782c940044954030360010344458054403a074800942403901c01e80b040d892690080c1d4200b18262a0108180d5000300084841e50500c0340156a04884900900c0340318015402968040341484000002030204c03513284640030350040c10160709000d040303071100443c0c80d8030764043c03c1800d4640000490034110301803004920b50110b0381105910030b00c081400501a160091a034180 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 435156942 1250 435155692 435155713
    0x9050105060403170f07050f1609050103030e220221060307180203090703060911100504080307030c0804030206031905010b270f0907030f050a0c0c0f0c0b070c0503 72
    0x3260b0046100007840c418207054840340084c880005400e80000501441d8286040740d92102c0c01c1c28903c0703469031819030210000d580307030071190324a82000304040f4404008550540d2030040c074100d80400028050402c3e0901124420800a82c06140c0c0c004031a04540b1006040d102c00001403400b04140200901c000200305649808104041140d1000c001d12071646284d6180c0000383d00000d00c5402c031401082000000b00d41c40b402042c81180c800d40401c2941074082c0d04100800140f0004541004014041800f10b0b600c0041140c943e540c050620070f0600f00d10b883c080300144920340000303400c04004020300c9403011300040c0204031003940740801c1c00260f0300c0700b18038802805180b40909000340402038071031700c001c41c8244c0300c01c0c0000041d1403d000101d814012680800d03058404200080c2c2c4da400721541546148110b5810000c1c0240600940b0300c4030030000c100c03805c0c0e9440070b403804994410b01410400c05091402c0140101c10140d912030070750b420200c0320261184642c1e4001d018035000c00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 435158192 1250 435156942 435156949
    0x140f2e0e1e1c0305070606060905101805120a0501020d1e0908090603061903030f02240402280603020a0e030a02130c03091403070c050901061d0a180609050105 70
    0x6850707241c007806a0302c1000c407984080c2c41c10b0345805020b03014400f0070031007840461018050b4101400e1540ca40a00c0240382c60144114210700c0901c00007041001c405810406c001680303031408a84046131040ca080805110303039800c004003070300000e040d0f610025072056660065008000700328031100ca10510040ca00001c8030944801c854000c00259013089011418078105001c0e54008401518802c02901c544800c06041a03507030708181d0124800b51039510300782e03038100000d0366844003038041414414002050f80c56614009000203200345100c1a0241c01071a1080c0e5100805020080b0002402d40d2140f01a00039070241d901e100000b00e2500c0043c090b410000356101ca01a03000e8840c450070038210809100900c0e04070a50303c00c2503124541c00002c58903071041e0340d040b12038550142d0b590342400d00e0280008181035000c18014042d034001000031907000142c00c102c41c006401210b9401c0f102000144460707030140c01c4020318401c01c2c524080010344130351001041c1d40103040c08006603600d81d0100f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 435159442 1250 435158192 435158239
    0xf0402032505070503040e04080d181e0b010b0c0a050a0b01050316061b150627110a030e150906040b0f1504020d020403170d0501140f2e0e 61
    0x203004c0d0341c020002040400440d8000d16131281c0590003140c18152154070800a498441d94803402d1581101d0780c10081c004d5442c2901d900c880300c010b100c0c000b400c00d03a907120000c1005102c3e05064000100700442034201c14040c003030099070300c1401d0b54454425480c200346070b0002030044500a114441040e00c14001c505004015121580c40d158152541c0c118841c1d0081d4540500300c0d00c4480700c16901891013124007801020f405016854100144e001b02450380e44030f58413013500e090a041200c054001c0704404115220380c0d041d458041843c3d107070b0485961820340c1c1359400868120510042001d404001f0a0182c00790b40700d041e0f00c8003141c075a4900343c54005825a11416845100d502c08001450a64000e000c404a211009030801755661100b0b0750541e000402c090032081c3c00115404041c40e684162400350800ca1254642d071088140812004907400c20b10754083d0030401032040610111943c41c801841000c14064066140040000d00c1d0301d40c103041c0d40b4000c0401c105000124100c4a40 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 435160692 1250 435159442 435159457
    0x601050909040206070f320303010f031506030507150e01020715030e0c040504060c1101200901030e010c030606030605150a030b0a080d0c0c14090103020f0f0402032505 74
    0x403100300360b01e81d5000c0000551000000325038661041c08100c00003841d61407440302e641407500c0c040e088a00e068868640305c0003100d801001e00d800c2080140f0090744448500c8081d00e410040d1809500c60f0f03161103a0007048250400381452140490004a00041341c5131900215481d58801402c2c0c0030260059aa0780c80f00e000300d0f00040300c0b1003000790f042c4e0301c41d0788443c03e004460b00031101c03034001d0070303020030700702c40701034a090fa0080d4403140342c0c408654000b0400003a030041a0b0081190702c8a03c8031038180401009800440200b0008205899038401c2d00b00e800c04d098030400030003c0203c000e001500a119030710980e40480d007050000211444c001107a00070780d11071140801d2500c4205c202c11001082103640c80e5a0290424501003079104041204601311090b5840e1107000c0b40e01410809420742c3c00783d01009880d810159608496200c03c150340c0e044cc0d03815651042607000392400111003103034050015400510200130805840c48020b1007164241c40c01d0a0303005100480f1038125007501c1540f5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 435161942 1250 435160692 435160699
    0x180f0605040e0c120316080301030c0e0108100209130f0605130903020c0d021c080409060f141e15031501080609040f03140a0509010e1e0103050c0f0a051206010509 72
    0x543d03c80d03071804d00c40030030241e00c003a440036603103025120740f440261203420302d000740d42140c8040018820005007012030009802d006c218103d00d50700d8a00c280e82d0b21881546000c00a903008911650152a1020303803440a5840794401e002d07080320305050030000c00c0144503c0b486200c001504401c2400b251281c070722050741550140508000e52410720000240d5002d04980182c00100d120300c03800703440450140c59503c580d0344079903124a004800402d403400c40d0810340d01c00d072202604000380c40841100d0034040300191807170749441406494503010700c82200840c5030010741c4600014500d801c0701b00110b1155015150034442d82d0240c4004503072070b00d0101c982540101500c0040707000708261188018140384246400e1004600c24800022030350030030712085010400100d0348001e15030b001030740300105440642d10940104c001410340f0241e10448240b06041c15034843c00f240018000e441213540800898079030f1a50344c1c0380c080008040d584420900c807012035402020405540c42071007185d20301c50005 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 435163192 1250 435161942 435161953
    0x109020f06160f020d02040203040f1101020615011809110c070b030f0402151c060e0f0c0a030e0f0f0708101401140607060f061d01030515040507180f0605040e 70
    0x240d807503d180c18250102660b11001a907841801a074035400110311480c443c2c1103184a200c06890903610040c3c0b00880c070743c159000340c000c001c00700941d0032400c0307407200003446c0880600f8040f80301070f292944150010380c0c0c1d140c20011801440101600102035504003d811102800c0d034500c9000341ca4001503600041488080020801601e400400d00320403400110820b03244c1018840145080501001000c1c00c1d00d84503c410402c050180518540c001002e030414441440d010764900c40510035102d07a034040c140e032240035014101040103d031401049060803280030030a28a029541c94825200f10314032482007a60030740039210140220302d98442e1541d0403c22507400d208004058807494076107290804028404d80c004681c0750701448280b2001c00c41c00003200c0e82851015000804110350b11040b2a103000010800074000042000310320410600319059038440b4030302207090042e5640f181c5c160101114903810f41c0d80c0140e002d102e0882c0f002c0c004012456444c8244815204031484088494022 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 435164442 1250 435163192 435163237
    0x31203011410020f03040e0a0b031c1107080303010b03040b10030c0302132c0717060103060903051e09032a010c061118040c1713020a030c080109020f06 67
    0x5212400c0861520f0054030030507021001130500c0d580080d80040305201c001414080b05041520500c13031203050680182c4803410759403100d4000040c413029400c041020a50060301000030074003010001d030501c007064982d00d5a69401c0a40d031504152401d40750000080c001c1043e4551008004040760b0f40300102c80e0140d8910717001c2004003000e650060201648417102c171130712031030190710b519003891103031427032000708240c3c0c0b0030303041c50042c2542004000c8048546000d01e0400001409811a0340c030a5001c150a45180b4046078180140024003810107205ca40c81c468499400000e460368a8040c1c0448204690645082241d00c9040100c00c90400c05450040800e5203d04aa00c09040c018035000c1081040f0001c007002c207034443c6c003442500d0f4100c2004c41c801071900740203898100d691031404a03940c20f09040d100002c0e000190050000000e80700d02c1400310348502d00040003d54020725601183c5e0b0381d40c0f60b600d01804040c10102e00c9640100c01680d030300e250060035905a400c0c3c01000501c2c9807030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 435165692 1250 435164442 435164449
    0x9030903191a1e0c040902070302010903030b0a0f0e1312080f09060c0307030c110f0a0510020306091305120a27060f0c030201090b071709150a02030604020904060b03060312030114 79
    0xa0140070303810200c04c10000820004001d00041450510a60000071a1289428001c04403104031008034800c40403a04100b01d000e6543c5003010030385a9000031282d25865120034402d8800e140138000f82020384001114900d0358102171010b118142013070810440d540c4403e645a03c55070203e400c000940c0c001c0c000720302d10900c00d502507002241c8130304010f80e5030064801d140d840c1070390180c3c13030400f250f04c0311000b1020080140405c12a0030258441035041d82498000280e0541c401880a62928044407400040c401c08005084140e0480f0081d1550f82e070220900800161010070580703413087d081c10340a9007850a0304207001c201d0721141e9902030240d21822040341c0001454400790210341d210303d404804940d044200600540c0313151286a1103010f01e0880d440c07d448014005080c9800102d0280c08040701841c50a81c0b00c846c2c4080148c1e260341d20000a0024021152581d0b002460f2030310219032440311000450061318110f00b01e8940078034017604194071340320900400f00402020041540c1d2400d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 435166942 1250 435165692 435165751
    0x309020a090b060315040e070f0f060c02060a0c030c0602131401182d0810060518040201030b0105191715010c120c140703060609090b060909030903191a 67
    0x300f0042001c10003a07e9074041ea0b01c0d100540d049a1209880c4210402103658042c1c100d45c010943e50510340840000c030f0300001c1d000c0c0604c2040d1010705c6815042102094481c03191380e0413080e0304c040110345500300302c0c0b0034002c02d100c44d0050750b0504260200701001e0b5030041c06105083c40418244a1b021410005651984001207141220985004c0158030000210724800405040b4003801001004044034002c805d4179003c4e4095070040701e00f84404440c2e1111000c07920351145e02030038041070303205010300100e030135100743c0032003400d80080a403c0140c51940726031100d00982941c0c00c2c8240e01c0d120480d11a4000d01509050741c04103000c0d1344003030009007850046800025007402d010403840301c01c0c1c5030b00c1400c6c04060040f00213074001000c1441002560700c1600007038800f0000c1040824902d41c1c1d06070001c0b0340940128451980340c00094000300742041241c801d1700d806400d880e0604440c12420f20700c10282a0226040c807880c003503284c800c4c002074002d036104004031406658454445103082e05101c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 435168192 1250 435166942 435166981
    0x711090123010509040e012304050727090302030307121803200105010f0f0801020301060e01180306060b070308090f1504080d1e0c0206060f0f030f010603030309020a090b0603 77
    0x5802c2c40281090b560380c0c410021b4261000001207113800707030a080305220000c3c14100d1076002410b881844046000005d02405443c072440201b900c1ca803c420800b007207040d4034010405602d00b060030f040101035012020354010710440c1c5130201c02c030603059011419207407440b4143c80381390320240300310001c00d20402c180c2a0030b030040343c03076114601d078080c0c80d1500b035840036045051040e109020030404500454005001010810700850955061810041200e0050341801d4100610b080d02300103a054801642e034029039102c1c80801c401692040c00f4411908603007400e41c0403503109400030b0380755134020400030250700701c4901901d91542484494640104d01a00039070303802005101008540c8401d00c034203c1c3c800c507403000d640000c1048200810540c0c0c00242680110f40021040c00101d8440c12010405100211240c1c2c110304616004286461a140da00025942c00c2544c00802c0c107405502c9880d5050090b80d02e41501526405042c080c0d4a41e034800031f421000400001e943d9880071003104000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 435169442 1250 435168192 435168197
    0x3021213030606080a050d140304030309080904050f01090c05040e0106050a09031202070e060f010e10020114010f050f063402210d03090302060c0d0605060708071109012301 76
    0x2401d0322038854000f2100b1a030480041580f10101000c1130180801055031103821902c3c214085000303c03111a4118040500010107058032031000b0001c1090685c140c0c0c1300c005000e40100300e146868010102052820700c10301076030519203001c1015a174400d0003240c007583d8861180000b16481c003017003210540d008aa510040180250300400025041090354410342c4c029801448901c1c182800306940101c0902820310941c0070245121080c1d0300a140303460307650390840b40c0c01d0b143c51080300140e01414080c2031200542c0807030000400c0c00c20100c145081600e10513078041481600c4c11090040e02e10408a44004107024500c0b03d018002e4407031002641c034618058442c15448290b40031078880902210101d0b036040c0e0007000c1c404d61400410110a0340c00107480d09201d45407564501035101c60001c1d29085c2e0307203040003801c0e5601503440d8115900811010709041c2d0f0f00c180034200b85106400981c0c0c01c0b180e0f512032500303500051520413030b114183c40c44039000e1100040c0035a6000308201030ba0001506 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 435170692 1250 435169442 435169477
    0x4090c030c0303080c03090d030c02010b1309120201020c031207030f02030a0504031706060a08040206122a0a1d03010e030301090605030606040504030e09100305030d090b13030212 79
    0x8005000210045100d8405022a503045240c041c0c003c4100070842102c1203414810456501c0d00001e81102c4e40304a418000b6001c880c5041c12405031101d81112604841c4040e401c42c00480260700c01c1030860f0050210084403c4104000c03400e1f17200c2c2d0844546190f1091080c1c0140302044020740d43c00c0452400c0000c0d11584000284069800441c1d90320005541c801c03c202c01d05807c5881208994940820010710703190100002d50f25009140d161410050094000340440d203542c0c0c21202040510202101d551601c130fa46240110b20241011940812081d00b80346c013039441c0c01c20b0700c1c19a0203580740c140300720070050b101842402034030743d0b465410340d02e030110f8000400b0240300071800b13407034007550114002c0c0c00d040900d840c201c005000c0034021480d000c01c20010940c03144146243c11422a641400c54840011602c01004a9080034202d80800203405000c407445900403504581719070b01c1328400f0760329042c101c0e90780c1c0702d80c0d40082d0144c3c000501c005500c50b5001c0c024200b100955680c502c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 435171942 1250 435170692 435170711
    0xa05102d180b010e03062d0f040516030507120807171e1804021309060b13050f0a0513060825052205040609020402033d030b0604 57
    0x4808000d6600000500200741008603009101e400b50064024003803c00e408803102d1007020942e920002407414003a034005c2c00007007032810042c1170200303541080c0105200c054240307a484182021000d5404442510404800c40300c11501402c80313000301ca0304540607100309443c141604d10812900c41003112518010070402d400280101742401960480105950700e4407101852501c0c0f1440145111800e6542030006014285904000c030003414801d45000d42c0b01c04002411005070301c51303508191900e90406801080303806110010b041c0000d0307604a02900c5a9860051001200800340b50310303040b060342d107002e00060500c5110394812007200000003403490342d501c02c8541050100c11200d90315145512190b40480c4080340440c020701412190000780a07901000c01d10b9034021200129106070b03c84000400744603055000140d140e0b0054815541da140200001c0c1051381c92505a480c8181500780e0340603400c0302080b07440c4c1039040b2440c4182040742103440b1040c0c1002d008021550240d180c5201c1c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 435173192 1250 435171942 435172019
    0xf061d0d06050402130e0304120323030a0b06090904141006031a07090605181c06022119180c030b040605060d030f0f020c04110c060a0510 61
    0x25040140544070009a90400d48100082900c68a01d10302c10329041021502080130044101c40448014840700000403202c0e10382641c14002d200783c2070808000f141c00601010342c21000440c45500070441c02c014091212003004018042c8100441d0800c01240009000824900d8804181501d1000b169003860752102d801003030f01c0130350700200c401228a880a00316424404041340e00903110381003108000741880c1d001420741c018801050552580c070001d02c101619000c82201c03542000c4a0740160310b512a0518601075484030140c408610700c076107054041c620300c002800f405444091007414a140b1510100c2010f0302a201007210f44030f101902e9940005c40001403e0002c510488a2103ca031a142c145030085407801420b0b507008500d1441c4150009a22090009894080e4200070030403c043d180b00b03d2901c002e0080300707a040351820810b4902050484050100316000704215107a0303680702c01c00b01081c2d90050700c589080d01070030b510901101010403400400d00c2d0104511810f00944070014 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 435174442 1250 435173192 435173209
    0xb01051c121101150509040f060e03031501020c01030b06030a0b0604050d03181203020309060706021204140c03120702060c0319080109110c0706030c030b040e030a02060f010f061d 79
    0x1090106038036110000c40b030103082c003030016500401c0b5030b8500c00d11319150100360b6804c0c008000409030320300412000c0c1082450707448600301203d02d000301c1361649031400c103038808014012419405407040f21500c030110361090240c3d01666001410346030075500e400a14030054040c0c507120a502190a10000c00c181d152114010900741c000c1c0d07a0303500103221460703940d400c4900d690001e5090100c81c13007030318000ca134000040b10050a4291645552032219041070307402070181c1100c00c0c22085c440020f0105001c01d49009401d1420034600b51522003c812042654980001800180f10340003400007a02625003c005400b13492459020343e403410b041c048031042c01b400c4505814012035407810051000d01c050b88500e5440e1121520b20500e02041031041503680c00c000d210701c60815403560586041180f00e03400804180c24080c00c01e218000484003200d84a80240e0400d1300140f03d5800052940c1040c005000c0c12186a1005842d03428100740301200c0148146200310404102c0504840311512031140 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 435175692 1250 435174442 435174473
    0x9080c0114010b0301080705010c23060a0501140f0409031b030c050c06070b0a0c090b0406202109060f07080d050c0c19050f060106021b0a030b01051c 66
    0x34603030107900d00204910010303080401e41e0782c3c0500050104040000f00745041c2e51090810200d83c491070b24118008801308c0380c010354126080142007000c54000500d41d4002c0a1282c1c003803003076a0725a40207211400c941c01c5c2c03496200c0340403801c10b00f443c101503028058150091410001c0c21004121400800f00502001c8001031128084a800d10106000300220390000f260f00d145400550707111401d44a50190494141a80c0c6907402601180a482c04200030411411465101c5940d840058100650f244030009407101c0513112480c604004603043c20880141d46c0c000f1084901e60241f500030b0340200e125285c000b0b2003008a410400104006406074600c42c034081542c43c041c96941c0d006440c0e01401405080800b2f03c42a80c501b10003280014288503c0500c2021141a6003071941c6400c404250040282c02000000319038030390702003004908444c11403030f41d00c0f80f041c070f80c4148a06804130303100203000c04500c480140728615001010400d0380c101103540b480c00d55000d80350550b21442c0b245 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 435176942 1250 435175692 435175717
    0x2103040f0e040b01031b0906150e03010e1203041410060816030c0909060902101701060e010c231507022407050c030d0609090c0905090c060d0908 64
    0x2408005404150860201500d440d004401860405507140408000107000003010005580c008245100c08000680001c00203c2814003003e40d0340d03c140c0405000b624901d600054400c0750300a46414140180705070588800020543d00c1d40561110380b4642029000b140e0007034166000c4004503608100300e4a05030a448000112036281140c1d66151a0760303050741d0303281c1000c1500c042001c0f83c100c0e1341080c01c039203200038003140316002880c0c0f48008106410000394822800c56010702000e03400034804124024029840001d0790300c600003601c4400c0000300880c0011901c0c0070b503100003205062a5001e101e629400c1e035002ca00e90301801420002032408001480104c5010041450750401000d16288070440ea0704d004906442d07910005184020310070f00a206001440d01d81068080084804280e440b807000c1004603219240c80000d801c110405482d40242e022001c210400386215040c01019400c005010a01020003440000e030850007002e0b1000d035a80d81070300046541940201203e42000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 435178192 1250 435176942 435176947
    0x10050c0a051c0f1e030c1b0b010306060b040806070c0f0503031f06140d11040b070b09011a010813050705060f03090610030c030308060a090204060e100f021203062103 73
    0x1120083c0705118640715082002241a1182c04e4011948141902c00003107145c0400d10b03040540040da010300300020300701c0200c1c2030002440180f006861150b4180d0b40f04080900c402903440d40091080e0081e40103000064110b20041120140a460306003091031055402d4405a4440d481d000c0c11074004032004103010a01c4040316003542c07680040c1e10050021410000301107071442110301c00d54081d29400d2440c440c5e4840c1399007400388611069074001d001c8030030382d256603040702c2c80c1103d8800420303160513a46e50300b40320041c03034001d0072008100d00300c50040c0d480c940c083d41c8424070f17002c5007440c05005481a0040c01c401003a25102c62000b0040a0291100c3d6503890610341680741c41c00c3c07001460100144001c940038000505020551011a601031400001c140c036400001072602c600d50340b20020300c030302c005400a111070f044100782081c07060448401a204071190800e5a000c14941d11100041c1c0110010100c40c0e0440c80186401110107011003600c2615004c1e80d42000140e041e00d0021035202 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 435179442 1250 435178192 435178243
    0xa180b06040b031501031a0915040603150f090308060d020406080607030b01090f06090b0310180911180105220903082a0a0507030215240f10050c0a05 66
    0x3a40e40003108401b881d00700301445001c403455241000746960a48255200320100d40302080c070a52031003005038014010018160750340b816803540242d03441000d2580c0c1c106051000a0a075034450141001d4044d1202c01850b41c407401000201c003401d150803030b881586d804000c1109041005420720072445500d0003d5490103030740c00504811110780c80405e1520b00079105002c82c56110301c40d0700840d00d06040c01522900d80d941101481c04641c2c01480d03401071202e40f2030000080c40c0d00300d03c004900602c40c0d03860b1a0681010300c40c25010581180d80100145ca00420481c2030043c410f4010400f095900e54001856000d94400c2d204416026800941540700f8000b00414000a1001910040080040304190744600c4002402415640014400049070020905009011f02d090344251403c40c1d41051034240081510107480e0104290340c203c14940c404050f050003140e00c0301500b4000d00c84a54121644411a601e0b840905000203c0c05a009400001441040340b0701044901649030710801e01d5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 435180692 1250 435179442 435179461
    0xa140d020f120607120e07120f14030f0d0605030105040c06050c0a060204030c0e06010507120804020604030f0605090c0406030308011a12070921110108061f0504031e020a180b06040b03 81
    0x1c6c1c0c81300108181d049403d0070841d61040c03505542c4002c4e07203d4100c0508100c00d00300000d0700e50744056003401b070340400541e5541e1004050010081240c1d40c030310801989484009147c200d540484000700343c1e00d40d1450034440e45000e90007901102d140c00e82101d100d001580d98007030681c0c00682c0304585500c441d0300144000382c0e0490030141d00500130300e800c5080c03400385e44038403484118802d01041403200d650041004e544818080f20701541c0c02c1039065400301e48600e0310500404040361500c2d480c0c000c0b084800d0a514150040c1812250560340341d00c0c260342040b031641684502503089000c008010010003c4149180800610034511a00da900180d0f207004401c4d1143c44004001052194404080b00001400301100070070700d40c400e02c1d0801140d99001d02150130075060b118016101211f200700070503c154040002c0041d03a00c2290b8448844c0d01c03e00e5845040740340058000d60001041d40305005000c00c00241085203550580040360051100300070403000d5010342c01011aa400010401c6a10f80 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 435181942 1250 435180692 435180701
    0x6060f03080414040c1e020102040504110315010906050d0b040e0a0b1f180905120c0703050f03030f0705030901291f05030114040b030118020a140d020f12060712 71
    0x2016a03040c800201c03083c500078010f46c01c021280b061000002d1201d100d05100b58166030140401600c1005010701a0b0811007040d0400c6490181d08100680d90316869445040804115606915958100841b400c00c0102804030f0700703102c540160307646100050b03801081001101c1540030307010289190801220a026910300d02101801c02c00302e8240c10424598554500582c440e50081c0c0041c210b0158942181014001c0000c20146c81000c91260040354002c240703801180e110307204803006805403417503c54407808203c03080303e9001e05402c009026940544011036000052000002da800700c200d1625450f221440c01048143e40618681c5c425803c0c010340c4500c204078009560841c2c07240344d240c014114401406019a00851700d80c44131040d45854215040103007009000303120840da04420241306002c43d0900340d01c80c070350200740002d42c015600045540c800c1c002c0d0130000c403221607400f40201d841046070410b41210080b075a034501d484041c4103c5000b000303140d6507011690041c000560984 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 435183192 1250 435181942 435181979
    0x10224090d0804020f0f040209041d0d08040f060e0a0b041112011406010e2b02011b050c1005040e090c13020414040e070503060f041203061203030906060f030804 71
    0x45403000503c00541e403200c1d03408140040c01c07291404218500c80110340070b4050f06c50800c0d00079007008410344461403880c440c8161412603404841c040e00300540c080700d0820060700e001e0110040341e0029004141d20b40c0000901214003000c0b01c5181d0241c3d61211440c035002c440c281c84100c0d4038041d8809901d4010814a0440e207568001e01400703003052100703421010b01804c0a41404001d07a031460050f00d03002905030800b041e1003140304101c0d00908602040c000201d00490000d1101410b12a4242e04140860740340c41d000001401815965803d00190744e9a241c102800d1080c140800621002010034603841519003401070030003c3d0405041c01714680c40790241400c03150042c0003d200d055064440810140000c035404140c080442d5109070900c1c1d0590401c41e0540119003c11000140360720226014511130641c2d214540c031250400c404450060180c00c0d1421402c007400c030701280c4650021025107000306000220103556601c200140110b80d40100c6c0e41c0a404141001420050b000c1c14410 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 435184442 1250 435183192 435183197
    0xc06060f01120b040e0106060504030605060117040f020316030501090309080318010302070c05060a020304030c0e1501030b0f1f03050f0610110304030c0905010509060409120509010224090d 83
    0xd42062400280400b0034580c0504a8607940719000e070099501d5030001c02e0a425840700801006803103400080c85a8000e0100b035a00608000c0410241e5100da40c2c0303004511100c41c0302c9000c5403a00d5840d00d0400007680410399051040c0c1c11241508605455600c0095200c0d03000040c04407403d150180000c401c5074002500c03504207011400d542c0c59040510881a2024a8010b940310b0032864800c20500c0780740c028540100f03003c0340308103206030000010001e6078021004540c0c0786a85504d0320201006c121404004200d03070355002e1899501079000405c0081004040050034115003022520f00f002114406c40500b0144883c481c04a405201e81500418014100c00c40c5d407822801103042c1d010440f07007030005c1198041940e150b4007014030680e40515031240c4000b000d180d9807500348002e4002802414030030072900000c1001c61a040c07003000c1d14240d04c0801c410707020100c01c1041d1030940010000e28198082c20510342c03803074030300307205c1e004902d2016080300c2c411401c013154810318114403601d44009 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 435185692 1250 435184442 435184459
    0x9070f0f081b060912100204032a140607020d061e0b1207030308070207170102030103020f040209181b032e06020303010b071a040c1410050d020c070510050c0606 71
    0x202502c0b43d904681c072091094039a51685841c00c103007a480c0103003aa00403d201c500c08038000c030400c0081c141400c0301030903188080704e4030410380c100a1480c8082d40b1a001c10801c00c01a246114140040540080d5000134810100d0120f0781e21854203aa1405014041c24884480c107101804030f5881883c058241c141e440c660001040c01c0342d5a60345502e40406400c0c44100f20010752080d1080040300080d043c100205d15482c0340507940c0601070340003030004911906445685e40c2407030070b05209072a40301400801104899560140c2007194401c050086418100d004011070f9a82c55400003d600410050440300da40d42c204204007402c80c038240c0c0501000c6030591408110050340007080c0c905640102c41c80690b140307090b00e00310b02c0d01c0c6604040b29074080101ca0801062050501130350003100c9810b41ca07001e2040c0c03030504001307604c50541c010030302080080c01814600d4500d640a00416094442190b110039281e00000d1a000c901140d000002840012501c0a840c1c0500015401440540702e490 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 435186942 1250 435185692 435185743
    0x5060106050c0a141c020114070f02032a0a0515011d040602030a0b12030a200a0311010b09460b010314010f1a03090309010809070f0f08 60
    0x1d8444410b440044c1054441c250018801001400040ea00f51040c85a012160b000b07014080e01902640b480c001480820394001004180142c6201e0000a841c1c0d010b507141c1100d8503800c40500441d50302d1507941c900f05a01c00d03400004100b101900d4a80104000d0402c0c5e01003109846142c03005811184010341c960101c03402c0c05841e5500581c006a2041c000341c0c032507550403096401040603452065008984401c10b262540001c40240071601c216954400a418001107a4900c0303e00d04886211581c0145012130200344212074854401410781d00218071000c2900000365149410f8501a10a02c10b8501c0318207158010100b181001010565981194140001c24070000b460105070380c803095241c4484104985c86640700144464030940c0080442d6103c41c1144500c00b400c1c0940075a0441d444c40044d80241001c068a1186a09800030341c82c007896200110b43c1c041015081003409d200b01e2501141b0400d5160082018144811103070703400300d1070001541d25000b00f2008204031030901103902c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 435188192 1250 435186942 435186967
    0x605073f0c020a0b190213090b0409031407140f1e060906070806040b0312030601180e0a0e03130b120106170c160605131127060d060c09030506010605 66
    0x8040c3c030b9810035118003c13a500c5a43c00e200c1d640d42c0c1014051481e03c00a51002180c500d03010010a03a01909400c00c03c51410a060008803503900700040d001c21640300c014258051001d0080c0040d038825900500c0f20145170040a203070074400a0040c00917000740b06103295803a600a0552183c0307020500030482802c140c040251550405403e0008010300840051440e0315a0f4105841021024040303d185680c07042425038107800c19208980014042d408500007030404ac0780c44c2007a10b207076198210f15515800614801000c0c3c28000c0d00c840e00090103034400c181d40c03c00d00c3d00c0c02449540d24040c4e0b140000b01c0c1400c03860310144c0000e02440900c00c40b0092041c02c45a04980c010201c001250f561105409941c0486241410041c0002d0402042040c4141d002065030302071440381890440f44480c800820400707406c0081c00b2043c081184001c140fa220b102e00105800c00000380002055002d50384980d429142006502804150000c00030810088200310860040c0031502e002410600c2d0607080 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 435189442 1250 435188192 435188203
    0x9030e180f0c0702100c110f06030a15030f08220e07120e030a0914040e0303040b10030f2307050a030204091e051b04020310030605073f0c02 62
    0x307200c004440d1800100450b0b507110460b50b6958004180c03855402041d04028003181e8244421102071412043d0f490250801d415034141441d0300a04103829a940c480c07442009009010315032504400ca840c000012071303180b16210b1000c40c050f8440c65514075091072960108100d000700f80c150b0031030790041000108208480c080d0080d0251074183d1105404045100103000350309140003490100040d80d0281e590080f5048040360071050b251018a000c050070002103500c406a0307035445400030030004001403020040103510802107180d006089440b5160030032011107600d02140c0000403019103020754001c02411031040c144100c0100207560503c0b000c03c3d9007020510000303000d15120034480c002c0140b00741140710ba5021030710365004480820706102e40c1c1c40c8c0245080d50303200c807000708028450382002e008407413003224400001ca002d1480d5556580040800a095404206620140c00140462101d900070f03d00230b500340b0048022110000c0580c0940012b16500d12240b5001214011031380100340f = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 435190692 1250 435189442 435189451
    0x70b1609050d15022a01022d0403050316050c090c040504020d0b09071e09060c0209090a020d0b07031d1b011101020a0215130c030204110c010f09030e18 67
    0x207203084051070034505550a407040080c1c103034403c2e00229001c165012001c1c100c8020000380c0503800511058800303098200d125070104001144060810740c41c0405200340844d030400d0040850f6440c16580392510790840e044aa507848542440d00004428072204120746661100201c504003c075003401030b100601d0703100364410140034a402148038003040102d50320001820032301030030b20702041c40c107080700908580020741c182c00103c00020b02884040d10401e212000e035405500c03542d03202e003695020000601c00051811460384586000c030303001a00d444080e10b040c0d034410000e81e0141d05001c40064140c801e8a06d455111310030304e0aa112104c40300044541c18811201c01e070000400d80240100d070150a126228401580002100003100b0390001c2c000c01a000900c0c401003581d210045030001088850744081c1412403103040600162410380c1c02091000201c81d241e51402d09000015420358254000011721566a0311140090541007110121040411610700c034501c040e10440c980000400b40 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 435191942 1250 435190692 435190699
    0x3030909011403150112050d11030423180a0f09020607150e0708100c0f1e030b0a03050a050105090a0309060c050c06181929040911070b160905 63
    0xc025465181401069500392500c44c1c0c400b02580c407001040017002ca24801101d0510810407446045407158441c1c0643c0d40c1702002842ca490302e0402e042c4002200c81300300c07200521441101165a45c0c450300b20a80c202001c4100301007e01d032450041d0226812000f820810070b0906e4402801230340c5220486420715032001c07142c0405903031500500000c4c01c2c0c00c80d0440c85481040400700d00b5490026034002d0707004900c141030000c0c01440344225034285210a48801041180400442e5130141c80c16806036160a4600000c0c4541003a000075503401541c3d1084c0e601d41c01c80c4d0125400c0c48800c0c003400344e00c82c40340401011a0301b06560000c14000d0f05120301c2c020002d208600004010703051141609164004090395100d00103080ca0004404503005501e214804c0d4840620141070001328003030440740e81c681d11550004015202c1c185000d42c44c1c6406070f01c00c80401000c2b4000c003c9110b03d054480f0100041511146245018000c04030041c24008108000c6000060319541c02405142510400d5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 435193192 1250 435191942 435191969
    0x10e06010602031e12010b130801060509010b032a070510020301050108040b0705160809010e03070303141602030102210f0f07120f0f05061305010810050403120501080c0108060303090901 82
    0x94641c0082802078807403859980f11403170000607504e0142c002400c01d100c5580140483e140d07407042464200d0b20b4500c64950417042c88001000111180c5000e90341c4120323007451841005050000c4800e85d00010f070390072070741e0340c0380480d501c814000e080010681c160310b8100114955410b00c03002070a0000c00502c02484188400009401c5901c0391054540c408140c40d150852020345280c20a5242c211905071070015002030503005842c83c0c00509501200d0305520b0301d003810903058000c00d03c0ba0b803058150050108458880c140180c07003d00c000c1c11a2005161045c40740a090b040e80c02d11507101a180e03040c03240903030052192400c3d40100664101c2c81d10700340f1550b011082e1504c1006001c0e000507507000140340904050001e440d0784c00091241c1d804842444a510b6502c174408205c48007805420601d90285440507411103a0350b12664000f40641800340c240c00004100c0d20076180709810100c0d054100c480582c009580018025070055400c4000d1414a07621002182d01100140f08180003807444 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 435194442 1250 435193192 435193237
    0x10e03011527270825060e0109020904030e0307051f030c0c030f030f110d0603020f04090c210b010f0e0112080a140c161a0703020a0f021908060702010e0601060203 72
    0x2294200c94409860000385c081c4650181182900300170381480c00d903062030034040e040190b0b06041c81000c0802d079005103400081d443d56242180d2501200140c03e400d4030a604010445030340701400c92400d9407070314858200f54403824400400359803140c41c004041c04400f240386030020b034110719014030001e03262400142c025490381881c1c020b4207070180d0818480c4000908202140c00d82c0e007060098030700995a0040c0c00c44254188006c69402c0d8402030021281c080082c085522090b01d00040312034401013032600c00030543c80da542200e00030380c07111002085003001001803800e80d02c0e1703450042401e1140c0c3e00d0207625503207134000e0500c5400880020031407000000d00880d00e0781000d5030082c080304001c0390300d0300070410b0002c00303100102d0040482003c502c11a801c4030314450000c6407100c90341503001d05003c8a0680e1064110f01d010380c0300700e03449109020f01c6280001e05642c09402031078164018441c0307041c5010040d086481d56002e1803000d80000e4014810300782c0000c211100030415003050002d0158 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 435195692 1250 435194442 435194453
    0x3010603091a0412020d0207061710030206030f0703110f0a0807120c0c05070519030201120b060a030b2d1c060c02071805010f0302010e0301152727 65
    0xc18845425402c1500c2e0244030500040711100d41011910740c00f1200300301c13440030040c0d0b514400307441540c000a103402404891500f070301c200680c01c4254050316106041d26075001034000d8200f02d9a6130342d142d400000300800746070704d4001c0180030b92030761840303078504128a003e800007481604401c4d4203000e68000406d6032148504294800b924a032441040407140f020f20040000850003000d980f0fa204100c804234080ca00420034505a06541c40c0c03c5a89a195600654013442ea4285508006541740d45c44031a546450f0000c05030744180340d8002074041002810401d164a10f61010700d4020034000c415030098100b420b0780c100e9900b0494071322901e003070781248840040ca178024000b0816410900c401801a40001c0d06900380c601b803000d4001c02c0795594030490201d4000348a403d596409d0084104051350084888e80201907018001003501041504040c014606680c06603121a2041c0f8060b00a141140301c0c510358104005414440303248902d414042050282e0f170842140d03481d81d48000704009 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 435196942 1250 435195692 435195713
    0x6150a081302120a0501050a0c080603030909041707081b0a030207091109030a1b1508070e010509090f0f0a060501090b0912060a0203070207050f03031615020f0c0c03060c0301060309 80
    0x8602e0000c8a44c01c0c0d0280c540b003400303480c0070380c0c28802280c148004403c500d401000804d00c0703000c001d0015070410100e102000070b880d001400039505240014901001a0000401040154001d00140f41e0390100701824140da010054522044d42e00322048180c0001d03400301e5076108407810b500c03011602c442c0c0b000c4000030a00c100300006501d4456035403d0410030106010b20259a28a6014074000540da01e0080b10b0020101074004005892000090ec2581c0181d4800b802c45c04180342c2241400c269101281c0380c41025a281d604c2c1c0c0d0780305020001ca444e00c410902c0d130f0002c880c0030280840c0380342c24001390291106c0e0090b414800004a03121201c2e0321032440c22200d82c80c54604035452030501c41200c1e802544180c40e01790040c025800301048500300000500905480038008625050124042c074480301d000b0074044a201c084084409484480c0e030010380b0a00503002c9120703a403807410a0041e4035140810b03522a0103074001c1c0041101800c81401500c0c1161201c0c140810036441510700b22814a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 435198192 1250 435196942 435196969
    0x40207020f12010b182508040311030702120102091912080c1005010e040b0601180605090102070e09011d0d0801032306010b04151106060103020a02070302031506150a081302 76
    0x8010171454005030401c0c4800300307001c0c11503800c400054800e2150700d007010100200c4184080740600c4082070009120f20b010800f41d40141c0140e0b41031083c568002000c00458801742070041e0340129480c1d40034900072100c500131110000e01484c40601d0419040108040100d001d04010b034003007017048401c5802d2020301103450500804000c2985c4507400325030082c0c0103940c252070004000700003030301c5940a4041c800d000c002d2500304040c014508a000c0751690301000c1c80504500400c94001801c11805031080d0081403003000220b0402074500d000c030f81410407055013944030781c00075200310185500001c10b41e05590b0070169002540307441c01401140500c124075103c08a200c1c13140002076403612000581306584910102e0103264846d00011291481a4200201d40d80c00c1a001301d40e0f1903000e82c0c02414208414015610415078a800003420700c0d05000018414245944c204503040c40c1c149600b001e1080d10002c5241403020310743c0c0080042d9001842980c900d03407204000400c1d542c0f030140c103a482 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 435199442 1250 435198192 435198199
    0x9050f04061a0703021e0c0f010507060911010e04110409091a0403020c090705090f06091210060503070807180504020f030604060c0801060f1704060b120a050c040207020f12010b 78
    0x1070044a000a902c581c0c40080190010701500c0783c0307025482c0070682184203884800004101030491041007060011221f84040d050241c10018900062020f0254102844c00740340d40800d0000044005040b00d4212214148070b0361901c00010300c41d03045842078400361101c0d41d03c000303604c1800f46021403201c10000850001401072508000800d43e0010780e0445540c7c0642d807541c6c40345c50306042a20b45019090520345d1040380d040340c0480034181b01002c1c05034490010490000f11540700d807441c1c20010611161800342d92524020700290404011580013020403d00030180c0c2c1d131030002e406234400c2c01086121940d81d16040800d042d951108850000c0c014018142e400c03506042c038044005042440078078010070f4000d000001c80340c0c09641d030305081b41e4050311100031704442ea1000103019000140215405580c9008001c060b46401c000000e030728188000030301c1c00f0000c90619515041c001c4070301a100301e0041002c08016255007028421042098803162031030000301680038003400300441420740 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 435200692 1250 435199442 435199469
    0x6112d030414030d03050f181006080c15041a0d021314011404150c142508030327010b061c060e06010804080d090b0712050a05040309050f0406 63
    0x2c12407181c01d110400018202c04591940c1d040072815016100111400509504641c001582142c803950030f04403094006002e07100d810195001c00780494441d41c000740c0d02c0b40c0c00b510b1149150304005d0f41c0c1010500c59031001a0406103040004d2540311407545100e15800400301d03000c0329180d0070b81c050f545004510400c0d50004ca88841a4070b0845090440701da00107448194001042c4d0420310807070341507500141003640d000b40c1c408070541d229101c940c3c040b40e02da080e240360055600c80922102107419007a500381100c0040e0031240140400c0e00d42c002e00d5040c4c00410034041c9680311409c00e1604074120803c2000503c2c2602c41c01801011004c180a03040140001d01c40409040e001c682e030f02ca00f00d24030301041190b03150149503003135100c22982280030a03018404100482c0b03848024141d000c68a24002c62a881913039030b000721170a070a40b54400400c0d2140701703080703c024090107881c0d4400c0c00350310300300541c2c902038500509000d5030781b2589005071603100500f103490316650000707405415400e02000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 435201942 1250 435200692 435200699
    0x160f050d0203070518100518060c070303030221091506030a06060612110304020319020a0b0d151e090f0f02310e190e0d030e0706112d0304 61
    0x8110f40e20030b49426035071010409007400c486ca0440c06410301610b00c1d6071003500304103d5024a8035110a80100c42c1d0348040d0910000840400400000c00510712030fa4025864035540e045201010020f2443c00c120b5001903020003115440c0003400100303081c4003550b4085980c03a00000b10b4100924084064a00ca044c8040410b1268101e00003824403201e400c0d00b04045808182540792900003078800a5141c0c0203411405640914201c0c0003050758001048146070302d580b030f075003940b50703070303c0007461030140747e00c1d500d10084102d400c01c40c3d40003c04007006182c0c409180c1500c4001081d0840c000d5000c842c1d9540441c001d030980b9640081c1d044035038914110754528070101d68038070040824140d800c40d9000c50b11a40a9105410491011108901c2031403007142c5a00c01c0300682c1004c0c003564014016502c61000e660a842049010b11405590700c0004850240d041c511781000e209070000410301a186615500280001445c0049071501c21150700080000110140c018413442c40320450324413000c07c010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 435203192 1250 435201942 435201947
    0x306060f23010e130903081605040905040203070e040309031502030606031b1312120203191215090b0a080c032524080603060c070f0203070e0109021809160f050d020307 74
    0x41c1030303540c0030347c603502c1d90390390b4400720052520381c548081d0000034814041003111031010782120390000d1005081d07858003a1146112038480c0801c50b400e400083d00341c2010414003d030050b450405c40110715003540703189481d40110304188806042c0100f2182c18400784012211004159190310010300c401c460000d589002d400ca00c0020a0701c16205070b0050856171007014000400c903440f8520449051490640c4980700b0381b0180d95850091548a40b51201d00404d11954881d03080980700d1040c0c0000c4081c0200305000c60320038981c00c240714176408590411444d580025042c0b81c00404c1043c41140e07898040d6440007141c03585c0c0d0149164000042d641480c021100440140d07146080e42c0d401f01030359415040580d12541030b503102e10304200030885000424099000001c06600140465410b01d6580200101d5103009a0103141601e9005c9501900101c1105414804071300440310b42a25040c6040c0c40500350f01c6030f9142c0003c0c402101c003007011707075401403040c2c1d0b60100d0085411501c038601070601 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 435204442 1250 435203192 435203201
    0x30a03060801140601020604081615060816062c120d1b020901090f0e06090309120102071505040309150c0b0c1c020313060204030503040306060f23010e13 68
    0x745449542407140212407001d0315018a40f080078141d004000741d03116911000700560242403012095150b01c0c4941020030607010005c103070403084420000d400c07171409101ea410041d40ca0034602021040800c204407180d8010b00b0403469642e044200c01294149548030b241c2c48110351a0540c200c84100400c101210f0081010028888a601c0b03c0220034620b086509058000c04402948010032000500c1404070544c031030b1420212401c000a0b54000fa0840f0034500f03074086502071a42d81c000954030f182e604000e142c41c2c40b010003070002541030024540e01c8001c80c1c14a108030070031082d0365800207801d0500c5886500000c2a0141c40b1001031240d03540002d04840012106980c0d11400401091544c03c901c001c66100000200ca54800c681c0c0b0003030340d00f000c0d41c40600803905013118a1855004141c042c40100021803042c0000c554481c81d6242c03150070340e6501c1e072180c1d0070803021841c100606142513080b9465038a40251541d010200c4100507184c3c41d0304060f5864004000180d4040c1002c1d80f40d00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 435205692 1250 435204442 435204449
    0x90702031606150b0313080f0d05090604020415120816020a0914011220120d0302072d03051c05090604060b06090105041e08010e0304150e060405060304030c05030a0306 74
    0x603e2001d064441d510450b2a11041c1d4080d50210f10705490750011a8001d4041c0c440300034148411440c2044200c03060302074581c1600c50400ca0f400001c140401c62174203200790070360342d0300201800d140c40345000d641c04610b07106000d01900008000500c8900c0c02d0707460754500404e41d402009801e0301e0740c5405150004118200c1811142e00c4402c00100301401400c40e2880364990145602d0380701051040c0c81d402c1072541244554000c20702e0340d0302c00d1010800303105121210425980068862105d41014141001142000f480742c2c1c401540c0404c0d000c45180660030090b0305420640e54803480285000140f00030301710b000300018940000d00c6415080401d000d4000c901410050041000d500104410b520444e4074040c0841c07001c1104100d214080e4020440e001d03044080d04da8040c2d504c043d4242503415410b81002d10b40c00000f014403000c00c0200320100401c01c50b20b8a4000c220a0901140c842d200301c1c0201c51150310040006020503100e640a02c501a03846000ea03070705c8525602000c0c0280c500d500 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 435206942 1250 435205692 435205721
    0x70207290f0f1306080f1f05030601061107050f0d140f0115062c040f0b063c040902030a090c08100c0c080708030726010e06030303070905090702031606 67
    0x3400044c0003446003002a008a904c070125030102d485450030703200e0707540704809030001503040d2000008140c0e0301808540c0c001d0140e52105110181d004142e40e0801400d900710503c1054501d610794410307110103041000741a444468110610200020325141000a00c07100d841c0e036080c00c91204c11000026814000c6030b00e10703100c4406400080b500e03003201200a103410507030710300000b10154035441d180c0c0101800d18850840028001c207034a004c039510750b212b000158550046501c3e0719101d1902e00c0c00590300790400c480e01100341040303069400000d108600c280d050040d0044013107214400f01c0d90004000c1c507404445100740c6a6541c00d0395484100790304c0305a0310301e403400c400c100303806d805a60341008141d0300000361460203026946a04041e00080e00c000104035512945030121151070701c461003130f1000f12907052025071400e40800403104e0010191030213074009100303000140b83c00c520200140d45080703030300d80019510503008a195010300841c403901200718100d03603414405a40e100030018807694 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 435208192 1250 435206942 435206977
    0x331030f02010b010f03270c05030c090c03070c29010e2409041a01081f020a02032d0f030109060501050c33040b07020105070207290f0f 60
    0x2103000da00b00c0340307150101c41c003061a0412030901d4510070750280c410700c0c945540d070194502440100b100f0100030404122030482501006004c2c5182c200420301400a08448440f07003840d05a03110400f078000900054180000d04801e003042240d00255032006100507044c031020f5000c061920382c400c040a20544151100020120b50101d5461411000246c001d0f180b082c0c603102c40c0400d00c0030b4000c0c01042690390f0304400144161008020b40c3d424000c2502c00028103e6499881007038101e415001c094807400c81c410014407100765004800c2e250452030741e0046820505e00c80182840000c42c1042b00d1307a41a5000a0307580c3c0d10764400c400b03176042e101c151904225460300e0344010b55003031040303207a110400e90141384110110380083c155038220341608041c000d07007882302d50450340303c480e0300f903038100c1e15040c40c00100024a43d0903c0341640c80f000174070080002a280442c0540d48074a804010784008190403480743c0e806a01c60708441d042c46000580315600c6941164084081c3c200e28160f000907400c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 435209442 1250 435208192 435208217
    0xd0f020103052d150604170111070209060913120201020a02070f050a0e0a061809110a0317090d050706210c02061302040b0a030501020406030612050d05033103 70
    0x181c1c10910440302ca2800703d20384038071000d46032052a81d0003070501d01016504003c404580e00c070400540000c090500c08040b0b1020620051400c0d10034120180414aa00340008000740e80c0e40558a500204117075001205500c0e0b0a9004001c0140a04081c2c19401c02d4490b642c0020303415802408000303403071750983c1c800326124a915144000b0909c122984010170440601c100d1942118041d04072030440000601c4c46d9036611607801a416441480c04001d9a4100303400500201d400003c8101500302e94181d0040d0455483d030a2480701300c4180744000c1400308001c0c4081e01e910044d5544c50f504181115482c03582d4500c002c1c40c1c107020040e90802c14940070000d0025034800c3c06246210f0451350007070401a41d9800f1f50001c3e254084100303903882902d82070306002036100e0b24459406180100c002503070303c505241018090725010307440781d03406070240709180d0041400421104440510703454090341d01d4032540c54034080140e449011034401500c20340b080c12040034050004a04078030a4a44c00040c0c0308 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 435210692 1250 435209442 435209461
    0x31c0906110c0d0c02060d051e0408031605070201020a060c0903151b0c080301151205190b030a05060f040c0302090106030c0201050c03090a0b07090b1204210c06050a020403020d0f02010305 83
    0x144135600a4100d80184452480c26200b50041c96000721011240c4401c11042c185400c2c1048041e10252018000007041c81405a800f10070440e4443d060709001d03141c042181d000030f40e80e01c01c2401c041c10f4980d48000c4000d2130f074420740c880740007140c006008101280c0f00381203200051982c2580c5040c88000880ca01080d03030b008028115000345c000c164242140c3ca071a020600400c0804201001c0003031864030042c54104522442c0d000c1d00c07800b814a0301e034522861800d01103071003944900d4426031006142400041002828690040410800120320345440c60156101451900001d40c01a0342c503001107551981030307000000034040c3c0c1d40248841d2711441044030036444156101d00b016045400100040f88103c0e02c8190002078514041b01d28a541d416290065044421700300715039a00311041c0000e2003800301c0011890800b044045e07044291144018040192030200108411b45500c00208210510340c140c400071900900911400e1314945888100e8440c43d10040b40440c0c6004042195080b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 435211942 1250 435210692 435210707
    0xe1e030c07050d020904080901120203070302130e0c1e0903011e0c03151203181401090f080607080a0b15030a0e0c06180406030203010e1e010c02031c0906110c0d 71
    0x42d000340985d00c0580301c54079081c00b10b500c4541d01c903042c031082e4202060849224402103100b4803440d9401600c5405ca944a070005148641c071054902c165071003802003101c0d0742c00486004500200c500d0014a01503102c1d102a4007541d0801d9074994641400030340d2001e0b900d0015004070106280800c0403040c0103405501700c3e0906c0d8244080c600a141c0140407100114403070808650003418160003200e07400d090b02ca08120590000c05481000240d2a1890751700440c951000c5c00f041e0900000321820300c4500c80c0c0d1180010f03d442c0c200035600740803614241c001d62000102850250450a2210408510114961007941e003a03a40c5441c00392501300850010410210003000203100c0382c5000c800c0d15015080e9150b8000e2558025034442e40040180e40c00d1040c10141042c0e5005004010090a00d5100780d285019508110707904040c0c081110310381c0032040310a11800724070703600c1c000d0070f0b94a03032000207141c3c0721801400545003c0541c60209051006418030074501401c507518420700c1007045030b40070b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 435213192 1250 435211942 435211969
    0x1b08070e04050402010302070215090a0806060d020f0114070302160605090f21010203010f05030f0a0308130c090e06010503010e0f06061203070c060c0308070e0d060e1e030c0705 78
    0x2a5111080c00554541500203c1c1c00500524000d401e01c0d11030380002c1c50040a1342d0000040c0480040c0501c858144404214001c11440c4042c0000d417900801040d01c402900c1c0c0000d0ac60710300d950740d0030110307800b800e000310080101a41c0d4540b982c40f241340281d40d54503101a1040d03403845003400000c0362803040085031010000a84100341083e014011301080800c0707420302c1090f040c2c0d07000020642c00c80074405907000741107513840d449440c0d18000500d400c1608503880343d0b4140d001500c1500c0800d40018119801031502c5445803585506820a48142030b100e410176101103082a4185103072880000d411030580b50101c0080040d0a030000d0304aa54030051000341106030070241c0098040d04c0c0c13082e60420360801c0c3c88140c0785030a085585021008100d07400c0500454a140350000c2810350201d40d10780d00c07001d507042403c0b40c0c03003403000001c00108854134010440c1740c9a400166481c07000307201d030101c150000d100d40d90954440c0520a5280d400c030b150013201c503126a2000086900d000c000e1482c02c0c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 435214442 1250 435213192 435213197
    0x60403080a1d2707090b0313032109021002010e19060f0507080f0f0114090405010f1505090a06260102090a12050d0e100e120607031b0807 61
    0x4101d10380d5016284a400c03440c112002002e407660301c12003901c2d1000007508422000c040e50380e280340080800e0001c5000645014204400c02d001849005400340403aa040780c901992240b040d0464901116050169900601b40f41030044c49840b0143c00d41c1c0001c503255208a03913001414103802c008a0817140003100404103503001d08403004d091301c03020142e100e405008107000301e01d0200807155101900c0b0103940c0343d030010702e8480030411264815042c0540100c0c0105e4150704951400300380407600a00360501911030300300000401c0411100b5031050000e1030354000103000003014211030303070301c059511700c03800d0300031000400015075100b001d101d40415240b5155030181e56460100312815100e000080b440303495035003000840540d0396a02d81180c0141072200c1080000390346031a0190030a000040140240004421400381c01c0d501d4660300c00200240b45001140403001d030303000503004c1d481c00d4a10059805003c0610800b20b80c1500681480d036142e060100c208080c008040740c4820003110403c00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 435215692 1250 435214442 435214447
    0x8030412030e0d18030c060e01120b0904060209060c060c0a02250b070206120c180414041403070803092838190507030605010804021003090f060501090b06040308 71
    0x348980a060310702c290080302d203882c40c4c0d40382d102d6039100005086038000e02d0100f445440001841c0d070303001c803000035a030880143c20b020803e041d0010601c45140a44010010307074021900e4020b40c1ca071101036807041140c02046403050b080220340a5400c1d0302079254080140100c000444000b452102c4101e20f40e5076602c4010b5181c1d180c0b14040c0072070f030080b80c4100d81c0070108011402e48481d01d0744207207000380c5010000a0b520a01405140303107842c40746182900a50a04100f06000c00381c1807081ca0340315401c040c00c081c01c041054842c038150710402030001e1070a007000c02881206900054004d41c0a2030340c407540c1156004c0c410010746011405d100090500407810030030312262400f10340e111241c4242c401560700b110070803083d244c81408115120b40206003207901c99149160b1a00580e500020142401c20080d410600000d20100b00188040c0c00390000b190041031617886a8044170101d6003203d00541c0883c8a0f1a000f009000d083c45101061401c0240c900104c1c509841214100ea0b48444603a2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 435216942 1250 435215692 435215713
    0x70f031110141501020109120f08011d15030f0307200603040c090b03030d0e06160e100e0d06020301030803011406090d0b04050a0203120d051015050705100908030412030e 75
    0x59249542c3c01c0c0c424115500c1c0d0f48440700017003002c1180303012682d6170344800c468011410303002440000168011850707400c184030311014618107410341c5a080150700c038002d10b242280700040b80c07814081c14548042440f00040c001e0a100c02d092255010070000311005480010580410130140016600030780002c928580c20055039419900a540c1c00d040581680d0034200004412803c50300140e100c009180c000c10100645401001a0144840d110b4144842d82c2c1e400b020100340919a011404024400c1c000c001807519078540e80400022075014806541d650703100e142114040d002032040c00400205008560700c0d0749024070075a80160b002401807a1f030100700740c5821181c0e400140c0207503004d0140c0801e02c409602c00344404006000b1842081d55510302054041b000c680c0020b00c01c0c620f07408100001d00891142184a0244220318680142c844905041150906079010031940801d850040c082c410000b90b00040c6100340c0c080e1100024040f11030300107070305964103101d0308252604100490b0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 435218192 1250 435216942 435216961
    0x20f1209190312050316080708160903060606021e010509060f060d051203160201050408040b0c030c010204060306061407150f0f090c0305060c0f070b060402070f03111014 75
    0x1148094400203000c001075582c0d848181c4038001250608000440c0042088004004258000b41100151410300128680300d84014441c0b440a015203045280c081c100050701d52003814007101964028004100031a034802010355a403e111452105d0219490314448142c0c1044c82682c2c454042e58000d0001350b9a44146183c05100080003658001044040840420400c00100c5010f40c11810101d9481c1000c00c3c4150048841c1c88121046a051038204000035070318a00355000c41c0c204444198490090800326402e60003500d15028507580302190010362164107070811821541181c59045100440800c2d45069110b5254043d1070f04070b003490b0b4224460701e10b901210180d00800c80001784294030003000300a42d1000743c800c2c6c0d46c440304a401803052100c00e10030720b0f8000c1c1c0c1402403030780351450350010815203006601002d0040e0075a00001003c070740704c0d50110341a59038849500c0755075020525014012040107001c001f118402e0861303003c0514260701c601100102284440e0385c4660b10180c01c2c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 435219442 1250 435218192 435218209
    0x20607140a031e050901060e090a02150f040e040506060405010b193209100c1203180c08031309020c030d0b280905090a2f12030a020f1209 61
    0x10340f501029051152030790031100788110750007035100200114400b860803c45600001c0040c02104e40c80e04140072a0b001a911408e6a114082c04204070a403200301510300c5128a01540d40b102c4905507000f8100020440c012482d144903c1c422542004566260b50b42e040003801091941030b03140e2582c81c0201105402000c0d8170f5481300504401d42035181000801c41030824010142c1c40c6c0e84400841c41c07082c03520384a4503902d100340c05490502074062403504d4080f031000c2440c0d050018541c3d02d2185e242003161012a00440076007200c0c200c0c03481a03842c040f080e900e9012600320802500301c01030105000d5814000c6440c0309c0407490040d401c2100401d02280244000355155a202d00b5510460300440403c0780b00d40e02ca1401e10b5907a2181c00d180c105410113450000f1311251040c0c010705d801000213101e42c0407005a003900580342400c001c07400c0d07402900390f95440300c1013940703c80c41200380e00405d0305c0040109110394031682078500800c0300403461580d860f101010b6101c00d002c103010300c6a007820000e40 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 435220692 1250 435219442 435219461
    0x30b1e04031101060b0c07030303060503030306010818071203120b12070b0f09040513030912030903061e0516020c0d170c1204080303011d06100f05091906020607140a03 74
    0x281c40d5551340d036159500d40c0068810900da0b001f00d50204241505849110010a407c1d40038510358940b1034002800504020825021104e2004044250240c00c018200150070517403940120208242406090500c2c4071150684c4e9a041c504840094105440240382110b1080001d101841c140008138a0780d4010890051b0001001e001c00d50203503445000b02400340c5410b0300608100c4000d401c0c028101c0780103820296280d070880200c080080d1340701e004007080340d411400010b1543c0426008003040e68905001d070b02814144414068500c660301114840c009040e022a44000c0129040c001000c200d01005020f1447c070401c4941100c4641004040321130014050720b0505a04000c5015030f50010742001d00316600100040c0200a103201c52a5a0a66008461003862801c400010204801000d847c07003040b11380410721070300b14011426100d8101300180b4051840010140c2e1780c841d60314511030f510040c410507000c2828280128442c592601011044a2815548003401c0d00a081a4071 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 435221942 1250 435220692 435220727
    0x22050604031101090b040803091c0e0607030909020a080108010f0603082a0a030801091d030d0c05130b030411120303070e0a0b0301080f010f06060c0f11060c07030b1e0403 75
    0x1d2134100024502c8100c18031951184403580e44074100400c000f864100704c150024941201c5101c00e2007000e800a040880104048504964808503454201c498000503032240300c0580c00460880000307070700558602d0503114110000c01405401640907026281244800740c101c1001b000203803010714000e2001c440244169049500403140c4e206140d26041000c1c500b5000541800d0051048200398040d000020f0101d1310401e80722600e2032045920b911075582656003c954400c000c052241c045d500b0b5456032280104990030700355968000414950046400300c5880e2800e00b0081040d1a10504204d18004400700550540c0d4503100251140318011100c41c1d44039064441c00207401d0200790046010301810006407403010390310b8140e42c1c20f403800b00402002d01e5080000a115490380071400850740c581003000b5020074841802c100141525142d020380c0c01550009200c2040c81c2e00080c80d00c12a4410000e08000d50307030710401d80c00303600e0420440300c00c3c2c02070180201307002c00d20450b4455541841c0c072 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 435223192 1250 435221942 435221951
    0x706091419031a060301090c0608040c0f0602010c0e0306010f0b0d06050d0c0302030f0703080d0f02073009030206120c1329030103050c01180b0309010522050604031101 74
    0x341414189034049070b00841c0c030540220362000305211091000707900701d20154000e0007142d6940e40c540310449103034040c060821031981c0020f8107000f600d08444008090100070190141d40304c0354000c0c080c1c00c00e103071504045120300000071803900380000c000e812140030240c0e01c0035090600605403090740c00340005030802505c528021505a03585400c0c000c540c0e20520003108501e18510605043c03a40800818031243c101040400211307941c00121204180d551100181d0040d04501c180001c2c020440c014003282079002407010101d4041c02c0710f8803900d1840030440350455503500101d4008003a804003d420110501120a40300341c11005241c01460f209280c0c0e0a08410500510118180794414076000f503c18000b140c0c40004044408540342284004524660454072050340d101704c00808141007142003544142e024015aa40401030700c0c2c0111655580e040146419021b000d0541e01c24043c98000341c012290040001055000d1a03400806403116a45586080e101c000d03c40c0616032040d502c0c0c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 435224442 1250 435223192 435223219
    0x10603060f050904061e14100608090606121609061a190e0a0308030a050f0123120705090109020d050106031e1109030a06021e03011a07020303130909060e07060914 72
    0x19400b40308070141a9050074807403231610903d401301c0750701e203944070100340701e444024010134410203e1000c0d0b1101d0145c1c0e200c0d0507034220100b00307072030114100004034000c0203064010900500c46d400230821618599801151800300b03c5c0300b100c2504c48d8030710580310901040b00403074105005501040c42d00354014810502d03503030b498840c04503550040340c0b03044161342c2c0d800420401010100303507540504140d94200405070a50f42c208041e0400e1481c525104e04071103180152414410048000a898003030810341103545d5400d02d200c0650014000144564141000495028800e00c200745e10500007846104051900c102800010011180c078046050b01c03c000b1408913860800282c4001c1c0d20038440142e44055081800e28022a1082e022400202c02c0004011200c3d40034035401d141c0c06207890290703840030a480040d255210360384000f03150740300000340040e0307415242d0301000c0201d01551051140e001d060090540301c281c0c07405020041072a40070240200003420740d14400c100009000781d88038204 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 435225692 1250 435224442 435224501
    0x615110118140114060607152a030506091e060d020301110a02150907170c0306070c020f040c05030705090409061518110403021003150806010603060f05090406 70
    0x1504003060316002c0340700001c0840300d4000d1144080e0103e21079000324140c241031000480d18469948060060210300c02031072800340306544601444a20400080e4510411070700c124541d0f001240541c000c0f900c0c003400220581002404680704842d5000d2020307c200006450301384458010380410303088110550010010780742481440312000400009079161604000001c1ca0031031a0300c1808c0310129664180064084000340d180162100e99500200104aa0400d140381032541340100303502d8403400052000241d044055103424a000795148510b600040c4103020a5503035500850000501c10030001d40464440c401034120410300038004a2134566984508040d610f00c1c0f22024104130b0210801c1055203880c00c03481e600e40d000130400703103c2d200d1171400840700707030142e4800680500c0120b46c910210921036485141401d017040d810b40f80e000c2d160108240e44030b00c01d003e0800400d1074030102203490308960580c0011100300901070700440d40d59650700c4025142644600b40700c04224000351440d4030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 435226942 1250 435225692 435225731
    0xa0203120c0709060b0708030408130b0702040f0e06060f18100504180503030f1b071a131119320d050d03111303050c04060906151101 59
    0x20302540c801512404900c115074108440c0707500465065103408401c200e90030811050341ca4840d00b180007152a9035039400d09031518404c0100005280552a00c04a40c1c0c004000141c011030b40281ca0030420030210009000031100c5000d810840d6522480000e1035070302e03200c40c1d001c84408014003c0d61200c8801154256420400c0d11802c400d0004c4a800740060304040c4190609480d60043c84a5845240c5d202d054a070300c0042c0c1002040095140010120304007000002040c84001e104540d840d07070305007095849165114081d00c601e401c0070f004120002003400300740d900c058004882c010285110f074100b1004a07088040d440002d0540400050403103a03078000040b640d648a44200e00c080204481c1d00c1c4d548601052161084100c1c603002c401007a80020740c014461694107001645103420040380c940c6025440b100e5450428031350380801040030100d140c10b0011f00c140c409020140d201da055100351440c81c042c80030012600754110a45900c03c604145030420b4050000940d502444074944170748 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 435228192 1250 435226942 435226963
    0x121b090c050c0d08040b150d020607030e13060510031a03030a0f080714030c030601090f0f060801080c01080c03071b0804050306090c01050910030f050a0b030f0309010c03110a0203 79
    0x1000800c400d100c0380400e01060b120090b01e4904a400c500d081e555403c480c0071b01801400703500000c8002c1d0103260b03d600c0ca802a400f40c008081c25114207151070028505070b8200d1a046c01003240c13050000ca18441e500801c02a5140101980d004511030304045000707044c0c441101944058100d20140799440502c02001d03070a980783d84251004100707005c060040c050143c00d11040142c0d003441d02405080d18010703650040d140109642c0d4039210040101da09000302d410056021001c03800010310107010101250494070075403114a15680d0b549034454031003040046490105002e040060381c0580d8074002140d20041c0c900700031240d44c2c1006500340e200d40c0250401c582400d00014244440c0c80c04021155015024400400840400c0300000b03140b402604500c90040901c40c0c030743d094241c001c3d0005020040c0036a420040b51501e828204003800702807407002c1c080c1c00b401409186200003c812580060010307180e10001955940d01210720100702e40002d000d6018019020005941c20f0011419070f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 435229442 1250 435228192 435228197
    0x50c070e01032d0b0103120e10050408070b09030604081606060801050712020901020a0206160b0a050406200a0507150e0a06060609030203120c011d010c0f03020301121b090c 76
    0x20302400a10400b150a4108400c0d41c030107200d03e90b4407002031109240c050549600c801c1005060301440c00546521001d8060076074010541e1040403000d0b6408030242040780d040c0301c101c0d0700c46a96440910304a12500c2c1c1c035560150403440000303000c5915031006259030a003032030083d0300074a0345858a0044542c1900714090701d946400c01d00690640c0b10a84032041015840114501410007002035601c0510880081c010600441d4081031043d00c03840305040c281e0017494050841ca8007041400c000c01d021542156403a103000f2804600303d4196218803940a000b0584920b42070300504d083d9029042102d0807550900300f4124041c0311081c90248039000d00788000140311002042c42c0800c103640c06608172a041040e007100c2000540e03400a40030602241820609641e404490318203400342660b1201e02e014529068090340f801c850541c04480502c910b81c4d0b8003010740c240250218103912080c458550840c81d042000b202180000c0300c0c40da5801ea01141c07050800350346140c43c2d41034a0104079201c01 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 435230692 1250 435229442 435229463
    0x61d070609090b0909060403030504170d060512010638040e0402091f03021e0a1706091902011206090c03060e01050301090807080a031103010906080f010615050c070e0103 75
    0x20120b103500a602e20600202c40d804c0a074504451900c0c2d86142c0104007038101915900840c081c400300000c2000714602401d0a60fa40b41040103600010f08500e2060500450b406040f02018203418420202500c0b42e2840c031000d111840d040450101c0001c075488041e40104584654185100030f000703000a000b610b1036075016180c43c0c0104089490010b0841440c00e03610881b02c10002c030801080c00540740d04075070880504e0348031005e80752140b00061007240c000c540c071000071980c10031202a2816080011045619031350f11348221644446034520803d5403035003074403201030040d03001e01141440c005022800182c070310b40d140446000d40c0d25404003100881c1d0f50f00014080b050f014000103015080c180c1c0280701000d22503680200500c0381c8140500419808208200c04074440c1d0001012130404079240d603180e50310b40001c400100700c203208080e018450040e05094018040c01000110303440c40c0740790280c604500300151559072000752164650b02414401040c045070070810540070354004d940c16413 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 435231942 1250 435230692 435230699
    0xf150301050f0708160806101404080f060a0e0a0b0a09060c0f0311040308030a0b030a0501021801030518060a0c0908250b0319020906040e0406050601081302010c061d070609 76
    0x1091260040d211a105c0284840080c2010741c101c0c04058001106941c0810b402406407403c444a00710112505081c0e40005000034507180001041280c1c880850140c40090702c98010701011a00d45008550075a001800d241c000724592000240d13000c0c20030000816411a640c0e2145c00f10340707000d814500418540e4980d52100c545c14400c40c00e1307050801e501c044c50035055460b03c0740640001407180c0c544079207a40141c48951428003c1c0f1901d40e5004000b503456400f083d040300c20105400040c036001170b1514000892861445681810b00688440540419200d030b8094001900300748860345c0030322174800c42c00500c9000801c0065013038107003c0680b1034140d07282152182241401e40c41045400d000f402400021410070300309201e2200b0f51800181d5449901c00400d659005661043c0307010a058800c0000f44540c680020307114034026a240a266a80c15400d007800070440e60300640003c03240f03400301c00001c60f507a00200d800e284104500c1c50303450016842c24a8210301d6009040014030054040 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 435233192 1250 435231942 435231947
    0x1804050703110d1502090604030210050301091a06030718050d0305270102070b070203100603080d0c02030c0c0603040f0f030207060924030903090b1803060a0b090f150301050f07 78
    0x303414204116010740c0a403125884e80c04a520f001e0706213101c81d0303500185101050340c3d41022070b17001f554040c001601c801021080504281c00905c0f070f200f105070030482030361050b8071403460007107110340003e1280f0b0860300e071101c0480c1c3c240010014900da440c0d0880012a16984440086503418400c3e078640b961105c00416120b58003106494604d0000903001030310a01e61380105d10b10302034a48000101d5115192800000d20300b10125440c0c2144a24082021050084180050010440d608001d2201c0031b101c940880e0340c3d2250090400c06500000481802e9240820055070854000e5080c2c000c076101d10340701d12082c00f44403603088001d80d2140030101b000300e8000360707010002c09410a80c401901c00010000c200103403c0703000c101c20181e8681100d010180600e82c004080c0c10b0395007031152104030400a98814243c051007181c841d00c83e00300065030340601c80c004d0001304d100240071544103403110b42d00c10380081000382200c10030030085000d07860b49440901c13602d40300e105141100e015908110401 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 435234442 1250 435233192 435233213
    0xe04090c2309010302030c15130902031618050616080c0c030609011103191d030a270e041a040803010e0c03060114250b010303030b0604140f1804050703 67
    0x400d070042d80400d0041016a801050105401c0419604920005551030314211503215514443c3c50b45000c1c0100455107082940c007a51141d15208910794040d046071400740c840c4c040c19080d428840110a03410710250074814003034908402d9032003080f9440e030741c1c03a41c8500240d000080036900c07591044104540502e010000c841c0c011088000810080031448006c40031448010911224810004441c00d1040300030b40c000010710500748480c4464002c1d0040941d26507001500100000e041ca544039a0340420f5251150000964102611070480c980b031410704030700c00000e00980c0e40903600c60000091640c4112024461031040c0e540b01da407503040120b4034801001c0500074204500c2c050041000c680d820200c02d40700c2d090003a424a80303c030184031815080c411041c44007002010500c481d1800c000301c0050352410789119403014018404200d0038803416000d03520070440070b001015120611401c00c8150070b0f20180d0050601140150440c504100031308082c0d8048030341c3d0f8000c038010810300022141 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 435235692 1250 435234442 435234509
    0x90408071e05150705041e05040518060105040b04020f040e0a110906160c1a0c01050105090c0f0c102406081006030e0703050d121808030103030e04090c 67
    0x34a01a400029180e8941d43c10111001c1200500030602080c04c1a01442c251070041c428003108420403480000c0c081d03c080d8003481403c0c0150306150206200d103810070f00e41c845a0205a005098580c81c020070030001c3c0440c030a0341c0740c00a50070440f8000b25007042d0004c1010b800c07414601020360601d00c540c0700480c3d843d00080004400103100b01051035949604450700070b29207403105801c0e68040c0c01d10000241c440d500108100d00480032038401d0090120183c01d22001d41c174006c000980c1d8034020b00c500c1000c2100e4107142c00b41c00700b00031000c41e9001c0d406440700590040480b81d01d0b0000f500100111b5014929030400c07908840b990088140500c20054013802d010300d440c42250030400c1e44c03080052828091503003815110180c2c000309800401c520300085030010116120900c0743c040140c030004510300101401030401c00400344001e01d19260a510552010a59142d680707913403000c50360b0944907a1042e6100b511000300c00c02250f40004024080c00000804162182028254036200400c611 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 435236942 1250 435235692 435235733
    0x30a0603231011030612121605070906030b010e07140a090e06010e0114090f210708031e030901180b0a060608010810020f0d020c0106061b0c180b09040807 68
    0x1410200034070400f00980703401c00c0007070f1100741d0501120f446282c140306105903e0070660f00080b034a041205290003281c0706250055041e1000c031740c8c44440350000c4c2c90702e9002c0500a80c11003c0100b20030b940fa81c200a5000b8181d240c441d00f080306c0c2e000c082d09503a10002400000540d070100c20f01c800a40d0306803250300581c0908201c00e1842502001920b0890349500303405d000c5a020648400340d4031045044480e030380004003010080584034200f020b195540d484210058402ca403008601601e00000700c030b50352203070081010810a0f0350108900c0c0b5600041c0240c00c9952280e594207903000003110302c0c400d40740c81200132050300e10f810b03c2e5100c100c802582c00b0004014000b40100145000030a08681c00703c00e08101590b500200d0750f0415982c40b40ea0300a0710260702c0054807502c400e00661081c0c041d600d05d035407141409010480105008c14032a000640b4020202100b04000704a10705221288282c0400124048100348005580303840211420f035040c20000545204000a0345603c0381143c0421 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 435238192 1250 435236942 435236951
    0x30b070801031a1005040e010b0316030c0e04030c0b0714031303030509070617090a08040b090405161706010e0303040e160302130608060f040912020d020d0f05030a06032310 76
    0x10110302c081c421605c0790354010355540e1110846540203400019240300094110b5040700460280028188058803080da6070441408000c9440351000d01e425014540641e0b03210126103181e01c4842070070a0150005091080c2402030366441e0140c040507500c0303100d62991000c011040c909020301540c0c002892102075030082002489541d811080305400b05011060303c2d20541d40c4e1024151078944681c0e000303040d11401140001c2d41000c4200104500d02090341c0a11003616070f03c507280400302d071030602c50021034011541003055044141d1140c0c2e000c44145801008018204c0c04a0300350751054000300103040844041009082c195190400e10b003039035180841c64100040886848100e4038050030707003001f003004041145030b601c2c0c1c0075601000100070820070101380145810526030421946002c0035008002c404103a49002043c0400c144050792580740c0724408400b01110960302c000c01070100d031030743e514011001c6040358500020000482e4401446801a4445546044203c4542090b440d042 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 435239442 1250 435238192 435238201
    0x20d0c02062514070501020d0203180c010f141c0f0b040e2b0302040f0b03010303080609010f061211180a090203040c051507051b0a090b0901060c0804030b070801031a 73
    0x1070711110415098980440e1607180c0352400502a02c940701c1b20100c234600200a1103401104080e0300884a10f14500308e4001c0707980c07031005603052042e4085042c0402c40a6480003841684040203203020b4201c00040c2370700043d0549a01c0407900c041c6042d80c2d42654443d016405802d080c814004010386841c01004000048070202c009125025008031038050300715101444180aa0181c401a019031101038131000c0d2030b0031011180c0d030000d110a03000602001302103041420b04ea403542e03058444000b101c80c4024100030341515410000103030720300e903660348004001d21164100050b1103000e0740c0b0032000c12003142c11003c0200466850308101c01c201d10410a00001845540c100c50482d45d00382c1d030719076038000a289100c5150084a002911600a81e000210000c1141716000b14640c02200c0100c165034a80c0900c008840d41a45070301d8008203030a005200f4640255200e0074440c4c49441110700e4551030365600080c00384150b6612b00403505d000c00501c2045038100a4240c01d07240b178805140a80b41 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 435240692 1250 435239442 435239447
    0x3010c09050f061608030103030c1502092809060801060f1e050d1430070f1112030f040608160f0c0302120f03090c032e020d0c020625 59
    0x40e603540f44103160000c3e43e0b800b0340c064000c401080ca40c00c0a005500d0350707902d0902401204040b9405ca8918402c0212854498403074800d8170741c00e042c0500304004031a0b24181000b80300301520620880d881e04041e00041c078070150702424015040c07800001c181903207000c50103255800c40e07802c000307a0b00d00346040075003e4601c0090307084100d0300100c8440c101801542044660040d0582c22402c080c02059105c501e440e04400d440c42503100b154207109080c030901a0018054000c10b04000c108804c00c01240e4046a880d500050242c00010315100700e1041042d00f1924650060b50b41c1441c8a101003010070a15400045107580641c06401d00c8865011540004100c2100000c42805001030060b078a002d2500c02c118000041c0f1b04201000c1d5204143c98602c0f80d0364008030340107991442400303c08001d81c10042800401e00300401d03010010241030481000406d080501d900300e05550902072850b2041160007204144a0343d50068070260030320746440906050002e0070302e210100003c0e015000c00390b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 435241942 1250 435240692 435240709
    0xe07050112050c16051605030d0c08030612011404050607050301030c0902030a0e0d09081204060807050f070501090b151f030905030403120806030f1207030516020d0b0603010c0905 79
    0x1114060009501c0e5109035840401c1d00545160044284004d103542040000020380643e00c07410741d4440c004415618010140c0e80c0c400d0022200000b0070744119017000030140e030702442d0418001420002c015080030a1542110380c440c4c039440c201c850440c00d1100f407207400d0158581011140c541340d451503065480e400e8030b22856110301d040b450750000c0000d072480000e620405e0b002101c14103440b0364002d5848000d1000c01507005038503a5010304500c1d840440003400883e41154402d45030800242c0d210350f0251101d41205c0e00c80e5019440400811002900a11622084a1103040100c0032030810840b1040c1011114615500801400300c2c0c0c000400e01c54035401040608519011071461100c0c0f402e1400c60140d82e02c0107050400003000080d0240e00048070500c00d8000b03808881c000302080010941d5041da440803500806000c10100300480c0c4a0001400301555007001c0b9542192283c2c0807132029040d0420039544035803110180441442c0c02e008019901d101890614034845c00c2400081c00075 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 435243192 1250 435241942 435241967
    0xa120f09050906040207140c040e0a0b060108180604030206101d0a02031909050c0f100912021809060103061104050603190b0d110a1a2a07090902040e070501 69
    0x35802c074400900e1560f10742e0100e42e0801d60205c0c800d18a010704d484606e965004908005d44298202410780b50700c40c4000440f03400e40798004481a41c0368171030400645e4241005441300100030018591101081c0c810132285011700d02ca54003e00003881c02d81c40e5100180c869802002880708642488910141c06031000741c1c02441d5114016a2911007900002c065422081100309007400c20300a00103210010801c214040740075290100c20040c44402c100c141c0601014060205004920600103e501d1401c0882034074405015a02000c0c25034128484089044600405c154041801841000070b5400740b885030900700f43c80d003420181000001099030100406a010229a17001c110800c02042d0b0000216a40e020b4840551103025092030184c401140f011300380102c2c01c3c04400035200d480000301c40d00d0280c80c881000c0c200a80d4290017140280c031400c021041e40010f900805250200b401400d0003400d81070000201c14140d8414032058404004040450780c121580400050340c00c54072148c0310 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 435244442 1250 435243192 435243199
    0x270102150c031503160e0a0c03020c0a0611480d0509060409150e160f03020a0e03070b0927040210030f060605030603060a0e0c1c080c0a120f0905 64
    0x11007041c00030a180a580d04000c517000884030074001610125003040034000c1c0b2114105100101707106a00341c069115860a003d002e501060590b00440c040d5404001c03400c030a44000c0703244c6105102c0812004804400328004560140311460a0402c4460100820818180c0503171003907030441c04203134646a00100050a0103030019086481d40e4039041260060418a1070411040b84550002990b05509000d961382ca858104007044159100b01c0c40c00d03507662041d40c0c030b0300980400454110065044440c00d4401d1280b0109404050764040c420b10001c0c119a00b40a91980445000c000b100a0302c003446006001c0794501480303000041501e4ac650090701941d0404842209a10440081c0015260f41c8100c524000d400709029501c800190301910084040354200d80320750022000719460742c0100c1085a0140c1956000750034510b2a000700d0b440c4820030450300202544411200303900c901030008068205c40380e90b500f00720403500c1c4c040305500c40c0e00d8800428015030340080c1011311240140c610 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 435245692 1250 435244442 435244471
    0xb070c060e010c0b1f08010603081902010e07060e1c03030c1205060d08030907030b0c040f060810062304030503070204141303031a1c020f040207080405100203270102150c03 76
    0x884061700c04550006100e01002040040d80e00d00382040d540e00074441f002c490704e600854000000c2d10500070180d10004180103091701c280b5004007650f8160088510b02e8100042c81c241045844083c0940c401c0305001c1d4034003164610101c01c1c024415180d14005654007442d14050040b03c2c4c030b801c0d01c03072034a895211405039640d44a07156898a010000d5100a00c0548080d04110907102c2034030140c011070751103590b0ba20007640c4849042d00c3c00441190007801070520b00c0d4041100d0b03841002c4c100c14050700032150304a4000803206143d0342c0c0d44590019101a4000100c21045003000d101d03010448060031001d01503801c1c000b40e00c1040f8510844013034101612103960a030b5688050000820310b0000808080c4031a1280c00e50040980c005402680b00d1508038041c24203505013030007110700d01c80d84114411710b041e0030401000103c1c0142100e8008520050003456402e4080b250340b51226141240144801201007000a19190010390240b000052510622146481e01d8069a402040440c020070 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 435246942 1250 435245692 435245731
    0x40902130b130204030f0b061804030201090c05090702060609060f06040320090f011203030f0c0c031e120906020f0f1803030f030414010902210601090626070b070c060e010c0b 77
    0x80b2780005024005019030000b200740000c05405502900c280743c410401c200b0440c2d034034010081d20500c11544200035070440e200062880c81c0100350340e580b0130001407001c5606550b010102d10039420039042112134148120146507a0002c24007103505004e41154010301d0b51401c3c85880e24803a1043c4203031200ca40705800c4440425020b5081204100c042c050100411004404010071090125500354041401400000c240344281e1102055000007902e824580105585c000c0008060f0076006644050f401e00090000c0d018240050038110606016540c45240401403080d480d100d403617034103110360310800c40002c0103d6444180c0380e10a8020351000707900c2c1400c81c0090f014040006000358000c0d030343c03003901c040c50036035154071240a54000c0454510f80c1e29492210100c0d40315004003009141c0107016035044003044000d03861003440d65025204407560303031806410103811200c1c085801030503681043c401150f004c4a4181100340910300041d81e070300d554840c401d520002a11449c200d444c1c0c8412007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 435248192 1250 435246942 435246949
    0x2806020403020616060f050124180605070311060403080c0705100504030201020a02190209310602040611010b1807051204080c120415030b040902130b130204030f0b06 73
    0x5400071500500000da4800400c01c4030307503c054085500b107640038603160030104011002c0c0304090580d4075081013401203000030014100846c4d01500e1003810401100300e1095084c2d0880340741f000629083c0c550301d45641b00c515014081c81902d038042c04281d40030004000100382d000d420f861f0880001e10380941e0310500c0342440b604100c000d1f00e0300b065990806041c030040641c15802080030709404d42c2a101d00d00c070854207200d9001e400d040301039804000c80d008600e40c0c030003010b401c2c40e510a00d41403070801400c0000d0b40003a03a004131582901d050381d020400300141900710082107040c1c42404001c1003100d05003000901008900303000c504101c4030860002d400240100300f1600344075a5401c41c2c491501c0c00f8071740308a40d644030420490390b90140002601c000b030461004c0d00c050300d032a2040203007020a2050101c0040c0003221489912070703104e0740c400016171116500300a4000300310380c0204110901c24103000c12500c141c4415800184104420030200700c2003404042c403030b54410f103003c2c010703207440000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 435249442 1250 435248192 435248197
    0xd0207150e10021e010204050603040b09010905160806010b091f0203040b1b12091003090203011803180b030601050405190e090f0607020a0b04060b1201020d1409280602 74
    0x4032070304a0750080040c0e556540004d0b034950f5900030120600f586410421116090740a94484c40381c002d88240b010400080003140e21790ba0080d03242000054444041d00d61915101080481d084204a1b41c801400407140601180e400b4084000d066864000c0d250040b4150002c2000041d080c0040310302c41c00c80d42031080c403c5400503d0070400a64030f4840e4010160f80c02460814505640d118801881e0100c02550081c3c1d9040c010080c00700b00c0321480daa40a5001c1e1416040c200e13819561401c4004141c0559201e00c00068000da503000c18945c0e00590350112115941c015600e000300600400c00030342e0b40401142c00f9a0425580c1700e2080450000040e0203110507003150b05140030740001c0090f102000181004620f00b0380003284d119469010050f6154145002c0c00b4103551031340b03030028000c520644c00400d0589405085030310350358498101c01d400ca802501c15212034548450308031404080881425410131581000f514500400483c05054205400304584006d82064856018090107505 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 435250692 1250 435249442 435249467
    0x270a1707030c080304050a080604032c03030a03050f070c15110405060a0507030f050f0f1605010507110d0e0306070f0207090f0c080a020c0a02010509030a02030313170d020715 77
    0x65401200e440b0f055040d1650001c0c0142406030184c00350004260703200003190b80c0a10f4141c6c0311940c0c2c000090409891010124900c0203882e202591421480e4030304000410b00700c00103590004441c14441508074003008d01030540410440035043d400c0204070140141034010003c0800041c0c88000091f160781c440c000c1c2e601203644500042030070041c01e41c02c03a00034000039200c0d0380c1e004003514070740070207456900942c8600c2ca060441070000c41d41b85070101c002410180c1c1109001c1d81e00d04290780c0c445096500c101c0300140060100d40e20040c960fa000c0100086140450400c000e00c42d040d030300426070b00c1e04010803120030086046070154445000b070000c40040c0c0304000e000d016070598016100c002c0e19400c4c0340e0100144402d000100000624800d507a803003240c410123440140d080e600116903581100e100c0f1645802034410080040c0d40410007024654003d841024400c0e107441d03c03d04103050403151600c03043d001050100740b50307540802c0c00415034988940108890946c9030781124915074422 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 435251798 1106 435250692 435250703
    0xb0c04140d0c0b0a090e070f17060a17060103050d08070c140118060506030105010602011104171501030803180d05040501210203010308270a170703 65
    0x1800760401c18040c446404078251507542e1600d06500108010307000c034640c00707010081652440d007401d030300c03e0041c28003403900c18290002402d03000001c8070340c400307200314040060b280f03680e007852070b2010307015100d038030748050301c0e503183c01070b901c0b0020302043d110f03807242c420344000540c410480e440c480d805030b5840f421070486507565049242c02e41c1c10011110b54a900b504001d40081c108240d28050240c0408915170070b20f10140f40c01c49406170084000c59050004510780900170400320760880c0c5413907070010383d4014541039440c10440030032070161040c00400000018800c450000c2c5004215400e5110300003001c0c05800c90b42d5035104400c2d03901180e401d003c20000c0d51301078003c014100a10101c404a815013041c5006c1c201d0380260011240250085a01d009400f8050050410314400c45401e07800340840e800026100f01141c8100244401c80c800407003040081805003500540d0b020303 = true := by decide +kernel

theorem cover : BRFrame.Cov 435071942 435251798 := by
  have h0 := BRFrame.cov_init 435071942
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435071942 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 435071942 ≤ n) (h2 : n < 435251798) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
