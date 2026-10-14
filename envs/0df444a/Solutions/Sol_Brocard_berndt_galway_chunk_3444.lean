-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3444
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:40:46.201377+00:00
-- url     : https://prove2.me/submissions/25d5b454-8288-4462-a987-86cea983e929

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 619244604 ≤ n < 619424460 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 619245854 1250 619244604 619244609
    0x90c0e0f0403050a02150108070816060206060607240b0f0102010c020c090601180609031b031520070507180b03030409050606270111010c0212160b0906090c0a 70
    0x341500303015195a54100c034182e0245400404512031510049024200c10440f01d008102c804000c0004521304041e490074141641c1c4505921038614104200ca20b40218529520004c02c540d182d58502052400d03400411410710180c150895501090380c01c150140e110b102074000071540030101c982480012400c0e500c5200528005812482c0f441603942061000b60b87c00c01414105808507074a0340000f042586490f81c404000201c500c0020010701269081100301c200c0c00c014801c1c881411501ca554041c0e16051002800c250307503030402c00c091413100701c85520f880b4101444582e90040c505095076155514082da4036070a074500d106000000d803900c01c0b15031260b409000313075042074581071b0110001c1030014401074000e0000c000388421603005d20151580c0d6910706641d910040c4002c00010803103c2040f1052031242c2c5480180d5000726000100180701c2001c081c0c1e0240e890940000440290b089500006c029610880074002e0b10341300032503514421400070084440c10400351003000780c0d800152 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 619247104 1250 619245854 619245871
    0x170a171323040218100f0e09060d0f03020705100905011b031e030f0f0203010303170601090b0913061518030209040b060103020903071e09202a01090c0e 67
    0x40200d420500b0650050103403c107000b800b15103111400001310300040d12001600000410700201d103000b054000410b00095002618500f4142c606900031450709c000d41c01010740b80d60307800180641058801c010442c06010081c104100c2c0c2095504003a0040c1c08038000c0d00c0c041281c0b207030f4030321004c0b503a01c000441c074680503036841c000c4c190a558005441403045221604041e103a019102c050b50003402045118920203000507603a40c59820010010241c0b200340b0000c0704090b8091240f0f90f80e103c0100c0b41650401910a03aa0310b5848001075581c1d0204030307072441f115041600000c2c503952402c0400b209142a130311901c0702d6200100c1440701001c541d00000f940244c03101c0115003c5030303010b590158400c00c18100180340024850001e49820280d600500e00e14a844031041c100c82d6a401480d401421105000d0044440500d021106049009842540c001001c503504101403000034aa02d9181c03075424050609050314107103a800307400c01c49000da03420f2503030075000142408601740c1d071803048450307 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 619248354 1250 619247104 619247159
    0x11211306021207080c190f0b06031b0603060a080f01020a09051009060f0e19060207061d040b030703080d02040905010512060601030f020408010213090b0d020a170a1713 74
    0x391381d10b050090300101110ba10314400d00f900310448808001c131040c0c189010300c0e1880542d0703c0c1d515103010501001030a09019400010485009104c080030140c00b68404841c01c0351a0b075a800040780c403044241d40030311140c1c40703910120903000324194000d00c00560555902c11680da150b801f8000c08068084c5185c0018a03d01000c00440788900b540100b0140d031032901e0499082c01c0303070010740300308029107074000302500c030000c10008260100001070060550742031000915000400401400c00c516140174045e0740c403004500140c1d80d0030310409014503130004090317440b0a44103509a00a402c10300600074803a1501c00085100e05c1c1c10001d50101000040c0201015030300c1f8001100600540507041c44140c0e001e0201092050007070001c0c050140c103c80740b800480749000b549409644c41104114010302e00c14659502680301d00694a081d6411402020506d401580703146142c10004000a044d41c8080c28111501d1500400284000304411981580c0ca5844481e0054800441203052020460 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 619249604 1250 619248354 619248367
    0x20603010b0c0c041e060f0f050d0f12020a030e0a030206030a02180a06030f0510030b0c030925030b100e160302120a021c020703090501112113060212 66
    0x3071030340c02040440c241100303a07000c4418601c00304e400c1d03038643c50310f50807a00e8102000c001503500510466006100c0150180c80c490716025585c00c4040f0503004081c01914001c0340710b402c1c440d40c0900e0b0100580c0c0458458562501e0142c0291145e480d980304400081c010302041406150968100c070542e034008080610307640f10112644025070000311b950509807002c0500804998480003580018050754070089840071080e4006011903600500764035420324106d405002190021005c0d950200480301c1d900c1d0360f505d03884a01e920b01a000510440c0c55a003401c1c001d07003480540144403040b00d20075076540314591505070075400780602a004400d00f0742d454200040d4060f102d240402c91700c2100d410014641640400e020800c41021500800d020b0f40000320b0200320b0071100029100c3300d03145002141010404c0d030b0000d0801d441e0744074450401c07061051030300c0046004d00061059225100f50748203900000c103030460a603008403c4c0b00c1502c4031001400900a800400c0071500c0e441c0c0301044625210 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 619250854 1250 619249604 619249619
    0x1202030607081510020102180d080a0e01050409020f09040e0105061e0a120606050a0605070c030308060a050301051510020a02030c0d0503130909050712020d0f050309030304030f0b06090402060301 86
    0x300040c480580ea4144000f0700007552600c500c11483d024450b4000759840625080c01e00f490000140024021112092081c000c41d44034400c2c1d4005131468500784580340c4150004070340c203005a800007402248006512001e099030103006190f05c41050350240102c69074890384500700c803030032528182c0040142d800842c0802d84401101c814240040c44805d0040c1c494a82243d44000010106c5965070f9803441880381d03240c47c21015004004500d842c3d850890203550300017806185200040c00e0104080c046040c40e900c50400c4d2000e00400740c020481440c09a03400c8101d50041c2c01560b018604e1400e07410801440440da00c1415600540200141c5440a060005500040900780c7e0240428880c2c0880300158070f9202e002084413100101d0302445070304209003008400c0d8803816440782e607400080010b1721000d0181502e2508020040f80c01001c0342409420752040340c0070140d05002c0010007104202c0c0018a18035981e000c0d000c003603c260384440a001c0e103140d042d20060b40c068800d000400258 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 619252104 1250 619250854 619250867
    0x5071101120f0203090f070b04170c1302090411090f06070f0b04030c0c0b0a091203120e1506030106140d05031314041a090126070608010305071202030607 68
    0x10301d003001c0241201007080c012101c100c0b5108008540000500940103001c00c410802d0072008000f8120b0b0a2900044149510807407003410a880190b00c0203000e2401e00307108803a1180000340642d80350603110400e04000350300100c0181c0c41a494001018448140c080c25280900c001078550380c0010307092401c000c529000180200c41041010303002600240c6080d03002d90141d44603482d0a07421140e240303000d030070300c80d62504411201d48045c0541e080c0760703610841c3d030011100d900134800407010450030100c03491051740c207040c0050790500c0c1c004941c00b03c000600341d4420040004c404880d0300c900c800c0500b0b0301c190b0300c100e0760398801c44a00303c00a450400ca00302c3c0b007544030b402120b2524403810300617184814560310070384203034900100e07442c55030a1600841855039080c40410500c1c00041e0f00062035004103002c4c00c0c0b421040c0351007411740828001d12811301000c101040700c86150380c84c4c41c01800c15000340021142030291050008000c01010300f1842e81d42d40c0207001e80010350f5040c004a594 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 619253354 1250 619252104 619252133
    0x10303121a240f0c010203010e0c16030f18033e0f0a0e07020a12020607022535120a05030a021b010504231f140702071806060507 57
    0x40c03082c2007100320104202800105142903040d800582c803589002109011071000402d440038480040000915032480041d04480c82a4181485090101c1c455030131200740036501810010b150f9552008030074455046420048005c101b003507403042c010740c50300d5442170440209031148881102c03180042a03180c04003400c00c46410140c0b1000506035030711210410803106032146e2002d80c01c4078000e04148001c400205818580301d000a1100d401c0c402802555060107042226444900c3e140a003034444045004a005008010a609540c0910818091310004041d10722140c41c50540c3e0030303203490001240291007000da510b046414004031704002d89866000400300039050313908109004041d4064581180c81d01c2c8600000225880d00380380c42543d07580c0d10740307404d0300d0030041151001c00d01070300003409203407a0100b41d0400340314050038442c440903001c42d601b8405039102d03280130000b0301039000840741d044698a00030070000c00b00001c020b5040356420300454000610411240010170562001e2812 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 619254604 1250 619253354 619253419
    0x70306180201141b07060305070201200d05070e0d03020c09010f030c0b03060315040609060e070503100207020a0f17151302060c07030624050618091509010303121a 72
    0x4a90701d0744e0400c074182905034121401090b602e100b40034032a54244504c00d20a01c003141180700050080d034041e8441d010b0444004d18035074585000070030b00b6106c0c010b2041c4600c8064100340c0c0740403807490007039214900c00749036070701034401e8030700006042c210b1004007000c90b5004824001060b0030020089010303807000f02040d4040c490002501000c4400f091007902c00e43c0075086c000750303a50130385c84e1032010758500f01c603900e4282e0301600c4207022550703000c103c5018800220100507914151440403600007201503205054103905510001044240d8140a424610071041507521642255204040d02581500ca05210450b0f207207600c4010308044000f031081c40001c40840758242e6036965804142c60a0b9a403240564148010031400d40b040b070500b280107008103c8010741803003904402d0101c0301c25200e03042c500c591840c40101d00d1003807090b0140d803000c1502601000180d0307100e043c064001c0c140d541c06040d8076868011450f0904501840d04400c40c00010801c19052100d000d509414002441d140503 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 619255854 1250 619254604 619254637
    0x20904030e06030703051609060207050609120102030a14070302120c0702212404080304020d08040801090b250e10050c070f03060501060516170906070507030618020114 74
    0x22582d0390b40c48055071207a102c99a000c80c1ca40b0703000042200c01c1d4011030741d82c0c0901c0006042404000e4000c2000c605507042601e0164075039907901d0010300e0603a09100c042285d9480001440f44403221074001c0781c20300d0600080000302e500d40c01d108504034419110280309080052002c41e258441c0c800060899500042c55200c41858000390381d09541da4040c10200240c4c0702c01851000ca00103408104503c40104410070403c0c50a611240041c1c8001080240720741c040804c03490030068480c0035500030b01110002000448103914104404100036900c03110f15a14080e880000d980e41035801ca001d140803a03440f20043d01910040c4481907101400800034402d003400050042e071810899103008021801490484920b1418828120340d01a0442420804104001d004c04924040109030722030f48281149190000048408900c0c000c2840859101d2400111402480000130b0804140d0f400703000304011802e4002d450386418800c5a200034040751040203100f02d61071211000e441220300d20710200c4d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 619257104 1250 619255854 619255877
    0xc030403061109120a031b0c1a07120509040b040501030206120c1b06180f06010311030a0b0c0c120a020d050322200312040302281214060c0702090403 66
    0xb0340b45204e10b190030300d4070364000780180e4107141c0d012000c5521480c80c03a641084810482d161400c020900c1d020344502d001c450a0151100715007481210266900000300007002d040a420081055200c004c4542c40786051142140e00c1e86450300c1030f581241d5004000a1618058654582040300000c0840350125018080304034508000300350343c00301c0410b5201502442c41c14482142c0001090103403a00990300a45c8290103c000c001440b40c190703074001c00e0783c0030041c20543c00285081b0341504020008240c8030140701c84c0c075024001a0502001c9a419a80500002408a9440d004d0f01c600500160320108000408902070740045070082d1010070074161500741c40392051120701207502c00300c440c08031400ca802c00b0f100a1010352050820202e0141a1500c0c190b0700d0003080d4091400003a10660385001c41410005111003d810b01981031036040d01380e070f070380d5040d140045242904280c60031031100c00340c0814640040340e40391003080b0504803e42411100c1d020300c003451030000c02c00c60074004290840c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 619258354 1250 619257104 619257109
    0xf1b060e030d06051e01080c0d020d2a0e0906040b040e06070e0a0e0411040f1811182e031e02100c0b0712020d02160210050c030403061109 61
    0x60020120409001c242c0038a000240041ca00c04443c5c02c0000507513180c80340e000c1e42c0e40b150086400c01e420b030304d44030384036400303010307210002e108251402040354079140051500c205036110400c2c1d6803001c2d0309038000c45c00800d40c041d1903115101c0d500580c40050000040d000c0d02d031580c01000c44140203040007680c020b1a4180038a800e40c15070b40d41c00810008903810240f0328010051401420440392903000d142407076922822494082103800c5d12554aa020303400008906070300c2000c5414098041141c268124140f04035621703044621207010702c9683d680c1d00001512844010700a003102c084464403518071a0710404020058907110702e0360510304000202103801d1500c1c0044e60005503566845120841c0b0411034090314a00011080c8020400030501143c50ba01316280d0000c81401c110102880e01525031000340b00c1c0c4140b208000d48041061208030340d88805a0038404e200b50350308044440a108227894902030122b80c100300b87d00401040c00018401d40050007600c0e1214582810444071000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 619259604 1250 619258354 619258357
    0x6030513051506191503020a110d08010305060a0e0307080f0f0a03020306040f270201030605030304061706010801080703060b011403090a0201091509062102030103050313060f1b060e03 81
    0xe00082c41600b4081c00f51074034008818080d030081c03d030075800e42ca910300510b50b42084094a908000d01d940840c289503c01c0c06580a5080c84060724280c81c660303804050b024101003002c2c00140d13083d218080006224030018411105003030070a100460618081ea601e07081e165000380018180e0b804140072203014011102c0203018103c19a440150b103d191110901040750840210b5092503030a00f0184181c0050320030095031500302d40001040010b88500040e806004a41e01a87d0140b00021700069010340c000c540326000c0840140c1c00742c0a8a4200046a11807030038040c0307040a422003801000044c5807540300740308409040c1402c1c48010840c070600c0003d80c03c110742094142c0c002c0840481190781c003150311400f0341442d01c005540c000002c1e8000341130302807034080e410501c01100040c60075682c43c40d0b00a0481e00c0945025941c96840e4030f0407a889402141c225112100c4020b8041003a5002c0c140c100c3c0340700c0d41944c0f4031100c4580a40c10b040c010409503015030f40c00740d5503203402c44030703450510 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 619260854 1250 619259604 619259623
    0x10b0d14100212150406140607020a21050f06040b06130b060703090512060106050d02160219080d0908030307140903010f021801170433330603051305 66
    0x10b030300950b41d1610540e5094011361142455118519004051100034211015559510400e587c0d640d00c0314030740e1000c91307064075035034001004851003903c2c0307400002d105064603c1d4003842031054500d1001800c1c1d00715681d0304140d600902100800c00028041d090492480c14046c5044a0100c0e288502c40c0c00701d2419408001c09400081102c54188603d00b01114048105142d6000a2010350714200005105000c0c4410040046400082040d014007000449102e0343c0d03002030030b01140c58203e03401000103000310710510440303000384005130381400d0184010704101d8510b2405035107903595442c412640141c001d004000011000d003d14407043d1424421488c045090300001a942c40840260348940d804d071310348082c1040003088003814000c030500f19540c0c005910141414049068905c1c2d00c0e000c0070382c0c02c1c9080034071207003031709071202d45415030070180080410000c9414504040701c1212044084000381ca02d07200f41800080000b0352080c0d1000d60b000e2249a100c00c549c9802e43c1c0c9a41c01c041212 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 619262104 1250 619260854 619260877
    0x70c0306050949050403170304020906030604110d0c080f16050303091c0c23040605041b08060334080d1704032a05010e010b0d141002 59
    0x480d00e4000800d40b41448080100101e1109800601505030f95010808101049010310200300c0c0e070001400354003a9005980d00c070141100d08803d180d604645034104540c107a10070721141003c590719040c04148a405942c1140021016000079000c1c80303c8907000800c01c591056104c01c00081088080c000152601c103498040c0c814070420b004031000c10102ea801c40351003078208122000ca284c4d151800410b664800130020b04041c0d82d60300b040030360440b0a6104800b0790100780071004980b850103e03021005002214200216034881c014802103907140309604c4a5015502d00c00b440c0c59006040403540048002c080b1030f42850b00d2450f00c00b107021001c1c0d41105c00c3e8a0300f10316941909101c04042e010f0040074004142c0000b60110042c40b094141c50000c4a6103100808101458414034084414894903650a031160040c1c500c1c0c07406410300c000d41640c582d481e004413404586418080e090110314002d000746c04030009900c65018869100629018911550303000e2050000603001921010414 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 619263354 1250 619262104 619262113
    0x100e0307050705010f090302151605070806010e130b06041b050d18030f050f090301020712030513021f120903020604020a08030a050415120f0b040e06010317070c03060509 75
    0x380d2a0062500000e80c0209060014901c0b0503c5100d034405449070480380c048550441100d50350070751040520800004000c6020320002ea9005c0c0840007980c141241c2c01e140c119003450381d80310710190400c6000d5804049054400f00000701084e9003102c00c64000340c00900000d05c010b16000c40215100c0c8200400010801c00309070301004800622400e640c5c440400e440e2010b144807540e000b800e140610386000280007002c512902d070440c0c408252030b000e0340050003c541c1d0f090076041c0040b51100318244680028100000948882c1ca880840e600c40c6901401890440c04024002a55549030b034900d0b004005071101c04500711803c501401c0c40f20360007600500b440d800c00b80148001d02d10190841800c60b441000410002c9a0100454040f1494010101641005040111480350b0350040e03404205062081415070016141c1c0003c140803000c4600304110b031800c1c00c6407621801c0902c40901207148008905020300061401808024800d42d0b40c0b01d006912550f070b0104803803003278585c0c20b4039510 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 619264604 1250 619263354 619263367
    0x219060b03011418010f0218060a0215070504150302193b0108061906200a060f15050603040f0f0c030c090b010503090c0f0a08010e0a060b010c0b0109020309100e03 72
    0xc1c440c180c6c420419040035071911074040140e0400c0640684003034010f1600280c5c0780b25a5109010703003041c043c200d0034180802e00380014001d01903045402298400070726400140340700da01034801c58900c04a01d9a08007402481c10909613180c5c4042c5140c140400d090040360300b0000c0094101c03401007021300c82c0c01740d080414140010261280100342c24001c601032004500e24512441c0d00341d080302c0c62031070000d100010b4440e140d580040101040c92081c400e0142d041c040000e00d4001a1030070301f09a200300002e007405141e0b910000f080313124460b000b8004001080206011998040340280125001601c1104594480f000354005920588011580010a004104007030184204442c003d10301a802e6083c000201d80d2070b450040781040c840d609050088180340c07a686096001810390200801014801207035540c0c440115150403a4400d240c030214000f158007031706078102442e40040b5485003580c05c048006000b54005462000d040c4030310103001c12803810900a203500348846078051511000c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 619265854 1250 619264604 619264651
    0x12110705010c080601120e0304030b07020303090d090b0a0e03010b0d0c030308060a0e01180f0c03090b011203020607080709030206070c052409040f270507060219060b030114 76
    0x4100c040d00c1010002c800f814850240e910070b140d040070714618940001d0105c0e41c800307020720350702c15a800142412580d42c10030020540200245124482d40d0b42602c420b000303c540704554012440c080c00704d180c4d40a01c0211081c0c0d00c940e042d56413942c8080c000252080c00c010000c5c14210304441c045a408841c0c00d000d104041d4040d00b130940045041c0e07107690055081c10310301103802205024600b072801d150315002404640f15000907000c85150a010400f00d4061080140907100d0000181d41c6483c1400c00001c0f20344202c034400a5041d050381c080c3c1386503101d28200321440e1001134140f10402c0355000000c001360307640ca070081180311310801051101c54070300428010b920300d0901c03202c0030405110340c0c0c25892200000445a000c3c0f0704490000e411180c0d0a65100102000000e04003141414086801e80504590000c01c1c40c9001c1e0301103481e00d03642c4e903004985d904260120400107080580c0d100d000035525411026042400400120328641c0001200a01803004c0b40c081903490181c120041ca9903 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 619267104 1250 619265854 619265861
    0x3140c16030b190203060d06090609020a140f03120a11100608010623090105010e060f1231080304020a24030e0a05151003080403060b2713031211070501 67
    0x1214000c42542035107401c030300051f60140700c6400503203a913407101c00c8401009003542c42a91407581c003d1950104a840b24100d485816511200754000d202880071400145400110440340140085245181c2101224110307280c0c03205005003d234601c01d1301929201d402d0a402078a001d00740000c0009002440d11300305000f203011030012200185109500e080700c980f83c000c5058103445081c28441c604c00c07003c0380852040e200d072200d0300c1c10300400402d000000101034400c681c044e10012881c00b82400d0703038003400c0c90400d00c41c9604440607007402004100140f000c07030103150b21600092100200702d507554054003106488a03210548607081c4c00c01240165018842d803041d8a08c4007004282e07140309a50f800d81c0e0b030006c2130000000f1100500000302c10401041c9914091940145030507101c0342d5900e4804007510407541d0f064030a29052034642500740a1003030b1490321641039100c64103103407a4000c1d54068000000010f0342000204080c0728003443c1c1038000d5900e1001842051b51b600c40071800c206084 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 619268354 1250 619267104 619267141
    0xc0303181005030108210f040905160e2d04050109090308010806010602070501030510050d050604210804060914010e0c130b0a03171e030a0f060303140c16030b 70
    0xb0701a0510044c8118400003c2040c0d075540483c444109000c002d001880141c000c510221034030b4400001c000c40c44000030340100b4020401c00340441c40c0314110351000c0d5044450415010340140300440c5402e4a0701a40b1003c2c0e6900f05484801024049030740301050036240240c2080303c0c001d884407040c0b410507503c104060300412140d8003500e040d50500100a448240c00d202d038904064450001c58495280c0c554140000c09004000c07224004951400c241c640c041110160303101411000c1000d0303803000c00c034181401c0035042e685224159031103a072a5401400040015195040c482c0039148420340240320740c1000c16103070300082001c00116003c00c00020a400780104015040801c3d201060322083d0407042903070382c803e42c0c254060942d400b00700000c1c0542d068001800a91010381104200520002c600403c120318003406010840d03e820030503200c003440f000b000114110000d001c2c2d50700c500080d04061040000341c446061182400418110f05504103950188006051010205006414a90 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 619269604 1250 619268354 619268357
    0x8220e180d02031621030e070b04030819030f29010c0f080a052502180f0a022209050f01060807020a020112020f0307030609150b1b0c03031810 63
    0x1424103100070000d44030302511a80c085412110160f80303003000780048220b00100100c0461109460703000c03400030044c2440ca071440342d040c050400045070301c000c024200e0b015030b0782103101ea80c60204482c041900030404009404200b580d00d02020405140b240500d010584070f10b92404420425801c48008110a043c1840e040c0045050034078001100843c0100c1c090b508102070548a500001d001d4460b0b00c100c040705100f03074074062603c2100c180c12100c100701b03e030300a0343d40c640380d8115400c00684440c400c5c1d525008215854000440f9150560014031151103080140d501709864441103071002000f5410101c44252030b4400c1000080b03480c041d1a0050015141006240c10400b070043c4d1903124140e0041d040044540c1e44900400154044600380050b40610996900d40701000400500743e90080c0b5001904060506516803001202001a0340c50a1910303442c0c02024254040444c2c02c1495001c928000c4881d00e141c942c1d0140301811000b210310485039202006201080b0040c0b107940c50400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 619270854 1250 619269604 619269613
    0x216061b0306031e303b03190501021804020f03191d03070210020111160606050301050f0f01060f05190903050717070902041208220e18 60
    0x8079102c84024500c514130542c104402909500389648085a5111000348400800c00c0c038a45c13000041c1844d5003290380c50740e207000100036100c1e01043d101e222504030a2084803440941501d2850f1203443c0100c59030300504480da249a558402c446401c1c801d03c00713540c1a50301190b000c480300480300000316200c030100d0b42140b0f072500020762145a400050100c4450610302a000341d01d0103907690200c10680c0340b03924403240c0581c80e400c072580d4940c0a0030040340a1441181c415040a005005080c0042e180960980c01e103c05038542c0052b401c80305a0540c0c4490702c50200040300d4800384501401a801544840300f01e00d081d460b04c006140060348102e08006000045104071980182aa10300c1000000b001010310b036140c80840d4001301c3c60300080c1c19405030050008850145501c6901c909a1103005d0b1094541d50b0b0000344224001d910402204050001c00a070000c3c0340303c03000305100040103000124000440d0b91100201180e5000328140c00d04200a000d840c5030700c00d210000c054034100052 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 619272104 1250 619270854 619270859
    0xc040f06050f0f031f020906030103150b01110d0c0203150f07021b030d0809010f0c031506090f06050a02160803070308010819061a030a0606050f0a030308010312030216061b0306 78
    0x70b50b070b0340c3c404449043c00080300f94134400c2c2c01461b804a92042c3c2004100c240ca0396120b00b00b103000c0700c240034035009c003091070b0880c080070315400343c1004405015810058007a0014000043e00c6d565101c0800f00d906000300050885c078071400d00e0003240148001304501c82f071882c103014042e00d0920002d400da44034040400c42c640143d0740026001071006010b16000580d5124031610b0760241500014441e5018101501003403480c0d81603008a011540c105030001009980e402c0c01d0310810090701614031400603103101404803900410040496000600c1181c0c0c0d1900b602c40080ca50720380540000b41d261b00005030810926a205001c64050070460780540802485241c54091101894000400d01a1205620903248807094103c8405400c00b4055031404031842c60504000e066030b000d214400d102d80a544006400c00b05404c80a481c0c0c1600d414079140d0031519150081110116032000b09a000c02000704182c1020000d1a81d20b0702c11000446c05101201c0303040100307031200c1c0f0300004040c54072404 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 619273354 1250 619272104 619272109
    0x60906050f0315040905010c0c0c05120604020409030e0915030111090609011d03030a0512070306150c0f020604080303070e031902120307020a0b0c0609060c0a0f020c040f06050f0f 79
    0x100e0360440f092801c2c8000a03400d1002003000380c808038102610f954078000540008035008a080c001442c414890031540589440c02c10050000d4254400b140390300800004005041c180d1280807854043e0030a8400e080b00c2d18001b603400c101c21903d2401c0f10f07860700400242400c017401502d05044450070030fa410004800b02141c1c05014205a0504011004001846050084114400c01c038000b6080c3c0707a445c9854030001e001c0d82d000146024000d214003000400841c481d20401c416501503200c11040da00c000c0c5401c403800a00c111003aaa09100d8246d0b200040c0d403010b0040c00200304079005103403a0b1a110502410400c1c416542c07038020340000c01901e220040c0341c4540e80e011075048400240851482205a1840c022410025041100a07402151f1640c03900090a441017041d001c4030380c10343d1056a501c1d11554241c072525003044080c000c00005a000f6504140c0c00046d0344100d4400c1ea03c8400050b01380e500341c1a004081310b0352081c0500c031504010b5241213001c082a2070010400d03085002 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 619274604 1250 619273354 619273357
    0x504031d040207030e240c0706020c0402030705030627070c120816050f09060c010207020909120d02030604090f0311071d16090305121305040b1503090c0316060906050f 74
    0x1030b244141d4014241340041c449140461007000850f00c0116187c4d070340403540d0b0390303940401e00403000948541100c01c880e41c0703482c1c001c44c0e10072480b5950b20740c116190441030054007006500c400141e0740300d2080007844034032030000b41031107a0102c0da40c039058128141810812085003415510800800c0800c220280e0b280b0350807004d0444440c1b404540e80d1900c030303c3d074415078018050f020398070420020f0030388010403054000c0c14180e4005c813941c49240d00c1c0d16940725660080854a1485c019040c80207295000c402e5015541c4000e0227400407542034a6a928014000388010040b0080384840b41841340c01c01007040014060300ca00701c550701012a0fa40a25502418014410b02c01440212641e000702c62103804d06034000c0d580f250460303100144051002c01150810109141c8207500d0110020b17041c5001d014070700c5980c0c2d01800c8100c0714a08004540c020380c0c4010720140ca02e12136141241c9c8103441c2004002e4400303640101c991800360424000800075075240d031100741005420310080000c0100d620 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 619275854 1250 619274604 619274627
    0x3010321021b010c0b090f01150f18091b08060c0906070807032006041a04080d09030302091905030c030a0210030e07050a06030b03060c0c0d0318060504031d04020703 73
    0x5241c2c0004100c058012100303003011003402401d080d10a024070580040005002c41d45101c00c50081c04440c07514100840718a159126000d58001d10301e03420049101c803041e0b9006a586000f9010401c0f69154496149030b2004641d10300740c80042800800100c0d00900c601500b020410791210710b000512000070302c00703024103d00503146803000030700d142c10540209108009400310038146c070b40c089402d00c0c0652300d8050031107054501092100804041840401c40c40384610b07401800c0c1800d089582c0394801c014440d80c0c204405141d400c01068006030780720940910000540e400440c2100d0510003418207018809032828000e9000442c0b142c0182d13140c460400010b80c0d0351400060140c070520780d0525180450340140d0b0060b811100101d4001e516801201d8680001d6040781d6442d156445145014803504000c4101a0843e0461480e9248070f034000d0b50303c50310000709215002c6101c1c5c075064200c0f8420b4500301c001c40d408074a0000c09404454050304103038000c40303003103083c00c68948000c0d0000c4250ba = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 619277104 1250 619275854 619275883
    0x16051e12010b15130603090c0b0c07050307090c03060e0f06090a0b0d060f0b030a0b1603060b0a02030301030b13020f06030613060e0601110604051009020105120c0301032102 76
    0x400c0c2400803100250710944180790014140c074507480111440407220360040c107a54404200c510f6001c18014002c0c042c042e1440d9004070405221071030105040030540040d2440320031802440d0b800211903804002c00f001800500000007516281c000c00501160001d5201c41c410309800000c001e5802c5d60403503000d60000d02502c01c000b0640e0b50714811001000c6040700301d68091107000c0124188680c690202c00e41d82c1080c0303010000c0001c44400c25070741d640c220760000c00c4082500000b48402d04441141c00404030300d424085512030301d03020003102e00c0c1c001c030280707000585c030110040081c414403a80f410b4110940846c1545528416000b08000c48400c2070407030301035113000020a410382c41e01020800301e00c042c00c004110302a201c40980b003400d10250742e401c2c00940344d81501206a8804200d080c0a20790210090100f00d42c0d46100b2400f6020103041a1b05000c2c05000d03841414216068285c03154107001c0740176980e0f604601d8030003800040f89031400c0c0040b15002d001180207400190a20386208030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 619278354 1250 619277104 619277119
    0x501020d0e13090212060f010e22141f0c0f1e0c020a0e1510050a09140d020904030302040e0a1a01031e061214060f152116051e 56
    0x101d00114200b0285c00c0b4903c5030910504041180c85105101e485041c1c07a688518040951200002d650643d07a050440f5410300c0e217245811000075880e04054082641c441c0b081c1c0e510790070700c1012142c5032246403004c01100e40d141d130340d4040700035402511902d01c0080380c1024809101310f158211a003958452002d018404100c103150103640d00e4461100051054510b1480349103444016081401042407030f40d0b00400304840104038403030040c0141c0d40810b02e40d6541092007440c2801000c1180c0c803603400940c00c82049001b020250708d0b1000319501c61070190301c0150b0344518042006030140c5004003004030407403419111420b815440c100703a0305074080900e03011070080309050448400c13001c444141206189400f000144490340a5125100e0501a65000407000c1400c0740154640c0c00c201c4448440a120b80000b501d003505000d58010f0244010f070000300456070140e140c075040030340c0c800350359590b0344104c19410a880c032050002025040503034541200f55140644911361282d501e1489118505 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 619279604 1250 619278354 619278371
    0x303050a023307031116062012010b120c030a0b0604140910261c090513200901020a0f0c05011803050a020105071103060c03010501020d0e13 62
    0x3080001c441c11902c1c90804006038200340c80c0000078036524542001200a200c0001120303a8042e2050318a00e8040c0d170b800c103141c07005007110140e840107900c1d42141c0b0750356141070900900360580300d0018014200300541d0b5491140041a41810605901069545e4010070081c07a0415400c201c03290007011228450b43c80b91980345001c1c01138104080c0f450340100d0042800101007003c4012a600b40000b6034000c1031988031180010707400e40c994052104005a40070388140c01d101171040c030501988222064516184029000036450f80d01c1001900000714418802e025510b080040c59840c0c01d140c150030803150400680302485099254010f180b0300d6004205010310364000e01c54203078119481644c42070000e203e403400c190390815500903030b40012142103008540210100058050341e8005005104116a0350300448140d031103d541128460344030003880780d1645080101a004035a51407100d502d80d81410002441d014065000d102003100d1030030b0241458441110418085068000c045100c00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 619280854 1250 619279604 619279607
    0x906010506070201050702030a051015052b02181e01081606111608011b0203070503040509070302070f05010501140103140606030703060305032d09100c060f0f050a0f05100303050a 79
    0x2704d42000191590281d50310038a08194130758041031072142484803403803600752900c0a004026800041d5203240e03200e0003030622005c828581c10354144501c0140085000c11300d406201c1a0f11000343d8920200c00c01002d13540c40440244070109001d046044010821040008180c1801c12458071824003030011315602c03404c040b00c090180d080c66652200c10b01c0402c69480304440d00134003d9501e03140e41e0810554000d0305003031002c800c540d03c8a400200441c145030070281004060326000d098102416030070044c00c000100c900d501d0f1040a0b0184000103280d40c9425890000c621450300398904041c90074022403254541c5102c01da030000800e0311003548943c2c0320740d020790082c6a10f800144c0144004154140d020580185100441d18101c800c443d801c02c2e90340102080d4054144019882031030300c000c9c110302510440c7c80d120a135001c0e140c041420000c58002a00329108410310101460b210000c110f00c030700040c014034412500d0038404200601e000c440c6098101c02600000b000c1000015030b0b082c195 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 619282104 1250 619280854 619280863
    0x1014180301021b07030b011e091a040c030903080a02040506040b070609020325120804050d15060b0a0e0906180406021318150503280506010f0509090601050607020105070203 76
    0x10782400f18041c40c4807042000340f40d4554484c40211880c6c1007290011444081d0000100301b4001c035000c1c0b802c0d103907003401c58074400b824401280464441201608a00d43da4417801102c0641d512606c00140103911403c008203000001005480500d00402042095444000c111021030f4003007681203446103000c0c03034840c0c0900080e0700c0c0694507128142c0e1000001c0743c03030405d8400400c1d04440c150307200d9030384482c14103201d83d0042000d8080501030000f040f850402d540c115000512806a8110041c0f00242c00d80c02c94009401080c160b1a0126a00401e039411919200740540d0445241c0c055207007003000102c4c42c08a401003000c03c01c000703001103000c000c4142c041d0303061440040a5242d016031642d98001700181c81c8004502038038100341780030b20b18184044800342a680007501401022286050040245508510111800e110b151b07084000c90303410b01840d4080d00360810500e040a141204010340c2c5031015080c81d0381900503000412140c1d440302c04460185d642824800d40b505181d00000382030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 619283354 1250 619282104 619282117
    0x30a0e0103090b010b09010809060c04051e1005130902091003091406040b061315060f053108070b070303110c0307030804140c03100f110f09101418030102 68
    0x43d0b00b030080021440c000e61302c0c0034042c41c081c2030703940d0f40b80740d5034141c10340d96100826103081d8000d15007013000b800a81410b50080f0602d264540300201654203540115002d040565108800030b240031416151382902c074010302000b04050441907041010540018668101c0300c0c1e10300040c03540d101501e00401010b044451880c002860540303256113881e0616842034001146c1941c400c5c25a0b0000302410202807140e071660709441e82c82a01218181002500c1d003152000c0d40d041406010b0022081a498035840202d04402892122114800369501c1081031016a0407010361900941c4003030001c68910419520307401e8062a02045c1c01514810304019846000c0c4050050b010000c0c84200349a001600940140e201c1c0d581180381880640310643c031103a64480060f071582200c0001c5650385559002105100f40c24040010300814403500401c440d449100040180319011594003041d107015a0b510b5041030081c00c1c840152480c1c00041801440740b003140e079000d64846031852480782c400754161500c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 619284604 1250 619283354 619283363
    0x7090b12060a0f110412020109050109210213060f03020a060f0f051305060a0f1707020a0b0402040b04060e0718060527090a020c10020901021203131712130302030a0e010309 76
    0x40e6140c0764a812403606c09040400c1c0d01140c00c1074070000d844d500c5486d0040444060840c40b1710104500c0309848142c0075071f484181d9020f0510901d00c1000d005501c40c030402013a2060b8881040342c6184148a03800c1c0c1e10364000c01c24020304883c00c0900b136400c103041d5003131140320345011903503442e80304000f08800030b982d04010342014021556840c92908003564080c400d0958445000808409480340c0e40c15a01316200001600042c0d8810002103c10504503003040c402400440c0306030821010800b155042c0d40a03e9642e08030034140300240d900450f0341e2a880f0080c442d0400460b080c281c01400070b1003078404000e0381c3c468200001c00c440d40b001c03804145c4100002c0602c8020b050556130b42020790401481000e080c080d50308682d002c01c250b1710807600f90050607005042c00241440c90b600103030b00010901034154140c9041c1e080012171040304000c3d90100f1175121031b00c800c01c410600c040801c000308120728070050181884042038000060342c200010520f4984201e080841c012400340025041c01130 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 619285854 1250 619284604 619284607
    0x10512060610050c070e0f09070513020714060703020909070f08010512030705010c020c1216061b06090f1a0403020a0209071b080403060b031605040b150c07090b12060a0f11 76
    0x101406d200d000e05024892103d9800969100c1c101125140d010510841d076001d1029038004207100c0341900074064450060110141c2c0109848019040810488880d80040c2c0e00040700c81c5145490034555403c19550301e461070800c940540050f10b8801c06004051140f05001504401d001c810011541c13066488802804003036042e82000e5a24100d9240c40b601c04d800544030000717842e400007154299503003015020024245440720594034280b402e01c0d1884003e5071041c44030040b41484c000c07400c59511411040c10303134a0240c20098038062010700c04130345200070306081c400401e50004640c81410380403141008252686002620008054501816200c0441c1c07035090034485d07010b003d40101c0b0701886043c44444404810503403034150b6461282d118107034003c0248218205540003c100074405043c100c1c600308141c4011105030402104202c10364007021060000d5003030b81c0105c420400c0207070f4030f00c0d14280f6014400c9444100040c6454a040e64640d000d8900c2c25064000139818a190103105 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 619287104 1250 619285854 619285859
    0xa031805072105030c0d0f020a031e0509060f031b04050907031104050a1215050f1603110d09060b120c0103051e16030c0912060c030b1309030305010512060610050c07 73
    0x2134031b800c0154061b0001c5005045403182c940d0011503c1c10b00070754565942c608007204201075000240b5030042850402c1803e01c0460350b0760329030078024040501c05002040d100d1400c100c1c83c50701441010240724841c4401e0000308155107a1b0083ca50700441d840c1000f04102c1814080d0302c1c2d180c003030790b888a507010700f503100c0025400035548140300956006030700c860504090242920203882d4155034036200440b1190010350148495001512a40c5041c5004680024004003440c0642c0000701c1c04c80505541d40e144404020044c0708060700b12205540d035032100060a01c0f00d5440304461582d05051607100ea001038214a40c0c0d80e09080e248851045100c164100344213035030481d4881141e00b001280c0341481c1050300310302500f01c1c401102d03401c3c010034200c05c04503a1a14017804440172130038241342d25211011016941d00e6900b0741c2030f00c00031900082c054641e040080a85406902503801032900391200d480216000c00c000f540b00109031105440c2c001015011070f0648150f4940e06a14040c01002 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 619288354 1250 619287104 619287127
    0x30c020609040b0a0b0409150f0b0a050c010f050126070501140903030a021c1106070c05100c03020a021b0a03020904051f020d05060913110418080a03180507210503 72
    0x141c0300f0381f00016010408060030f4101840003e8490080b00d5105620b294100640c0c034400006003e0500207151060074250105e808030700b0f4031100c00640c400152580010b102c0b52914841084280780203044000d1a222004000340c3c0300c200c103000301c6041240e01141000c1400c403610403900600d0000c1d0489507500c041950003900c641d0025001050300c1c00c651000c90100d4803510309038401903000800340075151103c1d6025500e95070400c1d81100d0074018240303507654010303942c81102c20180507030300d0160303859510001c020b007464085880c08000407501c020323a003400d07196404400c0070f4a50544000c411900e031400c0c12481c040c0f44c66403418900003030020110410409401520500c0000c4200344a5916054100700c2d2503c02151134140001c42003010001091032211040d01004010f40001120425030002c0041029006821b5500200020301080301951510800300d081040207441c80110381c0300e5482c56140c1d4540d2040c3d54051030061440f5409001d040c0466020550007802c0300d03600d4164400c03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 619289604 1250 619288354 619288357
    0x5030601090902090f07021510080d09051203040605040510050c030708040f0e01061205070e13020c06010801051603020304110a0905061f02030703031806060b25030c020609040b0a0b 80
    0xc1240560350340800b00c5c2e0320180d0f800d803e03406144590080c00341100103e5a0501101c4020040c040c01c168410000403a40d406104d206448901c0355644108681800248400f910140b4601115503008000401400e9404426601a10b8007150843d02c00402200110361500891081f1320203800b001480701c0410001c032001b001200c450780940e0340610359403011524904801d220b0140030510005040214080c0383d84001d900c00128204411110220b20101d1038803228036800e40b49050380001c1c540240c4104001302c5005001280080c440d030301d0b09805082880e034500745402e0a260300440403604104000300600783c51000a440e4130540307540d400404003d49000d540041c065121321001c2c030b4608002d9240c8403545000b503001149484a0b6640840050031041c28824049581c1c0040c0d270300003400d6024840042940726170f0507440d90700300324400c4c10b5001c00741803414075010b800d0800c03400070350845c904400c915012192a612920003001050240c400d091400d584018180408100c1c20702100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 619290854 1250 619289604 619289621
    0x80f03150303040f172a09060a05060a050c0c03120d0e0a171305090a02030907060f1713060e060a0b0604050604090b03030c06240316060e0a0503060109 67
    0x800001481100c0380615441e4880c0f03000b16a07404822413800d01140c0e602e000c10031100090641281c0700310495854032000c40c95603000c0004034050001c2001c045140001d0703841d4014800720356608801d480c00c400222140305800f5030034140030000c40c013220640c13001c1c41080c1d447d407009000d903141c1c4001c20b01034425603441011482d650a150a00008410b0350000d11460002e900001500c4032401c050b207182c010b9084480c442240505e055000304042e2980c84030b80e0700801c015032025899040201c3d04a080004079004401042114440c3c072140ba980815840549482c00e1b14240c995221601c414030110940744002e0910341c20b0500c058031580c070000e003040c4100c41c081410030880351843e04000349440342d03104241d80000144070500001c0c107207074442001900f00408031b82c60500e805466900b07089044542d6800091081400b103081803070289007010000d0200e001e400e0907010301c00d00a601e0509030040604005003842c0d8440c00b600d43d420080090000142119a5584e50f0700300720003d8032029 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 619292104 1250 619290854 619290871
    0x70f020330031608131a070f02010209010e0415030804030c03060b010c030503070302160b281a040e01062115050705070609080d0207150f0c1707120f0e0616020c0f0a03080f03 77
    0xb50708c031880c0301c3e10610075101070b00d8050756140d214135141e0b010040a07080c000498040840c40c0c620000c0051032010041004620a569000c00039165041100c100d075000c9000d14140409100c1c514000703688182103e03840203940c200181c0b15000e10500d0308600050750401400300d413891040c488241ea00d61400c503200303030800d4484502102420505000e860040c0204260303031649013044a40ca1926170071108245038403d000081c5242c4d07a54810010703021604111081d27200a20402042c09001a5841e00221103500180101d04202100800c80e10900d90090302075175036040e20b01c1c1041810821225400011081591501c909081c84062100d41038490700c01e26140c2910200300c100c26010b6019500034540b0b903003c41041c00032003c006a64020007140400c110354601d400e80c4c007401c0c401c0c40000400500d00084907142c000d902450484054a01e820320b018a1007506070040e80000c1c55061000305072140c2c44030f400c00b6030100701d10352a6504006c1c41c0880119904a804414501a52117003104 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 619293354 1250 619292104 619292117
    0x8030411090108121b030f0304210201090c0306020c01060b0d020a021e030406180f06090e060a05092a0705010c0206010f1406070f020330031608131a07 67
    0x20f486050f90755014251408030101000d00502c0050342e00c201c03850100c039400e00b041e20718059210000a22662080360100c43c0021003d81d006080200c1c1c0b1807614207020240003c100c1030a4a446d0020328128510008007625000641c03010488000c2d003010300103140494404c0e4660300e095021801940110240310018480c118240b204000e00d01c1e4100d04001404000e07502d01403c0c07100460380090140756148c0c4003c0d031030000080100030f160b55003004200c50350b0b86007000d9040669200500602409182c031404841c0c1c410b0107645c0d83c502e40c0c913030072200310003144142013005d41415000d400d0341c003545503139000085074417414004190845410903040780d0a450b031a07030b26150140b410007024010a0904040c21080558a00b015001005190b0007940751000e0b48590741c0c0003034584111061030b080b07c45140c000b1440940d44149000d0751a0a10054070782c20352510315068012050380c0d00300c5c0c00c10081c06d107001c00d021803585103100c5ca0142d00310142d0b40c84220518840e03d0381042c180c880c200007468 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 619294604 1250 619293354 619293359
    0x40b0c0f1e12070b04020d1410050103060c0f270e090705090702030a0210050709080615040b1203090409230a110108060d02092707030c0801020f1213080304110901 72
    0x1110421124401d600001e8068030b074940d07401340040e647c075001040300c448508092001a1020400c0030381c14050341e10700003050560440c60008103440d04001b14009208100907004140d6401002c1d0006180140d00c070301035800b01c1b00050078071440c20fa5022500c8884a00103101e0004804510b103820750318213a50140c1c1e00c1c0c8078800103c2c0c1d80d1050102d0030b401a0080c3c0c80711445600a90410fa811807860b10303200c000b0603101c0c0c950034200402039980340c0c40c580c5500950140b03801c0500485c256040b0032184a001035001c0680c42e03840e80305400c00280300303954956080040101d04042584040c051000002c140780f84140807980c0c582102105803000040c4050710401c0d50702c0303001032521500c406411890304c80313000c2d424420040d20251403049002d0054020361001111824840b10420b10303900240311103469420724004503a00c0e41c2140b0507990040001080c800700c48400c03641d0802c00c41a5800041d5692100d15003001c0c001c01d0018000d140000611040c46408410004005000c50744002c540e41e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 619295854 1250 619294604 619294633
    0xf041502190c0b012c0606091002030d0b060405030d030b0a1a0301060801141f020f030c070501090e100b0a0c05012d0b090604020d0204080a1a0c0c03040b0c0f1e 71
    0x1861400c45490f082185c420720054001107117840f036005840607103d60b003403014400004080d81c503440c1d4800016800807030052400c0e0142d000d8034485801c191048c070316080c01d00d03000c661138440e0030001c54145512403c0086860b140e03001041d0003000401c440c0d0310480c4001d02074500541c03081c03056034009200c640010030f60003007102c103481d03000360010540c3c000e600103420f83c540448404c1c40c40105500480039100c0c80740e4010304c014208000010080c14881c0d0802002501d0017017980c0156401180703003001c20005010745c0300e00f0802e8170101c00c1c5086e22041c0d218401ca900d160300e013800400b954200808010840340c016989114440380b0958001d42d40405100c510480e0010000aa07010310b4800215980b81400d600420081c11510000345c5083d032200205031030403665101c12248816a007032614468001c109076103421028840989180004844145689000b14000c0c0c0046a00025a01c11011020401d00024030203c0041e1003000d807815814102846960307400c1205030050804940c10318 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 619297104 1250 619295854 619295879
    0x120f03160207081f1e0f0e060c030117071502010f0b0d050d1404030b0c040302040c1d0105090a091a030c0f01120e0307050a050c13050f041502190c0b01 67
    0x242e40d4040101580111004d0910b000c03e103912141d8003199450080100c20b1115031202e92441341e0004c0c001c9202075800f010002101e200c04603c0c910350b0003140074884c03401061011a81111103000248401100c13800c0c00904240707540d4041c03240c40c0a411009418180c064214041d0280050410000f22400c0340602502ca40f6601c0024082e400040b810800d443c05404541201140795940608080d160745d101301d050842603a0402d95100040f4081003145400d005003428540e9910300000c203840031040311048044400d540343c3c140940030a0205203504c40ba8104d8000f046515800d21941d803544801c859080d05030f0002900074059020f408606040000002c088540103940c0d42c201c0c0003103103800310020a414411510903000400400000c11000c00080ca42c1602403000b41c60404004400c203d0390360a910860b0400c00d0402040203114000c0c4402c15902541000e2103203080510a420f00f002480b03181c0c1002084041a140710032140d030b0102e14458401e100384207850841e40c0f03a1850b0b4424 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 619298354 1250 619297104 619297109
    0x2180d050606010f08132604030503030405070b1c090f0606121209060909050405070305060f100e0705030604020a0c0b092409060c0706060308030711010f050108030d0c02120f03160207 81
    0x11b01c15110130341c2000503203181000811001d02d100940030304d2a11810507406d0b5015134800d0351168008024003062000038040d41e00140014503100d03140608086030036041c8001440410b80c4696262080c0c001d1101600356404c050398009020051151129041d03031441410400590b142034200e0044a5141d000d806868140e641689541700300301c1c40c18610344060100200215214060008000002042003001c42d010f850280303103194441c03510b0750741302800d09816480320500412401c18019819002030489800143c241d81c0540c0c1c44200303000036030346051081001015003a8020030000b07088c001003101c0c001c000c40402281a20400110000f40185c015036012419801c00b601240084640034020040148201804070b9110341e20f44500380305800440352200462018030040080250038851104a542a888100b000703505201201e80d4074042c400c0c0c00c0300381c183d0799441c200145008004580e41d01c5042d0600d6540c9541d146100c4245402c01d45100c1001c2e0088440c007103401d800820388006 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 619299604 1250 619298354 619298371
    0x30c0111152712190c0204090303062108030f0c1314040f090519150e060a0b0d0b0c03060303041809020306010602070b07030c0c050402180321030103020402180d050606010f08 77
    0x10300c0d00c05801034030f1860201101c5001d006680c04018011f0322640991840d80303000f078400280d40b51408640350b0200d00a203c3d900c10201c09100d034040003411002c00e0f0382d00411000158081030303441161042a41c400e5502a503240d0fa0351850002d041008202c4000c031090040e2404e000d02051010079905590000381c008046401c90004980110300100c0d2101d003060040460714401c00ca4605000100c078240c0c0b0a102e0f09401000822280d850680140300c1005d00a85440c2030800403511100701488000d1b00b8502e800b10008085100382c0d80400c00e40700a0b00c00610142060402008941c1c0180b6001108a00a008242c00010202d0001c00c06a04036003038581341707501e005010303501154800440035045414000102c004035090300c03144040c008880f00610b000c1c108030034010405181c20f401c1ca41f0003c0c0d0f11010010011000e01d000140c0341144d074152400358907246206202c5000e00304021200c1d07001807607280b0741820301030005186030003000c0a89802200b0a048502120210011517401c075 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 619300854 1250 619299604 619299607
    0x1523071404081c05280206070c0b070f020c0406090f060807060207060f1b0302060405060f13020f180f01090b031207020907020c0a0603061a0702030c0111152712 71
    0x3c07600c00ca08022514444000e150040c900240c030100200125020750080c0d08220120034070600301038040160a410107038904103002d0600403a41d07103e0030340c100145040d0030820b4002e540030304a0700070007242c48594002401444180d441e100c1120003480360408070052181007640000340c400703001c41c03908240d0303829901420703000d410311340c01b5079482000e0f110b82c03000c200141000c1c0011002084480c5c0304284280e001c1c024504160070407911f042400713850112038000d040d060103200000a6400ca80d03580c3d064035a80301e450714400006c0d4110201140700414015000100a0100c00e5030040906039548028200020b10300300d01410750f00d15030b0780700101e202c18041040f90701516080710b8482e40002688101c0707040070a14000302d80074231030580c40940801e443d00c40a03c0b215428416444812100c0314155042900b2500000d5440300081c041d5414004081c4014160038003c3c816a4149002e520401c0302500b0141a400a03542043c002c0164850700103460304102800400c0c000c030700118174041e0a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 619302104 1250 619300854 619300873
    0x32a040807051c02090f0106030c110706110f0d0206090f01092d0f060510060809060604230103030c141914010b090406050a0c02030406020a152307140408 68
    0x310518503102d034000c0742d090810f00350400503a980c4981901c2050754601100c03640d450a07002405aa60801c02101031100300700900e890b0a20000d1101c00f110900d240c0b201c2c440ca4616166401d1039150041260315003e500e0320324509940026006000380e002d901254031100004c000709003210108000107107118103c915040d146240c2d03800b24440410003185000c40c4111544d54490345000b00e020455400d030b1200e040102d6180f03080441e0b002000c560030402400e01d000b022480d261080140410b1145545000c50708000d264091a148003c00c60601b4112070758484c20042c0c0150b00e030003012500f04400251100d40b56002165502615181844615411200c0c0cac1c2c4d070310265010354420355500c0d983d48422402a0703503803a03000c5024030700501c40010641441c9885c001600d80d011644010765000300010020f255002410116061300041c605030740380751016000700641030000b950554100040722001400c400c00e10221300640d11500d5110040d00044604041030149101d02c0556800a210303c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 619303354 1250 619302104 619302109
    0x207140c2706040e0d02150a1503020d05010b120303191802121617011a0913050c06030106050c06011703040504110d060b030f060103090209060420032a04080705 71
    0x301600410028401308030480c0e11040076150003a240c1c2184010391060a11002ea0380404202c01e0300110840c0041c80303103201715103080806010368440207005016080300141070103400c2d805001728280042c80c070340a5100441400e0368030b420079100500c41014101d07413040050014841c48020b410b120349400d145200b1a0204040340f00c141c14507120f64043d075001c1104200104081d00082e1a1043c00c800041908588550031502000804a400065501d4440307072030350b034024411340c0400400e02c0c401083c446468840c2c10300b1002ca040f19003103940400041041d642020250817126540c2d02198030710b80e61170316031120001c00d80001401d603400810060100d814281c00c200c500c001c003049038616101c42c500b4103604407545030b440311840420101c2805800c1c07111103070080d04490300740b9040c4840f085079000294144000b4150078881c0755213900b541e85032007800400c03901107a50380d19075036140c3c9001e0484c0c10254003a88030350341012075280e09039a6100d0744001a00e0a0300c3c00035004045160a0105 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 619304604 1250 619303354 619303429
    0x30210120603060f0608010e0105010f030f0602071709040e0a24020405060301060e011e08010b0703110607110c0d08030412051603122f09040e010207140c 68
    0x40129034441c84040045500750203205100c10302d410300003444510b842c024a003100e072000c24161881c0d050800400110445440d100e0542e5049034035100b00c040d1500e011030091181c16001001412200440d8030b107200380710080c1c520783c04152000c0c000c5030f580140003910340c0c034840f60051020300b44c84516a145c84508607004000408100d006140646520004070150400d82c04540054070b0130524071402c1d6440b01d40c0381120311900c032009554118200020344402c005018100100c080820780d074040c903100c1c1852111078162282501c0e1103080c00c0078028070740d10110303c443c1701e04c0c8210550508a800d00d85510281150403800503401c5440381da8402c45035004450382d820402c20180500c92040011910500c00c0350b01c46d854296400b0200308813902520800d0300c0d046c078449080c018980341d070094094002146100c03003100d603580e82aa640014000e0083c861109440c1d0300c0800c00200f003000c0119420b05100b82c520854403029400b504014441d41011000400404480d4405030b011000e42d0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 619305854 1250 619304604 619304627
    0x6060e0115210204030c03080309011512020f060405060307081b0f0f070606080304060f030c0c0203211b0606040b090402011b0c03080a1706011b0318031a01090f06030210 75
    0x410152030130750b1300e484007604607942e60815940941c0c000180034840b0703002d115040a02640403000c0c051546400c95123902c000203200040d000b040008041c4202e0b0b0307944000c482c0a40001024203403242014080100301b03c4044411420801c2004041141c1c92050415030307040c919600c044514003426000400c0d810342218104407480345c4c1740c51000c00c103140c090011f000035000d030b1350764004c807040508001000e03030702c0092050091149403403018026803808182018005881c1c1c95045082207607103040c00461107240030740c982c4240b0003440c5d040c6581d004101c0c21700424048070240300080034002042084e10342903800031b0118584680500503041c0c0c1c0c403c03480705030340a01c56078984590740c0e490340c845a51008082000065400310000000900c0070300c426000002840d2442d02104113507803100024002440103418405002850140d00300e0308078981000e03682c80711504641c1411400160750b40c1d40d0a000ba008850300f030848440003003215104040450381c00030424101402003060660b21805c990 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 619307104 1250 619305854 619305917
    0x105060f1804060e091603151d030a0302090103061401200a05100b09100303020601351507140405041e0e0706021e031812070306060e0115 61
    0x41c01c00c600300c0d602c41c440c2d031009000041e5264801e2829030b03205800c08541c0007480320701600400c1c050001c210303442c1c99289a05103441d00098545404002444c1c40b031000e170020704840c880081c00c2c0b60090307819005007a642100381c1b014804c0d552522814103d040740400c0c914000340b1030306800c460100110041c052441c090006030b940d0b4200341e4541c0341c108410300c000c0250007a115541400b003810310640190348035070746890001e6403c2c25680c0003900c90406104448620b503445050035802402c000d01820a44242402e000c030350440d0582150300c1d14001c010200e0407102d40400640e41c14042c803030030a0882d00e50140649000e00b0041000010080c000705010045601c0b0300c044003031240c80c440d088124803414000c20b002450b0400007494180030390070b0060b101d1801c480303000082400200307444402c2449000a510040440d001c5508000d266030712080500c28154004180b00c1d1a40c88481aa101352820000300c0e81ca07004080d0ba160740e004442d00c00100400c80c00301107400e00b204000c0410620703 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 619308354 1250 619307104 619307137
    0x1103160e01050705070b0301031104022701170a090b0c0301031104361412071103122206050c0d0305060103060b0a0e101b0b060103020d02030f0910050105060f 70
    0x1940ca404d4902901504802c030180700000050052041e40d00030340c9030250046609629243c480804480c00f00106850309001d1074100d80c90000680c000c0050f03d5080ea15a080c0e03a159240041440c405010f10a1040d036083c07590f280824810305100c1e08403416250400601070490302d096040c04020806155200b502200c00e2040401600c075048040018014100c61030071020740b2803e040c15107910440c032100803903001100c5000301d0840c0905a1b4403081e0482014010341c8114004281001e01a1708001007008001410440461020340e09039400040c000030396a403140c58060a803000c0c801c40201c50410741c851600440c5952207904000c2d40004107140100d641c90703072200c80d041d140c1c2200c2000d90104a00c640c4918040c1044104525081114509040700951420014500d6800c441e0050a191801d100051031640250115000c5001e42d000c01c543d03030b01e4441705c40c0646541c03c1d244060f481c00340c110002c6246855000b000e041e1036008025074589001d94050460592180e880440c800c1c05 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 619309604 1250 619308354 619308367
    0xc0e010c080f0d05041101020d030c120207020402040e09100501060e060316030b0a0605041a12010513140717130503090d03030f02040605091c0b0610020a02091005041103160e0105 79
    0xf1800b035a40180e01c01c403200c0c00c5400c2d001001905000b0041045030030140383c54591090140d00050b0400e1040901d00010f90300e0256002240c0a0309c610f80104660815040500c0313204000091040d82c8200d400c0c100308039591b202e11003229440415101d05520110900102d5401c82c28180015806c880c00d0400140309102da03000315041c64240c0e880b09010a602081c20010710320201060200ca2554082481c90150001d9022440000c1801004c0c016165040104009042daa000c007451440c42c40c11b0030540c0c43e122000502c2d01e241000d0a80201d074004010440709060703210410b04190b445406181801140c409101d000c0725200300681c105500c030320181c008207642e440180702500d503d0742c0f11640d408003001031110f50090321011401c0da02c0c2c00030480c001b0441c0f450360f00307030886c40403103c1c446001c400700412464501c0010020390305c0800c4805200600c412078a4250403548252014030018040c41e5200246010880d1589074500400d0507054555210303030000120704c201410300780c0c2041e8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 619310854 1250 619309604 619309627
    0xc0e01110a0f030504080c0f0a0303212f0c0c041e02030f0603121206010516050f010917040806010308070503130f142b020a270c0e010c080f 62
    0x204081000e80100348006170600203040e00380544111002c00b0742d038081000d00c2890208000440500c00a010400208400041c0c0400c42201e2090003030608401e020102c06419208490600d0440d08001c11070440c51009402d1504000c0d43d042074000006440e403101883d0921000e003e0740403002024012031400745404000c02d201840c01612010f40d658014a054814107142c03400c10104244070402c10712460890fa030110142070742c450420300e0450b80300d50075551007840c501c404103002448e5000742d5034400d07580c2c001540708100c0c80d4041d6401c0c1100c00e501034001c80a03403007103004804503500000b0050010960a900a00144e84240c08032031a019403024031000c0041c150704034a2003a12021410004482c3c0b071068000309000444582c4854400ca03014000000c5000c2c00040d26199865401e0040d03584c4c40c0b0100c001824000841240c4d80e070358201c100340300c000120200314102d02d070000c1c0680c1c1c07900c5445810805641078540c50403004040d12014019003087c8880002c403141040b00403980d4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 619312104 1250 619310854 619310873
    0x3151d010c0c0b06010c020d152012060f13110c030a0c0302120f03130c1a0409050a1418070911042303030d0c090f14090106030c0e01110a 61
    0x90348a0303803030054015642c60b10300310f030940150100341004008a841000740e40c0d41c140c81c02ca05030340150305d007408030003442c003502c00303006102100c4401e80c00e80c0b820321030540d541d00c00902010035007070340700c1c00140d84e103c1c00c0141c10b001c01a0840d4101c0d103070710f0200e49101d0040d84164a1052001d9000341000584000940303076501c03480b40c0d24001707440c10310244100f42d01084100f080c2d5020410003810034000d5080d650040c000246044c03010007000c42080c0601c407060b24402d01610b0101d40c034215001c08000c524515034801d00c40d01e940c152800c00091400d0202d0711078007031003060344c0c10f0368095a226180c0001c0e081d6400c0382d42190030b015a40001075280110f11a5072001d01e904442151164642910784440c1c010307040700c48160085a039400681a40c0100848120074100b45c0001440050b00c00129401040e503000346181c409a0a4045000000301e00040d03402c100c110394006e0160b880c0d060440035a11500c0703866003c610340c03414550656001d80e091100d024040b80485078420003035181c64156 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 619313354 1250 619312104 619312121
    0xc04050d060b06130f15020a0303111b0304050a050f1005130b2701030516120608010e0105270303070503040f080d05180d050702130204080d02010f0c080103151d01 72
    0x76621013130004c2010900742c51000d0300800400d0983c06256008540c040d44507070040800400309543e60f200140e945140c0c1094406000010100c100020303143c1d0803080c7e0740c0d88180101e07841a641c104001990f0318113900e05202544010301408007180d140101a20590008051031442036034050003c54640c8a010280940404500541e00f02c0494941d40601421085800904040c102810404030101013000d80303800410b10b02c0c04024002c4800c540740700400030b64200c0078865007405503c040600054210501661b080d1000510550446842038002050044d403823407560030074000103468a000b41c01039684103005a82c0201c1c000c55554a44c00c141e840a03604030641990b038824400c0c0d101d181c11781040d10819940c000e10100301c0d00440607159000e0404002c0c070480b4010200c01509800e038045d83d00074800303c4112440205000e0019010f0000d14500000ca02d01d048a48440940f041d000103048982006500c00604016488580540b20402d8035203908004852403684d0080d007403040c91607 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 619314604 1250 619313354 619313377
    0xa030807030f0504051e010b060711180910021c02070501090311070513020904020903120c01050c18010e01030608100f050a0516081e0406050117060c04050d060b06 72
    0x205141858020701140e44515805290754545401c00c000100001003002455149030421a80c01a41c0740310240503142c13070451250031100214020b000c004074540b0603c6c0d5188115240202c0c082200d220751200c10013150b0310040d0b03600c07021281820064550041012070a8100c0d500760034206090301c002642e21121044541d690740d494004145980004010794103c0b54030007a1151500c3c1c4400960299200805d1900459002891105503901d96046856246003e41a5445003210f228400301d00e0700005038580181d420f00c0c001940b002c041404444070351000080d0503c86450150044031908500c1000c1c0d03060607920741020030825000c00c00010b6110855001044a1000c3c0000c04240c483c064003450040b420070061204c0c500c5c2105103e004804540303400841035880264100326070404004078240b0740c91038414081441503a410560588006002203c00c403036102c88802e03544c01d02103a500c1e2547c00709000038040c2e4540b04140b045114000c8001045007003000d000110b46910602c032000c0d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 619315854 1250 619314604 619314617
    0x50705010207210e0105031b04050d0c0617011d06030f01050a020d0c17040204020702060f0c0a03090608061311040b0c0c100206041a0402060706020d0f05010803090a15050405030a03 80
    0x41d101c10007040f810f08a0070701454400702c001d500c800040d18502025040da20000c0a80d180410b4449285080d83d0003440001c00806112406051030343c4681544d0140c2000101e05c481c010810103040e0000364100d48603552071018404846518041c2e03403c3c007070140303503041c010341501071041c800074003620340180741010780186d8624450080000315880710039000203000502881514803407010382c4445d8400d0301914056541e6403e0b01c0014820b00c1009400c00003a000400e440d0038584c400945414441c1c844d4032030080a0740c54044c19141c9850841d002e9600001d05042008424840d8015410703903184d88409508291310380d0041c400980103030804910a6100b00040700c3c952500103d001040030250002d01110700b0541c440c100c031000150382e8405e030180c412010500b1503c81800716140c185e00700b40d0440d100e01d143e855400262a522200d05880c4d8100f0001203280503000c4211180c902006014084192624801b07400c41010b052312031040c028244070000d4192002e01070124040d120b580c950 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 619317104 1250 619315854 619315883
    0x32a11010f030917030901060b03010e06091509041506230a060305010602030f0a0e0a0605030f010501030c05070308060f0904050609060f0402010e09100f17011406060712050705010207 81
    0x40021100031072180806043c03140ba40c020808028800303004a10200505559035149115103004d01850703846800c009000000014200c06440d0324503002d680201d0321140c5179114054000d0b600425807000c940d00003c00070200740015080c3d901d100f0642c0300e81101242c519030341c0798401d50303a0f84907000c0c0000c2002080000d00c510310b055003d0b00045c081034181004154107003840203580b4043d03005401008130002030310607540c03401001c0d00c01088030010081d04405844682c01440ba410036a4184d01e40b0650380c0000c1741710360203030141c50a0351032141d440078203000464030b0484520b540540880c0d00605106009201a181d880c41144503038081d0004144074100f0110701454900014001c3c0131410301c15040c00300607070b0700201e8000404030484201c0380310f4444214181c03200b04141e002d071280740d42030400001d25001d81805082d0141282008200c10343c01003015030300d400022605a0f0f8072620030002c5000003000041080b007011114a8201e0500510f030742e0f0b17182260700043c001d1b90181c00501c000b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 619318354 1250 619317104 619317107
    0x30303070201090212030a08040b0c0715061d07050a3c021b03070506030a020903010c0332040f140a0516080d17060301110711011b0f032a1101 63
    0x5eaa9a440500541c038121000000030444000034000510b009485000f0030b45802e0180d040d02d00c1a078020034045210024885c00d440100b032213104500510802d002c4441290321703040d11007445400c0d6a2103007440c18010b1074080780c10340b401600034180304a195030b50312801001889901180003114400c007569908408000c0c2c40c0c410000604d4800d1000c03440000e100f5140401c5980c229581640d145407a9254000c04038040c0c0112488950107611703124040320340c00e0385a0454a8000011100c0f054421450082c010409804107860a86030108001140001d080c040c0c60281d41402640440d8035411000310031401c05451003420b441d00d90080c2022044840035000e40c42c02041c501c4020074880851000c040c02d441c1c00301a201c0f20304404080060041c0d1030a400c69407440c0c00d20b28041b6a200300718038203a4009240300758040c5c0000d000380110060380e55140d20000c0c00782d40151407071650980d2507800301c0340307641d40c070a00040d42070104c80900781c1c4821410382d500d14a44201c1b640328100c2c0342c2000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 619319604 1250 619318354 619318369
    0x1e0306030b1f05031209060304150e0715030608031b03130e09070902030132030a0605010f0806070912030e1804050c060313170c030c150a0225060b0303030702010902 73
    0x1005100f84c00a000c1340c6800903100381101c1b00c02070700340c5a10303860707550b5404e01104100c006940101800e040c95903100c0260300200384d041c15a0400d00041d03000c181200021011074485010361110b60740100039042401c41c48010050440d12494200ca10340b04154840302004c5145a00044c800030b0302800b84103d40301b060007600c02501e180002182150314004025580400740100c2c052041d12600398500102042580303480c0700396000d0100e44688459140c0000200002d110321804040880000b003881c40002c1500c0d4001c241035502d00c00306c0c0f420500707009080701b141c1500324103228150325290002c1d15100203007161002004166000d901d800d0401d035084c881303c583d405d84110310400411a0608802c1d400580141e0458030100d02601400c20b002914401c0300301401c0284000705001c1007680c0c00083c0e024003070403022020000c6880d94800c180c264000d900f90035240c051a00003030103141c1c034014081c1c0d000700d00601e400300c0c91a000002090645c1d009580c9000180d4540031102c056050101 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 619320854 1250 619319604 619319609
    0xb0c0f16151d0d0f0b01120302010b0a0305121c06030809280b0f070b0a1d210c0313030507090c1704060b22060e0106020a031e0306030b1f 61
    0x41c142100710216140e010030b00001e100091043d02542d140b0360034482d0f691004a6800d81c03110701071034070703503100d0f0030041038000880000ca00640c00d010100420f82418906901201d901900030b0142050380c0450035103980101100c02c02107020340e420b010400225008003001036000e2148240c0d68461441846444049021001e009100e0a0702d80d6800300000d0140d40e0403a0b00804680f51a0190568980d115115018015081a1000c414050000c0d01540413403151005861020074805c120052a1f484c1d11085103402004058261069403a4544200814580c5540d00581e45400042d1840a140d00c84a40054425510044060100f251144114050003082c0d08081c1208403d03980d00258402d4014001843d403a12407000081c030780c03a102c1c07044d001d100303102c0401d40c030710110b00102c81d0043c02584200d60022205c40000110b8030300100c1c0c40c14507240c050792003114106030218560094a08000e5003c00c1594901001020a094000c0c0354050b14464031107110107110400b001940c04541e8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 619322104 1250 619320854 619320857
    0x112090807060f1e021620040e1f090f0f0b161404181107080c06070309051005040203191a2d0c070204020301121502040501090b0c0f1615 61
    0x148810510b0007103106800c0c84c44001130f4050307030304c1c8088401017800c04010040100640d00c1c541030070500c440c45070000003a2550039202000081b01700302480b60754200303845440b200c168086034030760000703403094202d420040e004440800c410032031556204a086003910090300c012003080b00b80981d040300c8001181c40d07002c3c149800c0b542c841c0100c61032202c51081d407182c100840380480450484072103d420032400241507818040d111802401c1000d1958400303010164180140c0f0001100c41c1d01a01c00d4494881d0031000401c07403030805201c1d850081030094002c0c1d03454466550801c04030620381010104c0c1d10300c5441040018102c1440c13400c803640002d40000324833070f00241c1443e030015241e039092442c603181d0401c07039140c0d449200340b134007482c402d80c64040c3d000f41c0000004628400405140104648201122070307005031106800402c0340568040c0d00d00041c0000f01c104201c02c5850060014406a802070311031016041d040103207030403049140c4203448807001d0001c0004886860420f200702086 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 619323354 1250 619322104 619322111
    0x706080106020c01051308191b0b0304080306010e060a0f1107080d080c09150406021920061c05040c090e03040b18040c03270218060112090807060f 65
    0x101107020b500c440c8682c815604000c8045411030307028403050202001051080241d8264a4035070511001240250f0001d440046442880c00360000ca0404200200ca030340860250454580799106c030718545c0050309150422450409041280e501d140051010b40543e031200208108a104041c000c016150a410b005402801e02080b59031004a00f090341c030072a40c500004155501442101140a002501600044141d00380705044c10354000400540307406070201c0d00071a03c0c10b200741803d55a10040105510b80c86000520014041101c803100e1903802481c031410201c80041201c2c9480e08892241b14490700c8006100a20207403650b05805001c000d1402d00902c0c19110005680784158803c01074150000241d004041542c440346800e00314006000340050000d14030020054000920030301c45081c140c448410515040000d1015515400340000b80a194094003614030b0100051099060205150700b401c0960001c1c81150521440780040c545c0350951410b01c0c00486811401c50307201c1518 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 619324604 1250 619323354 619323359
    0x90d1d130f1401030803040b060102250f0503011503320a170304030c1e0212011b0906020c0f1f050703020c0a030f15060906061d060f071b03020607120207060801 71
    0x5c510b002c80e513001d90000140d803c1900e070480100e280c131441c01202c00c6002c075072102008034610780180f500111a03200819141e402d44071404c01d8201c801d001620301021081e1074003080020314881c0c5204100c0c00301d01108141d124400000003104e82090b1168102e0340141001c04104501100d24000c4501e0340140b030340c118a4542c1d03010b019030101c0f40014000950202e610325411207002c0b08000c0b0603a003e00070004060011440a0103040c40c1e01c0030482960720340700c0020f100c5114402c0174040340c00350380c0241640b03000c410034003901d04440e00c511504200740181107403a1040c2a03c10f42980b40a6582d4180d443c43d0508001f4202007100040a118506145080001c145207045100700c00c0c1e084400c420312551003203d903000070411a8004d082140c180080040d41980060984d00e215052484809160b403d03c0100160340c440c4900b2403584e40d40901a01000c82d00c1e803400241c001ca210100000d20035140d400203001ca410506040306d01351a40414444841d5040c010040201300b2030400100650 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 619325854 1250 619324604 619324613
    0x70f17120315030309040e0d080c1303060b040b040204030f0b011a0d0506040b0a0909030e03030a0801060f0e0d0807060b09070e043204030f0503090d1d130f140103 72
    0x400584044520b40220344010016a410320448441c0744000f00300300300e60300c1304034101500c41d542848001c003c9012040022001a200c008a500d5180c1d01542d0011603411643c1c0c1d94020105001c20b603803c035075140c0c04088141c481c0d1005101071402440d06601d100d4041c5400d0f1050079058000500b05900f040c14100c4101a0a046d0f450036440b82c24045015a21a400b0034014400c00c542d451344100581b20004003100940c1c0082c040501a076903100300da0501e141410f9491003440081d0b00090141c0c00100105031107a015a050f000e120720b0202c03551a8550002203d40d107000c0c0c0309640048000a4860401545109a0354455002d4a0072303c5035103003a03030002c2c0288007101e0040340039a17250310075076090b254110840c128003c00410b64511200d08080f20050405040320101c010039035410f001300d0480d00402c16248107a10800040c40c0840714000d048900c6111100449440d2005003003000c00c42da0303080e146040c05201624004ac40000c28140603042e5400c0c540786551040c0310000610105 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 619327104 1250 619325854 619325857
    0x3051b06160303090609150c03020304021021050a0b1003142701050c0703141305010f032d0b010e090a021b03030c120a060605090d080903070f1712 65
    0x25071101103031a50540c0500702074014282d4400010100d6241c581c1c1c5c4001c1019450742c11070400c900d04c004201c1001c17404c00940480c0700c169000781d03019003600079482e6647d105007103495011442c0d50030448000d00310400700b01616030a44240c1d81d6a41c0b100b035039922a0401c07034a03d00403c65140741c1801003c0d0350303001400d0b40030340c0a4044605c203604841c490340202e656080200c0b03078040e680020400c070300c0c01d04039505141c2c10100003100040c2c900e01d0301e1240d011882003900e01e803020078200d80071020315200041d00e80800b100d070680c0034962039402c590360803010003140c00701641442c14507010009000d9448403c9a90904006040c8400003541003500d0b244d2104440c3e01051440c401030350380d10644020300d0103007604c12840e07080e44000003c00c2018801100580150040c14031511015181d802550042d125603004450003e4018040d12000d464405c8082c5545809a460246051b11840202e0b06000720703a0000750101e5411201048100010084200140d8076074024005030300c045842500a07 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 619328354 1250 619327104 619327117
    0x2100512040b0c0c0307080d0b04020306061b0a12031b02010e0c04020702030c0d0c1a04031a1005120c011107050604170f0a1109150108060d050114090703051b06 71
    0x420036002c005401c0c200484200c51885981108503901c4030340c54a0981c00c541c0c000d4034054500e600b000d050540302e003090b0003642e000d40340042a5a041c600711f40c09030240e40380e40743d841c0c00e118844d1041700380200341c83c10442440b841c025034010884c041005402d080c0c0b010211402c00c11685422001c1f01c88900104099012140443e805641d40d600c50002078901000700e9510303a80724641405040070010b00501c06400c5414200703c000c1207000502044040b40203520015160700c646829207500840b8400c181c41c0e20400c100c2e00c5200d07941d107031004039110f40406401018036912040300300b03c041d0303003000342c0c1000070b060400149a41820040403030014026032003040304c0020316135500c04194209204001c1c1c6100d0700411079400f440541444110403599003041400703000e141c00400d0595643e0908030124801c182c4070310980342c40341424800710901316181075030655a15603500c03120800701002c05000e0740c01180100301441c2142005801c01d00000b280981d40c2c1004240c0310201c0d1242000d07030f0728 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 619329604 1250 619328354 619328363
    0x1b0e09040b130311060705030108120a090315021204140c0402210912030903130512070612090c080a12021902060f0d0c0c060b010c0f062d05040210051204 68
    0x708440c6034a015584c520f5410030380381050084404021083d84d200005d581214100c0040718400070300785000b6403403841203040c00c100041d000c61060000c0349079007800c001c15500713000f4014034103221100e049121810035070b0111056014001e48032000c2500300021407148000300c03811880d040b04001c0300018521441c1c20010b2100149000426058042c08944402018044140e549141c0000507640b00d600416000d14802c4100303801003054102480340c050038007900c5000f400242e082420a6944a01841080d500740f40c4407030801d070001e001aa10b60008040b09c1c1c00901c1140c01c1e914123000c400c00441003040840d030040310355412010000780c802038240c0d01550000d589000131803450f41c292040901d004610350610610300040c5070300c200820480750080c4020004182800011600300d480c22002038001c1048441c204045426540200030156420003440c03035081c04001282044d40280c20b0801503650349030104419404c0c074000c4503048c8015032500d980785c4602c1c3c106541c10384002410150 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 619330854 1250 619329604 619329631
    0x6090815040f020d0c1d010e0f061201020409060513020a0503011202031e0c01120506030703020f0f0d031e0207060f030c171303030f020705032205041b0e09040b 71
    0x8041c031642c0b41c60304440540140907500032505600342105001c1c0b13a4070800030048001c40341ca00080c601b00007154140d50410303141d0685900c1d01c60320600e0120018000b5540882d411070740800c0c03960248014802440040c90100d8580d00e010108221060841101c0d4800342c0108515800e00394001c040341d040d503014440000f0b80d200d6600110b49805c0245210020300c0d203100d013044403c1d000019a80c44844400d0f0f07101c031003070202084004107844c01590780380d40590104006000600d800d01c44801000d40182541942d045860006100407801c10030039404540000320b09002820b8000d55421040458001000d4442c40c000c2c00500c0306130082400f0041503540e0111000704d5100340104505502001e84202071402d01a00b01103501c00f40744400c401082c608002c2070b400c3c8000c0d00940d04141c6e0014040d5040043c42d00c641c0441101403414001007004180c0042020f60729131090650030215046080c001d406508009421012134500c00c602c07400505c1c00b04000165a1840f00d58030140b400304c0310 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 619332104 1250 619330854 619330861
    0x2191110120c09232d13050f0603070807050d0303150b030108160509040f050a1a10080f06010b0a02150c07060b06070b04061104270b1c0605060d140c0102060106090815 74
    0xe105d504000030317030107500945c8680301204600d500d81001c0d0280040048071a80d0303071621400c142d90755006201d4000f81e50085c510070415454840d0141408600a050200710380f00d00d080030104e5001c060704a050170000c084018804d184041122010840b502c40700000360034141000a591800000e1006000396084203940040000c240311685003181d210942616503900b41d040030400e8242103035605132080e101d41000030811310029203403915400c3d00e0042c1404d0f908003106c002e0b09070303c1210280b0962140f1440d1608141092410360b110b40c5000c104140c58811030b152074802c0d103405110640c41058280320b00c2e030200e0084180a500180d20201c00508101c485030024054092980090701002e10b400c04d00c0c43d4040901d011103400c815521040045280040420498001c4101e40300c41811096110000065060b8029900200c0040140032140320aa0382c030402251100c0040303e030340d006a80d03c1c1c400365030104142c03405403105003006d041c11400c01c15103561791107000c15808460f403042d4020 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 619333354 1250 619332104 619332169
    0x5060f06061216080c070b010504090609051203040b0a050610120b190e0907080d0c020301110408030c01050109180605100e130302191110120c0923 65
    0x1210001003005103001e459160510100c480f066103468840c000c2050b80c8002041c00380503a007121786a590000003646540d0030081484018049030380201d0b00545c0d40d5505c1c901241c03040040d80081c80d040b041d40c035640e18046ca400300309404081c02d1065042c0c248014040c80e50342c2c00c903418101407035a10340400c2a100008000d0041d02e040c08005410244ad62074040c41d18406041d15015240c3c0d0f01c140c80c04603200c1100190703480001c3d100b00ca02c41d4008500e800c02181c40b4444c3c0b0031907580014000724602403101c1418040b544154020311440e80005002103000c00c081c0101c5004000c00c000400241c01b500c900040c0180764100018030003aa00d00001d01204075074a500e00141c46858880308552030312400a0114584051083e00540700d200036a50446103521060400d00f50702c1046a03103524244010701230a80b0b40c0510160600c2a14505588400c00b00d02c83c0c0000191030303030344102200c0d140c0313034011a0101028550075207034100d684052095440d44900c40308035454641d09140c1c0320049064 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 619334604 1250 619333354 619333357
    0xd0c0f0318030602160c050a060e01140904050a0b040b0d0305041a0c01050703020c060a0c0512040f0605040501020910020a05070b1b010c020c040b01182d0e010608090a05060f0606 79
    0x1c001d01d03e900c04584248660081040b110312588601d80c2a550700c0c0d00c0c0e4003000040043c40c40b4070fa000078100305001155500c90486c0300c2c0c0300b0308490845401c0c1840b9030005030958200725421120203035542514070305440c00c2d0007402004141550242c44400741c949000b07200740310780c1c0140c49914400341030b02400b150740c5100710390100003480c008200c01d0421020003030195200c914011002c0c810f40300881d01106051003000c030220707850707240c0616120401c8039020390040d0060043c3c5000d0038420108020840c10700400784150310134070005940700031007420015010440100e110441d841100e2040000b000090b40c2029180141c4856841d10710b1301c0540001da050344e2900350025420110843d1900d07400203450710080b01c04030303001c0c0300178001e040045412804910a032010300540190030820300d15502c550b00c8541e01a816408094055056005412507040c1d22400049541c0d60040102a03031101120780c1011084014050080850719055590f02c4080c105081e800101c0002c11240d42d1200d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 619335854 1250 619334604 619334609
    0x61b070507030803012603041208220305070602030405030c0405040611070c03030306141809070f0e010302040c0c08040e07020307060f1d010b10031808070b07020d0c0f0318 76
    0x101203410082d101e240108407034000f0720440582640c001001c035400c1d080505140d503100d426074002c43c241031504082040c4061040e90965032901c3c100241c03c5940d031065004203a100d5003103040c1101e286513140c01c80c0b07001e030305500c10340c01c540061200740003e0f0350210b1040310415040300d01182640b15410040300804400342c410310039450014010701000500300c428070407a4000d417000c01c2440c2d520312140289441500d102030384182c0718142117029011034903445030080360000460b9820f0341c0b580c0f09100c4042e0703290402d80710750000500400861801d4003584800000a217401c8003095a24ae54034603890056004100183c415030b00002c01d0240708106680d51a5045002800714056440a68009003582145810561900f05040d0b030448014004c12140200242044090b52240c1004078002d00c289510f10100901042003040480c00d208060001540580a018014140841c0c040e15019004403440c09100c0e0f61401c00d80032900541181500940508041d410f0101c50800000c071500982c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 619337104 1250 619335854 619335863
    0xc030b120f2d07030f14150708181002220b03011a09100c03020c010915030c020c040c1707030e071202040b040507021606080115030b060f0403060f050f0405061b07 72
    0x2500c1c00000c0c0f000090700c2810f000d02903144001d8060b0b006c0003154a038401f0401d04241ca010f0720000c507000c0b52180810907840b015070356440c0b040030101c154550421504541c2c010440750040340344800c0c086d11411040f05518220040100c061a004804445000501c20060308482da6080252084040012200051001445100b841e032109001030504540c00380300b50014860076404103959402030358610147c40a840642194a0150f80100e015020340000790045000d126842801504c0b18003402c8400720440c2c460b60300302d80242ca00d6131820030004003034804250400000740ca03503200c00310794030040e211001074200c4041c50a0020401a02c141c00c00300390018942010090019400720f07040c0324a0040703040002d40c07140e4440d412540c10600380a03910b00c25411085900d8045d0107079000110071003010348003600f05400818011041c0d006944192205a02c0f42c0080050007081d22a81d584040310b80302400c1c4608107615260b580c0c0c840101101d072101c41c0f0880f05c43c980c0200d0002d481000350320 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 619338354 1250 619337104 619337113
    0x613020f12040f060605030c090a02090409080705010c0215040f171c0905060a0c05030f07020f10020901080a060608070e0a1701140702190b0a0f0c030b120f2d 70
    0x51522007507102c0f8150099980c107242684c0440e19260202d1040841500203043c96119103d01140000a5010301c0050f5401942c3e4006400040c003c0c1c00500452401136000142010b92404040e00700245800d5845000ba1514100400109940744c4030320b00940056045120020a003003588a03881025800b0070b44c086a03e110542c1000241c00c02c0c02c220748950706440c09a21901010741c203851400304118040750081c00020069100c440d03820b54404214411214400803001c15281448101030301e0b84e01c11500041c10900035600b180c1d603a03802581c402810842c803454102c00910f8401e001d4080010442c03041c0180342c640e601c8030035410107030801018260b800c014441c1381500904000107001e010300d00c11400600024000b0401150b10310104c2e071002452841c60b511942d5448008040c60079850303845050141c2390170325109091200c2c5007510300141080b6a0030410054071540e00300e2011075448510b0404110401048164a200c0d80040395070303006201c40c02c1c89546003102c41101503541319 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 619339604 1250 619338354 619338361
    0xb0c12070609060c0807050f090420040914040c0b0a02010608031305010801140d08070807050109030e030c09010f090b0f270c0403080f09060c01051006030e060613020f12 75
    0x40380d910040c030040c400d400400c800c01300c280c000d640e1141c04031004c0f80402c80c00c0c001a01036500441c021b00311954010800a82d8840402c880e0054401d882c0c3d08c04640c54003c41c0a01c0890186d03c10310703c0101c20100040b110f4645503486480080003030040854400c0c004c98a0800f09000750010f01c0504a00803d49444001e80c00d45801010007500c140390000e013012000051110105500205104020340580004032098840880c6540204000c40f44000d08111030008518280f24004986d032082d951380300c003d02a203007014a450394050075144034000920040100b1910510803608855081c0030206401c10540c0c002000740d00852950341d0081d8240c00d0b000c0150380c500300348d0480076070680b680103100d0310b841400b0082030066000003082c5d0070f4200043e00c92050901d0180c074034810018041c51801820f813030050b0940e942554007641400003e40e080c0a51030305806807541d115600401080545000710005221400302c00030704c0541a400a01003031132402c08800c64000d0303010f29900304658103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 619340854 1250 619339604 619339613
    0x902030d0203031006030207080906031b160c091a0f06070b010b03070305010f0e0c07210c06050c09030c09090109081b010c0c0f02040f020d09050f0708060609010b0c1207 75
    0x3c0c0200ca8550840035140360110304140a442501e03020390b0000d1006080038078000a200460f0302c0030f820035482e400d0b44c510790540356883d0f000070842c0d5040740030100c901e81414602004851900c1c0c20554005080c4100d0b000c001040e0420319088403011a0505403001c1a0004104540320307900015044071168000858607000000041d4001c1d0703801e40e000c00c026a600c0780c1c541ca44d6841c901640410341201c8c0c01054000c0c103000c0140c44058040c40d041c203120800001150004c2080d01640008185a002c0110030301840b07200d51540480348403903061414007078000181d19500810324451142ca4406e010030ba20050960006520715071007080d0380c0c1e41d99640b664800c0d04181d00b0403404280c1d820154040c01c0144190413182e182c0d40e000b0b0554107000301380e60800c0052704071403006464050f0f0a00c50f0002c1d046c1c440c015224200c0c054400740241501000343c050034060280c0042071250702020610a446d120481d10604413940e100b2405c1c2c985186010300e50901d40300ca0014800c44501140c40350602 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 619342104 1250 619340854 619340857
    0x191502030417120403030e030705060c010c0306090209061c091e120201061409060d06050a0b091806041e02040507170901140127061e0b03090a06020703030902030d0203 74
    0x840c0385041002c0c1c20300046040695030300c140c481c0c1da08050380a01080001a0003030782000140c881c000c0030385000640302c0000c500c0035000f400d009031a0380c0d161084a801c440d0076200b03200c003900310400150f141c031000c0c1003c280684100042400c007051a500c0210900750723154005404240e000b41c205540c0c04a0210280c20700790100c100f40e41284950580c0161980144603000854002c040020400512402005051600106103541106205040740e000491502c43d05214450b4034800041c41c20392002800403140c0c0050100040605100c1003150300440003030aa9801036100800013107411884038110b40c2c0d100000d400941185c2880188400290054414100e0420021140c0e0066860041d0b00e82aa42844604030003642c048006001d503940054440302e1030174a240103a04c01c0401540740000b160001d5121224401c04ca0122000003861180c0c000000d20141401c181142000f2458589070700c8115001010240e00003040320416000350040ca01d2660001d007520080d075003002c4080d41780e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 619343354 1250 619342104 619342109
    0xb041a130510060e18040c150c08070609030c0501020708030609060108100303050903070b2206020609070b1804091407080a08030c18030d030b090106030203070e1915020304 76
    0x4444604100003200304500c10705200d8100140007102091400506880c1c80c014000c40d141c000700c007111000c11441c000c000d114011442080c080348014584040c00c1e00f039901c040d503890200161f1b00c4424012a09100545001d160071100005c4d000c1c01610b0292506002040c0080865001082c0700081c8910b0202540c861f80080d101d201c4665208001124200d00888001c00151403404050001c00c0c4920017030710707251002030b00b16154282c40d507240c41d80781e400007a450b0300e00320050a2803030140c8251040900007008240000c1c03500c0d0400d00e01560300e172002800b45203c0f00e40c0c0400c5031062605440380b00841d104001c0c004101210302800d100105108001c1c60342414070036000b0004d00b1407000106004001d400c801c205046031070301c070346424455103c407000b400314110600551019607410b02010718600419180020380c1c0113118240603003040164030090615205104000807203402a8117400d03c004101c4440110200c10030302c541d00180715800100082010280681c20180c00000500a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 619344604 1250 619343354 619343359
    0x80109030305010614120601050d14060a06090602060c070501060302040207030e1503011202040b0604030c2606011203300e1b101101061203050d0e0c0609010c0203010b041a 76
    0x803da0300c800055952001300911844000c200b040103024002c00d0f600342e240c2041d81450110702d040c002e2441c02080d91501407180c0004581e060612840d0300d03266805074010507007800c10030030031031078640040d480300c500503c0c03100c400200150342400c00c9020b50044002c1c59008008644031200d40c2402002444100582c41c0900c08002d03000100170b0030300c01a02c0c1216508201100100241c4d400e0101600c030765850541c2250081c27001100140780155110003a204c100c440b0300c28615003074000f40340b2304412001e4102c507812001c010301c041e1044881084e012501400d003106400b00c039102c1400d0301c80310125040c40c000050000c400041503a9001a00c2c001e80a104440408810314990b00c40e2969041d905a031100d4552855400c440c000c18944c215001c0d51030000501c0380e0384000e8482040900b18084000650000b1600700003401882400c00c0705820300e0062103c0c0f076401004c5104c078840c00401d42e040c0506035118100b1540d094010700a1740b000503105010020136010302c80f1078400350061492 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 619345854 1250 619344604 619344611
    0x120309050a0f150c0c0605090d02090708071b030801030b0c12091f1a09060a0f06030c09141011030c160905060d0c05060304030504081b0a060905180a06030c0801090303 74
    0x1210280710704c0242070202d4004000d81c0c5001c0c43c202044d075a81d81301480c10f5821a035012000000742e581c40c51b40030310a4202c1d81300c4590314a040c0c00000c00e4001090b85d2740760f00b401c14416900109501490b07690641e640420024a1a2103044105840d401030181003000d1b0032540c03041100e030301800f00d196812810240c441c03a0203d01e006d410001561000c429201d9411019000065140307019499282c0100c405000740c86400d0700e8007216004a0100e8016170046601c1c4c00b00740b08041d50041c6103900425a251100c50f4100300040082d0000401c4030b5840204202801c0ca030300d50b0302c024022600340c5490310302200d5451410042c0c0700c0c0356440070310481c48240c0c034180c0055404d0504000c030710a050b82c0b01d0003696101e0700b4842045003507040038100340c1c1003120501c004643c0074410045184507100002000d20040c4094040044c03c1d54103811940c01c01041c01c0341000b080e140e04104c202e0a0394032010001c4203130707189610100100581d50001d8641d038440c03440010303045010340c0580d0a543c041c3d074090 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 619347104 1250 619345854 619345889
    0x30e011a03070b040305101a03030a0e13060e0708040507121103060c0309060c130f090e0c040c121d1c0906020303150103020d09080408010c03180c120309050a0f 71
    0x100d10fa40076a220203001d680158015082e82d10b4607602c40e81e440c0b40010100d410a119150110b0301e1034001185640218180320141362089c900880818000300e42d1074018410a4108407101c100c800c0301070b00360030a1000500100b000c200003880040040c0c500b0302c8205414041d2418004001001000c1c0107020740142000704224031403503000ca078407600700c040040c403498032034070749101ea1580b001003030507030b14620180045058144501070900614501101081204a03184124146404031540d544505d207080503c1240e0390f0070031b04148007101d0000c00094450f0140110104508070191003072800d009402400100c140140d190b6628440e00c0e9460300030440d05ea000590f643e110079204807044155404441e03003958444d0b00185000d07184140301089400c641d07550f0ba01581c020790480034259442d40485c8104a03451f201e5000300320402014000e1b001883c0d1a06242600240508050400c01022150034580100e07250401090f005c1c00f01c00c4c900e03a5030186410200580c1c0a20080c207542581d48 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 619348354 1250 619347104 619347119
    0xe0909070518042406030b0a0e0c0f01141b0328030504030e04050a0b0d03020319020a0f0f020102070806040f0309060f1e0e130615080124030e011a0307 67
    0x80c441c542c4510783c181035807030b0410800c070308801c048101c13081c46032a2071011001540c2c80c040703540a000c0c00704012070340c0c0310100b00f258144003818100d1401002d002032000001e030380c021000300c50001500e0f940769990301c50030009240007851420141003844009074504040703040310549810807403402121402240381c04011002d54a007554064000354941000006c0c80ca000da100a402c81701500001510204490108503d0b028820090340580c101150030659032048481c102c4000c401e51010b07103025810b59a0b4140c100d03400e25006401001c5200c4c0304001c59000300720b006e0190500e0740c121412850185080310b10341140800460010380d400700f0025445011f40c0000080082301d032501c1c0f9004100107444480d10008a80d03480801a000c1c2a070300391a1659040701d9401c07042408007044d1981041c06980c00c29045c4160710b030402c0010001085604826041d071100707201821000301da0178002100c2203020700300300102030302c20f03520740340d0410001c2e1564180c0a80000d02a42580e4000f41d40c0c140 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 619349604 1250 619348354 619348399
    0xa05060f03010902091314060916050301030f0222020c15090a030e0f100201051b04081002130f0b0a020d030e0c15073c0807020d030e09090705 63
    0x4580440c184010300032060740d0b0700038090400b00074007100030a41080840fa000e035044581ca641000c02c1003010b001882c10045010340d0b2119000c40c4442a01d40240c0005125100501c00501190351a0021104564440e071025100703640c43ca00c100c560300c0260030010020741c080130825545119640c4940c2c210300107200302610500002c405018210f1040c1c600340d40100095200640c080e03100e030302600c032565800b40ca02c40c07400c0301d50340001941e03d00f1484904240c1040242941c00320750a00080004540c0080c013400350030000c58015807103400340a050309001d00c0c0381d0001502c4205d070341004031389080c0300c0c00902282007080d400c86940b1011800d003030b13040350007941c100c1691382c2144a80390b40e50308182c4d0403810458000c403002c601d0005540c5890043c0348200311408040f50f102c001126407121866200312988000180e009030641582c0d031500814030402000034000c480074603081050600070b584100c4003201c0540710304441d20341060b400b0784800890081510070301d0242c1e06c00d07144035135218 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 619350854 1250 619349604 619349617
    0x2a020409141b0f09180a122a080703050c15010306020702241602060f0309160b09060d180c0e1902040f0501030518011a010908210901031503110a0506 66
    0x4c224403440c1e00d884a01501d0030380b21800c210214803a4a180380001406000f8075100c2007056558000c08400c482503a50511191050903045c82c8515000180461620412a0f28540d89410a41e942d1081940d0702810114031440040741181d90030b000209000e8180c00a011140c4220381082c8000f00840d110405c60b51075441c214420700741032004480003a002c0324a0b10010b40000d04071410052500d1548071a030340704942c00e094940190b0b560750380140070300c09280d0203482c507201d00b1800c1c20b90f40401f08a00f400b80140d00c80105458100040d0808400c01e00024881d030010078001c025a218180810104410b992542081900c00451085030201d4800d40b02511191460003030800d01d8580110050a40a4101c00c0310244031200b90030504024815800b25145091240d150320000000142c80301c951984203080ca13422121305007051610f81418900c0c0341d403801400ca92100f5001300100c00400c8410b11110300403c1c42800482405042e030a40c0c10103c100312014401d8a40310414080d0901900 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 619352104 1250 619350854 619350859
    0x306110403171e0a0201020405030a140105090609120a09030812041412040b030c040506070c0305070509150d030908010c080108060105120a060209011206120201030b012a020409141b0f 81
    0x107843c0350091940d500200078119440c070015081036214000241807180124045507034050114241c0c85103182801a281e202074440040c111619241c50307074030745440601c4000080040c0015180e481180911120f00103503401240c0741362541c1d20741410100c0590b0581d404ea4005400320807103003840c50000380307805a80c001e60f0300b0f40e41481d182c800c00721025000a0610300ea0000b042c08045101c0e11460007034044140140c0070800300910f5424140d0401e441c81d001107000f042c04008200c1024204002442d020303009680c9110011460b0504483c0000141c0080d221542400c4c101d0014503880068a416542502c0550f030140e40d0700d40400403003100e5154480d0301c9403c48102c01c1c0100b089c56028000050041c1480098840740c00d00407011201c0e42e400030700309000740d0107480c2c00350350741407040c1e09402000703003000301503545100c1ca008003121641c1c10f0124800030540c0385104640302c5820440ea255800003c2c1251311100d44880358503021104655101c1c1a8400322010301c6203000140a110b04001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 619353354 1250 619352104 619352137
    0x4062a17060a0303031a061303140601030305070b07021f09032601150c0c0303050309100e121c0510080f01060303170a1401080d111b0118030611040317 67
    0x115603080c5c0245c1001804200005c550306a80c132002e4480340010112403441e0848414000d04510300b21100c10020400d1821170f5021000500010360400110307010707141c1101d00d1010b20740c0c0d1580128940501180e03c079080c1e40b0110000e0f9284c6d5415000b50039654401d0316071241e01c802c96680054440f40c0c01346220b072180d0403840100054485089a10341c1018145813400c0600200d886550020495500450000e1400010005810010b2221004050300c0420a03c8540c8010700c11540c0e90410a8040b05421030005401080758401d24040e641d44286010502c80d615085c520100201c1d201c0c403800685006000554071720280622a06050300e40c99100d001c0503c03c40717a603545100c02c00a0103010410f50783c0e140c07440c4020304500401c2c000c0910b200205103550114400500742a00c1302e81a104542c084480c5401803d0105501c031581c841c2071800400b0b01c1d4134440c0c4580d4400c92580050300035460f001030541070312074200050040c0c038000d00c2408c0150080304d080040340d1048407299181c0008 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 619354604 1250 619353354 619353359
    0x3071203020705070e07210506010f0e04020409290d0f06050403050f070c090f02040501021b0114070501091718090703151205010f09170304062a17060a 67
    0x41da0242c070099002c1c108485429031100e0301d441007a40d00750b4240300402c1c01c00d5050700400000d2650502c00c130070510f0081c071850600500180c0000d0110341007609200c800c20314680a5100e0780d050718020080200240582e11002c03012003250241010700b8000405108100b411508201c0000c04107550711840213400b020640d21000c1c01410301a108600b008030400103501290340100c05810803900070b42c5210082441c2496200803203050641204800340180000c102c507a03008140c0a00e406004151030f80300d02d00c2440101c0389101c4100f00101d4590000c1b9091050010562004070194411201064034060340003203100b0307a0081305455941d50b5021a00012141000c00003281c20002900300850645803000080303405400c16084030020342049100c080c18408240100c9503c002d002d60200100c034126115148103020000d140009241d000000c03d041207456803064405424040200010703d035075104240758140700c8003002c4001400a449040d9019143c80c00c140150f10081c07103000c40d030f031 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 619355854 1250 619354604 619354607
    0xe0709030c1e1503050f0105090c040939180b090f13051e2d07050f070b0612151b09031b09010b160204021c0f02130602030712 56
    0x28400c0100520b0007141c00780020359603a0b814144108151540c80204003490440700c8602d04500581c03041d0b10452903402880319608050003190150780c4240b00128075548040306d6030301860419805000004510b411800190003d03105d885503100203a900e400b07440201c200b4410f100b01c071030f01500b00500c2c410000041e80c0d00c0c020f202c2c48824a0050544200101110b082800b201d40031a6008094000725280000b880d203003141c0f1a60180d42d01040f1b0202684008101c488656001c01548010702c480003c140b255000b1002c0d591118481ca02c12940c882c0145856075002805442c2c00703008001c0c90308450400b400c0410805101507201ea032030000c0790b440400c5065001081c00c901c460350102000300c22a1501c01f48030200c401300c1c01c2188126aa4481d80601c0a1004140d0006800300001d002c110b0000b0b03104408080c0aa130112405615000001d41c001d4030420507004580c41245008581013001c030030354000c1c218056241d0180110350f41c4e5000140d8403442001d2000f05802c415111140b0020b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 619357104 1250 619355854 619355879
    0x9050109051210050906060109120f03111603030207060905030307020906060f0409020d061410020c0105070201051b0106030611040605033616090912030f11130e0709030c 75
    0x2801d520b42200c0400c14842c2c3c00c0c00480308150744084068012004000040d600141e003100280703021078a0401413041500c1e0040c4901c090100142042098040013080c10420804c8090132038a01041c011000e030f13680f402075510342c07152003230401180c500800000d0350b180c04000e84807041d030068951002d56861304100291350b4080e68001a080c01c003480085045480c5202500c0288542d9000007000d50806880c1c05039030b20380c0c01b40c851142000107080c1040541c08600c0b01d074280710a090041d1664103520060b03406000c0d034030302a1105c4010080c0300006e080c05403c16000c49004071010400118880081c9801c0e20030760141102043c001c20118000010160f030600303c0c40d0003003c1603000942000703544441c6d459281a040582d910244c2440321604d04041072500409a41c04100302c06189540c275a1281e55214401c4018107a031107d40c002c1d22030b0380e0f40003203003001541051955520b550707a150302641c41d90790040c542100c0ca0316000980982c0100001000e60b5044000c090101345015181c0800 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 619358354 1250 619357104 619357129
    0x1a09010b101d040e07080703110919020904020702091e010806010602070608040c050306040b07110307020f09150432010506190908061e0f06151b060403110d0905010905 74
    0x8299921080c0341a00d105000c41c5e00500382e241c01130501c45145040030301c00000450041ca02c00c000390070900c916030403c00d403411109582c0c0c0f00050780355800d0000140080c0961a00a500141c440302004101c00c1c10202111164100a500364140d0741c9541c002c50703440c0d109002d00320140e0720205040c4682c0f070081c03884c0d035401440b4600c41c1d203241f500c0c1c101003414020140c804a5004543e9401d000c1880d800100401058004000850500c150307030300010900400d1612250058030304002003108034800300510340d00000701034020310501516910704844a1051007000801c90851840c00c1d403e04001c88100d030403248000d10080c1401c00c0418204014000785040c131007440804540094031601c00d00c03002e07100d0024111021030031a45817006150760031000305010040101d09040004e140c1c0c85030341a10842400303082c000c0e110009a0760713071210040c5554225009114403001c020805622040019100c0e4503041034860302007410009503011000c0740150b9004c00c1d6101001d000904103040701028 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 619359604 1250 619358354 619358359
    0x3021b0d0f03050a02100b36041401140f072006091c03181e05070305030d0b0a030b0c0a050405090403030c020c0d02090a09030c1a09010b101d 63
    0x14240c010703039514044044840c1d04502040021822a250903014480200200c1c88203105000518440b000030b1000d10b90103034000c40e01030f0010a45200d0545010020346c0b074036441c0e0f10703403a034034105410f2881a0744000e10360202c10707608000c1842546408040c01d5401440b100d51504d24a4607500c0060f107611003481307600400f0034000c0c840f256040c0c0c020007046000d14005405014080c0c503646244190f4504a01c0903410300d4102243d21031541c0b03182141d0049540c00c1100c5024055400815254800a14401512920800302c0200038410088000e01008008090811403000c445050002c100388511010b400358550200042c007012031355005102607195450414900b945507400242240400e441c00c0c0c000a42e5250030024071074040100c018890700c1120340c000c88090070f500158050200809100c85161074012712801c16000b08018080c8590241e803844074003072800d002c1500b44070110b60001340c542c202600781d85281010550403445800b03c0d07a03080c1b03001c1100480c040b08403040707810068 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 619360854 1250 619359604 619359619
    0x1507050303070903020901060302210402040b040c0206100509070f080403031503050307050708070f0303110a06020406050c060c0f0702040b010c150c030b060a0507150603060221070c03021b 83
    0x2441400110300c52403a540740c10075a14103600602101500580001090602c1084234a150405010814100941c407076000501a540d91000c00c002e0300582e20180d40150810804025140c1c000c1a2207215501240d00040c0c620340d15020440410f40030303110ba01c0400d1000c141c0304019171146880560090090030085041c1010024140c02d40c4260751068503a030f08007285080c10000240145401004060002c102903800c140358004000d00c01e21000b001d02048040c804826503050002c042c1d0581c00c4003046440700da554601420a5124047c0b030119405841e000908a001d43c10656a1142c00b00241c2d6003000c00550134000104060840d150600c170141c900340e07002407052181d661101e61f0941d4046803007007807201c0250a4843d40c110980c0301b1101805410000c1717600a00383d44800f900304500d20030844206240c2c81c01441c550b0000f5045e07a000254185104500c000710903007403c2c0b5500307002d602e03a448100c01c03140c0603643c88000f00145c1000710450207011240c11042c424480052101 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 619362104 1250 619360854 619360867
    0x3011b12020c061003140604050c0f1504080105100b181203361c1220030717092409090a0603020301140906070f0309051603060c1701030215 62
    0x403840c0120413110130000d100c090300d050080103446d5031100100100e0b24000d014509261751401c0d103c48100b00a18000d0300c540a0040c81581c4401d0481a41440880510b9440b5110901d56019040480e8038040c02d47e200140000c0c540740300f90488941c0700c44c4c0c611141c0020480700822401d40c0c00004101d0241c8010f116070403e003120103d62000e03808100701c2071005094030f032600480c1c031030910700c0303180c46060010030088807a4461520000180e60010384000308001c1c4100644045405004c0ca10410203203013450a00550000000c1515602070409080301c2e60300c0c203080e40c0c140d105140200c4e4009401007680d25114110b01d100c02143c601c5584000d04290310740c0c021401c40740c4115000401d05441d0142041581028401c48407000c00503480028a498015404e940d9840050401c5040150300c0b40800c2a80784607078003518401d540f001c1a40d607101226203084a0440d21404203490b203174a03085440240e68001c02803255607035580c140c0340816a1031b60702082050725858031900d41065080000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 619363354 1250 619362104 619362127
    0x1020d020309010c020d0210030f0b060403050606191a03041b061e260a110a080408030a110d050f0f060d08070213110d050901050f0103060b180a0c0e03011b1202 71
    0x23100e030070156a03400240e03090705c1c1c079041c500381c607030b01d0b10709a010300c42c06c03c0280041500800c40030340c410b00690390710050403401505005d25200c3c1d923101510b501032070451503072150400402503001c3ca0244201c05451a905405540c030300c0c01c103120303d00102d81d808064010400e44540756061480113414000504403101e40043e080b000c0d00d008005910904008019400c0071902c103181074100c0784200341e0b08040c181200a021520081d1020300f4002001c00060301d80e480310f4100000b003910103c0e02540b9180e031a0f0706031000d4001600c0390303406110020005400e9070314800400c0c1c851040244401c1441025803109072456110751400da0f0803030352914180300414201d01400c0e1500c1c00c0103146558400704141448222403015000c1c074900c0e41040188800c0c5e00302112280d06494010320001281001040041c094031415040c0c09100340031001005134110842d400200340800c19220a038441c0a810708040c00c0380d800c10107109000c0d900c030388007017941c0748940c90700801c6107900d8400500d030085074000b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 619364604 1250 619363354 619363369
    0x105060319120216171c0c02220c03020304030201050a0c20031201080f070e101701090b0f012d030303020c0f0a081e03150105161e020f01020d020309010c020d02 71
    0x86522503185070f4400c080a0b0040110360000d4000c1000003040c00300c1400007d0a10b107155501a100c0e111076841c00d0031b1002c04030000f070648003440c0801c001160307070250054003a400484095025529140c001883c6101c00d001e01e01c1d0340c2800e5511022907203000d4400781c00c000c0315004604150b10090040440030200040150702900c0040010400b0884603458245004500d421104030340c4074003010320003003501054511058952102d14220a500e8403241c940c01040d10000c050711511128080c440c21803096000e02d41a5000114a054000c420302d0340c1140551181003041c801102c400c80800110348258090100420240d00340c0b0a140240c44a10340740c5044030100341c07801400040c2c01c024116000000154940b022403440e411403812420500340d4001c0001c11a060000010f41815620320300070802d59100d0740000028141845010060b00088000600724001c4003d1200c01d0269030000071041d41009140e4000c0d464403144000459280b12291070490704021484140c1e00160344c0c610 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 619365854 1250 619364604 619364609
    0x1905101710110414011b1e05060108010b0616061503120e10020c150f0f070506060d05100e0a0803040303050f0c09060d020f0c030f0c0105060319120216 67
    0x300a140d41d24008400c801228080035000051080402041140d6035081c9003250700014242029034003506100420207801c0c400d1a0000d216042465284181e00c95400da45030445008504075001030781c80781a114202c030203181c0c00310fa1054042c8800714200d486401410b03041485030f24089600351070b00e0541c4c03598031003a03042281d01d0b5061201d1640120352207040b100220340115000c0c9140700d00d030705000e510307540c2c2c034007100e0700030316520700d00010303600d806421202d813500070000715030b95104034182c0d40c115034000101c112818000c481c04100c281c600302c014210340e0360300100070701034010550503400014200c0010341c11032030003034000100202d040c00b4003542c49030340170f502d0100d614602000c02d0910900300600e040e8070013106200d0842d03992a100d080c0c2d981440d040760010b0717641c804054660320502600034200c1e400c1c071002802140101101d00a00505800c0784001c2c029a2a600200760300e44030000b5894201c0e0100c050340001085008500d080002e801e401510f1000ca42c00211100310107454 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 619367104 1250 619365854 619365899
    0x12082a07051218030d05121b04060302090405060d020906090a06080a06020903060709030c1a0d020d0207170408060a0207030302130303180608040b0c1e0a020a0218190510 75
    0x4619900f024002800414040e40210f024080c040e20461000e802e50149003075903849640c0600010b8030204107c424242803a086100d0980c50316a2604024042c0d8405050b43d40240c1c203002c041029030910102c0c11401543c0208860500d0b0307110003d0082444e8001c00342c1140e40d440c0c100000380e085090086101079801000056619001041814a8540b003d07000708d0070010110401c1010401e2a50f0715002da901896807041820480320100420b405021707040030311180f00090101c0301240301d500802199200d8544001d03048403401e80c88403680685c0c418a026a0451b00004040161036402400c291781b09080060420400b6610107009100a80045000c1358141450b543c0503840b0440c208000c0c1600e16060603585060703900c02018044c0603050f0303940c41c100819140360039515203208442140e4400d603030f07c0c1c6816007250020b541d400e400750b09a004480c440000301300744c03003011b0038248100304414102c241c400034010030b0002005d00410a00c0103000440001c04c1c000300940b40d05c071750310321503 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 619368354 1250 619367104 619367107
    0x100501030c0509010b19050c01090804120b070807090e0a111602040f09050c0d020a080d030f11090d02090619030807020f0913030c21050712082a070512 67
    0x2c11080c00402c0406170004074400c04203115844141007042102c003540405403402c1c40c0c84516103034005014000d54400108482c6c00824041001e04050754480d007110700801464074962207000b4140c40c0340b001911070074005070080200307210343e840388040c1540069606500080400d80c80c810b2080540107942c01c7d200a91004d00c0a00a52070907008001c0712085141d030400c01d4080554034599641c04018445001c0c29642800d80155508d045428000741031030300903640611385042c802070091020b03070400b000c0c581c49c19002021040003c2e054400c0100c0141000c00b0708a81038080144113640200003030b5015400f0800840703015104400c2c02c0c002c0d0720528889448000300c0c4108080003480114180c015140c0320208400030000d040e41c0400150181000c40d1800a242407142c1c0207404114030b4981000d10181c8809019405801080340a0068039024407807100984115540e82c8180c0d040c84400c2041102d0b81d40c2c1c2c91000c07600740240340803101518646011550343ca401c2c44070705522042d40e40710 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 619369604 1250 619368354 619368359
    0x1060302130506030c220b131d010e010b2a03130b030606070b09010902041b0e0d12050c010e06070206011d0609040303050c0c0f03090307240e03100501030c 69
    0x80300a000c002e42002c035201c42c2507241c403516000f00d500400e210001a004404c000740c00320340428205101510400b204255600e00b5005602d00b80c1600344038840c04120168a000c0c0c414684107940c6042c0c5844202c00c3d281a4a444031800880d04055a0b07242150410b0f060040c3c11422140c041d01c8840740c00b000f4503100c107031030120561509040d82c44900c52040800400c56150b50b803501b19940030394407540029a80e01e503265558010806204000d401915003c500068801d400b00c6140300106143e0340c4002c844d40301400c4c49461074a54030000c00c60b05103d0750b00300c007050050000d418402040d000004030005006455403a015080daa0300000d42c2009005018042080000c095524401c04040c141400c2810208005600c01000a000c0694941c00320301844841ca049072007107581c1f5812241e000482050f11389d00c0c4c1e480036565610034840d5400002d00c0b006102d040f07081d14640500d1051b00140750160540307401114240c2c141d4580140030403290740418a00c2030b2400386004541400f103a50 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 619370854 1250 619369604 619369627
    0x10c0b150d030f1101091136150f030a0308090c150406020f07061d040e060711061e0f0c04030506070e041a030a0f11130f06090e031207090e01060302 66
    0x2032141c5194140c070390401c40104042150404016155582500c00d03d160391382091010b180c01a900300310348288c0ea40002c0428040c080540c0903400b8141400a048a80c0e00f0316082010071911920480d4158100d4013070b0b100482c1c00340030510741c0100164107032603100c4002c40000e00140d003a0520032001000120302031048550410a480c0948254401401e144d420648003038030004071400d130400c0100c048417001180f51510740045603030101180c01c45109040c03204004d064a0b0229143c0e054520a0700e0000d0007000800814980750009602c4500f03036600c070b0a0745903070040d400500310032010030104000000600304004852140d206680d039401c2c40446142000203a440c0104600d0488000d07a220519565020820b4400c00b0360007115461040b2039481c2180482280400d4140c0c40f01e85402203d4041d90f458001c0c460036a111041005003503110145c203c00c0310300700007150010b68001e0240d44000006c0307605003a00049a82403034580302d556008540414a000d03008080000e070007040d040d5408 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 619372104 1250 619370854 619370867
    0x102090d05070305160b040e06040603080a02010c020606042304060902062101080307150e01060e010f06140c0d0f110105040f0b070e03060a0207031701031b1202010c0b150d030f 78
    0x107418145c615801c1c9260103403d41044c0603074000c001031500c030003021444550361075112500540c0c1c00340d580c544404841a01a008005a000e080b000d0700400d000200c692500b03101d40302d02484d10003401644c1401c081c0412401c440cac014003c480c80c95403040c005000d680d8800c0642080c8180350400500700b107000c1280c413162078060b0300c8881a6802802800300148140910813020702d444900003c13090b04e0030796543e01616282c1d000c04814015140040392429085031202e00f82c40302ea44982c04104460341915120b8418400c08000315045102a2500c0900c41d000c491242016840c00f07403038418007444040c1c2140c0055030104e800c845085a9003041000d044103040d80051745040103255589154003182e20b440005280c0010243d000404100b058050a80b41400c201e070504807a04940e180d140c46001d03405030713542900e402548040e0000700c0f0b02d103004c1d08020341d0360706030358810003100d40f95284402c00c04040e0031081e0380d1005039079104190311040c5048403010b020b90b035100f00400200c44040d044 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 619373354 1250 619372104 619372123
    0x2150d0e0f241302040609021902070302030c0904020112020a090501031118060309030403050f0c151611042d1803081815071e0c0b16020102090d05070305 68
    0x6030300085800c2c0341030700800e0051509450b82c10024040d03566078004101040b000300b680294000d10704100400c1400c490750151540310f400107140306152100050503691040648002545540b2018008041d828100741c483c1c4c0040c8107042400825554810700c90a9810840441c000540c104400304801e40c1d050085a8011850440c12460b00c14441e504200303080c8070300d000b0340c0540302c00008038400070420001c66000710b42100907a40f007251241d131000d4880b6240b1041521070303003a80a6104120021404a41e5800800c070100b205064099458449010300c80c1d603010341c065910b03800b0710950100220082242e48401d5140003041103601c040d0760440b004e017100b509000305280c4580c800203410245040d0880c00c0c2e810503044268400403200c1c902118803101c8105031011030b060102d80e640210300361a580303400d103085484007803003036000712040640340b20080d280d1103120700803581d401800b190000082070720f0701c0058a0099180c0104200003a20b06044415500c4078108006110090050521 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 619374604 1250 619373354 619373383
    0x403020601050d0f030c08090a08011409011413050c180406050c03100308070c2606010b0f0304030e01140f040e101508151003271203020702150d0e 65
    0x31040f6aa440e2010304450101004040c4155048140140709a07902540c6840303c0c020503410440d6240c00700c0074007030040b13100030000070719001d00440c000b800c0600880d4a8045e52550b28217080d0f8480e545a100c1080401c0165118000c1c00f084c40175a40340c400c1340603a50b01c0c06d0000c14500b070400707182440031207200030a0003402000600a102890300c0d00500317007040b81d40003410710ba11030b01c0604040d0407030220380c1d100e14012160030b80007103035017101074010300001900743c01920116030365003c4050702e034460000d0142621030200300040021303014200b0001c000320185440d0f0310070ba065010320407460348944400504500301180810a4100c01e11000c5d40c0002011000c5100d1841e14842e4240c52104407000e8043c004910b001500010300e4600c9046003080c0140205810030038808081c006020700741110300e45c0303006c0842d60f584080b180c00c02d07074014540c04448941e05008600e0210000c2d0001d1904a074401c80b04000c1182c80c01c10301000e021034407004600016803022541c00d49145c079030845045407 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 619375854 1250 619374604 619374619
    0x50702060a0b010f0e01090902120106020607020303090705010c051f020d0e07050a14030a0b04150b090403020606061e041e080d0c17040503010903080f060f0915060c070e040302060105 81
    0x40d0740f039038041500b141414080c10004048070b51031700142e50020094004814840c8003080004070814030071800d5040300c186400307803140b545613403404980703d00c0300315448202640500d01c200a20b52040384c0c616400e600420039905620444103072882a1100d040072029030f0f540118500c0708000c9580302c4d05c2e94204c1000001c02145103854082801d400c194454161007102034040c85000d9103061100c0c448150b88514481d5031840c09281840300504e02100b4007800030320700340d05c1c0301c56400c08000c804d0050382c0640080c644ea0b41c0d407c003003002aa12403406c10404c0001c4040f140c07403503648280980041d00106001ea203440800301c0c0614091019036009117240c0d400f00c514204006d8200c0000c40c6603c0d00182a28441400c00c1c12641052056520281d0950300e060f14807424158001c038030501a140b105040411900e0b450200903102103060000f9900c41c40201c0499005407901d15840c070981400b80107103040400e81140c1c40d0901d0b030303183d2010a000820340f042000b01a4188415400341904807a0032 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 619377104 1250 619375854 619375871
    0x9060a030e2a040507020a020306101a1216030608070e04060c02060105090a02180a090209241204050703240c080103030c0305031b03090c04061530050a050702060a 72
    0x11110594a4a04280107039904e40c0840c0b40c0d14401c0c80365040c403d40240c110381150520304842140b1400500c10203200341c02164000e04151f840310304a60b042903910a004185d034507088107444000e1116003400045c15a40e110000308020280314080040071101a2040c0c54601404c0c01e47c1543d4640d030b1f000c4d007103402034801070003a580e800035480d030002e001a40041e122000d044480004186603420150701100b810000140d41c501d0390000e000000e029944141003001180d00f14141070400340c090448502c0500400c503443e603200b011164807500400c211141e0701d43d2030b02d07812003190006640100c40300c9010354044900c03049020b80c000c10f905070b2620300107540c51078038010020030049070020100300d400400304031203211a03034030507141c64070034a5010f030b0320301b0080e1400780e0355292110018000d42c102000010303280ca80403c80b4440f01c1d1261200c007800c0005182288403102e419403041030030555030500001401507881400c2c13245084110029881c01d008001030b2501c0401041200c030720342408000c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 619378354 1250 619377104 619377163
    0xc060c040303020d0c14160302120109020901050f0d06021602011e05030606071b0807080d0201020f0306060309030d110703030501050d030906081315050403180305030a1409060a030e 80
    0x44c44014485071a0070b07000030700c091610101a510f02d114103151032040307840380304c0009030341c010711000c80340308131002d80c0d0380c90301508480e00317075014804060340c01144074004000703d041811460300c6800f070003481c0980d4000d003a60707417804036001400001d013a00100718005085503084440c2034401617985440348182265524010200c2c4001849503010b94804541101003100c0005a80128040b03d80d500070940e85400580e941c4521610910090740302e0500814640c0740107108845008546140c1d0301d00c2c1d030b41c401e0180300d200d41c00a090707408c1c0e82c4010800e0b0742514800c0c0c440d0181200c011444a90341d0009428028169481a003041d48202101220700d00001e03088030541044600030300b8510403540c1c1300111640305400000c1c0c05007080201d0b800308102082c990b030005220364440e40790100c82c00c8010b000300c3c0c510529808014060760040041040d80e601843c5140003040510401528100b6a01c001c150150800c240c0ba40110f501d07018001022a0113021651411000d807100e0060a403807000c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 619379604 1250 619378354 619378363
    0x3030403032405040c090e0921040b03061908160503160e0406050a11040803040305010c05030709210c1410110d08180a0c080c0303040f0b03070e09010b0c060c04030302 74
    0x43d184999507403100324428a000b03003050801000c2e4010402d001c0c1c9030107039246032a0144641c42001070f003a008100c140e001c0c140401d4030140c4611407550f0307041d90f13141c5051000c0c1c00f562080d65100030300340400006155004001468100c15401c88020310545014281441c0400c0400103605d1854007400070b2111040401d0560b5005400100104003501d80801100c0140384045044489960005002c20f400100100420849101e50002c0055201d82c800441d494001030714198001440c0300c8040007007c003444c00315511525103a0100c18001c02940c0c0e1491140b005c0e522030880c10580700161441c6152000114210103a03900305441c20301150f095540e02d6200440c1400c040c0520040030034840d5441c00100440140004102c8040030910b00706561124110301c600b048500c115800d07050141408807d8500303c41d0042174440c1400c0c00c00c100241351750401041203003005a0009851426581c081c20316008020785102e40d90b0307500f4081c0da19810703c44020420001c80b4010401080020f07030004 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 619380854 1250 619379604 619379609
    0x7121d100c02090a0b060307050702240301030201140f030a060e100506032a0705031b07030c140111071e06050310050405091c08190c020606010e0a030b0108030304030324 75
    0x242c020303c1c40c0d82c0d94122000184084000d050300001c01008004c81c6030782190013008843e00031581b80207c100c0241c41c41010707098034820401560010b200420055000b1031041c8010005050a0742c20b1200b210740270081d60b0421a1440c4001c0c1d103071101003141c260310b12140d98000f041d83e03004480e01c3d8180310100b460b40c4001b410309881d05480441c0412030300d5041581901c0d0581002d041580c501d42400d22680d280c02c40724054000070f06280042001c901c0025105040b01c1d130001d8996003151404030002e80701042499440d052021303013070002800341070034032143d005000d082d12203104011161400902089540d0071101c1808010024003400510003000103084880032903011580307640385406a03007403905404100e1400c803420001c0100307042d00f00c681070b40700da0006a003142c0040720f548041d10554540508a0b40540c22410119605500c25401000300300c4018040900302d5560307035a114040a1300341c0c00a100c44d0004000c0c8010550f150182d204c07241380e813064280540e060f0044150030480e051 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 619382104 1250 619380854 619380859
    0x1020705010e0423040c08071404020a03091a07080603010903050f0706020412051506040911010305060604170304140a0b0406080402130504050d12022a0307121d100c02 74
    0x1910b100d9259241c0c2c01c01310200607190762800e2075101249203001d10850540b8103c4842c09000e00204616900085540807a61400380310b8844118090a200081d031103020030004164442c025132f000715004908900d014003100c0801c10540c038001100500b800e4000d1701c96446079060559030310200e5805000c0c0c0b070f005030704681404d540319000e1030001c000f0300c03440e4000c08c601c18501240038140400490708800c4100040304d445555614081040200c6091400080c2524201d110b09056540710350b000991000c07025241038a06600c0d294048070400341d400d148040c3d0743c00000d0034401a1036049414482c0281503d40c2c882d0f507030a1043e10502d07030049014250810091000103000c0d1f5958202e03e55134000800307410030141c10241002c41c1c440759015240c1c07020400d050200008998648200c4404041c4040e03410107100f1015058403011010180c0ca0039a03200a00c40c02000c1640d04d1018019403185460b941502480000131102c04c07090f0b2482c1ca44110085110454482d400107068200203504 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 619383354 1250 619382104 619382117
    0x9230a06080105090a0b06180c07050f0613030215040302031c090818033a02010f060603200c0d0c031115060f300316110109090b0102070501 62
    0x150600400282003079448921190300f01414403030018404903980000c68000e00c0e0002455440005001502c01d028025213004d01840001402d800311000290440134820703000c5d280c2d1851810721451800c031085d10140007801c0c44039008400c2540401403004c0180361445551024641a10040c2d00e80c0202c40c40306c8030042035047e00992200a95000e80601d41e40a00c10940b20322202d040c0c9148914500c2c0d00b01d0081c0305801e43d294451700000702c0c5c0c20b03807048e050001d060042080161078100e020076514003400d540d240d04500740c21201c9802400060651a074001401e000109034410901d007001861604191042103056000705000c900d11165141ca42030149013000d03a482e0869080c400030407a185d840c0100703686050001c0c0001c00d054002d2904442e11460503007030340c04204546092040b035240c1c4903a8001c40704100c5120905403d1681404015a41040100e50252800c040d0039001150052040c000d035101070340c1c028160702d014060202041040b0602200041d40c0c0e2142d0f401380d18148601d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 619384604 1250 619383354 619383361
    0xf0705130c0207030b0106080106080603010b130c0306120f111801032612090f12071515030b040b0c0403050c0d0c08030f181f0305100905130c0923 65
    0x3c000d95401181e0003000d400d41c035a96110020420f00080c0034640008034044042446031505000300022101c0080c20141940e02070000380000745140d68520041c50b4840d000000c400746641441900e00d4000c98001429907850b240440b290030303004030788a01c03801405403074440000207440190f05582d0300040040103801d080100c00f074541100038010540d540b000484a0310900c4414106000e1aa11000c84468058100c00a920f0705034a0f982517403890004d101500104900003c8050705440f0300a0000b4591201c03a90a005010540c00685000c0d00b0310301400100003402e85000c2c2d10000f00c412440c10300381075036503103500c4e526070719489445000c80105110601150085d0310700145015001c03207a44200c3e14681c03850903000040c04080c0d40501c012508102e0030844582076031881e01c060010221030815030b0540081c03d01822503806812601e501043c072440c40c0c0324950040703c10728000c11468030710740360000301d008660b003288114a0070070f02c002040300341501c054524510b285003111690754 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 619385854 1250 619384604 619384607
    0x130201030b04020313050618032a0a03080f071701050915060a02011a100801060507050c03100f0e01061415070203060705031602030405031f090f03050301080f0705130c 74
    0x90001050b0b60240c4000700340846105a40320403402c0c00c0c42102079501c2a40c0360400150340804010b50760302c2e030b908101b2a4200300c1c00107024005681305403940c10f1482c070703005942c2d06181046504089011413440303814840d143c86000102a40114103241101210303220100a1791a0003040c498540900091004a0215a40354851048101e0040c0c92551034001d00d180090280100e50040b14800000b007074400c000341031400c4041100b01c07068444192a919144040ba443e178842c0d40240c1f0980144c00b1941e80d0b07543c0501c008603a20003000408101380c05505017550450340316004079900c0c5c5c0c0c580f0104000d08410b17a602a40c0201e400c64880490b40012030a441c070f01c1c420034000a504d80a940108205950072001850044480405ca400408a500c106a035684543c0c00f40c030b80c0c540e00150000d80c49103d00440c88a8800191300041030006156503514010300c0b500108502085c0b02100500150300100b040c50000c80c00c0800910025144c107012425607003e840423021440d071100b10042185 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 619387104 1250 619385854 619385861
    0x15020a050d021c093503040b0709030c0e01060801050f010e100c06111b0601380c1e01020405060d0b0f1002152d070915030609050a0504080313020103 66
    0xe018403c0c140540d10492801145c1070000038421041500886000c018000702500c1c3c2502090305290389900e03540301c5455030301035107900034045401c00c00105008000180c803101110018a0381c003448074019414842e02401c0000160441406140c51020100040e81c6c4407500100e43d000c00c1d039100a02050f03a6100315081525a44c010304003030304100c0c00350204c017011401845001c0c0a014a201c081d03821505180d118203003072090700072a400904500351464000d08003046080c02c80000458600701036a00b403c0e098000280d24821900418100c5d401189034210300b48803280389a0003140340c80c0c01c0070002100c0340104c15100c02103a51300c032803104803525420300b08510b00c1e03001403d4070046100c4000007541e400790104010700304001c1c7d1002c511580260300c041140c03e000101c0c0c402402c90802000c902d010401895541005044800003c0500c43c00c908c80310300c40c0140e41d02007501401c009011044e504003902400c101440c040801c0302007040c1c44243c0740c106015046882000300b00c0e0004901a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 619388354 1250 619387104 619387147
    0x616020d032f12010911040308220303031b0807020d0e0f030a0507090b060901081f09050108031b070e01060f090b03250e060d0c11030a02030715020a050d02 69
    0x8800c00c080c01c02e00c407442400280244a4a074038540b0341503a00c5a80480c182d403411030f00c216001078140018400100d8580280c6554078607000031101701c160704008110400c100d41d206030b0110355900c03400041d50290010078400c10303003142450801410400e400070764580f50441800e041007900001c0d848143e4400000d8420810300908481180415050094565105100380c2012924100c450005403c21500f641c042240c1611401c003140c2e220320407044261030145035403806000150000c20340345c000d4824240644580001541c58003000c001601011040141d0000540c0c090348080049401c00e580990540d0003516149404400c40c02050715210580d4020003c1d8202c04410440042d074020180407a2100750310282e40145110300742610844655200150000c00c00c00052182c5816900401c40050441c0b4203012800c7c0024221421600943c1501005030800501003050003000903140b02a0942d9010443c6814956030025001e4450003c10200b941e4021994011170461041d02605 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 619389604 1250 619388354 619388411
    0x2030405090109151509090f02121510030203060d08090316060f03060512060433020d140c0901030f060b0d0902030f0a0f080313050d110616020d03 65
    0x203a9611940e0f0b10000d44090b003038074004011a0100014080c0f15441000e400040c079841d2901c1e4541070188160141443c80000c0301a07980811400d000324207103001003803058034508451400700a4880402000c9080926038104060040c014400c4c10340e2003d0800480039444560b00e59a0201d00002c079042044064240741d140400740c000240054011011480c900010740c0c0410815445104008200000105061195020000140008600e452070100c2c00340031290074621210319000c8074001c002c103040380c0400f0f0764010540e0300b2540340c0740c000d4109000c0502d0041041e450484042102401203d40b044d040684400f413002c806002c5a101201401400076002c0d0365102c03910301c010240450321400c034080d10030101c510b01582d0020415801d6a50b201c0c1c10480319681d0703611180d9840c0c001400000703817402e15200b08030015074100b00d04c202c481801e0710307018034070380340489201e0030040003c003201d0101f0440b91021070354581c0411280c802c2c002c02d041c0041d002c060703144000c4140c0c460003481c5e00c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 619390854 1250 619389604 619389619
    0x30e070305070f0504050f0a0911100509041803020d080c39060601020a02041113230303191b0b07031d281716030305150105031602030405 61
    0xd01c007021400606039600c0000d940440b990740c800f40800c0b150121482140440e15601040701c216239074005504060150f001301b440740030500006082904c02d4040080841c10016a4200c1d9060900665031350010b0402d2802e4244003940340a5250800340201c4400c0102c07540001d0300ea0a6120b040d14082c8224035823050a007030002420313103001000c0800d020402100710040411070080015094407030901030380a80b910100c0c40d401e020203486056403d4505c04002d0150300070140000794040001e00004400c4880000c040750386c6000682d1a62410340a50001c0101058014508072440801071107442e0a0349540c107072500f1103480140410008114024079010721003460350541200907582c2641001c0b2030328401031008580c2ea82c540d4040e410625409030000003896400140700d41d5040d00440e03400e4500f030300f4805509895480710101800e416482d04901043c540e161180503072010709900c0c80c0b0000d41d031000c0060306074000107246100c00510080d015030645d02c280305540080601501c000d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 619392104 1250 619390854 619390859
    0x4032307030803040b240f030709020d05180c010f051b070e100609030c09020a11100207110613090b0102010b0d060228050a08060d140a05070501051c0c030e07 70
    0x142c24a600a0358150f4070805d2080104041c13120701325400310030307007101e41c0000316a100e00010f0224010b454540698180201c1100051000081c0020100c07121100030015180ca0000c00845215410700f944007451741c88106c0440700303641c000720078150003485400c1c11601c0343c0b140072412120700010490703004140101c08000614902004a00780580c0340c09171103444450f00c4500c1110081c0407840041c000501c4858200860203860303004212800c61031601e0320740c0c0c00d0912020392074425448143c0000d80c7d8005001c2c0203100c1d1800b0030750702e0306004460061410209040e500000c0c4201e0281c461000c0d03a030450751045a00035030000c060140080c200d004c100081c2e09006000307400c0300c05441c01d03440704054182d2400303c00d280d0110347d10065858040c00e00003098000c443ca140c0042046820640408071800425048000d12092900c001e00130b100c081c01d90301d030041c00c0962544c0218140315041c00b09a07640c0200c00c0d5601c140150101000440d010310103004c6000c0c04205549400178040c20002 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 619393354 1250 619392104 619392113
    0xf150a0909050d0801050411030a1d062d070e040b0303090301090f06050c090d0b0907170303090d02070f0306020304060f061829010c0201020c060c151602030403230703 74
    0x3c0e225102c581c89010581c3c1c3d0360030a0005544d10301c60a465458001c100040026129a03c89a0a00002d0910100703158941161910740780080d00c040302444112107020780d03503107441c040c1e51070584042d500f0407e150524800c09400c10011618491255448070090300454804009580b00c00c02e00400038844e0b0311242c1424113100b0403241c4152421410540000c18058065088864082d03024050082c0c198a544414080c040040c00501e001d0084880000350b11030701d01d0b50350344401e0885020b165a4142001c210b4075044d00e04502806541218030200300201300c0d001410120f0f6081403001da500d41c2c4518006008140b072100c5201541d00e4250003059841c954a020130710500404010421200c04080c10300c0c80304280407009007850141d004131465540b0510040300c0e064410300481d001c0b00403a0300090805d4200e034010b10f040340d0000351064180a03429000f02d400a001d01c220070310f03641e8801c3c0025207074801c9010140200c0308000307140084071840b6100548907094907040e00c0145449141 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 619394604 1250 619393354 619393363
    0x270510110702040e0a030c350307201f0e0303100f08010209060d09081b010c030c0509030d051c0608060106091e09050601020f0a0b041205030f150a090905 68
    0x101680038a1500c4200300c2e00d02c600040c14520303160076491b40b001a4a0a542d144c0523181c03035a11100c45902d84201c414842c6101011030b0301c00102c1100c0329500c03450101d82c02884244510340c1c0841404840e00b80028000010400206652034040065460b0a401d03800c00c01801503806848550321000082012800f08100d00748195079040e46101c080d5680c03107540074244e00903e40c8856004204000141c1d9500103984129401e0340715209250821803e60307529004030000700540c0703101d65140e078020b0114035418070446854242605013541440128000309a845100104c550180b1000090b10079842c6520b22000610452044040c1300e55901c900420781c50348030a00c0741c5404103226000118060008001700345050307408001d4401c5c0c452030304500300e0191102a1180381035009040c801c0e203103600e042c010110750034054060724841d8203042c0390030408603650400d00310030001c00b40248192007002e640100e4101001c031450401c4000c05100064007000d1076407000b0b450b94902a0340c4410440d0225 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 619395854 1250 619394604 619394617
    0x130203160501110d0206130c0e071e020d08061207050d03022d1b0a1802040f05120a06090203070e0906060312040f03150902061c0f27051011 62
    0xd03504940d0f42c0641804559484421102c070015810560020382c410100100d804d580d18001c0700f000451a40c2c802c6140c41d080d6013070340c5070800180c03c03061000e080309003c4800c4401450610042481070301c0e40e00001c00521010744918450103600c1b8192174664001c02c041405080010520302d000440b9180107581c80400c100020800c2c035001100700a4030340c1020b030a240c5002c641f006001d1039842440c004101d03001d43d41b0b4140d40200810408280041001d0001141001c04000107a40390f003400c000c05040d0784980c1c0003502c82c030000d030f02c000c011810100d201c1c81c4540e031100b000320302950588006400c0030440c1d0016a100381e1400f0421614000015500b0301070745051b03080d209010081c40e20300703402d03101d41c1c0646c00a0340010602000000e00140d0703c5601a005ea10000903080e4acaa400680c40b070340440300c2d1612070012010800700c0e5010b903110301c1002000d160002c10054980d0396034003511180940e02d03450301496441141d4284481401008080d0303010b03250400c070504000c6090b1400b904891b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 619397104 1250 619395854 619395857
    0x1020d110712020a12030507200a0c08070b0f03100302061218060405030a0e1f0905030d092301030f0e060714030f060d0f0602040905010302091f0905130203160501 72
    0x14003182e000c0c1400814189840c6070048000340c204101d0490980143c04040c0506041202c0c1a00b9114245881c19034184001c0d120030242500088a007046804140c581e04207001580150000700000000c410881d503045860300c40c0d15880c2d540e0b408200e00d4444180d84065000741d000207030950000c500701401441142c1c3c860610743c400b540781c0e580d80c1d139801c411680141158000c1140e41d81680c000c5a03c81d0101d030009098841d1103040e1030108a203100c1c0c2810a00116140f16000d0025280a01002032211401d03c3c0c0307100e5141c41d00c0c1c01c00c000300112511a5828804443c00c100480c1d119402c08407a41400038000d0098201c92134450f55202c004480e580005410112030000c200c070100100c034018841003c948032940c88a00401c408450100b6080310313613160340c007160313400603006001800c01818540c40024096145005100e21701a0041c0802507541003101b800e12210000c05d00315054a404c03003c000345075500d48003510900b2603d8207020f54140301d82d14405040280d12900c08042c0e440c203 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 619398354 1250 619397104 619397123
    0x90812090405130210120605030a0f060506030f030403060221040c050406140a0515130b090301050a020403080d0902121002030a0c020303160c0303091509050c1507031101020d1107 79
    0x841d0280f281c02c5000c8400258406815400c00c01c8582c401c0741080c2e4500d0100c03500144440d9201d0000e0704c3c1410f00501161600c0a400525007440618440c2592000741078004c1c19104110322071081c2c5034802c900000b1303c202c1e0701190441c07012041198078550341074803030030380004c5040a091941c8580301d40d11645108504100740410110381005080b910000060681062030781810700700251400c0403841207035501418000140700f49541c4007648001d0641c05a002d5590000b8014942500d074014152640b00f40104000c00025120344102ca40801c05180c0001345400f1034800207400445c0c2c0c44542c2d20070300c60449e4041c1c0b00b0f40940d0046000d40f001800412020050041c1680c03039000846990160600540c0c0712800c00d07024102410b086440bc0c9030000325000070380d503419031000400004200450765075410350100082004044012032080360348294280d02210072410a01c0f40050003010406002404000c2071025019915103280c0311030180580840c0d06d06a400b1a040342000303461410341d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 619399604 1250 619398354 619398361
    0x30117060105190b091c030f0f05031006181511190b0f04050a06140105120f03180301020f0a0201140f01030201080a090305070c0b0306030d0305061f090812090405 72
    0x20300f800304141000c642901c9000c035501d0040d50141d0307500002500b030780000c08026201c0c011740281540380d240901c00e44502160110042c001001c1052a0540c00c2c1808070420612020f401d10b0100c94003100d03d6441c245107801d4038107030208100040756002101d9070089031080c0c0c15554114155800003240b44088801840c003c840205c0c0091501c203028000440e02400315048610005a8035401030150f0100c662902ca1071f0f60b0f400441306d90847c0b201d0034190b142c0041c0407901c1c042e174440e507034104294010003001e0032500300183c1301d1140c44944108228003c00041e500d460070b40640d2201c0c600d0b40400c98480c000c801029002e03020811a1250b5514084005520700019140460603290181e588104c2591031a1201c0028071410340142e041c003c09000fa440007500417540300000e0f007039840040b0344a040242c1410300d00500d8111480c01d042c10041001226214807071805500000e00038a0240e01031350100a4038048015013000c03d19004105154031003810440040004e00800c1d43d00f004640c0c1c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 619400854 1250 619399604 619399609
    0x70206150604140d0c0308030a06061209020306160c020a08010b040b01111009020f0607030c02011103120c090103090803010b0316140a03110c011a030c0a080a0323030117060105 78
    0x2065003e4814880c901000030715141c10080c1007940c550340304078062144107449480c1c410445d01704031a034018240d1100424002c017a84110000d040c01034034501401010002d034006500e5010041c1088072144008042140c002c2c4564080c114842e0040c000800c2d1a440e8007007030f0302811240e002d0034015030038000c2c2c0585652080000c0a43c1d4520b89010b4821103140c6008600030308903805060340e02ca010b04075140a2540c903040141541c034408d80312600343e18582d1001611210b403019000c0c8440c1c0050048424445983d030528bc0d00c48407200510399079a107480c1c0103800401d10844e026100b20b002000205488200f40b000394041d900b02021143d00c0c84070100c0c11140c0c007000b481000315400f070030701c00304141d0b0340241c1003102054140030035141412500400c013821160100034600c0c0c109980741e41c03154035003010303c0341c010f80f10401d480110700c0742d080c0b40c0060390303404040000034104191445000c920116600030441203003026414103660b0759403920228108240000e0388100d60044000002d26031 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 619402104 1250 619400854 619400857
    0x60105150c0307030f030902120f1002041a09031204080604110402040f0e1017160b03060f0d0c0306140603101e020f0f040f030b090106080a02041802090702061506 72
    0x101c415074000c40c545115a5412500301d0001c02c000428142c90705020b00050f91140020300c0e0300103c03c002050982c080c1c9143c5072408080b968220f400500c10042031012034905100c011600c80c28480550381c92444d0b2000c0b0380f4116003120300044a05012801045680000c1010f0380124081c2c03c105030741a0000003003204a205502c207000728019a80310800040d0542d0b0302c4143c1c4050302e0300c008106156500e40020b20007040f0190407090741c008049682456080c03000441c0901281c1b20704074203502d0000c0c0862140081a91440d104054030313501c2030304001004104e50059640900188030510107045060410041903c8080c424095010528808801e91240c0c0740d4480d0745643c0001c1d0301c15490320b0301e4004c1d880001003000700c40003041090658020140140014072000140100c41c03882d504000c042c0c040301819982a69041800404c241f980c00070320864082d0701160002184403800005400c4440e10340002500009401308128074680c001c140346105e5009401244140c15191040240a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 619403354 1250 619402104 619402117
    0xe030415020d0801050108252111030106054e07020726120c0c030604030806010513091e06050a0602030304260409091109040807120e1206010515 64
    0x4100c840108425841202da6603040a0b4500030809020703041c000c4084c00d0200d4411981c04181d90741e0725011420100c103001c01e11603299400402101200b00012b00030742c4010f00ca03a90800401007801c84034840d090a180004400f01c84602013000e00e038801e01680307041c0c0508c403e4164200d074024841003102412003d1f01c50303003096003d84052400d03d2080b1828106842000d0030100c11001e0541002804000104c45000790340c0c0515281d00e181b0080c5480c00c5090640306000c1d070858404c2c0320020f44c200345000d402000c2402c281d510f4801e0740301c0c404070800a41c1d111496250411501811020b0000c5140d40991144a1f0a00c0007603225018400381d0300e03a0340302e003800503481000014049803035001c1e44501101485030180c0e84c4428002c4602e81e54015070084da200a58034803500c1c04200b502413141c40d4480059843c5821460aa02c80c049240120300010b402d0072908909060454802c44401c0800f080003003281c2050400038040d550745a10034003915000b50855240304404000700400d9450 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 619404604 1250 619403354 619403357
    0x10e0f01080604060c1404091a0a08060a09061e0209010905030102190518030106062d0f0f0201060503030a030f0f0207050604030c05010b0901090e0105070c0302031611040e030415020d 81
    0xb01620b9641c1ca680c014102081032404001074107080000340501d990041009208209004c0360310300001000d40f40b0000c900c8007007031140c0401c20741040745400c046000b0350f10a120403c0041c2d010a1400c0ca40044c1070201d944a0400800c070101c0740a107030780c0341c0c01361900100a0380c070b40d5042c0d9243c0003414202d04ca4980d90341600c50815500d074129920610082502c2d40681590300da110f009000843d081d990140c00410105460034150f89240d000c102c260261000200040315412201000180c42c2e140280b80c01420404210800c2c48424003d41088004003000b408580c1d42d05801400200100160a41401ca0a05100340c0b035041d202e00b4001d540500c1d8101003e007100307859595041e1100041c181d4121102d540f00c0d80c2005595560a040038020038036a5000f05074000c800021608403007000b091041070040e4a0110340110742d001040d2259200750400d18081000e40e0708000c1213540c0324044d4a81e0150421030b403039001e9240403001c1c104640c1d01c00100503801102c07107400d0340c4030b00031400806d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 619405854 1250 619404604 619404613
    0x603050f130201140a0c0501092406140d031e180b070803010b0c0a06020a0201050403080601020f1f02090d062a080a050a02070203030c0705090601020c221e05010e0f0108 75
    0x1d400c0b004c21001001c800400b42020803a03181e166603844e00391030b203808041e115007044070901c0841c580c0c48820354021881102c420443c0504003400d1031070620030303000e515004151001c10b810801d030140000388805540031b00f0706403242c40b80f100e005004488221168a0807003440308000b83c040310940c29a5100d5510103440350849e801c00134030b4a03041d0006264000944103440d442d0012030f59500c0102050812940080344034503081c18003614001018007158110f50101800100492001c20319911074103072070b01d6181541301c00f105140042d0040e240340a40c0105d135000c001040150035030103555000c2040c05001401808030058002504025810300701182200703001803084921540303c541e00c03182804006080c141140c010a1554011041c4d00340300d0f81c011407041c001840d103101040d0b400b41c0c2c2440100001a143d8010036070481d00580b40c0c220010b01a04061504100c540001400030314507a80b1507403203031814000b900503103028170913510620607800c04a90030605150060741a2804e0710020b0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 619407104 1250 619405854 619405877
    0xf17030f16090f09020307031503030207051503061f020f150a050901050709061101020f0412110603160818120304060e0102190c020a0f12060e01020c07151101060603050f130201 78
    0x44c0a0b6100130f0029080540d1501c014080c800f9510342034024601a600900301c40d810242400101c000d05103031402c0c1001c0070700070401c581c2e0351680c0e4400e5a0f0300804014844902c032500503881c1c018881048020790107850500c1510100a48410b032003021301030018405900d071480d00d02d080b41d400b62811400a119442c0c00e018960091200d4012004110f000510f405194044801c968205400c1802c0348164a40e135081408040101160b0004080350580d29605010420000104c03003902c40310b0a0044082c0019800d075000002c0c0c42014038810191303112142c0c4000c1d000314540c0200d400b11611460001388092415051003034a4440b00e80b035070441604000d13004103440340000110304030783c02a122400495580000064040242080d0200e031003028030074640b11050740c4e000d07480f02c60716030310620030340c0240d038000980181220b5910200300039603190444121004013107290194910740c20160000360701c0341d051780300900c51070184034401216243c008103030710055946070f800385c009103844864 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 619408354 1250 619407104 619407119
    0xc110a050315041505010b03072622050d0519020a0507180f0c120c030915020a300b03030a1706060918041a130f17030f16090f 56
    0x2c840e08035000304226042941d1800302c180940c0c41c01d0b0055408040c02001340b1200caa0001605075907541031a442180d0564800c0400d5546003005184032444e080302c0000764419113880a4000b03007150084151140101080c0c00a0050740c800b4030b80611403044a00a00c0c1c0d01480807074501c20099010020f03000451070400044c4c05003e615011042c5a503842380043e155844d2031144010707440b95601d03107442102c4034002c02412202001c0d1524140340c2414100c000040301c102941a0b000010400161070b80410380007100c18006c0c6490900100904500c072104110412189082c0032484e40300c14413841c5003030418141c99000790503c00c9c02081034181c0e51120407140f90030321540440051314031800e00e10050009018816040d1803c0c1d03024000b07001340010700c0115035818000d00c120354500c002c039007042042034000d042d46030380c06001e00c03921880000c10803c070b15402000da40c40c1402034a40b00d09042072356060144090b5010f400f8100d899240d190b0050041d0000b00c04c880c03020408a9480c0c2c40d0414 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 619409604 1250 619408354 619408393
    0x70e1e01081e1608150a0308071b0f0302030c040603020904022803060e060901150e190204031101030605010e0f04180f0302031c060b0d09030e100c110a0503 69
    0x182d58201d45406a4980c80c0001d1880c180e01c501400c02c04040e03190840c240c05410b02002402800c044404400e4032103c41c1c0341d02c4140b41c100c0f0361003a44240c1c1c40b019410000070422031190342d810f00c002ca40000091441100b0240401e91b4000c13800e0b103900d81c05000404c01242c0452200a41004100c00020003520b44884202c204083e07002e55081c000503154800d0b60030103103d40080b00c449a07541501803a507041000565070042c0c0030b00c020008050350032410f0007010810300c10000e070b420a040000c1d0944101108400700c0702c0d0b000c02e056441382c0d260319003a480604200f05503030009140080000d0769600c541d610101c9418064102c202060020003800301400403c1222440a40e8480c680d0380051205010980c10718003c4e40619154810300303404082d05540303110680c0d24142450428085090301c0d1017101c50908901e107000503480f18034a070640d09800101e100d15880145d02580c4e00403150010450b00c00c0c944500810070400c00030a0800104c00c0941c02100e8140d07000d0224000341881c100b4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 619410854 1250 619409604 619409611
    0x3010203040f0209090a081c24030b070201020d050a0e0c24070201111002070b100312030e010e100204060f05190c14010c09150804031d04090602040e070e1e0108 71
    0x6d98407144411f88605056602181c075020b03010119074070f02c1080c0d80603881407481c0b40100d50003040311441c44001800e10f1510300d0101400a01401d000b10340c101e07000350304580b1024051a002c0c0103070b19010402c0741c000c02e401c84110b141e03030082032a054468508050b0b40e40f0a070306541000184529801482030450f00012012414010080c07100001220f0400c44052291010440540d0710451880c000000720800f50480360f01c41120307078041c0005140d0b10041c0803c140d036440d0006000b0416000c140c00f414408608036410700501d29200d000d030f01107800500c1662080e8541d50a4004000d404459030700c14103440b0b589004508840c4242540b00d604907030383e420302401710960741480580015084030301c000110340103d0444042040600c854035a0a038211034a4100607101e032074151009001c25102c00f102118078920101e070500640c2d21035124204490300b0400c2152190b0b01d0301c030206810481521040080751101c0084011841c0500e110508444d489608500c01030604005403104440030b03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 619412104 1250 619410854 619410871
    0x60a23240306010f0f080604030f05090109031b0317040303020307120507150603031b020d02040e0f0109030206060f03071809170c030702100e0a0608060a08030a08100503010203040f0209 82
    0xcaa04280c1d81c204180b40c06410415250010540b0305607841190242c1c1d580048407941000c0c0802011a4000c7c000c042c0035001c500b0445c0c0c3e50071215004890004294000901d148bc00c086c1840e81500080d4541054a1040c0600c00e006208084129218069440010b005a000300700c000001f13031100e40950050750003400c0c02400d003180f41ea00c01c2500061404004040c0351b8a503002c0051550050071390f0440c0c43e14140503800e0340069004240c0b0549003401c0640141d031644608000008100100400b603058400200b0a02c41d6519000b0745851081d980c0c1d034852404039100792401e02e404280b150880d02d83e0944070b010310070021210b43c0501220b0f00d0035110156046000d0001240c00402001d00c2008038018582c0c800c90762040044003090181c0d00d0701001100344003680740c1c1d21180071b9841640d8441c104146d075540e0751000100c005256030000400380c080810040402600300d110640104101c15209c10704540340da041c14200e002c125009410010107141071005401e00f0381903641c01240300c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 619413354 1250 619412104 619412161
    0x18050f010b0a270c050703020c04060b1210030602030709030506100506040303210903081e0c09040f29091b04050609030a0c0602030d1d06060906010c0b0108060a23 72
    0xc101a00100c4480b84c07009070201d540002d114081550501c03c8803260001240c042000034200f0b440c02219000c0c845540000098a5001c508070080e000f600800555000101b5940d03880e0180b001009a45148003c0b00c0d244110b0020801d18404254044195800681410300b89443e40d1012184c9090300b9601401d010400409142c0480341c500a56004a011340c0700c9001d035040015050284a120401d90121a0b0b1410180031000c9040b0048036075a41c03007114040f81c0e5640706101507000300560101020010f0310100544007c08183e44040d014038011240e582e0290b440079240000309002684481c003202041005214a00e80440645042c4102038202c0341e0161455440031a100c52540001d00035900100b413110942102e8041c208505000030303003443e15410351070361055941da00075083c244234101c00030000e20540d00c43d884421015400c00300f0b080003542c0d00c10032a51508425100c2c140c1080c14414200c5c022008900c0002d83c580c0004201c0e510780d40c8003100e411184040840e0b001c140c0a5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 619414604 1250 619413354 619413419
    0x1e270a0b01090b030a091a1003122601090e030304080702010c0c0b03100906080d02060a180b010e0726060d05030d06180b011103040608091018050f010b0a 68
    0xd14401841c405c0650050016109180d81002e020840c503614009481c4641481080b98501c07022183c0021130f079200d00d05c00c0009031402d000359a4404d2030082c2c05035101c449521801403030b00c6207800b54102d0b88514800c003d000c20405045440e0b06c01203c0140000f64100f20a03001035200e00382946d00d05c1e003d1407000580315110b040280d01c6500c15034100c2422404c0e190107000c014400d01c26080140640310044c00120440d2781c0280d25000c00900c4940015a0380d103844400418400c0d590882170f900500c13a414943e140c90702008030002c291112000140300c80d41450140444401040400c171951101c0e10742c0355038003801c200c850003040c00c0803a1640024031800040059074099940905800d585030b4620307a18103d580011034541104a904000114644507a00d40f0040110350a5612502c1c006856680b21002c00e407900c4110500000b55610300341140d500080b000380d4907013000b4480c1c016141c0c00e02440c500c0509071014008240d81c4615480401c21699080c5e80906e100350b031200c2c00442d070305031 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 619415854 1250 619414604 619414619
    0x31315060302090924071713050109050d030b0d020d02041d010614180708070516080f0703120b1e0d0b0c0a080a060b090d02010203091e270a0b0109 65
    0x401514100b400d40e00a28010710b085c0d0b106a10010407480c04a00c004592929040041000301401d000e09961103000004c12601c0c01c40d80500146d0582040090101e91090b24060742d451412a07110000640740151103222071501d41804102c6c41d1f001010410900001d40801c030003032a24030040e1407100c81d200000925080280100401000c05840602e0134500350380501c0200700c00c150302141240e40d41d00800407030942203001e2a40102040c0b4000c0d0b10780900030901000401d58440c0580281400b040c1c8200b84000f81c1c0043c00348900c265918100f0f4001c803401380081d81c0c200c0549950054003441004054215110030750610f9400034030b55240000308d5202c81c202c40c6d9007594054883e40700002d03a605015041010990802e080500c1000b40070300d0070840706000d000d40140548903030400c904d05015a8400c00a840303106c80000c0038800840f100d0386031a4407a9600c1c40c1840e0040d20f0500d07a07400310640c100b05445596180b4100a046031b900c80d000307800200014114103050159002000c10400c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 619417104 1250 619415854 619415869
    0xa020a0305070501020f03070210080408070807060507090801020c06010302012312180708070303050d0905011a0f0d03020309091b070501050604140915070207150320031315060302 79
    0x1140101c0140044600f03103400207007801010180c0c003500c1c1d8810003d110041c2c40c4c02820a001e00d48510b0042c55640b60351400c220f19102d00311000e8880000802c0075001d02c0700071390025029000e5074884c40c100310b0342c84a5441c281d0165840c02e01440e000382c0010800765009601c0801c400c041810551103000001d40c444120742c01200401007100c0c6204c0801182d01070000c1d11020b00203160b00201031491800440036036541c05170200400b0088041031100c14110070307030000013069a01c480240200c059011490030703010701d510300b100e20400d244072640303850b400c01c079030004e1448d81c02d58061440c0c004007106102e031031003001d03010a25001c07120002040359044500602181c134130a400206441c10300000b08010707160b07800000780c0020b034108140020884002034019415545501d10121913403030140036410024281d01c82c1c9299400441c0e1a00d110342c1c1a4062011103010621040402c075115000b43d03194041141c0b400c0c40f9410074200714000c11035141e8800a115005400450003545030380c04074460707 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 619418354 1250 619417104 619417109
    0x501320c0a03030e0c0f03060c090f0a150e01030203070f08040c0510090f09050105210708010501080f0105090f060105060d1b0c02120c090a09031416050607110705010806030a020a 79
    0xd80d52040030b0301c01c00050002c00c5d0b60610440700c8810a100010000e83c540d00c01900180c094003000480d8a02d0392a15004002104801480364070342582c2c0790a85a082c205050362000002d6441004085540c0248241c900501071650760240001c2c3c00c03079042e110250058000e54142084640000d4144c2c2c81001035900001c903692091a9689844818458070300c860f007040781200d04000040c0021b403140c07805100303592003035140e40001841e498559400d00115800000c0341d9428507001248448000502072803841042c4002c01c5159140c041c40e903100c00750460b0700d9403207800ca10010450381c80d0080c040c04403506850f40c00900d00c06e1a03100150f15001c903201e031402062a014002c0150300d8240c1e01c203515400000080c021640d000c000141c01d00070000d00d1000031955138035524060611640e642512804051203280d903c242c0d014100704140303030910040b10284191000181002d00c44e903450100c644244e00100600760801005680070400245815054810000814007607910740d00079100 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 619419604 1250 619418354 619418357
    0x3020309011b05061e011403060f0a0e0714012006010e091c080402040f0203070e01051e03091507090e06040f0b03100c080702070509010302090406060b0a180501320c0a03 75
    0x1c00c400d8030074070405c08078070580c0305003a030602031050791000f1346000c1505948521a00b50301400c41c1d07101b402000c02444406810021413040329008121805003010b40b1503103040c00d0320384080d101550100c03102c072a110440c0319000340d0400c0d801000200032940d80140c011704000c09507640701e031609040c4103a090024410000050f402810720003941018414134070842c200307010951542c40c15000c050030340d540c181c1600c0d040020014400005010306146541110300d070302550703581ea040c00404945e880402407101d61049040c180895030607400752220307208413020020401d109544060400000381820760340300744c5050f201c10760030350203960900003022842800d43d8000b0f01001d000f00001c101840080c49007065602c40102032046a50301c0303419904607541194042c1d516070329480e1410243c034969000001c1e22a0100c2c402e40c441d0340180c032100d00140f05681c05201d140e0780e00c00450304100141034411140006030f111b607040c00388108080c0803542506214520700200c03ea9058a080d003414003e80 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 619420854 1250 619419604 619419631
    0x150b011407051c05030106050909090304081902040506030105041e08040f080307152c03120c1804050c07031206031713170d051303240f0903020309011b0506 69
    0x485444036400f40700401019140140c150360515101500c917104a041ea0b601c0340003040005a031124003002202d02511490058405115441e825034880c9140c5c8903049206c1d41c1403500007155820144200307031040341c010b07108651b21055000004110f0b61101410303507401d07004010205082c04411240001405524011652540141410b150031868100b071420082c0c1001e1a00c14007603a060000410b60740e0685880244080e07000c14249140718003083c00c00001c071403900b08107008050f100981400e0002240120411400c2c908001c2150422900d01140030b00503c03d840c04248030b95118414410f1464001610540766220001c90004000d505849820002072900e0120540301004004090704a200d01c10400d1203400240c584400120001c2007100100b00421150515442c40c13000355004040c6801010510000c0003080c1640034104d000d007401c0c80c032400300074000351089090040d016409103041004c454011907680f0b0907481c00c0018550480031182c0800d6041c0a154014100c454018 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 619422104 1250 619420854 619420873
    0x10f11121206180c0901030e120702131e05041e050f0c0f090601080403120504060212060603040f060b0103021b0a02030705030d08192406030f09150b01140705 70
    0x50104400040c10b0718003401120020002c221035101c002c40d041000742038442e40390402000100c005100301103a1309180d1040d00b40d061840746552004210040c0240d03100401a280c12456000340c6a0501e10600c0b580d070501080600d440c241d0f4000c640291051104226011070340401000016140780140ca0710341000120b800d401c41c0c00c0040754010b10040d12803c20381e0203501c0000c0d10300c103001071409041c860b071000010205889a0031184601c4600901000a42400e08042c00203400841ea207061015000c40800c1e0b8501c0c109007624440c90b800382d00e9420403165560380742c02510076100e43c02d05042c1c090200f0366105651548142d40f643d40c00d0004d040c0c404850040520700101544004c1c0650044400307000d00035804800240e1003002c4a203c0424001070210030300c0189403400040c5480709101141510920f005c860060480d03101b59000d101d40740004580034102c0e002c800004109141c940361b1103008030011f80040b202243c050401b03481d10700e455500304003554000c0c0800c40d4a5005034505 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 619423354 1250 619422104 619422127
    0x1050705030304060519060f031e0b150108100e1b0c1905070b0301180923030a09050102011e0e10022206020a0b0a0b0f03030c030a02190b0105010f1112 67
    0x1c0e411b80e080380c02000c1c0101403500a0001707030212035000103040e46011800744919524103203075492041e94040c01200440c034003242d0324042000c41070411070009101030081102c803d071844547d420341d00903c074036040d551292500b4115184030514041030f401014080d250940d0b00030310100480203441c200140c41942e00d440d18500304030b655009800d07001d60031300c0103201c07850940e1602e550322075030312000081030000c605262500400014403032645c6e129040000d440c01e04040301402c03005c01c80340c803858011522200164243c0340c80c03608070800301c1100c980260030405103030401c40f140c0740002e00b80c40903299150401030036070380200c2c0304e14000b20707103010036040c40e606203204d19008010a20250200d60000e43c3ca0340800c403000792045a280343c8a081c1441c180c0d0300d0040788950500024220f80e83c41005c0b00c8140c0d2a500811408409400703602d0090301611814082854405e912103400f01c00e603805c00005483e915498206082040f035032220a0026031020045200046140c041c00768076421140c54 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 619424460 1106 619423354 619423381
    0x7020303041d06040c052b0914060c1608030603010b100e0f0609030a081c0920010c05060a051503060f041b0303050315010507050303040605 62
    0x74000790524440c0822150b11000e200341c071000b540e9031070420003100c004c10036040204404004910f00c001c0c950310740d05002c00c0c0151014044940d07000031802290264102224030381c0003505152200b980030002958400544a03e540c588021088660104581540000d0220b10f000c00828002e80d000c0d0407004100c0c2c00900f508445250146008048ad00403840d100e000c4d10509000110324100507080341c160745030240003051941030325a80c020303169000d00030030703610101c664240c1e1009500071b008001e866800791241d40007101c03092055440461286501905010a8991000000300d010030301c568410b45440300041c15958400c900b40d450690780d03003015458022030040040585007058100d00442c064652003220305e142400ca0460100103000240129205000003011034400c0300d000e55540a040c9080c41c11b04480d40d03543c601d035401c190307402c8032199211420890b41308071b00342 = true := by decide +kernel

theorem cover : BRFrame.Cov 619244604 619424460 := by
  have h0 := BRFrame.cov_init 619244604
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619244604 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 619244604 ≤ n) (h2 : n < 619424460) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
