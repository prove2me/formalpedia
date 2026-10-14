-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3115
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:42:06.090495+00:00
-- url     : https://prove2.me/submissions/419b8241-5591-4029-bf86-65594b30bde0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 560071942 ≤ n < 560251798 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 560073192 1250 560071942 560071969
    0x309060e0c0a0e04150203071209150c05120403140405190509010803041d072f060601020a08040308090d0c0f090506180604090201110f011b03110f0d0605 68
    0xa60001400c401c542c07508500e803500818501589103c2403070f19a9071343c1200580100075480d441e8002c40821030039401084007070792040008008000d00c50050074020320a0452160a949051070301c429410390910400458551040d10140c00c0342c03644803542c00300c0e009084142480081c0000b88400300c5c80ba44c0340c91550002c3c1c51003215042c1d00d00e06000400207240c80691051885900800003007001c1c1801e41080c1f104ca0409610b0b18400b5641c1600a40718511180c850781100075042c1f2060000040d9030503081c415819010881340142e0781d400059030381c0e1481840c060f0038503400388001c20019403004018189800c005e807048024031410b40d5600d07040304413500400200d40d40b03440244110100c0d84a010b91200044031a140349032203a81510340000409415103000d241c03035042400669001d51240340405400604442c1090300140380b1074028114091001200c2402c8030100505e9807190180c014260b0100c18000d05c0d002201004081c10b50180f01ca10300d50380d4a625002a030b5a66400d001200d1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 560074442 1250 560073192 560073221
    0xc0201032c0c0307080d0302030c07020a060507060f060506070b090115080d020c031902060903011e0b010e0306091c030b041a012007050d05010b0603042301110a050307030906 77
    0x903a07200318401ca0510b1014032400e07009a00c006010811070000107040d1080b41400e00b13005989880c0da50707a25655104d40301e4060741015880000050540e03000009108a80c011441040100b001440c90b2050b01c9891103916404002406003a010403c0c4002560f0045920303000010140240d4820301500c2102e41d0040d0703280d402c02c43c02084055018840218849012800f410707050811a400300701c1c1a0416101a005506c0801d0701d00302c54a0075440440000140c04101d0121403440c034990010305103940f5007600194400c00c80b1400ea0a00040c0a80690000405440340c1c02c108028a82d841b400034860408254544c0d8541110b522640700344145005190030b01e45103000f00e10009045810150404200c001c0da0380c414901c1000d0204402090319030440b8002e00342c40e010300300580900080c0c2c1440d94040c800205000800008030f20102030000c0d40d0700158000108081141d003284c0c488246003014440030440c034400320b4401c00c02580c0c0510765003000903880f4401d4840000b11486201c04002 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 560075692 1250 560074442 560074511
    0x50609010504091401051302121504150311100507050a0209100315020301090b01111216060515090606030c071106040905090c040b120a1101030219050d1a0108070c020103 75
    0x61801c0c580000d5a0851441c0c0065289c618001610940d4036402030400c42e142c481d10000e45e40580e071300c0d0001c20b240614000e0825a2540702d0403d141581c2030710701414410b1640c0b400d4051032601035000e84020680003070192640110607024400d18040c01400d07a011107081e20310210000b8075040b601b0040e044808401622503041644050407038604800903410b00240012108a0000010700296000c040000d140e445034402c840f020704680580c0c6d4014105818036080140c0e104500c00820a845411203180109440700401d0080d144000e0f680901085c0f0108031300800b05212400d03000c0d60602c09031005141a86c1c4241c03200482d88180d6407107005401c086d25111492909000d841d0780840111010130131480b0200b0707020350300c07d085039009011510400c006610780e802541515030f1011041ca1558209101d464014403e40c0610b842c0c200c41031814460030200207445510588480040e1108d005944820b603080e590120320710000c03030405456645d0040300c880c080315903454040000c000e581 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 560076942 1250 560075692 560075699
    0x50a0204050f2701180602070c06080103210e09250f020307060f0612030203030718030b2e0602070f0e100e09150f0f0f0907050609010504091401 64
    0x800e07158050074404001d0090ba0a0007040765901c00203100f0f07400c42070410200014011801405000e00b1556800c4c49072007906035005200b0190020165248030f040c00554007615034400f521340140a02024005e00c2c0244100b42c030600c2d16030755180104055081078021554410000707003180000300e949080b5012140c4201d400560100782da1100c0c40380d1810159402e0704072001c002d540b4000d04a02404c42e54031100d401e20109041e0348510060711030045103802c80301d06810044c0d6298400d4a205000903442851801102c043c101d2034000e59174820900200380d240d44800b2100b4104220340d40030501403608000310700c41c0b0844c9011004100d55005017801a190210701403c5030703040d07401400c150710640c01f040464440d80d84441305441050004465070386410b01290f00d0300b046c40c24050446680c00c0180640d00b034400111a200d14040c0031a15125524103024088011094134031202e01da20036102884146006d0020304030300f15040c9800380c1072035529024801a03071942803a007020341e21000c0060 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 560078192 1250 560076942 560076949
    0x60b09210105010b120a1e09020a0b030c032a0a0c05030909040606051806061b1207051608010b1503070c050709020c06072a2306070908070e0402040905031204050a02 73
    0x80d849111806c04200c201d402802c00000265046164621035aa504420007199240004d29014040e00b0304903076100d2034044008080c03940165011411118141c00d1040380f0505140c107800c800003245002d80c10907000c0d0f107007a034243c0d0148030f086423240018040c100503601d8005000e48164000c0b00b022546500c0c2505010b2180700c4090342c41c07000d824640030800c441e00c82034202c07950350040040c40c00d68068000d01d468181a03110154400c68800040c0f02010310000045c0c1c81c002c009040d100e52240c40d580c0012a00701c40498800e284c10408a240d8600d050002c6000395071f00c82d40a090441ca1003105580700d17824507501e5004020001e9000c25840c20303103c82007021a038080982d007080031a1500711856540d4454144922014011545e4405420446141ea00201d1071410041c030880d14510301c42c1c0d40780c0701e0304101c801c0030024111680c0010030b10400181d07242150002608403030319445603002c0c440544141441a640c0f03110401c04c08050501440c1c001c0c0c030490003600a80800140ca1040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 560079442 1250 560078192 560078227
    0x17040c092310030b0c07031106041a07050705150721050906130209160e060a0201091101031a0d1b150927052a04031401060b09210105010b 61
    0x9040302200031810500004040021880c0c00c405c182d00ba03640c031408070f86000c407001e807040761401d00325005c7c6d4414481044511910403102491211150040c0d5403107400484150040440240041e80884000c180c0a0b0001103040d822840510703000031b10043c0176040c0326007010460801c000c1c80307a0710070403c01a542c05102e0250025084c025281900003560001203242f4000340071194804c644551104205025014001550300003900442e1141d1070350340003038003d01740303900f0070345440e00f5440e000e100543c84bd118440c840001c0303283c00c107e4140c14500b030180030613040c0007c6503080320011040424200b00851500201070061000e003400b0300107180100b43c035899603c04620101c40038440d45008026100c01065034200000000e84c982e6502001c800070000d0040071411003047d4035074007543d0704034100144150f034002c480c1d01100450004116089a10074440c0709010030702030100d0442d0340340800d01041c161801e0401c02001030803402c0d510342111800c1c2d2144520240000b006048010781201 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 560080692 1250 560079442 560079451
    0xf0807050a03030f0f0c020405010e070206090129010c050109140f03130b090f0d060501230d08070507090c0201090c0b07020a05010305060a09330617040c0923 70
    0x5000c080c0e00c0c50340c3c1d0f0203882c0c1d906002c520710601944000381c8180d2441080c0344c680050b0018002d004650b941d6800424202098030100010b00400b40000c144110501524403441e00d03c0709040f03202400c6800700403240d5250044607040003004452200802d100b4001c40d415540103004940c17140402c901e1281c50031543c603210300701940051205071b607404054080882240c40740141c941d640c42c0010005050351082c0562141d0040d83c1000d040280f002c140e0000c6c0c16211188010307542d024004000e00780e03007000407007210703800080003207000001806140600110b51059007214011500c8a02110648000160260060790349041c0c440c1448000e100c8000100310341d00c0410728220050300030492510040c0545410b0544a03030120380951078036022900100340008042001c42084000701d203840304d5050100c4043c2084903054101d90074041d81401c204c4140d62100401d5007042d0102c401c0324000140103440c091480c0c2c0b00090350030854052180302841001005003100880d000c0d803440e1002c00380 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 560081942 1250 560080692 560080699
    0x50303130524070615080313062615030a02130b09180606100e0d030c1a090312040602070b0106080421021e0709020f0c060c1608070314040f080705 65
    0x20001100b407152422903500b16000000482e49041403c2c102c5a070710200e0303019251900c030001c0c00807000c0310b910715074606807415580d0303024104844440808032184101c041042249899005c01c05110090401030144140034003030766501c128540010b580014007070b250103092512541309464600c0c00c0204180e22903a84490204140e41c0e0880c6250b44200c000e02060203003601300009030942d0300881d0b980701c0141f0020302440503140039180040401c0d100030710488982d005102020302009100003041c0c800c0800000550401543d05a05807403040046e0040e6001a401c00009011a5178041070901a041076110540c103800c3c2864070b13855000d000031f24000e00800384080310a000e03902017006c006141441640600740d001ca207c8140c180390059001d1114140700003003201c16650302c070000d81502101041074840c01e0b515010110b007244280c1c0610f01d180078440000b0f00c00543c0c04805485a83d0003172810492214900d0707140c41065100f030308801091140b2110400120705d040003a10050700c002c4d03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 560083192 1250 560081942 560081989
    0x20f04180c20070906141e010c150f0504032006070801050f0a0e010e07020f012d09062a020f03030a0c1b0f02010908010207020f0f0a0503031305 64
    0x800d0024007440110414100410082c0304208504908114070000390096040c1080032941d00c10380000c1251003014054000e4814000404410141c40c074101c0780c01d001030f143c40720365400e0355550b0084282c01480c074800782a5100c5c810744c0002c1281c03081e41d00c1944251a8145100c51340320100ca03c5030009044107600d603110f04100441541e22684190464809481c112000a2000c3c00509144440d0b00411142e0002000000c0c10a240c10769050007103020382c00341e03210100001c2139a82a03e505d0446070265240c0c480c00301c400c80007541040d0204103840000000c0c00b03005580c888056501c070b030071b100c84150b800020500101d8011122112250124001818000c45a040460f140c0c00010000d0312040d60302d1000c0c4580ca40982a1002c03c0d00818280032181411807030941e40b459092841039000a840c4030b0003040d0410140308a80c0116001400ca00413a408501003040e080c070076101d080e4200207010b0340016139031010000707080c00f100c200e20072480300e50400040c00811540003c00b01740b900500c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 560084442 1250 560083192 560083211
    0x118060b0f150d271101051e1b2e06050d0209040201020f0d081015121e0908071a06010818120a050c010f0b0a0b1c020f0418 55
    0x4000c030b00780100407010032503070712900c1a01d1504014008241840d09040d040c01c0844150589840c070300c201c051080d604000c44442030001106c0303a01441910496002c0c65850003004004100f018040f072000180b840341900030340b81c00903800c010710020440c2016900301da248100f00420034403c140c090058004110741351400b030008400709400c0e8000313809801e40001003415a403003804900c80308600c0401b21541d946210314000c0c1a0801100c81c2d0b04038801154002c40e410140e1071249a00300d0305940e420b0000006c50271500014650051084203010080921035001c2130640928032015000c1c0d40043e4540e9107030304060803001c4070240c95001c041070300e60070480c00d40c0c0c000c0701158000780f00c40c00c100076407030100c0d0103a49421400070b4070f02c4507002d000c98441d0606501500400900d0740f010001d2040690348030608040c1c03500c1c00521a40550300640c02d0010f030720709102070800c130109040610100c241505e00316089a00c8501c041000071800501808511546400994014608002004034505 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 560085692 1250 560084442 560084449
    0x703110703080a02070206031006080603070f030822080106030c05030102070c0e040602070203100506040b0111060601050f0405060309010b01080f0123062101080d020c0307090b0604080118060b0f 86
    0x210003005061140300804240c45400307640c152402c26601810603a07813130419041d5255101c0c418410b440006400000040307541c00c01040c0c4500701c03903408042d40c40035419595880c0d102e0304492002501c7c1c2c140ca50a15881c194130808440040600c1d1000054503402c40c103000283e002190030490081c0e00410441000440c402e02110441d03071032040308227044e240c600d4140081e05c01d03540040c0d458031407162008580c1450754000303806803100700c40c200503030320742070f4019180c4019034000520240c00080008409500480040c94085c1d00c50810903d0a41c0f65000034440c0d030010790301000e490303544148400507942c20004880d00200c03481404803d030342c0b4041441c0e038100100410007840c9030500d64900c0f0b8644070703803041d180340c2c10301c6100a20000400c5030b48811034030700c24800c0c401284200c48617a07000d41c2c000300ba081844000600a80202810700303880c580078020408007550410030412000916100030b01c038903903c01c90040c600012400f014100201511006018640700b4500c080d8100081d58 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 560086942 1250 560085692 560085697
    0x6061326011a0609060f0a02010c1b0308070f111203010323060c1e2b060305060f040c03050609010c030c03021c050403090b072603060307120f0f0317070311 69
    0x30720403911a59142c15134070124146000321408607400d01c1020135401907040d010b402a08002540d40d80d520300400512001c2000d25003000c0001c1c000c1040d6a0102d21044e00c03030854120304082500b81085480c88660001d403401001c03060300d18140c0300120041c420071220a18400030210086901048500b0840003613844d0300c1d01820000800200068403842d10040b101100c9103140c2000300c0c80d495820340221815100841a2032030480c0540c00a000840440342c0700309003d85e40c008004001a41d90520f5842c1d03007070720181060740c10010525001001030010049903210755050000403c0103420306030003070280d1300302c100741900b8140140880b64540100c459645081c00c512038011455841d541403d80d041403a5420460a0801c00038040090001140d90fa1b104290300742445104035642c0b240e1044640000d03141c140d81500144810450010300c0c03044203416a015000d0440340011030354590075050801002100443c44221101e8520155040042c2d03120b1054102030041e03490b40c44c03041c0d80c240f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 560088192 1250 560086942 560086991
    0x5150f07080907090f090c080d0e12010b0904050a03091d27010204060203040e0a02120c0c07120605010504180302071e080a0308010e0a0212010303080606132601 71
    0x100c4071500080351218100b000c40000d103110207003003042200070018000602500c1d881513504600ca10341c001906803000a002065540c80d68034004204204800c11060850941c0d07507034420740d00c0e29200d18083e544c42512602641c030602c0101860800ca1601400c0c000c05507000b03e001d0460007442d0900031070700c204000d40c040c00700040300e41641c2c01c000180721315034611035141d1059031020034082019038000004205482c0c110828207195660b01c07503106c06904c0307005580c0c61002010320110b0542114100035000f00350640b816074143c4c1c0d48410710800c040400090544e03015482d10010000d5041034401c0d99400749a01c2d51900c031117005610040c1d07860300103210311000c25103260b8003080c820314440a24006084204103880b100d011600700109032030000e0007800300407100d01307000c1a600d610b54401c407040b01551010314102680382d5141524071a0009244a0f00410200008960441020107540103022891401c070f0120010104200d181181c183ca5103085138503251400c04a800040c1810012 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 560089442 1250 560088192 560088197
    0x21b0c010813060219121a150a05040e0f011508040f1e1704091404120e060906031008060c090303070b180304090f0f02040b1e09030a0b010305150f07 66
    0x6070100c0f49400d000920442c905550200003680c0b404900551006004030161400d5805014202c43c51001e8085219a07a00c0c9617440340f1013011101000c003800e40039000549880c1071242c1041d030b40f1140303121908012541c1d1411500c500340180401481c5c946041d0030001c007481c2601c440e00c5c060703071800e042d010295005011407038590b100d4a48a02d01c1e20911070b20b00d904c8600c500d9031311001c12504130700c0d0b0001e0040b258a02d091805070040d0b00c4000519512903500103441504c080c400960690f5070408007900207030840401c120010300f0740c4580c00150301507511103207085100c51514042e9402c240b0007400c80c062103039007007100c0c4110f560004140e80d400b981150000e1076545500c81030381c82c5012901d122a115010124000a01a4a903400400d20641d030310701c1404401d0032080450220b220b1406808031551050100c1200301e0000c0000c07000036100703c08031503e4401a40c000030b24002d103292003102c035000d6050040c01048403c0c8001b40303190000c3d100040031030074415642002e807080140400b08 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 560090692 1250 560089442 560089471
    0x50a0813020a170105040b01090b0603010e070513120b07091d060a030212060405160e0106030c20030a1803080703050c01093c05100b0607060e01021b0c0108 69
    0x540d40c41030b0211005100400b036460f1030800e4100924041d10040703500740c80e001005000002c0e20451401800000c1c0001002d0510303527030a0542d13000c074442c000b80c042001c2007000d1003581c034008000c01e011005442c0e0346442d036295002a15005c20155401002c1408205103810100031f464040404040c1c2103004007410980345e600c840c0845d21082c115030001e0760100399480680140c0c0c0c0c6c08202207015900900590700c0011a410b911128a01d40d03100c0c1c1600c81c1c80d02d90041181520a46c480380710030a9510b01004880100700a4141101c408020b03411103800c0061031101080d0000b60700504d8000d070010300103e0070320f980c40d40c100c00d0041c03800140600c4000144025a5003080d401b24003290340c003505072800c296070a10018440b05180c4074060070384c3e4400b10825500252040d6076500581c0c09802459401e01c0759a041028220545070b803a0468402c0c05a5000100c45003d20700643d1204c0000507218860321140c5c00491444894a00607a0400170b0303504a140d900405113a0300c00002c691709070 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 560091942 1250 560090692 560090731
    0xd090806180c27010e06010e0f0d170c0d021209150d020706060609080309091519033c111507030306030501051f1202060418020405010f050a08 63
    0x3820304042000495101e880300700b00c240c2e01640a00302c007000040744003400f4800d03070b200c4104d1007054405a956030702003403061400c500f103441d1101c11176042d50005800300b2503154103035890080e051162901351900303010118200d600c1c44010050f8409070106403000781551000810200300a10811010720f00421100c5100520303040c4110844045c281903110840d5144001e05040380104440c1c043e020001d0105940060010000003d070750a84030014201030103500c1e80c850110121f130340600b03007a0704401714014124903140303640ac210000f14000d010015603c0d544c80c2d11401c00383c124902000401d4100300325071075007a00510640303800961042c402d0b05048111000030300044810109181070341400140d010400d645a0824000c482c8100003c1c0f0440e100c0c0340c0c55000b0350807a20340c0c0c0d44001941d410100000c600c0c6002105090740090709080c070f416114030081080855440b0302506032600024100001c2d6413001d50801101d2141c50000d00b05000e0a4004001000151002950f112041e0004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 560093192 1250 560091942 560091991
    0x901050f0615040e15060a02030408070e0402011b03031d0a060605010f080c0d020d0609140604060b0a033605060c04030c090e010e0607090603050c0c030306130605041d0d090806 78
    0x245c4203804018226600c520b85500000e680c0d0b4400d00612030b85000e0264001030740090340d42c4180c0a47e81c16100e0a107802203010400d2000500c10b10181d0405071515070f41e00c0300e0180c0010726010401c40d203002e06095261401c04109640103079202a041007000c1d5094558a580462255003107280a98101e5564a0b6100d0300c8000e40101e40301080c4c40c0d484c00000080c941410303400341140740b408030240c01c010f03a500c908005c00c540c040d02c500201000d04018000c800c0f4801e60001440013640840900038240701041c84141c0d11440e02964428520000c141c41030200810003540d00c40522003000e45442c2c1076540703200200d00c4501c0341030342c0e554a0b039082800200342900701f130001c00260001c035081454820f00c01018000c4a2017240c0109240401003840702600c94102c1d40400f40038402140356482c3c000500024007084a601c0305220758601d0081110341d03d40c05549480190141401d019108807034605013000e40c0a010001404200d43c41004107410116456a0244070032068080c46641103890 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 560094442 1250 560093192 560093221
    0x902061305030f030a2f1e2a040f061d09060108030f0a0818101b0207150e13060803040e06060307020d0e010c052512171806030901050f0615040e 64
    0x242c103058058140c0c1c41d11f004034114080b0b030001c0c0d103240440d400030038060100c1850007102c25482a464850881d101000e04080c3c0201220388000300d000140c4030360381c401c2e60000011064140070700303c1d0f15200340071056408024060240c110b4802071440e20000414400c454441c02e04100c1c207100010300000c3ea005004800d00e800203903250180c440c0c2246501a5000802c24017400c100b400040250403980148005001c3c400d881840d01c0c4010110740d0003905484220b01301c0040c0f580803039141c6506541d12400d0080c00010516040195140c50070445440000f0703c0041156019030703010300411101c1c950019580c05043c5007801c003103111a11500040320f40011103c4098424458080a0a4400c1d8040c3c2400c8503a0a0070b061a21840c1c0c0300c40e010702d03c8100032100646150b4103201010008541040107026150070b20560350901d010550114503c0c1c0c2088582d540c81703942d01c00410042d0307202c2c240040d0348058103c40c900c032201700030340d010301e507600560080e0600c01d0301c0900050035040d4015071 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 560095692 1250 560094442 560094527
    0x402040624021b090103060e0c0a030c050a060c1509020609040c0c05150405034303030b0901081e0325031218020d03030902061305030f030a 62
    0x14609484038556201141c0c00740e060711408014490000e240c034101c0940300724412a0032004010780e0141c0d10b1503c50801524101c000e545443c00f07503130320428242c0ea603ca84200110310441000d50b03c3c80c5000104408000a40e000340180840010040c1c001038100e030700d0b0001c0070903110380001c0c410141e0000ca04039000b9848041e800902d890b0403000c40130740000311044210310076421582c00c10f080f00b0b964405240280c4006200d94000e20180344240230034a15210b05400110403a500ca00741050303080c0c842c2c0e01141e500b24409400d181e000c8203059050141c00042141605c03801a15494403a94503614401b1400d044103030500d9103c41c1c40409400d104442181d1841134182408020340d41d0302403802c0510020450214449200c0c08402d060325000c0c00c82c03c581c7d54501112060340c80d402384414040a034204800301030380d9800c403030016903925024159950100781c045c5951401c08082c50706c0d1070301500310809207600521006401d6030380580507450800b510040050a01c100a40c030342c400310b00f07441e03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 560096942 1250 560095692 560095709
    0x90210050a181403060105030d091a070606030b0a1b0f14091e120601050d1217010b041502071203030902031219030f0506091807080109200603150904020406 69
    0x10703400102220300f003000c004682421401d82c2d50a0341c0e60f4007007640c0c1e1401e41e0444800b0940107082007000012200c10340180c01c201d8008940f81c40b80999448044a07210b4004a503400f0002040c40207600d094815a600f2441d5034581104100700884050103400e59078a62a00b0000c008031441c81005c0700e80245c41444070b000d403810034814042e86102a00c513104403a060700402440148203041e12000810f01e0484101030500d80c1c150f00703692900421001a01d90b900e043c01141031048000c0601140100c0c020aa850b003200d803602d040189481034407a000c1028404c542c0300c00c80c140039006412400003412645400c001422410900c00310341017281c440c0b46149060404555001001058010300c1c00c0c08986a4080101c560751948500468a0555100d600101d0680000d1081c4110326800c040740900d10003101c2485036038590045c25900c0c10442210701e0395200d815100d41c110036101900300d210b41265081c1c114170b003641040503a03140308401103200c0c0301014082010740d250b175840784d0080e00303604c0d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 560098192 1250 560096942 560096987
    0xc0311070b010e36210904091e03021510030302030f0d060b0a021605120309010305070201180c0f0f08060c0d060f0306090506010b160201031a0a080607030c03090210050a 75
    0x600f40c503c4c00ea6141480b02d250042e0200a80e510091540e02c0645500891a850070101001c0c248802016880c1e030444549007190403441e51440d40c5d50b21080c0f21486039005040071400c4e4800d40c818072038080c0403900140300c0c003c0306100080e008000d40b041c041d10302080c1c43c0c803032100030700385d901501c04d0b64020104c41a0014020b0300746030380403c05a40d51001c45c41d110710140c1c1d9a0b42800510410300c010041140c20500000240c3c0d0300c0381c1c114a4000415100105032030700c2e046141d01e055001404c0845030000c034803070300304000f00f40945a80003d10148100040c4285048020358940c08001c0c020980524001110311a2482950241c2c0c003400391a41e410082544a00e03200e801021860415030305481400000200808404101c1c0e403400325030007601424400030360065001d80f0041c2c00340c1501d0001c00d4801740454413503110b030380d0003007100c14010000c600b480d0901804564080e18100201402d0100c440c015864018612140222500c2c02d83d658038280740048403003d803c5400d080003203a05 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 560099442 1250 560098192 560098261
    0x717030d091b060207150e040902041d0f0c1503072c03100b0a090b0315040b070f030902010e0d030e150c0f03030105090c0307021f0c0311070b010e 65
    0x70342e40315242102c2e105800c11810b915004266540c550b0380c440e0400d40200c5001d1400351611a980050681a000d0b1001c100c4402c0d030350000701030b03810140c4d447d0341c042003481105141c104108603002010151501a00c034081c584c01c04180c0d401d012984810044078000042602c4a128900e0400c0c130307140302c03001c1c0035031502e03100e02552121244c2880e0b0361080c0b040e140203504000c410b215104000800401142e02c180c81d084030200a850340002c0e8507418010900c43c00000c0080f201c007030388907500c209441580c070310308842e014100b2680b503242c03101014070f084036140050741c000c104240210ba0855210300c0b044054a0215881031402c10389a400452980c4800302425144000e060328031402c4d003c1e5421903c82c096020782d00c1c0001d200c0c079075100b548040490140d15a0200941d0414140d105076526100a0395044031007042480229401035555965210b600f5450703c11780840001d07045044c0d241c5003068071182c0d1035810600400c0320031611140403401825504102c140c0c2e1561210480d04014072 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 560100692 1250 560099442 560099453
    0x110d060c0206190e1c180801140c0310031e02031e0d0f051905190903021005030112060c020c1207150e010c060e0a0605090a030207080c030717030d09 66
    0x30507903401d01114000201641d41e940f0038041c4060f00d89040b03004055590076403001d0901210454028824418801e400018100e2500900300180410600200754007100b0f150090310f56000600704400e0300c60600600c980d82034010300b02c6045940202416000c03121480340341d62480301c01a8001e52501c00c0c3e000040f102c4142c01c0b8640e110404850560f410600241d10a441d811820484040040d82c00c1111000d1011034a410443c280902d1030b00d01d00780031134042005003502d0311401c1d00780800c65900c400c104500d008444840542c04c0ba18201c1d046514040c0d0102c0c114903078850050030302ea218804a95a144204040c925500000f4804101c00c50101c5290741c4030211401000e0700c8088461940c44810302500d40c800d40c2020603555545082c8540c0c1300c15008002810351241140201132410012950740e0080da0b000e280140047c040c0f4a03964903001c1c0c81c0c031003558040d5410f90001c9804500d10795004c607012044030b0048400044500032502c1160440c4074914046000c0d51034070907084103021 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 560101942 1250 560100692 560100703
    0xc0108240a030b071101270819021e0a08031302031f0f0b03070609050105030901020f0304200a052404031502040806070903050a0303020c010209150c121204110d060c02 74
    0x110561030303011764040300a503128242d0b01c07010075200c0003c44810549513480780040b003511910f805070744260f080980d8019a0a04450075101400c01a844081109034118000074420074100300700005012250300e541c0c82424501000f042041c1c29500d1038005010f5441c1405801201340402d080303010340c155058500c00c000d103c400b027017007007040c64041500c1c00760600040080588240340c803010b0030310b894580116501c0c0e10042034041030355024005050412a12005035009501c60204201062000c038241060702e00746a100900c1081c0400c03080041e42c0360011041c84500c2d06502d200c01620008000d0b1019106a520003410040d09281c0b4684907a86640a00280c07441d01c0191261926041c0d0201c60080b524080130f0415080340c0706e8100000c2c0683d0052094112410000d030070b21201c500091840c189083d49030700126000242d1150044090241041c14032a0520a509050f020b03840c0da40c010100a000a084140440704180c083d90352481c3da5005550200f010b0000d0055294025280da = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 560103192 1250 560101942 560101951
    0xe0a06030f0b0414010306150909030801090522060c03020c030409150503060f07050a11060702010501090c03020a020703020409030903020910030b01090908093616020c0108240a030b 80
    0x1da25000a101c07252a00b80a08081407281512034a030690071500c42170010040c81d402490340760720103140059000c0340d50003082c041038003079103404241c2d61404580070300785d0708024004800900c42e880c0182c050101610040b0705603400c144002089030150a094000340300d0a908404944030120300003440c1c02d51504040030000c5c42c1ca0303010030200e68640034559580800d440e8010b4400380d079400900b846101c1c0c4094000300b07180b07160a00c05100241580390910074290380d400010307516000140301014807030040752200851032504514142d0800310007510b84d0701600000f8803807500e42c403504050512481412014503001000c400c0300e410035511000c84e60389188405c84000002100000f6524018411b25a9040e0004100f51801252200700a49114080303200d2114814112000001002d1501880508030820003513040b54200401c021040d440303e0740d160f0007190310002c330300f00702c40c5d03800040355030441046c0400800d00303031140304581068614610100c0c0c005840e0380000052002c1c1000c0315008 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 560104442 1250 560103192 560103221
    0x1e020f031b0c01080912030604020904020a2007082a0a12030311091e1315060306051504060503181516090b031501020f071518060912030e0a0603 64
    0x64010b401528007800448a03802c6036000038032803818107140400110341c851401440140b62205800c00981245c110340404000184001101580c00d00d00e41510041101008020f18a0501e00707004540e03184210060550201442d114444440f1259210202c565030014421420940c449040070300100016000354000382c01c010102401c0c1c402d13481220640c1102419000754501120206082c01e60960a803a0700b005624a12384603643c611311421050500b00d070065052149403c034000c09603103403038202501c207104a0541c0502c1c1c940c40790484040796500c1c10241d07101d5440e034082d58000401034010800b54003401c1e82000f82070b00c003034180300c0c840c803000c20380341e4250040304004491860150149121000c800c10101d1201c010300d500721a64082c0504c112405103055003407460801c00d0550004517500e60b02400301024a410820a03103003600000b10070f142403882d000b001003403200b007171007088410a5449170000074544501044000d00001501118100341d0707030ba030000e00501035031400c00d40 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 560105692 1250 560104442 560104453
    0x1060305160b040e060d080d0f0203060f150901030e07081203100801091101080c071e0b090d0c03031104030f0302060f010501090608061c0f050a020306060a061e020f031b 75
    0x51a0710240c05442c01e441007004c40848030307a1450184480821200301c190382030403041c800c51440d50381a000742103101c039246002584908200c014411501c10001089101e540d1850b03402000c10a154103135403684c4000d18011941108030011b007810400b0640003582c2c02c0c01641681c485408184000b10f014400c040c040c415225581c1084500b02c1c0d201d4800107080c0c981c40c445030795082d0b1041c0141500105400012890846150b0b1003641d40b40d9130300c80945542030b04200072410301072403080c8194400104800350041e80c8003090020301c03801d6400d40040600d03641e242141314004402c000d1b200a9944810f124000a409040c00b030340e20701007210000604481d8500102e80307544505200030440d01c0c240c44080d0591650b40800442c0d941c56040c072405119a40254030200d404512000a0340740a03802400d248070013030052608140380102401d025080464007004002c0d48054909030200303000c1041c00c00301c40100422401c201c07a55841c500240700110701c14a08902030300401c4040400f8408844 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 560106942 1250 560105692 560105699
    0x70f081213030e010f05040504020a0c110438040504080909070203090604060806040b03120c07062c040e0607210507080f040c03020a0b07110904121206080106030516 73
    0x490702403900c81c0100051100f007041e810075400349204040c02503041c100941003940f04c0000c00c04980205d0b1040000428040d190002e000c001034400d0000d11003a60240311500d07050032101b07231b240c82ca244908084c0070160600e1005509a0b00d20951b40e01c0010800c2c010b6040030300f00049150403112034203100340c1003180801c4410780008200c880b03206003d03240c14242031a200065811000040003ea0001e03150101c461883e60284030b00064400114200d540b82c86162170503a15200140c0c110300248040d0300800301d000030307d18188807055000c620103040582d0003080403030090440d0642c428034078400c2d0800d1011058000d90914103500c0d0303150301d003054907607802c48110507100292168404900008049507804200901d40d542c0300380140702d9400c045649074081fa01d0811294005030552a02144070f4081281243c032490390400112469241414541c0b5121490400b201030701080c070890b0001041844d03082d0300004010481c21008000c0c465507400d00c40d03100c1d00c840302c20100f42c01800e070011 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 560108192 1250 560106942 560106961
    0x50c0715200601061d041e051603060b0d050a0b090f01150822141227011707030e0328082a040e1006030e0106050303030408030c070f0812 61
    0x25412140740756540048000001c3e40e178990b2040009200c0c1d006500c91010305a1410b640d001d020b414096407400040341d140000c3d0884440e01202d415004042c00c00c80104050002d0b0000d4490210311040b0001e0710b516100309181c02000d0185400703403c888024200301840d51281c400b91304071802031034440042404c42d0030845403a0021204241c140e10125130864022440960080c00680b140f80030034110a015440d191508512003401c0c4070300540061041c603491800d89010300c4280080300310302424034a500c0080c1440750060250325038009d4010005c3c0700c561203904083c03524141441540d680303c1540c5c03481d000c44a03802c01001302c84c00d501d403204541c49109008103071203910400301108030640081d58804030407000700808049110148000305150018202c018041c0340ca819080101d140341250190580395551404075050345800410889500c0c04012a98481c0c2c3c4422201d50706e64a0240c0008140126080500f91421141c5007500f005038403801000190042d0126850790750390912030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 560109442 1250 560108192 560108203
    0xd060b040e12070b07020106051306091a03060a0e0c06040b04080606090f0c0a120c0305040201020f030a02120304081308061504060f0b0306040b100207170c0102070501050c071520 79
    0x40b070035450082190902081403082038540044581c40040303a1a6910300c00190000f901d4024580300d075079603481c00c00550b1064850401303504141c1c10000d07034905e1130600280e220840101510303403954650200d0051280d0500080983c100010301090312151100a800d9460300300b0701070810140319002c0400c285207410403e043c400ca0003248404201d44e11002c3c14407142c0c1050803a503050000b80b030080450310031a4061000c00041030f0b40c1c009800e10f02130000900d03003030340344480c00141c0d0000c2084a421075408540e80d101001200341701e90396501c840ca400c80c024424015121138960380701380702142c0c51001081c0d031b80c010604810160840414042000b084603094410300d414810480010003001016801441d0f0020001b1302c000317500110503010524201003040308500680142d103051201d814802c1d0b0390088e55240400a020204c100c1300041d5481c11140151814040041803000c41d6a00802603807014000d00e00034542052041d0102400030311031442c0c800c0906407101f00804409900160 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 560110692 1250 560109442 560109463
    0x603031b1a09071404200a0306030b010308190804050d0e0609040509010c090b040501020c040902040207051b1c0b010501050304080d0f0213090219110a2009060102060c030103021e0d060b040e 84
    0x1441b0803d00c100c0e031144406c0e45c0c0100b10030710505803034900010101d95820590b5000f58068840113030b48a00b40780d40c0b02188425015034909201c3c98509000c003292000820802d01c212a0502c00101160200004c940b801400b02440d4010305150030000d2920064110b12072a91240d251150100d0b241e11283d14540a54000c00f401a44021700c1081c580c5040e070131122400e80050301c01482c1400b540c441d64207140c10b003049038400740d01c88410007000d4103012034544c44c0584240c1600e400c05825a965480d002d03010300c01d4a04100020001c101407140c00d5040b40c04071401303000100a80c0200940c050065004880f80910301811040d0025030074250317000f11201030303040e0085100d0754404540180c6070604000450380d800e200e800c00301c0c00000c3d02104560400c0c101030401a10780341e601401c20550f2071f0020a070504540200e01400b2a810f000410349055075412075030408501c41c1068488401c1d40c074851041d80c000380c1d420f0f480c030074020561301070850b01d14142c40c1880009400220756030742d04031006 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 560111942 1250 560110692 560110721
    0x10b01111209040905030c070807060e09060d05030f07050606130504051908040f180e07060c030507210c0201081f030f020a0e040804090b03010603031b1a09071404 72
    0x721281e04440e4090051240c03241c0148006400d2582d07440c3c00e8950303004015604c1d81c81d070204009100c400b03003c111400091109144c0003511428090204007010b0b8040c4c8000e0080c2880c0015504003d418416603d100d8061420942c65031060308203103035102e00583d5568081d06900705005040c011500855114031340010050680d03001c8001413410b03000000000f511324030b00521001c40c008148600450007071819500e195502c0e080808601d0840d001084048910340c4024010048640c10000c9090140d80506100752299100d05041c074042c940e80c82004a20301c0c034041001d1800c0d8000700340c030301042e000f0f9850742c1542d903c2000795204028240043e801c4803460381e00800c0000c00c03ca55128401d4800341c01d43d840c00340d50302e0300400440c10503102220301c1c06c0c3c080380500c561051403045420300d95040700244026490340d02c0291076034442414500140c101c807801d030b03402d0203c000c650084800c1050403042d640c0c0360981c00c0d5034440085000d80103489500c04c522002525050191002c01d80000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 560113192 1250 560111942 560111953
    0x40b0916050919020a12050a1802010c03051303030306061b0b16034101050105180d050f011b02060f01090507091203030906051f03020405100302040207060c02010b0111 74
    0xc0c00b0802d00c10300007400500d0101c201102c0c520600d00f140041c28032201252549040310042e81030362405d89400030070680840f0700e40719280402e000800f000e0b18100780c083c00c041c0c440c0d10f807034103085680b8400e601c44080008803458001040542c181d221000b202e0703056a40c0e070807000010070580c12903e034011011300001c0030140440d84000442c040d1018031900390a0009207840e0b4560f0022070a01440da440c101c1282c40a41032240031b8030039800d81c201206000503a0b04540c117060010b03145001e41d010703a112480c03825850802c9616150040d80704503400070f003111001da82c2d580d8402e002c1e2000b07074106540f405090054a4182d4000915640030700c03132100100010343c0c24251180010071004002000300300700075400040da43e150b44c1240d048203000340d80118040c4070340d00304401514005410f000d0f081c503900d0124400c021002c0c01500130707640d040b100483d10307132614110720724410415000a98010300c00103a241c2045025485264200010f80080c0001070f92030005498501c000d400300715564002 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 560114442 1250 560113192 560113199
    0xa08031c0f090c170c0d050a170408030f1303020d0b060f0d03050409090c150f0f080601020307020f0f0622170607030509150903071109011a1305090f040b0916 70
    0x81404c04504600b025040b41c3c5c80c0340a20b8005010700317010740350944164000322103030414000c0000228110030340400c800303031401c2d00e84809103550b4400d603009010b560300041020004c2524080707182c2c00864000340030311480340503810003130a184002d8501900c185140485d020681c10701103c50109075401d61510307030600345404085006011416402c0f13a0b181c510700350108200710a090b144d015081241c0d505507417541010400b0301841c00b0090407109200e448020040c00740c0e4000f0803691110740c1605c42492500c0311002103402142042c00e403991055020911482c45481000b00c41014207a410b648003c140c1d944808905480400135002101d8119200064821b4081d810154100d500141103c11803080440c4500c0c40080c15502112103400005080080c040d80d02c120320030000302100c21054551400e521401000c00400340b840501d00c000c1070381d17407850005107003000050101404e4000300c0d02d884201a02c1d008000c980458980c00749601049544c9400036000f40c2102450a00303205050030f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 560115692 1250 560114442 560114459
    0xe0103020706150806070e03010216081c0c03290102250506030703021914032d010617100f0302060c0c15030702150c12060a08031c0f090c 61
    0x80815101d183d01d03000003c0c0500300458031071009240e03000c0a0704541c10141130080451101a00300f6100c0e82c014071040d82410348504103e00b10560110510b6540d9143d0303030188032050300403890849a2454503002e48580c0ba007542140d400c0c458005c04803001e007080f40b09100c4c01680c0a128040c0103034004940b44003c90b502d038000c0300d0a0742c032001050207a00d82c0c40c00010700d02d0303108942210000c0d03004030303941c0e05031320802c0e04502d080c110310305011401c0c108080140006010081c407400f05c00441c00410054083c51442c40b002104141c01940425a1240700103460007944084028030700f807a10300041c1c10021304070316040c2585c0c00c1c0346840c9581480c0d070b02046015000103010142c1d41c00b0351341c80800b5a95410b48100989030080d640d99849180c403201c0039041101c2c0305022020501c04600300f018200d810300485848240c404a0b80b003480d100c04001c02d005891a400800c00c07031000054454050100d000348060480c1c000005100c40c254184880c42078808043d0000e0071203031210340500040a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 560116942 1250 560115692 560115697
    0xb01020705120d050a170a091a0f15040605090114030d0212071b0503100902190e0c0304050a020307060c0b0606211b040e0a060603110316170406050a1a010e010302 72
    0x5c100c0d15190444c0c11000030402190702080c0da88240b40c0e42da0b88030003420040c42d007410070114451001c00c4011450f0084103242e004c0720040010303080300c042091001a644c1c0e01c0d44240040e2501400c105615a120210503015814404004c0c0c420700c9a440b83c0f051040c400a415049030200703680c0e40e800c2c884c00d540c94100c000f0307581a0960049000840104042d20704100360881c00c060070300089141d0035140140800b0000d00800c261a501500d0024004065810740041c0c0000300d0016065407030350380e420550300706025444025410700a0407000211140d100542071001c3c3c0c05062201c80540720a4108629072007030314215556502c408043c0fa60740e00700342c0030702070b4003100700001c403000c42c42200b6645035a42e12a401503903580d6a0b2500b40800c2200c0d510400c80030340824141044013459455011060380070042c0506030007032000c9800112503119840d495010b4601c8220510181880d14142010340303001c603640c1c0180d82c0381000b13400c128002d110304129054410785448000070342c0903004401a6 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 560118192 1250 560116942 560116957
    0x30102070c0b072f0111070501050f03090c03121b0a030e011d131d03070f0f030309051204030311060421020a02030d03140a0204051005070302100606030b01020705120d05 75
    0x1c5005080c88135120419a00742140303450965608204400582e001403e1052a81c0011803594401f0800340070b903980100440780e000700000031040e1290307591b54903989007183c1500140d0301402104803400c108480350b006801074281007003014100030301c0c0c64076180c0d42d001c01c8100074000426800c4940c4040d40503002d02405c40f001c02c2c4110582403070703d4010800d841c2c2c0d0150140441503403225060801e1100c800c4052404080c1000f0314034140f45502c505c40720444000000c0c02100e00d120f0303031208060181d441400d00c6c0e540310f410717992112000301411030103411510003600807401c0d22095100f505404074403240705a521000c030354060101c0d1708031116103c1404a01e2015803080c030a058025079000c000c002aa506203650109850144440200c1e10354800f170200c540042c010302090000f55900100184104080d00c0c0c559120034450608901c5c1c110f03982500000705240400c0418090350581003115424000c2e001c03a18456940d8007840341080c50001e490800e038005180c0c9150f1350388a0402403018 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 560119442 1250 560118192 560118203
    0x8160e0d0f02120f010c09050a0614120a021c02090d0b060d0b0405030301031a070905010c03120e1515010e090c0c03040906060206070311090904030908010f1a030102070c0b07 77
    0x340440d808629034240f142c86100455001040140c4501e03024010051a001c880c50403821281c54400883c400360317a5401aa82070201d0300d000302c07000326554419520030f40c8810032269014140105060001e6200311500e040e410300090048108030114021038042c1a4040c00c100d401940a8032401d801d032002a1078607500000001c590740200c0e081c0b01c4900e00903030203200a55629450340c42c051400240c03014180c080400c00c4010011140d07040b0301e43d0741c02c90b4001c0c01d001894001900d01100d5240206c42440b480d246095140c9401e40300010b05207000f001c9011031a005915007044002c042c840b801c0d080e5001800030345c1c00e4145820120b025540010310400441d05080035045403508603006a00041d03002903465a040000b142d040219075042451405c0410200e07031481c0080d41c0511583c0070b030728020380012003c01c00705445500020010003111000300305490307103201c024000e0070188015602d146424043c103001807070180308850560341e100601d01102c62400b42014000d81040c801681c1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 560120692 1250 560119442 560119463
    0x3021809152803081207030b130e011416030c030b0604050607050f010203040807110a05130b1504140f061201030f1e030c0b100e0106030b24040608160e0d 68
    0x90a0200d500b2032019501c80c80281d03450f081962100004600000d000c1d408150030700421004a8a404071107046000307a248010901034280803109001d040c010000b4510701106001304006c4142104003040d02c0c01050341c00348090031b03803603904405484200d640c8580c4050108000c00c01c038030302070006200543c443c04c281e8131000d55280d0410b0032a0400c5409a03400200010024104011030800540444040341c190525030308003004640280615011005034aa0b941c0c18100d6661f01c41e50b85c450351101e60010955256191000b00c00060442c5500d41d004882c03208141001d850544180c40001d2031885640e85c82e60301c0c48d1651801c20300c13001c2c0155900e0791a50880f185a0782404648410070340281c0341c40c00440d0356071a1103124031070001d160004044120009002e003182020342d003411502c00d0314003ca1030030024400122284e60303040c8407880241080640c4c00050100a001d00121040c42c7ca8000750350307540c08000c01407512226201c400107444088450703080e103070404068403400c1c0500300030079 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 560121942 1250 560120692 560120749
    0xb0a051905060f030f1003080715090209010303051903020910230310030309090203090a060c14070c05010e0a030809150c030c1c030c0e090a09120302180915 69
    0x10800e0b485480008450b83c030000c204004201d08900c0103030028402c012a15041f480d40e01c0c0c9074a0f5004090000302070720f55803200c0200d80741e620780251200d01d40050440f9030a50352441c000e00180c0c002d2841c009400702290b5643d603400d001e031003640c280c080080c5ca000c140340000f01c4e08035132114009042c1d010074a41002401001c01602001c0d52041003c4025580c101d802d605014082801c25884148a103004108104c003007803010602301d604a07070100012582e244410130685800c4000100d4000b8000049401010300c000c0040c19400c039442a21040da22000400034007031200c01c503000140040004004c404ea460510380c12260014100415107800c11400700460303811584141d04090981c2d00c601c0900844004190603001e05100d6409c0401c06203060b41006090320051019051003042090700003680d440540d000000d540381e10602c0a07040c40c4814401900030b40103d00320500c54040202c0f5140307030341001840e150050b814000e43d42d103134000090411507400078189105410b140090b0311103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 560123192 1250 560121942 560121949
    0x8010807060e041116126303140a120e0a17010506040b01031e0b120f070815010e15030f06012709020907080702010209180603100b0a051905 62
    0x8202c107500c5030181107101143d410340140059080b003210429490402580d80c00c14901f40c00b060a40803100240b0a140f0442e12400525140c40e0031910900080801d500050200d890036804141c0e0b116100b946c03270f03510b0303810401a954602004010000c44e1500c6640c0c1c0c2c1c1310f000d1040d111520100400c5c10102a03255a01604030315906910400107079115400d000891410380a403480f030078828039040149446070920043c100306440c2c0c03003c00b500e07918401090715850f4017030a0104800b0290448017107402201c0b440f40c0c0c0b002e061107280c4c5280100010444550b0588408030b040b5038a1101300380094503401060700145203001c110517070511600c1e803445c00c5094240b01d01e500a20041c0008180340d401c241081520039810442c03c580c49103040d01600043e0349001030581c200c0f103646020002d0f580d8109083e1300910446514030f82c0305182403240d05401540c0d4944610500090301a18103283d0015060700540e989118200d501c03444514041c001401c1034842288407400214400e030049a842c0c000c03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 560124442 1250 560123192 560123227
    0x601020c01122712110d050702010201182f01020601060e030a02030a03023003070507021305040606090b01032903010f05011401030b0d0c03111f020c0108010807060e0411 75
    0x1844880d42c91100181c0034042981510216818a41032174901c074864412010707200c6405032440303424044042003210641e4802d51040c0c07182c0c82100d2020420400318104020940c1441407003404401503440b2641e0910422401d07821444010780040841d03900304401a149400d01d540d015070075108012482015a4041101c005040d0298000d045009102c0806540314100e21060000724942244c02030070010f00a412a58001210310f0300303a0b03c03507120340300140203000010ba40301d81407820301c8140001d214030f55220104503011803104014100c075240054040c3c0c0e88040849003000c2c5d2140000c550b4040c0e01009925a800c02000024260450b0310b10000f10350b030070f0708201c00102c0d0303032800c01403203580510910b0b070710800440350901c64540950302c20081203100e010080280241c6440070f801e0ba02e42422100b900d102800891840e203d500100070364415010005d240051030510000074451404141c0d034060f50340b55910100c0300c919403010700000c4c0418000c5110004020040802c001390341508 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 560125692 1250 560124442 560124491
    0x30a14041101030c0903021e030a050a050105070806090402031c1407061b09030506070c030203040b0c030304150b01020330040516090c09030f03180f0f0e0601020c0112 74
    0x460444220081c4001003c44501d02010003d0141d081001d01c01b50b55001a080c01c643d50020383d01c4113020010002c40d0400030701450003050b5110702c010b075004114040d00301a1040351507907900045961000304100041ca000e58020303405801100401c4c4000743e02c2008000c1c0c149030390801c010003584902c0b003045143e20840c01070324056a6a212040e001082004051095446203000d181203411900e8494032040090038ad034051040c0042e622040500034005d440043c05110913554036400c101d11065280d80c4203c808440343c80a2000d4005183c0b580d21035012940070603402982031a48030700c0b41c54414207800000011018240900c21f0000b1284c1e07460074409e41c800e4000d0002d4039002500d94074a6440f03500901c1c01b41f030826402013241235201c01c6c242c0c2100e41007840500b5402d802d050a44034141c2000d5201b040a03042400414000c80007014081200c02d80c0c0d81c1c1200c1703156561000e10480c0c8040d9003460050708004000b003842d40c8100c040e890300000d0418006a201d22000d81048000742110 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 560126942 1250 560125692 560125703
    0x1d06010c0b0c040602010b030102090a0501110c0a06110607030e0304050d020612011d07020307021e0d06050c041e030503030117030c010905010b0a050d0c0603020a1107171c1202030a1404 82
    0x6010310044d9030a0107603215000c0150000d5090113820b0000810000640c02200c2c1000002804a1258a401c0041d54140e140151421006680f07500004108440701c50030480c19100f0380004c1241c8611a10030044948100d001840c00e15083c00208515a20210b209036030101c01444446002c12070f10f940c5034006d00c014000b981561840c40d820400003d002050b18041d500f0501c05100540c44205000c0c50701d0700d8000074100250755800015070002ca40000240502d4500020041544103503001030041e580040c0310400090040c2c00d41d040c0e5001341e404014070641081c401008500541c08041040b61003620907281801621000e81d03007104c82001e81915140c7d15140c2c410a80c0c145030750903401404040c3c0f182c0d491000c5640b18081c0f0b9001902c281c0007055170014990708020301c03074002c289181201e00c0941c3d01c400d80c1c801440a581c19603075501c480034000c80f03500d24045202540d4410b2428401e4507110b803c1e0301d0300b0b00c0220094000401a0354242c0d2200f10001444000711580d40c442d52144 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 560128192 1250 560126942 560126947
    0x41508030712081e2e031b080c1003090510022703150603070f030312050a1404081309060e1f05030a0209041a101e1d06010c0b0c 57
    0x508040364000341440c40c800078000318030706009040e006039801050350044d0302801c41458440c03400725000400300701c04482422043c441d145640140d1510346000f128000e000d45980c0540c24000003020025a00c56901254000c0510030f00601b00340c1da005e003041e83d0500340004c2d010000c2d20340508040045102c0d03244d141c0e0000321101c8100d900d542006541ca14951008103500650340820b5551081d492468000c80b41c0b840083c0c03950350100304250180c83d030040e00100969071f03854003400c60b1030002c05010313900d030600000400604151244001a1212004d183c00a445689810300d0541c0008140752815110a0001c14a1074250142d4002005a00d00301030040c90107054000e15a07100c101c801c038411610080800950b9030000b1001c2c29607404803900f030074544683c94007040700c2c41e61040000e0b03d613441404010b12031000b011071b2005c45035904491141e1f454120000c10700c52a0600442c0014404002d42c0c0d41400009240c00d54068010306100d901c0141e0368566001e8280122106207034607400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 560129442 1250 560128192 560128207
    0x2040602031c1104091a1e011b0b0106082a090f030604032709050103061b020a0519150e070f051e060a0c06020c0703031706030d050904150803 63
    0x50b00d1010300e89002c0008004940c0865081000d07441607200b444c280c903440301d43c00c9094071040340c2101d00c4544018810100c03070441ea1800f00048280203480c5020480001c0c1040780601c4080b2226420395005402c880203a00704201602c0030080a00b03038003031000d2440300135110050a000304079140d80b0200302035629119a4000c0140d44151014200c1c045d41054060100081e0000c0388143c00401d494502e10394542c003035585402c0c1c83ca03107510050403d402c080001050200350b41c0220100c60360000c4001d5152040c15050380d1741c1000701c0c0b00502e103501c03200c1c2c006024010071146142c100e01c2010344a0f11650615003400070703a039561003400c0e416005a0810444400c01d2000800100710a4491941075180c40c04100c45000c0514260350281d03100240400d052441111080d8100758041421901d07401d54055095440100b4081140030503161f110030201d000301d078460144100740041c003d00501549136422219a045007440c190001e80314542258151080702c03c41024043e000001c50301e0341e21 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 560130692 1250 560129442 560129467
    0x5101101141015140a030f06090501031a01060806010e0d0524100f12110a03060e06060627031c03021e0f180303040902280305090a0f150204060203 65
    0x1c01d503c914403540c407200d403240a081d007081e907030a0b080c1a204030040c0c903020044802e5014007417402181d0304076860003001080c101a107500c803c0c1641d014001c0c400b4403400e105103126141e82c0c01c0c001da801103a0600c00050066100303002103041c10b20702502401c80250b65980e05454aa1f040559082100018411420103501b04111992100c4000f002010f11840e10480800155060040018610907074100b4424010552402880780da07014141200c11550307410b000000b04901c1032959168003a10005c1600d82c5031030340940300030360291552241c1c803030440c030030607480050312800542d054060400301c0c0c0b600514040036414141841c0d100507940740c58086030760400d080c44d140b59400804081c0013100c00790055109032801c43c505d1040b00740440c0910000646580196405054000c1c00007440d403000d94900034150341c0001501a9140030b01c0e2403c0d000380e086d50b0b4201d0300402c55a200c00296004584489112420140206003080c0415003030b0142c0802e07644540c101102680c00010040700303260 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 560131942 1250 560130692 560130721
    0xf0e06150301060e1c1b03060b0405040201080109150902160308090f0618120a0e01020d080601080c07060e060406060501081608040308090f0a0c0513150510110114 72
    0x40304840e18038079660415001030800f442041d03059000300f554504004603000d034080048400d5130030003001c2a0100488910450102050000303ea0341410314218290f40d050600900e80902d9050711114100d80c00c00d01e4a81c0100380b513100c1018259600c280020b032078002d610060068025008044001e85d115082c0078019000140410f501faa01580d282a80848003080d090303000b140400b402c0d580f1a2514400341d00d4140c03e42c0710400c0031100042c000034420341003000014405800e800351211038201a030180c0300408121a9280480c0d040000520323002c4480c00101407503071107074000050382c1403100001c034504002260221061941c4200511496810404160384401440c410040300344d40900300a040c0000079000805002d041c03c04100041d00c02e006038184030825100b01e411001003030a0080c00c400c0710b44502e502952801900b02d41085007401030b10300702d00780c41c0b508041c1c6074a000f0501c001c4820020800081044081d54001c81542c2070081c04400d845c1c40680c0541070900399240e0a082 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 560133192 1250 560131942 560131969
    0xf24050a17071202010c06060e010e150121060911030105040501080703050c010e041805010f050c07050304050f0402130801050103031b020112111605060f0c0703020a1502040f0e06 79
    0x100000701004000c10000190310003a00c8805140000d80703800c0e84010f071058940220014400380c00c200c2c0110755240e0070801c43d412141d45001c440c2c0745c1d40b290681501910031070500a4001550305008030881a018100c031b0050018131240041d16640c2c90400301e0855000e18070207000c01f500080100000c0c0340034001e0750301400b02d440c0904941441d40d901c1942d40c5680f244168140000c0360f80000c02c59840c3c1e4804a8a00040215008255030510784a4020414003080720100d0381380c80c0101e400c2d00440700030f494202d42d00000943c41c3c5402d2104100d48a44000f1003254040d07000c010b45080052110f18040080c06003800125040d4110301d030141504a104440d003507400e451007410000350b03a00040355100c5592400000a901c100d80e4070120f00d030300c0390f0048032941002c1074050b0750801200044241c0b003507031105110401a1a00d0380d81142c01d200e500e0000e13005a016041c25400b2070040c030301200c0d07213100d032003c0107207442d0b5100d803615000e11203580040001e00e0030740100301982c1400034400021 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 560134442 1250 560133192 560133209
    0x1404060306030516080a030c050c040e010b10020c0f0111010f1d0f060c07060509010605151e0a0c0b19090f03020c0d1e080708180a1a0d0f24050a 64
    0xc0c1031408486e03854a003200c0c080c00300038000c10002c0034845d0510079685c03080c00141c400e000610344441039a01074958002003a0165202710100c804103480450480c60304032000b0550102d0041040c01140c000041208a890700d5685d182d0200d007420541c0b080950b10f11a110b6004074941091880c1414045c1e6040c800c5401c2d0045010030031a02d03016401c03103008680c00b41002800d921118840c0e401401141c000641000d1468210480c98500001400016400c203030140c100d00105280c00344035010b03c40340400403580540c40326000a030708901c040c0d40702090720792030700070100c10710600c40c280c81505505490204400840d84141a414800f24000c0744043d13490007202d145aa950448911601c1402003192100324240420803502c40211a243c0e81c100403115118204c1e5920003110490100d0854424440111300041200c40c0c07400f03642c0f4034108032402509040272040103c0181400700607100b0031036901d6042c503d4840502c5244042a5507607502c42440c64184402d0000d5588950802c498 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 560135692 1250 560134442 560134483
    0x2090f01060503040f0302030c0a111212070f030c121d01020102032e0302090a020309061803030114010c05010507020106090501091416090b070501050601200c1014040603060305 78
    0x50107402c0782c220394210340d22084200892080d810124154001e40040200c50300500c0141414081c1f4040f4451710311004880d950442c0c18613a140a60710200c0c02e81440c40701c0c805002c80000b2514025131a6000c074081e081540030121580e8440898413800301011001c54000600710010350303e118824038603c90203000852031814280c40540388071300c1400c9401c8503600700c400c1c0345c513080c411440042c00031580540191030038106902d055010790800c03200602144100f400003204000c000c1c002001110301440514a16401d080496080394806200a170500c1820428030000034000d1255911a0305c0703070740c0005140b600f015001010398106903c046612802c0005485203400761701c41c0300790450259000017502d08ca03201001d4a5680780c99021181c2c1c2c17a00880d90304148881900128410602640d0380c4160101038000415a02c28942414030294413a919a400c6400d22685c4040c0c55805410302c131500150000021040768400d41010000903111002082088001c000310041c88061400303100 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 560136942 1250 560135692 560135699
    0x603031b0d12060e060405070315081c090b0f03100b03071125060e041d060a1410050d02010314011d06090705090d03051c09140d140703031407080402090f01 69
    0x242010024204501c50347d070390804102d0b0140242e03c400b100300035401855404036076400b00d458680880940b10303c0d014440041c44040c1d140b044030004281e50304129540c0c01d14071901c2e840003031a0030050416016903071241c800f08071415200003861088070150740c0d003020b034414420081d0400f54240c10703400901860701d071607100d6030704c8080150082e182c00c0d1030304420001c07000000a0140007807005002480c403e51500300500400800d8017071013011281c0007805061510084540d40d200c00b22007824800300c07440802d1029103402c2115901d150300514000c20b003603506245595505070280e1003504514900f070800500c580030a143c3e81e62141c000c07155950980b91070a8050107500c00c5100f114822060080c50780c00f01800761090310f0a41b44c816890b8010b500d200e076918002000c40a5080e0b410300c500d40a81400030100141000d10001d66681d04803d010580100428641080c40114241529042030054980440324510b1003000640c0e58403260381030a0040c04a966809440b240c4030031040030060 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 560138192 1250 560136942 560136959
    0x5010b0f06031f1d1605030103030e0405070224102403110c070f1a07031d040e0f010b010f0521042a15030207020906090603031b0d1206 60
    0x503540503d1044010a062003044021285440e00f6004104200c1d01c241c05500b03441c081c0d1003900d00c516424900c03c1d020305041d920940301d03400248002800a210410611014181500a103401c042103004035402d038021407801030070048000c00c940d02e01006100400c507407000c450424400a2140340107580c00700400d50607008502640045d0003051549504403a032840d40d200c0c044542c240c3c0c2c50002d46522988882040004069910908100126207080700b102c805000040351400b680c95108c909001d44801c3d0001c412910303582840f80c0c460b545280300c221000b0240000c1c01d007004010000114403040c007001411000341007561804000d800d03c0704110140d01c40c8035421803007600c448804095500d524004d507590301c0c0c04400240301060341c0c1499541d00078204403403040d40d007121040c1a00c0300e00b2a00803012401403440203580644103030080345640c10203282aa42000000d000d6901c0e080c8a22009091000c0052178203080d5409101d0702c2ca040c96000106840445881c0c034180242d521f0600c14 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 560139442 1250 560138192 560138197
    0x2105010f0915020703140a020c0301060f05130e01020c010207210806060a0324081b10120b0f060a0206010906080102031302040203060406081204030b01090209030d0c03020a05060f0405010b0f06 85
    0x28800380b69800503103c1d0a01d8043e000d800c03841c0003038002107581e54044040082d251001d00302c440d03000e98240000826181c4c10034a19006689000c0e003c403035400f600c404024040c080048201c0c081e07540c208070014410000f030008195007800754004c41f600116404001000d80b45441300941003040b00c1040c880741c1e984030412038000e84098540856011500100f040101e15641c0860303c500080b0680040c200001180c52404048040b02c0745420300c040000380f000a000070b64190001452203101076010041c0c0d9441201c41d0f12001e000340b4014070805000c500290700c0240d160026a004c0c1d401008400c009018035005132181000a500b5070501100280d015000810024415a0040001006901d442d40079074001c01c5c80c0001c403042400203200b40c00c450307171081c002600c84240d00c0b000450082c2450084801ca180050000c007100360860f03034201c880300340240080b011805507800c011702090040140030300452a201815030b0714100392070800c1c00c41d582c40040c00e0245c5500062584903a9a0205 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 560140692 1250 560139442 560139473
    0x201181a0418110406050f09061305040b0118170709020d05010e150a030b0a0e0d08160c110603070507170a0f020c090103030e03011e14010e10090c092105010f09 71
    0x1441a11155030f105000c0c1039004080b50150271980104a0b0401c5c0c411140c6a034007122015902001071030078000045400048280e1035000004103e1020080d003a641d05180d0503c01c2e80e0829101080d4441d5602c0c016648074070722801c03032540c4510045c400c10350300d42d8040c0e400003516907041410a17070040200303041c2c46a600c0040e180180700d0300080c084035101d410044020a402e002d80e4810f01c142e401c084d20303107a01070f40d2420000401d00c0303005181c5801413050081d05078112844000c2c1d004804100b008940c80200b1003820000d0a0140788001080d208905000c40e000e034010f00d440304503030240140003101d1080c41030704550001710340000c1515a08030b803a0549401d49082c100942c10880407901424100c0e158812110758048481c00500c3e550f4010303261106100c00710b0800b81d0369a425440c21103815560060f168500c90350070400e103080c0b54000c912188040c145100095540c0c030f1040c1c0e074078140c1c3d503d02d0b420798010f0f86080200704d020701c1001003404890008015040440c0c451f096401060300d03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 560141942 1250 560140692 560140697
    0x504050c091f030305030c07050d0c0c0603022106150d061d01141203160b0f0108030913020d090b01080c0a0801110409021602030d0512060108040f0201181a0418110406 74
    0x42180300e01f103c0c08442140e50003004903040c0307008803000200b0f0304e1010541034482000c7c00c500400c045204c0d008641c500b004440e4401e06480e54061002c40c88a0f01030710081d03010b19100110b000603d00c00c40601034a07403000000190451170a11004c0c0d901518940290b0042c040100600261a00c02100c1c0015941640c0d11042e503040341c00402c0c070f14807400e000c000200c40e001d60507804001c0044011803045088000c40840d41c0da0302e041c010b0b500d0041c042c0403944116000e5900c0c02403545907015003070f40c044160f8081a020b505d030301c038541c6a400c03e0300090f01e240c1110048918a0034540c00f060010400c58008202a4440c11a0038280d80214020149401c0c0c0000e40c0341341080021280c0b45800c2d400030203a49400c071a1000150256006403030b011600340402000500560288001c2441140c00034080404050242e00456862803641902e0b0040d5100440c04a01058108100c802202050348140c0e174540c1494550008401d10f5004070f5400c0e81040540600c5040345816a01112600d0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 560143192 1250 560141942 560141947
    0x9120207120b130c050901140111070b030106050a18150314010501020c1002122209090b07031d070e10090603050a0b070212030c09010905011706060903030702040504050c091f030305 80
    0x13071422895150f52070f8000f550203030362030001080410100724a103a03034a0098a40341850f107a08494903460300d8142c81103a14894007403004010450180c4010568501c040c0341c01c044c203c2c651400041100c615800c0003000131001d0070036160198261081c80e00303e4a99900d040b5166141900003981d6242d01c4100c10702652035900001c1002c0d0082101c5540320070410821034075006400201000350064406500d03040c2501100002c030b00d0007a1080000103508220b98450565840710140d000c0c04600c8107401550010040c03000d2405800d2280401602030701d4660505420300007005880190b80b5000a203055140030f2041002480018030ba009a42c1d1007010780e0200e6a072000160705203200e060224400b0200003080003c81c000c2c2200414440009807120f0911540b00c4004680075180e107802c2603850220b075000304003035141c500c004d004249802000c89190840d9580490143e8906807803c0359070307a020720544002e03031411030b80d000d5000f10241000380022403082005a09403100e48005024407600 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 560144442 1250 560143192 560143231
    0x2030301091815110d06090e0d0c030801061d04050f01090506061810110f0c19060c060e0c03011103310602031b040308190e1806030c0409120207120b 66
    0x1314820b641c80b404280004201542e0386001d000e020b4140c13004100701c14058030380720b600d02c81d014840740a0201d8155a96490983c02d2000945201d048c11030b094030b2070004100d0764400b9a4a07409070f54880c00c0704948000702035250903000411307035502500071446400248804070443e0524040f001c28100704a9520b8215086080261124000a4004111400703008440c0380c8605000807808582082078a20803907111817403c81000245140c0644000a150f451381c807004103000e50400111010500280c4104102d11b000007800c558840c0c0c038900b10300b48040b0030465040103010711203802285d83c2840d038440c02d504001904030721004810081c8000e034080f0100e601d40344815122210b82445098160351245c5900341100d154001443d51078a51480030313003080c2c1652007541d20a4059801030700800d505004d0786060b40d031341440140042d0301449103801e100031036034031070040d111103034020305c0070681b20600071100a04180c010f401c001d044c3d1200d87c80b00304c00910041c0d001c0740c0c00200c1c0215146480d00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 560145692 1250 560144442 560144471
    0x9092404300e03010605010c0b18030c1e06130314190804050d020109150c020309030102033103121812120b0312030408030606070c0602030301091815 66
    0x200246031000400d8015140008607003501c1c1c200d000381a00d40c8480d00b079840080101400e9480c02e004150018240220607400615804400c039001000107148601d82403502180a1030341d045299004282e80c80810300080c1c3d184540034004080c08908080c0119142622501c00c0c2c05641d44001410851000000f018507540041a10b6401c1003081800401c001171600040009409907415103060080f00302d0085c0c99401445003102c40c55001440070307a040c0c02c2004401c01825601c4880d419030000f041400121381d001c1c4000c2d88900300b040e649038411103445140209503c40c0040101004552003049008280c01001711500006c58440206070f6072140050b0b002c514000c03510042880342e400101c0f4044030307008010300c6102441d604040011031910000c1640d1454070b81c1c00c42c401d81d10b0403c00728000ca160103005540c0090003900c100c1c41d003506540c0d40001d41d84950b0100300160004070061140c6c0401d4000d08000100c2e07180035101c0381c0025128109841c00300d40100180c0361303842c080380b00c4015 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 560146942 1250 560145692 560145713
    0xf0315030a050102031906090c020604080a03020d0915141b1806181003140a0203101a041503020406120b0a09180606080a1a270c09092404 61
    0x2580b000007035460307003402014422a1741000d04141c00a500303000780411004814820740c928030240c1c0d0300034000f540b03468887c260503a00039034105003007540030441a4080304403402010b0049200c0c803002446608003954a00850340f070a46510070045482c0c09221600740000189010100b80c028596583c540b0340280d603003090480c1d600e05801500200d00c4801d440c1d05080c1c84244500c0c02c0d10014056003460f50700714100e40c080030b0740030035030041e44022855015966010319030111020740d41143d12916081001c37a042d9078481480b03a0004002000c3c0603101c2582d080031001c980c0380c1800d5040030306007600948009422003040d40c04558a4090f07060a544195104009003581c00041104484440c841c070f6002440403429607029042000000303009400007041c0040e2500710b081030301300002c01c010002002c00d000e8040c5806c1c0146100c800060b4004c072200807a14803000c03000f80b490028010a0000752840140281d10036044586c5140c0300c002401c8417141c0c1c01a032000c0150060703031207140025140 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 560148192 1250 560146942 560146963
    0x2030c0640090e3c030903011d1501062c060f070209130803061306081b01020f120409110d09030801050315130b040602091807090b0f031503 62
    0x40004000003040480740d80074800f070101d00000d50b66003c681d40324640e2441030341e40b01314030038001d8010034500c4281507105030064403210342c055a00e00102000002e0070f460341101c1c03044640f4028402600c0c0071a00700040490703101d0100c2c2c108207561400c01d02802d0032100301450000503003800c01c0840d4a12548a0000c000c0400030324280d05e40c4501d40e4820702d00d800250b8200d025004400214903105071445868004542c080f11043c40d543d07031030042c8000c152410198000c0c4603190000031816030004e200712100070011900808140040200080c5000352000d040c00c130f603800008140004400d00400c0340e00380d41d0700400101d13221212048404441c42400d5402c0c181c5494449072504050340700540c64106d403070032012140805291080c04c0143c2c4410f64040c1024505100d00c4070000e008502c02d9580a4050b44005050000500c007092010030315080520416108404000c50190000e54088c0604075910a1906014460080c0c549a10000d861210f0084584090300310540d0308210321a201c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 560149442 1250 560148192 560148307
    0xf0a060e1515040f1802040905030f03070309020901062102030601090f17012a0305040614040b060103050a0c050414030705130f0506010c030e130e0a03020a02030c06 73
    0x5034034240b102a503402488005003072086060031040440c080310f43c01005003110452031701800b001d0060342000014401010101c415000900030f5500015450002e14800e8200341c501194400c1c1d02d1041007404907050b0000800d21002c0f03034000300c403e0982c10b403100c0e10300030200300143e0341d45500b40141e4010f0050360014000075a501004101048070601c031500c40003000000b030200840000d000a8080380c2c0344405049100d00c1c1b4044600c81d80310340c02c29074215000350030009101d60070390054030460758215400d48400d681e41040c0202960306100300c992240c001c580401403088280c0f40240f580c8224801c0f08840d1480045094083e641445510024a8014070b0480380b02c0d1503007081000b0300070741d080c8a8101450701c40041d040394011030402c598558035940d000c82480b030500821064042c503103003130015581d803500d030846d0340300c000c21100025030f000c1d030028548445544101843c1a01c4c8608441c081c01050141d46100c11415015940d01c0799154051165250b04500240b004200e200d41c0250 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 560150692 1250 560149442 560149483
    0x3120b0301020c1c030c02060c130509090102120703200706060905090f070803091011070911130b04051f020c030703060603030e120d030b030304030c0b1201080f0a060e 74
    0xe11940014008404800e510f10001c4140d69441045d4100c1d07441548071405030304002c00040710b0543c8a00244202d0000003d07003000b01e43c45401281e03405208603210100c030b81d40000c5401038500c80498055120344246001d2041d81c041c00c0841410540c03a2180d030392500c101107807a404000003900408017801d501c45081000340761082c05070303680320000002103803207001d50b03100031580900102c105c860011001e48182c6c503026440c3ca0884903041d45140d0303c01c0343d0248000100d00921103020303201c0035121500f034598681001701c5004110286540c440204d0300000c001c01c00032900c0781c3c10328220b0707140c401812000c10400030340143c0c1012017600030150b01d401490000300420400e0b5101c0c0d000e40303010307036900960400200240a40b1125810810010784e004154212025201e40c00c070716081c00d80501030700d080c07a40d2680c40410051682d00004000c00c40407400b90050b84040036101d00500d04100200300c0400f02092041d16115030060103132100c2e4403030688900b0410108029030b10350041c000c4800 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 560151942 1250 560150692 560150707
    0x105162a050a0804050a0b03010b0a0f0c1b0f0b070c0b0f04090603050a060b010e01080a050c0d1514190302040203060103061508061e03190c08030315180108030703120b030102 77
    0x10011340c414000c0701c0c0311350030510012510318880f80c1503d051310049588a46410304004054480704500076518041003070b000d000d03000040c60021051241044541881c0307650741000c0c900703618680e154003c0d0402c40d909016202c007040304441d170202100c00500301180c2e5007940000c85000d0388074503000513180303a00303090000040100c00124204960700403079041146188103001190a40108031115000500c0303c804510b0404060f030081f0b0300030454803003940c9402c1208003908152889940400a51921524104800c40907400894141c40044601c20611a401d00401c401c9040300d0001a000300e07408400107203989d00a0b8001c0001e046c0ca007441000440400038000d0000d5000c0310454000c1504802c000f05d182e0440c0d011004022006010384000030210b450448a40e840d86400d0311801c0b0401380c0003441610510040d8010705461840212100d106028003c00c1f5111003115540c241000d00100000403001c03040e102c0866041c80c080307041d01c1142e41030314007900c000201c243c0e05520002d1a031 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 560153192 1250 560151942 560151953
    0xd11040611060a060b0d0b0406150306080c030a0b0f06010306050a090f0c0503090316050a0b010f0312020a1104180c0f0302040509030c030405090a020d05040f050105162a050a 77
    0x3845401d0460048802a945540300501590314512810014020522410781c0300310321900003098640780940b0000f6490790360120035903c514100800c0000c43d80e906800d010004007485400c1d030386841a0300601403e402076031800340310070009002130701451803800890403981c801d4000308000d0a00510a1510ba600c52101200600403500400c400601d06130710200207a000e0000c6e00c1c4200004400355081607854070400e55a804080342c22249806450440d130300103511103401d6400b914080540428440c1903180200624890469620555004001840004a04040c10a00c4102c00e03a8080303840c5840c07401c0180d5000400f80018151102d45402107401e06950784100d0450740200c070144203584074401e41d02c3d12841a81e112a0140c0c00800042c0124145580c0103a000142504014901034405165500b110010344044941a0030f4a0780c41040c010309010315500128403020080f80c0d03950011000d400171641c8101442902d46942d034102a143c070004c0c8048016400c0f100f0b4950141d014a0300 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 560154442 1250 560153192 560153207
    0x30303040c091b231201030506180a0b060d1103070e0709060314040204020a050f0304200906211006080f070b182236170d110406 57
    0x2c4141880c50032441d12036200d00146041c07400001600c0c1d10070319180402c8005252071003056480ca4940003000302108071500c1e040b45034006d60040300940a1070505002c800c04000380c01e403401e0510b5100240010104001c0c1a6254016000303c99501d0802c84900c0e10818000c2d0701c07102d0301d9040c0190000080c01861914015114203190383d6403400d4162233070700540c00c4a00d0000e20302501d401283c000b400600300b03a0700034401900310342809401e01d00c0400c0d0482290b40111001c4944140f80000c514001200c0768500c141180204d0340d0742042e06e809070204403403888010400800175000080c1004422081c03003502020f010003002489555281c085c407964130081120300b0200e44c494001c00107002c0303140d41d050b10030243d4001c6290207907003034010400100c800107020b81d003c00b21030310300204088000792284142000c42c1c62007511040c078500c0303691420320708203016001ca000403c0021100085600e8180e20340c4c282c0442616440302d48421307055004081c12000c0c408051800100030134016009504c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 560155692 1250 560154442 560154449
    0x10f091d010c110d0c03080c0c03070804180f0b131a0a170c190e0405032104021f0c2018011703271306090b0915100503070e030303040c 60
    0x413103a100360403410844909615000280002e841e0b03c2c049100600500f0040402d050716400b201d0529420791904d030000d03072080d0b200020940c0315060b40c1c2d4206000d4010b141c4d00e030701d450710100000c0403e900451403407014043d0101003241c0d942c0c41112002c0d10356200798071692010786400800343e1908a1500f94045c043c442a500d0710603da01c010703140c50320401c10034003c004100980c441500d01401c44510450184c41101c0302c1c0400d03c1803000130417146030042c030503124940030104981454014803d0140000790501c0d9900390001d50002810f40140c00b903020107610204c004010700320030540c25180c00c90521029440040c2210000218900c0c96246060318094040e80e043c4040d5040b050b0703030b43d128190070203034022024140c502e0700e51020140182150005331865008450103a01481220207540010f030702c1503a01c02002601d420302644003544081030128012200004000084210341c50054040800100000080ca03480c4941d213081e5a081c005012a03032682000d00e80714519164901 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 560156942 1250 560155692 560155727
    0x6170115080d020c0130020406080912160606030f0b0115030902211501080706032409110c030301150f17010b1b06101d010f091d010c 59
    0x42000c19207030404903070514075540c250024002465084c00650345581ca0b000c510349001240c0a04c0200522210f6801c190800310702c00040e0f4890030704101902c5014068803801d400e6000351504140b840c0c0b884c0455092000c03813504142814003914182018000300d400040c0859425400c0b101000002c8034142d041c0d031070540b40d900c1d003001500703021401c850458001a50210302e0050030146d01003260024008014480d06441c1c913007030414001429100c003a4440e0b43c071544421000c11401e5814803d91480c403490001c4201d0640e1140070041c448040340c095a183c0641d2058035101c444a17000480d0800252801030b282c4035a03481140c03407103a0311810300c002e0106244001600c400d0303118007030f00070b51200942403a0780140d003800b6000c40035030081e5402c031310203041942e5100340383d09080009038440c046c15407032106500d042c400c1f10000300e02041c10060f90100c1510040c41120790f8500c040c0246d400c0071f1390000300954400066440399901c88040300f03642d4078103154100000d502c840041c1c132088415 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 560158192 1250 560156942 560156981
    0x7050604080f1e03041e080906090f04090f02090c041410020f0a03180e01030816060617030712030b0109123f020f2a030f060711011a040b04061701 65
    0x7511021b031000407400002d00e004030030001c0c0405403030514041e00e0700e140090407050004400c600410216000c01b00700341ea00e0300304c44215000310300c0d1500d0410b51019a0a10315030a061600803680c4070b208580c440a84150403403c0a244507510800040e900109640c084800ca0242c504001c1e20345840d00c020030302d8441d00b18002040e070258510030941201c3d40040b43d1361801c840490700f140081030040040700c003142caa00300000e0800390400c2d20010380310728070301450382d8084c50702e4510b01c0701a45a0328103041c0341c1441d110300350581e000300450007282c030b448400444000b01e0340b8040380c10040c0c0c003c040d25101800000210680351214a0080d2040c201442c0305490001d881b00340d90340c80140e400c800303060780f08002e8120080b040360454002c0749010303160010445900e10001c0d04154036074440001c65405901001180384e03000204114800d072035002000180c00c10014592030a092520042c003580c0c440c91680710580340c0d0340c8010010b102a909860303094600508490290107018540c1e00b5031200c1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 560159442 1250 560158192 560158223
    0xb1302031602070b0f0d050402130f020a08150306040807061b090801150b16020f03070311010221091203090405070306050315060d170708031009050c07050604080f1e0304 75
    0x1c40e040399000d1217401c0a1710f0501100301c814001030000207000300e8000c032011204440e5241c8500401049100d410005601d602010750020b0400400400e201868271440d00c40300d40380d48000c104507411980100b240342c0e845102c1e0404070042c04144007900703050914200035031a459031100900c2c050382e030204000c1c08000f00604907a2002c0d240b40c0699002400c080002042100303128260200c840d00c094007420010703221500207070400000d640207079882810302526401c9581d0522103464540c1144102001c48052070500f2112070048100d0075000d04500c01ea1442030003820415580c450b18002d1080c030240c500000018040c05c071510455002c1d00c1410344031940a000800078a00c5084041c00c80068400c45464109009103081904409400d0402660700407444110045118028a134104840745143c90303c05022514020514101508203100d2103001070404641903820035000111a503c0d040281409a1180300b022801d24444440007220485099070700059445180504400f00b0007200 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 560160692 1250 560159442 560159459
    0x2010b012d030509031908060f03030c1218040204030507050909030a121805010507202a0f0612090705011704030c140a03030f0b010503090a0b090705120105040c0603020f040302040b130203160207 86
    0x301140407c00381c115537040c0328440b4418001d0328012403403009801e01d0030080400714089a01c6600203035019040008140698205078603602e41095002c1c0045141c001442c500030092a80d1110324860181c8034041c41a84c004405207070240250090001c010a09000c0400780c4201034075007103000810148041c000d000000840d0008900010303070f154014a420300c020002c101c048044403a03500810280c02d00c0301589030800a82010012000c401d03c150605955141c43d01c01a035000a041000c100c4140c1144102e0340740d03064106a260030940c900191a141244292840c58855a142e119440021051580c1034001d0307841141d00040030001003210304011240c602c0206d9005140340c0c40041e541001074082d0505c19446007610f41655a02074490000035141c0e403a010807150269116005d000034000142e170144000c0940e4101140307041c0c0d031060545010f00840c80301a20581d41d451842d9015101c980c108480f00b100d0b054119543d10300402281d041ca040c0c0000d10006201b84c1c000881c00c0107 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 560161942 1250 560160692 560160697
    0x2c030307030f0213030803060303070c0b0703021009021309050a1e02040b09130b0c0d0507031e1a061809091507020606130b011e02010b012d030509031908060f0303 72
    0x718884004d40145c01d54840080702d40c000b6040c181c140c071040045401043c0f00101c02e0000d4007072406003590781c41450400a20b080245900c500c00586405000401070b50341c0c1c0104000340001d00030204110000c0d082842c04c043d0b80f0381c00500b100180f110f05681c0c0003001d50080c10310610031182001000b111000b4001480802c480a4001d540444403c50203d40a507030340c2503000e40e203200d8a0b0b00e048d50309403201c801c1c1e54081d111800429158000b8001c0a1102c0c01601450814280b0802c0905440c8403c030b60800c6488a055026400000d6040889504c89942c1c1304180000361030100c06003010000f103503540310a845034a00400032400451865480400c02a00070440200105a04900d112610000f0b100146080d414000b50204030300d5000e00000c41c071ba0800440340c0000910b0720044001500050410560141c005154003848086c40300d101c160003840d2045140008140d40c5260110345188107500303d85954519105500c00303010707031240300c8900c255402d441b0b4240b49015007080c9a640d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 560163192 1250 560161942 560161957
    0x605040e190b060a15050403060e06070f180801021b010608030c0c10030b101706030309060403110a051804031b120c020a0f080c09060a06122c030307030f02 69
    0x409061040101007070300c04000540100f00204801c5103580e5409205070084040c2682c01c010840c0402d003001481020b2003003102d0015124045e02e60352a00c10401040195590300307500034425803170b40d9010030011a180d540c0182c000407001711b545a210046400c580c80024081c500c0b0385d82401070100c1d0541c008002d640c00c41662000900200002d02c041102c3c0d448804011420940c0d1140c1d000c40c0356403034503000014107125071035450381303c90418082080044000c180300e0080d4801c10100e825a203640342254101d0390400a40c003a1082e429000650380368031a440250302203050f80341c000000e000c1069a50185100f078440d000c0c148075181510300380c00051000503098044804003e40414000c4000103405840185007024058a0320000c90b50384080303800054150b070091b100d90805041030380289401c464111580800031385491001410795440c40d142c26403240d1619401d802c3c0c060480c40040320014a0310095502100c203100071640d0ba00b080b580440082d003403e107400c0e001c2041d0700c01c1301c509 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 560164442 1250 560163192 560163223
    0x307170405060f1e0304030807200c060c031b030415021902060703020705060307110c090c0403120309080f0c0c01080105030c060a180f0518070207121b03060605040e 73
    0x34040c200418022503000404003104249061031960071024003000190712447c0700f501c0f40700c414107100744018401001903d00b0b89494041042240b01c13904001503101108000f00c954954514001c000c1c18150300650000b4100d9590032055801c2c8140007001610a841208811200e0030032100310480c0d8072854284800701080041400501604051000b0171003d402401204d101680c3c580100318582c0c02110003000007080340c00e150002260074002d110710f03000225011030441c244001041160311540c4030061848150580882c0c01501a0300315075003013a0003145494a5002620b00110140c0c00000c00003107a0040840c603101640c01014003d050710300280c000c0071a00c2044c01441007540c000806941070010081a072480303a850281040b01034149240c480d0040c17403505c010701124602c1c1e24075403e00c100950f4204504150300007100c43c11a00d009334500080d076000d00b80242c021030084051905418002d001000b403000c0d5811180454605550410003039440c06002a26004501c001162 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 560165692 1250 560164442 560164447
    0x1e010b0906070219060504050411070506070822050d08070c030c0212070323010b01080c0d050601050c030307020114070903020108062b0f05010f020c0a02131508030717040506 77
    0x4081c204103000c0c012040c809043e1000e142070380841d01a020000c0d602c5107001500000e81405141441e00412400c81d07078059600341001a07551b140f50300c1e04070040040c010013880030001061048101200000140c1000094402080c0c0b410f0894030b40b002ca40c22100403c0c05813001c40d507003502c0b42e441c0c0e090141e099a81c0381000d4400e682002500724003c2809401407080388804400709141c11402d5010505405070f80984641c1c507030007076095a61115646050041ba03e0401050a41070b20403548a48032044000880f50769000050b60f4500542c50040900d10010040040c640d405502848a00600e440141c500d9030301d880301100c031200035000c000d000500c44c501085032030901100200c0c69803550f1620501071403d492549009448020050b640400c40e540c406003030210a04c1001c07001c0400780700035842d1448480460b6a66500150300900801004135030402c0d02d15540d000c28024803255030800901940e4104950352904101c906441c03401190441462407003c1c0707000c42d411100050849030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 560166942 1250 560165692 560165707
    0xc06090806130c05120c030c0303090d060903020106090908030601080c0a14030a0e031c061d010b0a030b0a17071d0705071509030c150c0905062505061e010b 69
    0x1540b40e030381900b00712588030300c481001c500d40d61808801500c0c02c801074003e10302c3c42c50f075008140ca0110400f07401d6009030000c01151900d42c4400b880000c0f001d40210317001c1509080c070b143c101d004100662002d000a85000200010080560000c602030706090b0f03a0640d46031145406c0341d6842c0b04407074192001c2850380250900d0003040401565100c68021780008801140b4140541194040100b07100c41e150564000c2d5100c001a01c2a5005040ca501d031070780000503034186140c54520180141c1e0700e03280000c203414410b10f200e0f40003014040f8000d0200c04d41c0030780e1600741007005413800200034072602503044085585444010102220303003049200164586440c00155942d620032a820b59a400641c000b081c034404c114054003d00900c20350f585207582410381000d04841440401401c00d013807c0441320515551310604a80548038211492a0358400745141c0c0840c0344001102c4112064460081a09000f408500140708440c1501a404005004440310a11850900030715154010a00440 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 560168192 1250 560166942 560166961
    0xc0406050f10090305060f0403020d0e03100e0307021206060111060c220305030304052a01020703060b040f1104031a040f1704091407120204050a0504050a1509090c06090806 76
    0x30b1114155810802401926074584608001017154218030078841c18041c40101036042040b18032055151a280284440071130019441e00002d21080c100d01340c2325006114921002c0c4100c03448698010180001250001c001e251940800c40f1031034042840700e044503411081c081041849003c120030320528007a03a8001c64905968072841c00f101c0010001c00c041f00080301000158040c50240d0004c0ca01200074418000796104e283c0c02000c103581c80d0101215030390b40c002500c002070303a520000202d60701603800b0200d0020021960000c611904050340a18200c01c40c0c070043c0184c5e03000c0d000000c80549a1401049a00b50a45004011681e0030040c0408103001d4110040c0400d00d00d51461300c1c15070381d084e10b1000c2d14031007500120000052014451125000881d00722802c2040b8020750038545400c00042c0401c0680c450113016580b108001207a900c420b900026803c000b0750f0741040341c43d0b1200b107076000804403501c0880302c0742c00b00100411b42d180684042d03011543d41c50000d110f40d80e00c11410 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 560169442 1250 560168192 560168209
    0x3161404091103060702010515180a1a100e0a050a12170d0c020f0f01060b09010e0f0d08030a060905041e0f060c020c150306010c030f09091802030c0406050f 69
    0x781c401607044200c0c06503d980c18072003a40a654254000702e000c2c14840e03080d8803140c1c011084640305410079103c00b1402030030f0120550b402501e0b00000500c405450450b2015004410002070740449441d2000301215084828440c0c80c2106542c0101389540354418018644000d004060009910721403ca0014000f0320803140e0300515040c2d01820046002c4800054035403460410000d03800105411200940401102e8201c000000081c00700b54a0003818444038491280c0840c10400724010700c0b031054441030303181c251205025186c64005006410124815001a140460071b64100000000c0c0d5451174003d29015540005412110b944180d070240c11007a06c0100403103141c0407070410000450814070821140c0c0764550090200c41540500700b0001d401c10314401044c0090502c140443c0342d900c004004036540d414244152070504416041e03411101944c040d65460b400c080c00704050a10388442004641d2003601140c0c10300c08503208002c181c07140b90141710f4001202030540d00091400402 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 560170692 1250 560169442 560169461
    0x201020409060f03020f04050609150a08030a0201150803120f04150501090605010f050c121b070603020a300f0917220e06040908040b1803161404 64
    0x1840c16960711900c0055500d20b910603240e42400400420560a103203003642070100c0c04480402487c0f4103180080c80700000502007082802d1000c0f805c3d0b289864105440703004c1c0440380b00b10b903110012a20000c2c06450368420f001d040b031203180b500245104001003512101c0c0322803400c0b41d8140e500c02c040b02102110040c0140c0e803140340c0030307a81e003401900ca218050280016441c0405c54604103000541a81c02e81c0e001c540811070100401808110f001c01c6408480100403c415a52003071900458281c521085c3c1c0f60303403140125507002a440350568010300c101c040382d40301c01d03d20311108081d80740780741c0040548a4001700703800580000000303d0340c032045030100042c2000545020603150320b00859162040cc4080c0c020000c3c3d203c86056104440307111049c803e025481c1c03c1800d269a410200c0000741c4140d0050b0f8485041034100046c80054401030300c1e109103069180c0e109100f04020540c00a07040742c4c040c5c0148a154006884020390800c1070300c0c510b00409402c0b1400100f8000207041c94075 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 560171942 1250 560170692 560170697
    0x703080322061406040b0f360f0402030712030f0c0311070f090b0603040317090106051f120204060c08090d060c090905060901061707020717010e0139 66
    0x408410015070a4410000c00c3d0300100d034100618a096020f0000311082201200e00c00d405034041000c40d9502c065500407044d440020340c646500e41c40c0c100b00c1028000c0341c806032801c410702e020058601c6100303400600c2a0b0007182105c12160792003090b1a011440741c440030300019030707140b801c00d80d1502954003403000d64840d01d0004003158500000d00e08240048c1c12110346000c88030310400c52001d45004403020120201c8035039141d8201950040c150629a0214052801c11000000c254201c02c0d0721443c01800d000d8030311110b00f0348810100c0c0340382c3e1f15440b00034046108205280c1000c00c641c1300f62804c1d00d01e25101d02407000340c507880c2c0c100c864204407804e5501c1204082860300060542c041c00803c810a5180c07850760700c0c01c00400d101500d10080c400c0b4022407003800100545688281030315201110000d14503107548610504034103120843d0004080d0180964014501600540c44028100d85400007040418803110907000c030030104400068070aa0240c030030000e0b0102080e1190103a9000c0e0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 560173192 1250 560171942 560172001
    0x3060904031110020c0f070807051c0501060603020c0d090e070509030a06020d060609170a02013e0d110c10211e05070c1101120e1e07030803 62
    0x41100c1d45482c080403d40c0e44410f8000c214964402c01c100600454a0090005440c080d401d25004a956518a1142511400e052405644580551760350038480c0d641040084c0301041c0c85041c080c020b58008202c1e001644100010000f03882d1050380c5100c1521a280340014040e118501d0444d026040001d500794140503101039840019224030003050030458550300403418a01e4a1405412100d007a40901443c1122040e051b401100c0421903400c0d0702e0b03090a110759080d840307035030700b0000b20303040b40f498909a007a40541e4440100c101c901d107480600d18004462070502402400c8460200c0c40d001613041e41d01440ca030551034a0a08000b007401b80580c60040480c1e408100074044140d01ca96a0001c16a03440000c18014403108880461042c5220000d02280c240404001c240c08845038002d0541c84914119400580c4108040c02c0640d108280c14404034986500003600c5151030905540e0180100110100000c00071880c0b03400c40e5003003a03d081c1180e4900c0b4a290020025110201c00c40c21030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 560174442 1250 560173192 560173217
    0x1081e0c0d090c0f0b0c150c040305191502040b0d020307180e040501060b1213030504090204030c140108010521120703050c1203060f13022814030c0306090403 70
    0x40e11800000b10300650f03030000e01d207240911000030f0444582101c80c0190307081001890030940004c0460780d910a00549044a954a1042d00d595001d960070051041c0a00002c070400100310809254040d23009211004d079007850400918120b10992040c544550005d1104840c15400b036806940d01160b0b50038101e1801c1440c2120b9404495250400c64240d0b42080610040c00404d104030809005000603d51801c2000c0c0c5c800c52900c030006200072200350b4083c07400401c0510401c01daa0003070206200554403140c80307181142c000c50175406281c1da131a070081c0e181d00c0d05611500c0045d04a41d0302410080c1c10844218811108181d012100b00092044401040e01481c554004000b124000c0c0d036529128440c0e107158600784006103c07546403020703041c0280026981c8203044404425002c540380d032401011540994040e0003101201200342402c000b07003804903810314020b6809000c00f9600c0101d26140310802d49041e00040c3c54107600c10006100240081c104402c0d0070381c00901038104038000040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 560175692 1250 560174442 560174467
    0x1030b040608160e07091a03072c01030e012d060506040308090f010206040b01060c051006060512090105040317090c0d050c01090b160602090a0b0d091101081e0c 71
    0x2403800c2000001000400c1800c81c403503a0a608408940b0f04407603035911f4500400003580351210110304205001000c42c4e42c560088074445003241d2003003c2106a05110340da16000f04003444000d074040b0b410095107842c0300d032040c401c0c0d00c00e0220103401c043c0c0650144c11108140f010600300a5005035079603401041c00d581e0f00f40075100444c440d084240d52401044240200c41c18185200f0b07044d5071051042c07200040c0c40c04821419105103103050119900c1c141012450074414a0010089524240010034010740c040010304050254501986464844048aa00300d8108483c0903001610340390035007c0b00c40d020301966802011401c2114458183c03900003425503c0310307030801c03202640b02e114008120350b00091200018402464140d0810240d40404200d000b42520b004043c0c1d0382c00241c0940959030389a1040281c007000241700c0c2c640c1ba41d24202d100900710b041d01514480075510301c8480d258421024244034400729500b40107031f0014406010398886c0d0141c009aa25082802902500c0c0d0713 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 560176942 1250 560175692 560175703
    0xf06011412010609080105060f01080c0706090809030d050310030f0201170f0411010509010c06050901090b010e010915050105120c040914040b0f090613051005010b0d0c1d01030b040608 81
    0x8441d0707003808035035161481c051308035250f6500465890341030808100302c569800c03100c02e21052080c00c1c100c10079501d60540403081d214440c4010141c600e0000040180301e40c880141080b6541903045807581d024021381601c01d40001c0300d13000c201d1829014240002561a140590018810b052200717400c9846540e00c41c82810032113225101c500603034100700920500f0044040074810a003003c600d0441a800000d101c0b941c8003002602145d140c0000c0b03000014258840301c2200d400c130705004601c2d41c49502c80b840d840700130710a482c40345060584020524650852220450320705846442c904001103010310051900145101c0310f4501c00c1c000020350070514001d0112080e20b01c0300502e9180b90a1034100b81451001c1c2c4040d04414800c81007050842c0d00240f000d82015034610400c1c1c0113599483c00c2d91500180583c02000182003070000949030051001600c3c0000103c034081c04660030300e030411140240c82d41240302000e00b042640001c2940250302030458408080e20101c0c446440f0440b40345400d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 560178192 1250 560176942 560176957
    0xf0201141c06060905012a0f1b05090c030105090a0b0a080a0b150603180c03031309180503250204090b04031808030406080901020903070602010b0111070305060f060114 74
    0x20074024500032030780c0d1948200c0010340031a09005a54a0800000030f00592003240e44003c080400143c54800e244c104449081c225032140301c1c030099155a14200c504c9600140151007181509440801c040c50039041413442403510442040c1275a19240070000480009000041d405544080c0700001b80c032a8000300002d0440034006002c161010316029a184000404101c00480c10a51020103a034440c0c04a1740c000900c0502814540400703480603080008100036a6458800040c00d03281101e68118124102c45a522080150b1040300d203042c1d10200e038580e4020071a8004109428440a40800036034200380c088000301c4d29101070742e011400300d038041c10b0140c1d540c0901d00304000070036a200b800c52460b0443e12625565880c6090300709036580c0500e02a800c1403010040002e40c08602c2503060700c106c880b0050844550766038402c0080c2c024090b0740040ba00089940044400002c0300240030000c80340d00100800c11641c3d14101170790860005484541003002d80010501c0e0f00d524007000d406403 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 560179442 1250 560178192 560178217
    0x160507022209140d0503060a05060c0f101d0102090108060108070c08040933030b1b030a09060b0f010e041d0d09080c1002030306010c15060b09100e0306040f020114 72
    0x480e403056050b45071140413100501002010070030400309803112807601c0116002030b500c282d1a0b2400603406400d000c06655041520701c41c0c20911890010780d500071034214001c0c6595042814aa481c00a082c0c0c820303605d0306404039010703402103041c43d4401c0201503841455864100b0f070030b00040e60383d4000c50340903520122a1684a020040c25800d01040c0104c042440c45000c0500203141460280c1c00e1034039203c05003002c204100003401460000d4805007400d101103032a603560f03240c001c210100519641d90250340980c030f0315210007a203083c0300c2005260404140c5440504038400010000540390400d100340e8188a06c1808004d00d84040003081d08803802525041c0803c0d040031000c07480e001300500254458820b840b508440503801100700c0c0c0d0088405e10785404488c1050802e041304c1c60f8a420303801c00b003502d04071000810340001405054124011a540c0341003604159044070500c18103800c040e8035800c00001f040004841c13002d1075602c5807041c106560b4600d5440f41c1d9885a41003902040007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 560180692 1250 560179442 560179463
    0x209120307020a060f020a030f0216030f0b06090105130525022104030309170f0d0201020c01050c030103020303090d150f0501050f040e03030114011209050102070209160507022209 79
    0x21880c2044020002e01242d2070103030400b0b60502c4001f552030b45a00005000e0060b01d003140b8401c039109106c0ca00c03078100e0020030300f02411760740d26100390883c80c0300c0c80c207443ca00700b0304001c04d221f490407007441c074104da030014403c44d08080d907100e40100411014100b5001c105180301e186180300c034000460040c0c607580341c002e080080f141041849021220510019204008100c10f20010390481c526500303884004510302d50301c00e86900034918202841c3c0b00986c161150603500c4c1c4446905400601e40b80070484001e108a031255524040c00780028000250300d500207014070304440c20824903208202d070040c882c82d1640c0d43c10036031003c101c8480f44000c40b0b58a07220030040c082820419030752001e030001520108041401c1400c00794a81c0018000c1d1320301e400c01c6980d100d4440c1e1080c00340100c1e14065403020000180b440c40c01c4d034006c0d0311141089000d1280f28001411702c0c05080003990000603181c0316245464901c0e400c015006107480c2d001540d03901e511030048810700362841048a280d204490709036 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 560181942 1250 560180692 560180707
    0x6032d0e1501031b080303010509040f06140a0c020c0f060409090503040306050c0a0f0206040203300c0d03060b040b07080f070b04030c11041a06070f0506070e010912030c0f050102091203 82
    0x4410070b103a03070170200244c3e208200402c05904d9816840c0e60064028460241181c29850100c01510156400b004c030100500c003031240101c1e0580c010007121546400300d030480c440403c14406080c2800750301c9a03022506010811805d1005e4101841081c8111700f5649083d40780c2d900c08048600c02d5500042e8002c0c0800c0440d42c164020306036031450740030741c0000d065070300d42680000d80d148807040c803800190180d81c42426114045006402104003c101c40035142e020146100f0f6407402805203440c00a41401400100402d0310300c11203064503440200c1c14038000040e2903c0c445035208954404560b6010411a400709040910007070180d40b113540c1d070292030002801e042d1100304102e580c940c0300b40d15040c0b04150300400c4500d0345001280640b441c60b100d0110307043c040c5246882e1035000d00b007070041404001e01c46501c969150b8080c0003d880d030b2080b01da21450075407242c818034039004010030000301c080d201066400d55050401407080e0b00252810342d040780030407428410b1228903406a8800718440 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 560183192 1250 560181942 560181983
    0xd05100f0e071707090501230103180812010605040302090109150b0c0f01150b04180e07080604170a090504180606060207090e031905070c03051606032d0e150103 71
    0x84004003610178003032140754107088000000c12120000501c41240c015581001c0c2e07406900990302841c41900d8003142c0f10101e0502c030480ba03105000ca044543c00c02400030404601500c01e640c241e07a00a030403051143c2c02c007000c0c000200101c4071061808648200e0001d401c0a043e0010a0383d43c6079103005c0c0004076215a4541e0035244800e00c03442c0064036000062254115010540d8221046842038030700d07440700c20b41007034000c1405201131081409551004180b6460008009028611481d241e00801010300c00b00043c50092000440004140500801451515400c6840e01410150002035007203542d507103034002c58015501c104003503080340404101404061080d21031400c00840a545402c019100400030301e164812000240000071030a0020b01000707401e140c01440d802402c417510305020b10450a4000101d00c24580064146500624242c407208443d1086041482d0313040380e078050400d1400f002e00084010341e100c0b84038148550060070205441c140c02940502200003c40e2a5407511 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 560184442 1250 560183192 560183203
    0x2180405010b0906210405011409030c0c10020f010e0d1805100c030909061412030a020a141f06091401030b0705031e160e0d05100f0e0717 61
    0x405106600c0c2034010042041c4810868859000c225207540d901e0055050090150702120002540034501138200010401d05503c0b01001c40880084003002e948c07100b841ca5901d1160508601c050b41154110301c55a0511104852504403203005807200300c600c142e441c42c2162203c01c80c071185540b01d0307031002040a410046001c1124242c3c0140e81c1307664140703c0070510804264840404200d202c045c45824184030f1842c500240c0352122080c0511a65004006c941480312118a486042640b0200c16002000800c803014650150050700144180e9245d03004420918482c00340c1038002c181c089080c4030035036400780320f8010399203030300041180c209038142044600014108400038901320050012032440004140d0100c85440c0c03295030f0341d5950b20749007083c10303071038041102004080701400704c0108240c0d8116140c440da43d8480e182c81c500101005144404880080d0440c1c11024451280708400e40060003a0038007954042451001c0c480400c0c6004107652081003580c08000800c0840d0500740034 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 560185692 1250 560184442 560184487
    0xa08040c0f06050f0d0b15090109120b070c03030e01140114010201021318091203050402090a0506060d021605070b19022b0e061c050f130206210a02 65
    0x90710007800c0c1407014003d4855000890300101c8003103071040f1590100c1e00030480c00040a8101e50413016070a030603848076003141c40e8807400b1690910b008603d450903908503501850b0080101107081c2c45240c01a1001303080b4041c2030f410103890b06020745580909005a08461009001d81d070340d1903141a454200c00d12060010904690042108140d024001074106003900c0c003d1138081c400350a9640020300903d00d803030005100c8100588044101e9426038041449130f4002d40c3c070b0700ca06607101c1000200302c4034202d5403a94404824090b00680e00c40c59400391001800741e6032110a507244c540c40719840c0441035440505182400100c002c002c010055403000c00050900051a0400d4001e02e1035510161401d902e10034552804a250000c0344904903540e10200003900050355010030740e03d880c004040340001401903605160100d8003c0740d00c0460f1a1058002c014082074030701840c2d0800c805548200c0220140d24074942180d980309000105050084100d0100140c8d980c0705009208448440d818 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 560186942 1250 560185692 560185709
    0x405101a0301061d01170322060224010603021c0203010b0c120703080103020114070611030702010e150c1e030f070f1d06030a0626160f1a0705030a08040c 68
    0x81c8011849011224490558001080c80b41c6c18016503010f96107503000311040a8840d80c004264000c1c004620041081615916825a01c01d1801c515030706110b4010003032400f14590483c0010841d15119a0281881503c00a03056100c0301c141c403500008c0c2c3e0020f0700b041520000024903050740321410070070128002107840225040c2100c685018000180506c0064144030980004010b070031407010071a03050a80c0314100308081c000c1d044041c1203540044071064003540c0707400c0c43c5c01284400081c001314644d000001d8110646d1310384400340b001341c001c03003101010407a01401c556501d01f2817401540c4641c0c84114034114074a08454020b1900e05580c1c01c40c8207100103010101900c2035212038904500d40244c4030030307540391100d000c5000205440e078450040444007440343d40f98031100c5c1a000006030040d01c111601d02d4000a40e0100000c800d204581041300c02a00400c207164120f04040380b000c85034000641020380307075250030703046034407104108000034005010802001200d00701040a8140b10 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 560188192 1250 560186942 560186969
    0x190e0a150b03010518060412110312010e010501020304210201020f0a03020c1e132c03040801061a03010909053d0e0307060228080108010c020c01170405101a030106 72
    0x10b00641b01c4801500140800381307408088450f45014040e00511640008216540c40c1e2011000c441840c5c002c0c0a90480080c03c8400001c09603c0042687c0940740020301810041041401e00404501d05280803030650013221608450008280a10f039a45806900900250f240e400200701d42c0300300000040c0ae900e0f481c0c6107050030070340b58000311002d40252036100040e171031141c01000030301ca00700101404070301d0303994200312282203804809403044400740e00090084685980751040d19081c1981001205003081c0010040384007140c00c0045014020020381e20042ba0306020a543c1c214000b5624443e0b4407140d20400030f01d8a081143c40584846910400076894801a1a43c0303034881c05601030081c580110381c00310340407503885400d035030000b42c0c00101d03000321012140a400c00609101e240742c00d500c2c00440400c11400802e019034803940c165200c0c03040340c0340c802d014000508042d1050790070344103801880d2050f03541403140484040740c0590405880a5942c01c15080d5040c6070046103202c880c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 560189442 1250 560188192 560188231
    0x100312050d0e0d0e010318020301050114010e0d020f060a0903080313020f030a02060a0c05120409090c0905090c0907120f020d0c020307080301030f050f0105040f02040c08190e0a150b030105 83
    0x100814401544c2d0901e070110700c04510041a0784100101c1c032000c0d41c5035280030b000154140048900c000485d1082e02c4c0e11540080d8030741001251066450b0207900000c6210303000700796103400301c0245206840d03030a2038001035031207480b0070010f604101c90b4072400c120001e03003420652410740b1482c00100d00c1140145070714282903000c51000e01910b05000140a00081c1a00802c4800d01c0a020240c85001e40709482e1039650000f0740250003504010b4440418400d004541451f203802814400d00411005020b100b01c00c20500286440040c01401005221241e849146545026001c00c00f0090b04001d0303110480000302c582156100c2c1030034819940100010000a1683d00950303045079001180749221070400c1c01c106040050304008183c855180804001c02c100302c1c1424031700e000340256402c0042c10294070095860701d0098503051041b4801e0502002207411071b820908003940840c0030348944c0c0c1c0c0203581d42c40681c2000390048a00b0b035184d40310366059041c24803400e5400540c5d01c0015001809 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 560190692 1250 560189442 560189447
    0x209090303070e0f0303041805010501200303010302090601030e01051609080c130e0313091407050a1205100f06050d110f1b01090c150e0111070e100312050d0e0d 71
    0x3c2c540c60040c040d0100343d6407401e41c0d81d0140107860003070800c000403800d4140e4a0341c061000b05000d01a0340e010914050450280e4008800c07050815101e0400a501d5139085408020f4130031802001302c3d04054a42126012101081c0541400341001c001180c1b90806c0070ba034003030722204180d004250701d81d222408944260380c41e101c08500400340644005283c546d4001210304510030702141046484840c80006030700c4031941d1211110550103002c50f00c2980700e00700d0846540c440c80441d032000441004d00303845201da55911486e040300d040010000451b85d1076071800c0d000540760340910042500820002248849030160300010000d500603e0b00d491070590800c049d038000c451050f40d6405800141231032900c1d0035840903060340e40043e210209555034000c003520fa0710804d4032620005200380500d06140d406040840c0e0802036444c05000c030b440c2804003448100078010008101c500312100300102144402d20b00b60b80c11501c613914140c1c0c2e0741c0403900f01170555130002d5000140b90f02041e08204800c0e07 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 560191942 1250 560190692 560190707
    0x2011b091202031204170708060c030f13060f0906051303091a040801021303021e010806130b18240a0e1503070603021e030c12070203160f020909030307 67
    0x1644607100700301105050011a10741580820142020b09001601140d03045480e00f0f24904110302c0001c540b541501d074103801e5103610042d1404034400c0c4060003c5a244186038146c140d0100d0920300312411404c003030321f82d0416283e0b900440040c15640380400411312526001d03280e44442c8003600812410107a40d001840207409100b00142021211101c200c01000c00c2c0454004002d040025522a401a400a5414492880102d1188020080c1c04044c9410610324500d401c0050319014803507500c04052040b2002540c0c06400303056941c913512005640d40c03c140c0703900c4615404141c0c8031498201000c4005008405480094245c16000c690320303907494501100540d0420394090304140c0b61880d420700d40c1903025141c03540c980510a4042081641a40078050183d44103108400c240fa40d010090900e10003a2045013048a04200e003000a55036060000e403c200a0f00c102c918080b05154a440804c100320710444003c41d40e2030001d010351070310803c8550421200405146107081c908130240166 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 560193192 1250 560191942 560191949
    0x3040206030f180d02070501200709020a0e041104092304020409111c06060504090c170a0209010803030906010504020f0a0e0303041e170a0209040303050402041b02010c02011b09 78
    0x40b141400a5100d0484184640c0700e1003050040b6003044095800282d202d1510340240350005064002035445480e070314204a200e103001c04080c007481ca08008404010707500440181d014440300384a00078458481d8428251042d06c001c00c402c1d2220308082074282907401491054000e503400c24100700c0148401444107422a5046800245039541d9180c0001001140e03801c156000640c60210494030368010100d014051103850200400b9446600700400c031021248052301c64040c083c0144035045103600c00300342503020b041c00c540c1101240c2d4000740284600760000a41500007006100659508101050140c4130031502542084409044d007801c0e40224040c803030402c0a0b42c120b008007500e0910403180900b0401103032950060200915800080310751046c134003900c0c075100d050103a80170046002005180d00801c0c0d1441c9807030302d440c00c80150801500a07030340183e840c0034034030321801c040e1000684d90001c0d80000c00c0542c40d0200c080c0c21900702800048110060780307650b898540d03200b10002d0a4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 560194442 1250 560193192 560193211
    0x203100504030921020d03030504022b2d080c100b06030c030604060905090a03021504080a08090102040902040f0302090a0605090c0c01090503070501060e09070806220204050f060a09020304020603 86
    0x1420301d004222914484d41c0080690001041307026a0181a0b0541010344110b00980300940c2c0c00d0344103240804558600d560001001a4045141002071521381c281ca102410491801e400c030f00750404101142d03d16a0740865003a01d0008a200e01c400c01882002c01c02d0f0300c880c408105d150400e20205070544401007400c0480350b0300000181040d503e543c404005003520200821081c81e04215503a41c1e02e90010058015104a44500d01d051030700d00800351040341c0c8040b5041c10304d21104815100f06e18040c11000c450754007880701045408051001e0001040258007018480d0300d98018000c6601000c1c2c0a440f10720700b401010f004940754605810342100b00220451307070720840e4084550060511403c020300e14000058080180001504080151003802004041c04d4864500841c0c1d154802c0c42541c4013a000200013802c03100b00b2181541e03e82054120a041140d140d50002e000c07940126894810210f0b003a0500890f8107018202d02d01400d5941d10461443c18181c00043c15400014114a030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 560195692 1250 560194442 560194469
    0x20103020901030e10240510050a1e021005010506130b0c070302061b0114090a0209041a0f09061509010312140f09090c1204030c03020111040f0302031005040309 71
    0x219903c42d9002c1829149007000340c441d5100307003400380f41c0940f09005260a568107071b20b60980110303a101e2084400c980000300001c0700e440b0f04800c1a01d861300714521001c01d01007440219000e80c092850f4401c0c03100040e034040c1124120800740d64086420613081a030140030280400d003843c0c01034a803601c06071f610171654940c98100c9007842520303011980d00300a4021401044004800c00b01400c4076540b03100074002072140e00c0c00d0a29800005908a0307801c021540118054405800c00790800340d0071034003e0310249042548001120070340036050700e4041d039400d0020100210030100f400b900340c0228080c80e1903231504601c20002183c0d01e0042c00040d102a0709112203103516800341c8403403242c100d4a08900381e1244082e402d4000c040c0c201710460f0f030049031076030001000030301c51a08a0350307404a00d502005c0c0725280da0701c044404e0a8000b40c01c8080d5940d40c800c0d0b445003040800640300800d18a03807550340060540c0305044c20404030943d0908001d042c0400c0c840040c0d000f081032004d459020043e02c0c07 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 560196942 1250 560195692 560195707
    0x1170408120406060503010218040506090c070807030306090c020309240406110c04090c0807050402213301110102190c080403080f2223040212070e01022802010302 72
    0x1050541d1095074550320001d103003000400c0c200d01c03270241528100c07002c01070b5594820601484c18011a940c00c0d0341c0c03004201c401c0000d20454040c140c4140607250006140b40c0b03030503d400440d0001014000540d20210b40f03050f16140454510240c82d855842e40e030000c03141c088a1800353302840c0140700520102400900c0801000c000091580c94000e2007401441480d00300102d06900c903000d8083c4a0055800115441c246030003101c2e007141642141000c42401c20204045e81c4402030b20030512a10314822120103c64980540030010000e042103200b603000c1000003400d2a4038091000c11580d0046c820745600f007014030380c5131210701c0450900401e4200d013031504208910881c0c10050180c400402c0c0c451404801c4e0010303056129140510885e03140140440c0b070340c44003261281a001081004094400000c1c0c05042c03c9000c0020b03002504000c2c10310710504130100202c508000081000c00e8000b445d41c0c0c100441c500c141d0886440b08001007120312149081900841c001c0d040c0340d00050820b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 560198192 1250 560196942 560196953
    0x30a09020103151706090115060305060d060e0c01020c0f060405011b1502030f07020a0c0501141204050c03060708090a030e01120c03061e06081909050a03030506011704081204 77
    0x1148001190904207a500d40c507004120400c00d00304c0c07038403a1040f03c0c00605800d00522231071120442c18502800780170300c0d096040b0301a2a00502c800d400031410418a0002502c0e0700407800d03004c40250280a0650318000028600034505452501c508403040c0c01c2041c0e900c840c000c440a440080c41d040c0c8030b10011050351104040202c0c4010070491081074450604c4035180c0c05940511000c3c440113215446002c0200ea640320201006003c80460281c20051980510710b1010900f02c940241400c007000711b01c010005000484081d51142c0200040ca6028901885101d0380041d560400340b856042001050784c2d1080c0030300c0700409110341c12107411481ea003c1d00300a0706176018401c085c03081b6881002c004000d040248039003030b806900d10314000c4602c0c3d4149584025200544c1d00c244141d0b8a181001d0310140c641d40a40c032500d03030b0380c1c20314401056052219a1030940242c0340811070b401d104000402a121079000401e0301c0780d1500074000040c1c0b00e8403c85010032100b200001d11501e850400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 560199442 1250 560198192 560198201
    0x31415060c0f0307052e0b010207170304090b0123160b130b010b0a022a150a0e0603040210050a0915090305010509060f07050a050d050a0203220206030a09020103 71
    0x4121075124a42408808000000003041480d1094041e62880c215490028001c0c8522000c180c484000c1d04190000d1503c865020405442c81481194003c1d65152007101c071415001c006542c980c3c10016003031001241601071041d80303080c28a0b01c2a5028265245440100c190342e5160044401c000742560b900488480301c940b890f500100d41c01e0341030a0100568149841c1d040048540b504c0f05400000c00d100890281d840448054020788403942c00d0920041124500c4440e0401a0898131400c81d441d850340115411050601c11580e03954440382c15000c0c04142045051a11980041003000010385903078240301c0e00041541000d0313846845958041d034440c40313180c000c10710030514000700e40344c0950b00022600441c0d008000800c01d40d1180014213807203a0080750140d44060f9480f010840803031103000101102c42980c54543e0400350110100804e032441581c07140036103500801800740346564020250b00e00ca50b0f002c0c182c511030031107502062650000802050750030307580b00308220659000303801 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 560200692 1250 560199442 560199457
    0x181a040503040e01411c170c100e030f1b0f070510020714190905010f06140702010f0305060d020604090203100e0912070c05030f0106060f03141506 65
    0x941207080d41e1100145c8502101c52030388000101242902422081005181c0341e06481c41d029403003018184d120107014404611101c2092411080002c000c00316088050a100c1002814100780c2e540c0111200a490030024a0922000520b000906051040000111105002d03540c0700d545d1500c01800104404011041da0211740b030152800d119104480841d004c41070303450407a1f2031079070002c5003101243d48081c04e01480345540d2440d01e596049103001c07002104c02c0b5a0802e0081c060603111040c40003540c0080e4444802120b41d0001840b12039007059140070801c80040300141401d40d00d0700000e00040407400894145969480400c110341c4911901034001a0083d250980e2690f440b43d03160003d5104903080020402c6254011442c00d00040700f2900030f8803100002d04410107c00d812151640c82000100c0d0030000100000071162010321210005d0200c03034000080b02e61400501900c0001c41760400400c051812a0a0901d400381c880c9090300a8241c804298a6401201c0403231040d00c141d07035 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 560201942 1250 560200692 560200709
    0x90c0e0409050610090908030f09010b100305070207050618010e03030d1802040f020901051c020d0903021c030b2101090b0f0114030105010b03190b09010612181a04050304 75
    0x14034120901000180c1c41c4d001c1c000001404100e079076a542d82004031044520f00600701042003001c2001c50480d000c40582000d8241c0000500c010000e00050b2184a440c41050120307813a801001000c2d9014003030f120003401e06a50043c40c205420302100c4001107508815410b114400c94150202d48041043d176400000f07015080001c0c002c00138030742484000200040340324500b0711114612161140c000d8031702242d0306031612402c040c12500312600444041032030b044002d40c20b110440070030130f13540241c03100c0b180a5000740c10480f024605070f01c03411a80100c1c9801f81401c115045101e5100c0c038500380500030901c402e102c00e0341e105070041405401e240b440a4030900480c42880001d9950710740b0a0b04135000c0446204110200310305042c240c1d0824403c11880c0c883c1400040c4c401c51139a241c82d951a56520000a03104132100700081e1803601c20380202001801c5882645407950f503d206489084030031031821a0480c00b56584e040c42904003003807440c07008498101003810414104140d03000b818640 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 560203192 1250 560201942 560201951
    0x60f19020c060f250209060112021c060e06030f1c1202030907060207080d0909020702120703060b0f040504020a1203050408100b15070c0306020307050d02130303140c07090c0e04 78
    0x1d00c0d4043c03642e08111901d01003804414980c07152124801150583d040c0e02421030380f640e90b500801500c0c051801001e00f91103903000c100802c540300b05040f104000307850080c00001d085003001c02d684584070009194034001e40c03040030540c0b40e200c0000b42d410b06c508040c002c10031051403005422510500d40100112101d4008000d0204078040442e40c40c0035544c0c0d560880700007541d034900c40d55030b801c0c240180c1d0010402c80c100074040c04006400901360580050068407503450190034452401d10154010340350641e030392081c6a1103140c03540601c1c503414000c0b1024001c43c03c0a40002c1d030010018480e04030000c5002054a041601071002c0d10024051001030351034a900f01c0c1c1110003d80741d0400d14511400500300c508100902d0780c800e80b260650041140e407d92815952844020352003d0f2480c4d00b403141c01d003c00200100301d4002405001c50005803600003a2075490041e040c41780304003100c1c00c000028000000041ca0006040d4201c036080e00001c1001c1803610001c1d180c41004845164200d03050 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 560204442 1250 560203192 560203207
    0x5070602070c030b16051804090209040b07030e0a0519060b1018152304050301021b010c02070810050a060b031609150c03080a02040f03150605060f19020c06 69
    0x1010742d041c2104d004465910440d902c400d01c01041c0e0003004103030008201306004400032240e0304d014041e0034a602400001d0680e51036000a141004111412104905540304004195a26000d030b040d0880c501c00061040d042c0c1076880b107460f100c00c0210141c9055040741410148400c0b0b400035180c1c2c1c040506000b060002e0030384c00510240e5400e06007514640d61010000702d032100440c10380172814813130b900c1000b42ea00f9070303104250000c002070b8170591341142444041881e690a200828100da074040742c8403068202e2241c0d8900791180300c80014250741100304c042120000116901c0c010840c415070015541d6a109010f4004024640046205440200c200031038034030342c00300800d2a032841d500d4405040d0380e102841c01051449502d0180040c00030b60285002074042c5504a800605201c1c0145c07c02e070300c1c0c2c1c1080380003801079481540c00c0011000b6804002205128000c082c10054851600c0c02c0e14000203840c0742e12807000c1d030200369042e1901c0c011865100b48482102001c000300f0300c41e0748654 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 560205692 1250 560204442 560204453
    0x3021e070c0e0c04030309030b040f15020705070515091c0c09020a12110415020708060c120a140103080c031207120b0d230304030c080a29040209070507060207 70
    0x1000d01400c0d000c010b5910100e603ca010000a890860760b056440d14904e0313055940300c43e2107500c05071003200c030740c02882c4130400080c1180c510300c166520022001616000c46017072031442e00d502070307000741d015130007a20950070340030814801c0f0340c01a41d040d00c001c40e825283c540f030401408458400504001c20641000c0b403004900c0d00140851210703a601c0301c4850110344c4e240c508035400d140d044070400390204030030060716a5041e18801c42c1c00ca1030043e03528181d522038500e030504808454800b6104800614000d525208101464102d03040e24410880a000025040201c0106004c080c1c681c0b02c011918216088040089440d0210001c6d00b5020a0410f0030020344036143c1b02198002d001d08200600f00f00c2e040c4501240c4c0d80360b03001080a40d010305034046801009045250700906800100030200100c0d5103031180c2001001c0450003090b9000040c10f000e0411031307a00350304c00417920b540c010301000e44020005280c0c0003501102d0207416a100c40d07009440d035214803400142060700101c1e030705041c481d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 560206942 1250 560205692 560205713
    0xa051005040606150804030e060405040608030c011407080402010e0a080a0308040501051b0306040b0a0f0602071508190b03011d060604050601020d02030a0f02030d050c090f01031b03021e07 83
    0xa01ca248144034154482041281d02c8413010815400a000f01c1c0024005c2442000b000e11004c802808052420744c990011a00751502500110203d0703000255034400a48240719461120340c048520401d03078101140d00030440c0c2e01c00343c40641080b201a60540540c2d4070030280000401c5d51504a8450701403e140c00b900e5a08119410380d081d520b41000160420180b0140c00740820740c100445213543c2d00c02c4102302c000c2c145002503d41290f00810702064130b444183c8403c0150030503030018403082d864190404030f1786040c014001c041141000c2400078038452043c900c4040c81c21403e0101c2d440000030042401000c101c68002c54101d0203080c1d40e05803c4c40031440d50f0041c603040d2400c1c0640d603500380c01680d0b2000e1080703038140160b00800100c0a540d104080c0040c0c0c07010313284150703441c02c1280c04103401076510a850654031721000140e40010b83c81d00b80c13200c25481c042800c3c2030040c048140c0c420341c840c03820960440d0030b1640006103072120a0040b5050101041128805520b07541e0a0500c901c108 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 560208192 1250 560206942 560206951
    0x7030b1207060f030509030c06181b01050a210c05210c16140d0f030b0a032409120203030601090618090c02030702030706110c0d050d0807020a051005 66
    0x20061503040003604140031846906a91060322500c01090400e00100c008220090403013405002c10700005816010032720269025905d410402c468018500300310600700345c8420600311103040d0415052100d40d030450155040c25001e0305050714060344003400300403030590942e52044098903000340007091a0300040640a10010002a281c10350350350009441010020b50702c2d0b606125041c80740010100e01d035042d10f42c80d2407082c00b1511540d0001d000d420315020500040c480402c502003641072501d41d15200d0f0200e00c01040b542600114a186c070b0303501c15092020500120305800412800510b070a1303410031002294040038600c5030421010b0000d441350400d0f14040d000501824000940522541c5501d86e94032403114552180ba1400150100800c0101c0a210940c00140003c0001d48c1e003d00450009281903220003030704422503160030b428803410600c66840b460004c0010004140e002802a40f48141d90414110303d4075150400d0385006030740900107040d4428a10446400c003180c2e005907014 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 560209442 1250 560208192 560208199
    0x304171b1f060e090304091e020706090b09150406020327070806090601140f13140412030c02030d090206160809040b040e03120c091003050f07180b0306011707030b 72
    0xd40341c035200140711242e401e85501c07201764014001404a040d582d40100c000248110b00394000c2e80e001075044c03040e81c000300400d580080d9540ca401c020f0141c49950b16501c03400e40400b800300b559015688004950740034002400701640030000604401250f00c103080d1003048420820801005140a10b41c1c44045000309200c900652010903030200000611a040e100c40c21040120001540c05000400c0c0d00c00508a0b445101e0101196000509118040901540081c0303030403a850182045091000303012120010180361841c0c4281d45903000c0196050007c0030701000c207030320300b00e8000520b003401a60812441145500d09000030002c07190000c000d5540c00303031014002d0814000c1000210352145000b01d1a0340c0041007540c59922070030340c040758403003d203104041c00c00d505c0c0e0000c03880b00fa0700c460845012070358850038403a2058601c1c11866026860703140c000101c4903502c048452050b13040c8208c0001e0040400400d4903030b80501b00c51440b18420400d4038503980741000c0001c0c06801c3d054000d501 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 560210692 1250 560209442 560209451
    0x31b090a03051608011e110d05040f03030501050913020f0d0b0702030c061501090311030f010e0c15040f05060d2702090f0f16090b0703020705090c0304171b1f 70
    0x12514018021061b00c0c02c41c60780b5002d059200b00c0c0c00308025112142c0180d031803910800170b007007801959203d418000e6004004140b00102c640c9009000c40b072041e00968410309047c010024148401110074006541c11340c2d0105200070f03088003088032481201c100038500140001000340159002011300001d000c00b0f0101c4501d52102850110f0410f04000b0050004910500900215280072035501407004040c040f00c0b140b00e80384040a01b125038840b441c14480e08040e01604a80c9401d50075032000d134920b6420740e4601480d00b810b4030f0010f4102c0c4191405020040780c0f80881c02c00c10b510400d01340c1d00410480e006a0b00914100c0303001c1c0000c0750102d02c140c0c1c5050204412403071042c450780c407441c0b450f01d5010301a04d82d0740d020200c150181901c1820400e0400c0f01240709074041d000340201c0c83c400d80040405c5400d090070440381c0000180145900c10040c030420002c0341380d440e4801010003d544c0303032540d08c18105c81310710040c82c80d480c1190028450401c08880c01003070100c0500000b01103140420 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 560211942 1250 560210692 560210699
    0x6050402041e060c08070b091603050105071101061202010315030b09010b13020307021e12040b0c0106060c0f0219230301050a0603022b050607081501050a0203031b090a030516 77
    0x2c41c100b10740140070b00310320400d102c4d02d00014160340580748c0180280d01242c12040d50144c494041e0f1b41e45400c206c40c0c85e511041804903994000c455803034070103c900001d02400781400741c0e880000c0b222504c041c0c10580c889800c800310310380342c550344e00165800404092030340c41c0400302c09000e000d0f084d4003240606e0556603003840c070485038030a03680121055800340106105004bd80040e20b4924402c4c1e82440c0a0090603d07054a0340400400c0285448940303d5103560940841c2821a403440d4080c8041c09440703007164002a0410b00b084045d01e80c100c50a4050580e014481506040650020040b61b002c00004080c1400b0545d01a006400114024005991034514403070946545100094004a80c1d004d5110844c81c0007079003100c60703c00c524608080320140d440d00c602e0450280c2e03c1e200031451010510185810798120702c0b2840c002820500d02e01422024004d40d03d110050880c044608003980c2003100341031075000c591101304010040c0401d9502d030f0402603160b4002c4e0340c0307040306105080c4000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 560213192 1250 560211942 560211947
    0x4030303060608011a03040209070905100314060a0b07060519020408010504050c0a1a03062b031b0b150102010609020c030918070203040b0a02100c0c0201030c081b07050106050402041e06 82
    0x10344c0645170b01e644079030035a1100c0d4280182e454000d04100d081c0409204045825120304400b50040442503a001c0f68038000150300310300c0754601402c40748c01281024001e1010000440446006992250000505c0d43d01e1010703102d00d004078109046110b500014001070150b45c15000b003405180903100313940303d4618010030000700c10094443e1a0980b011012600c4004020802640c0d00c080080e08604c80c40c407034112420500881802c3d50b83c04180704d04414070a0541c49205803100003000c01c000c11440006071201c8ac141c140042c6203002d800f804140114259100f90032001c0144820f9506540f900e101445080c0c03690070500040c0c1c02486031014900340115100c00203402540544c000d5460241440120440d542c4864a850250b20072a02001001409846102151440c5980311108540184001410fa0342e240c40711034200720340d100501c4018010954440003514001c2c00c202c2d0b40d2511441e0203405001c03254801c2c3d40c4140b000c1400200c1c05055504a2181e41107101001d40c21510303900103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 560214442 1250 560213192 560213219
    0x303120e010b0102070501030207110d1a0a0203040807120c0215090f0409083f180c0f010e010c061404050c0a0305060c07060603080307110c0a0b1903110403030306060801 75
    0x2c50059119400070070095000f54000c00c1c0c1303039002d17031030b83c003100c07031249001c202c0004010030300701c40d407545c0c00100c3c000100c640c152040d0801a00003040d882c2d82000d0311110124010303010064101000300c01d0801407540120b00303500107958083c01d420084024801c400626401121483e03000b1030000a104005250034410065a02c3c0d1140d0494281003d039183c5d02c1c600142c0e981890700722002c01031115038100f80607590f501100054510600c2c1444c02c00d4500029550850f040e010552103070200e00c6065454850080c100741c028070b0a0000072300e19400480c0c2d40c081e080c001420b824501b071654000002c03041c454510a42c01b403000c44001030507100c00c0c072210081510000d042030300b0840c0800d000200f42e100624990303001c1c040105426482c1d0710b40b550580c3c010350760f030401715480d07004400e900c01c0144201c908100003107030001141c62a20407100010301c580d042000c80c00501c0160000018041d501403021801c43d89401600c50340c9900d800390042a090003640046807020000180000c51100e0307 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 560215692 1250 560214442 560214461
    0x30105040c0611031614070308071401060506070f0303050603011b081f1a0d09080f18061c230106081902090625020907050d050f0106020a080a03060f0303120e01 71
    0x1180481d03001d5516002c0b030110320b030028182180161000000031427074041c0a48407040c011040098200e0401c4a2642101c44e5584450b019500501c001c8011420414500683c0c0d41c040c18003007180c0d5601d100182c018407564040200002000c84080c1c001540100d05610407a01202c20440711034101d800c2d000c40c01d0079031080d0f507140300c14a50100b0424241c0005440381900c0070b0b201044201c5542da481c821a00701c94a18841108081030181c01c1c8100b40389940f003800000d644c1c079841c0200780440600420710086401c05095180d94801e2070401c021010145460b0048000c0801544c540000800415056881c41640e10f1b540100d80c0b4024140d20803a006030034010002d40c43d11200101414010702c00c0f81c020440541514810b60240c0c9400d68a144141450758545969040800c541e104442c0064401012900c8420040c40b400790002070390921540c11070740c2140c60f01039041d402c030040c0110b608861885468800d00108040d00004540270030b108510041c400306022803103050895500c06c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 560216942 1250 560215692 560215717
    0x90a020310050c03074b0f050928030803010e100644090f0f0a0b09030c01020a2c090118020c0109140609060408031f05030105040c061103 61
    0x101c0c5c0c18901400c0f070190380d00b072a10714001030003003071124481e501b05060020030844c0345444c1100c00110304d448088504003480d030030280e10700000740380b008240c0e00401c80d0751409401000e0403000455a0306a1041401e0018028100200d481c2e01c0e021803150020701c00e0a0300138400c40e01140c0c0b0f0001e11440c010a440769907030380380d46400b80880c8100c10105620b08401c4400300028544020301c0b90784080c03032103551032210100a03e0a20000580c5071041c903640d840c169410500c010b0303040d9180840e10280c1035801c682e001500e5107410324594214412084480300d00d62002490088640d0404009103489205088014460183d451100c1280b40344620242d03200782900010b0121ba802060140c10305c10051100600344801407500e02e00315003a000c015141780741e0014080781ca4403020450190b01070610030180c42241820703602c8502a00000c0e040c5201c100c1f020102801b20402001404010440100203001a0a00e8100300c2d10b00314481c0a208000340000f0000845100000200c1d84240c0d42d06 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 560218192 1250 560216942 560216947
    0x20114011d190e01060f151e050c06090c010e04110307180f0e06130c0801060c020409060c170609070f030902121213050109151d09090a020310050c 65
    0xc41c1c1125880401800e2485449031000c100541901c0ca100d80d42450300c0c510700004007182818141c07104d610f442d5000c02c3c4000030b2005829070705640322000355603046100d0320501004c006000c0c1500c41c0d0107002c100040c144152030800401d981d00242c901c0000340281c8400070346c0103040c030500c03043d40e5105040c0c504c407400402c00b0828103485140701d21000310819125403050b5885107a40d0726407000c15488048a07007812030500c4203034a0440d1005101c005005001c10040100140203011400144900010b00c041000c203a0190344664001c42e11181d0b00c841d04002001d01d84a003e400c2c003000303001e1164000340d48800541e050900000c01e5001c3c02c0b154441800b904805d9800314050200b40d4001c9802141d00d901c9c8040b41d80080080c4840740501078121074950b8404140950350b1070307480e449141080108881000f80c1c80b451145001c2c040c0580c40c082d15642001c44000041d502d07201002d50b0041500320800c0141c00002c00c04840552080301640c000740c050102d0300b81075a40c1941c8a002c0403804 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 560219442 1250 560218192 560218229
    0xc0810210f0c030b0702031b0304050a5004060602120903030715090b070207050109030b070e030a030e0a050922020a0e04080415170424180302011401 66
    0xc1e41c2603001c1c9288a00b2601085079165651684009403e884020159001095081840852214009440742a60007c5003000c0c60800010b00072241403144062000b10390188502a000806c0c070004032001c1d1000c0200002c22018103030343ca4500000340180c0003d4402044500d80c0b40078028002204c0e40c0c1c0d8020041d2804000c100001d90f840f1103e015810700c81005100c0000c0d11440d010761501ca80803034001004840c0707050540b981c1a000744081c1c00c640281006001c10703078100c419041078940110720304d209a42c1e000d00940d9400d000b820410341c1403140c001c9502c200740d80003900400b00340d826a01001d0b119900e0040c405000c02c00c0c1c50341c0102c09840c40700c643c40201c4038011001d04a0000b001d00b64065500c002200104006403015606800000f806001107050030b010b9204500480c43c140c030000c0780c2d0520900c0c42c0000900300a0043c1014280081541603142a0102d60400c0240070440b0102020302c00302c0c1101559011000b55007007007031009080c100a00c88504a40321000d0503040c141c0d4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 560220692 1250 560219442 560219453
    0x20a0c0b06091612150b040e09150712061e080f2a0102070b040608060f0f0d03081503160f050a031a04050a0f051006090b010c0b040f02040c081021 65
    0x541c2c4e600a102d8607603c03480e0342e0301110f031201690003c056180b1107656071401c05003032111125000b0a800b566a1020540c00038100459007900e074441940d2600564511002c0d4500d03015047d5680610a843c000d10210000311000078010012a91480c00310340c100e0028040c0c442e20362882d800500300840002d0f2909035090b9004030803240495051051324001a11621000510303040360300101c000072102d40801c640c0d8109440c2c40d02000b00f04442180d0008500c02c0011780e502080040142007281c03120100f480c984490036400c0d055440101501c1006c00e080c451409000a9481b45c900c1d051818907001031682800c800d40d00a40c0e80041080f030800041d030a110744040b02c0500226401d119190303400e804503010342c401210b078900c80d1015010b80d40d1800c8428080e11166004401e04c83c0c50f103050710180340e81000c440002c5a1303100c401d0b40001e035502e044c140194a40d005001c2d4100f4104110384980a600c81480d521500c00d55018100154980389006030b030340c0307803900b194440d285440c4801c008a107 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 560221942 1250 560220692 560220707
    0x1110d090e060a08060702160609050607060b040905010c0c11040504030207170c0306070903030806010206010e15040e010203250c081b0c030d03051605070f0210050c01020a0c0b060916 81
    0xb0710182403030310a40d5550b00c03040e103400c100300d0f80c440060b0082603002c44540c50440c0340c600180704138601440424108030000b0014494081c00400300c17a5104200103107034850b0b811040c0d069070031500070003c8000001018198209101c81111300090003121940c1c589064800c160045c2e0301036008006103800c10900301d41941001c6c4848189110301c82c40c246050780d08010003840b40d02196140000c0c02d00d14600a0305210010b040c860554000c00014810f0300c00301d8000603440740c804062600c500f0001e5021400812514040ea00746500000402120410802c86401c141c1100102e1716034451003032038101c0b20b2143c42c260007889100108024480102070400c90b0a445d070752082501c0c40c40b0340d8000002d02d01001c0038090f00110340c0352020003880034200c101001112001d41841c0340703418032550360288203200070700c002441401c105001c0b0707204138030580596041c2c40b80d20000710349c3c5080350100544240c0c0c2c181802c899608480b000a4104e040c0113800c54018188040c40c00425500701100380c4580 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 560223192 1250 560221942 560221951
    0x1023010e1306091203111603030b0a1809170c0a030302090f100809060a060b0717040e0c120a110702041a06070c0f142b02060c01050601110d090e 64
    0x584410011102080c214032414a80c0c6200b074110000100010134040d0564000c1c0c105169090002d00241c1b0f507000103e100e500c0410761500e000100c0c4142034000034000c500c607030004110380100c0d1403e5010340c00e2640c04001c199019060780d00380c0004500b00c000040c440c00c266404613812800096000078083e4000c2e00c42142c00038020b001041505002c200420391414032440001c0301d04090202031003041c0481900040d0201043c0145c90800000344100d2150840040400b8070a4403051540c408103020f80d00a0010707481c19101c6c900342000f101295800c040310002c25a215200411a4aa801c0c41404940404040c1072420040180c01b00001040792401c22501c0302c1046984905603910700004007002c510030540340f0255400c0c641c3e03242c40d0b01401d42112080c903002c100707030901c039640315001040f400311228410b50001c250710740505103268095000a402c0000860b481c8031800c819041a84251404e0381d44601000d0301070003166880100400301408664524400c4c00176108180038203511 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 560224442 1250 560223192 560223211
    0x9060e06040504020703021e010b030a080d0222031208010f14040912171f030b10030f0b060f041506050901020111070b060108010b03040512160b091023010e 69
    0x62554480200d002c0ea070280000300d00507000308c048040d41e06041e2106d20702101009008001238180c040100c5d80d40c10280d0f002511100010a403001c0c19015501111b0b500c00005201010f0a1400310480d000c8440310300081360400060036032208024400c00c0b00300e040303136404581400b81701d00e0400c1c142904040b00c0c8840da0000d0b240e003d003501040300645880d14010390355031031000d080c2c0800c445411070f80c409403040407120310622000706070144070340704101600e4101c62103038041c0d00c400c0b070a618000400e40c0000c0c050300c40c410f075140c180a00f80781d4440c810030082d038580204d81201e1b000c00088803800c601c00c80b20703500e10b4001840024800c10141c18003c0c4103000004e07810140032075441c05070300f011104660b14082001003140959005803405c0c0103107001c505030341c2581080e42c0c52607100e28070400003040e201400f0500307a00c2940e544400b03502c52030300109005014200400d0f4603494032560100382e4111801c000c0c0000301c403402144000481c1628000d10111a401c01010341000f00c00500310f003d4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 560225692 1250 560224442 560224447
    0x306010c080a1e081602120f1312060c2a0b07200109060e15011a0702090405070614090609060f04030b0a06140405060102061303091e08010e01050709060e06 69
    0x2280d0101d4855824807180c9074899885524240192000245d040c4100d4021500445010004500c422084c0e5503a2103882c2c00154035031030341010300703042c80781154080d0200c0d160704000c0c1c00610955038030003401d0984a688103591500d10280729005104503942c820424801d0340c00b2000458490300d00700c2d40015136881d1458008032001c400c2c0d00390038070001d40c0c803513280d5640303c4040800c1650f104100c1c82d1060500644004103201d4641e03202100140300d03c07220321800520810341c0280c00011566101c0e0300801070082410300341400b6640340c0e0103000b0703240481d064600440d00c50b1020004e4030101000140400d103408001018414250031144000d20480001d000100004445000a500c10740040e00009406032030300c03003610342c200720440310240114a09401c1c000f040e603000c200c9a62054601c48030705505004c0c2e24040310030001a9200c10006040312202100c183e259590300401c40e10464003d00003070200400290880d0020fa031100c0202d1611002041041d000b0589514074800081c107950 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 560226942 1250 560225692 560225717
    0x70f030519080d020703120b150304060e07120b0603010605030f030f0f09041806140415092f130c0e0907020a0503161e03020303060d06060f0311090c0306010c080a 72
    0x30300782e03005070381c0403404a826a00d9000d007e0f0445d115074500c02c0d40032501c5000d80403884072080c04522004e800580283d48960000e0301c0010100215001440c1c00590400303855040e0610b8043c1e80c000f51045071080d400c0101c009002e150004081d0200c540000245240c980c0785da04626207a880b800305103101600501c0482030036503c6d03100d21840b0301450858410040c21a1130010211419182c401c80c0d072806800c10310012442da021f910000110040001400c12981d0034228080340c030030103810640541c861095a0210f41034090146409010303a038550b482c0ca40700c0e01000036100c5298200000588a46c40d1100300c1c075004c1c151f1a00540e55005803144040703d80c45090840d403280c20401c10784020440e80c3c204000140c1c0c00d50182070781c8003180000041c05550b0080d184d20000c1d01c036a116600c804100c400303000065012000034841a001520050f0703582c60180500000107800d94411592400060445102e0b981280d100e2507050f521801150101d9440207495000340000e1010071008481c0b40 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 560228192 1250 560226942 560226967
    0xa030803090d02060a0603050d140d05040c140d02060702010804140102181017042003060f010312110a1b0305190203010605030106062c03120a02070f03051908 70
    0x118098840720000c0d048201c40c9000c0a441c112000d09014485407815104002050000c290952844c11520f400604000741c1440600b4038010107542c498428600f1007884204003504400a0881d101e0043e0900f0450440d001c0003030340040080069042002040718500540c802d070300603503120307101e84201003000c680800307600e0898200900c1c86906c04030120b0205030b280350030302411600c0e103414940314510a48051b10f8501c1b2101c0a00010100c079503203a00190003510203000c010700400060100c40040c900410030303000002082c801524000001700106520302c2c4038844903e506200d1070b006040e1000c4c540c0e615036503007089008c0040390a581d2000800000c10500100081d942147c1507080801c3d00d41c0105400c40300154400e5100341e1504200b0000160466450564450b0100b10040e80441070b1329031050710484440c00c15818040d5203c0180e001d440381c0050301d000d500703039400c541900f0707140d00040c900c00751680400f8186c0e5002420094100801101c014900741c81140031a08110160020 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 560229442 1250 560228192 560228197
    0x9020901050d210e0405060901080d0305070219111503010b0403030f1e0f080601020718021e1303140a080f030403021c020309180f190e071215060b0a0e0a0308 70
    0xb000010300c8070813030000b11305d850700030642c10580484292103154034103407000c0d42d54a800c015400526450781b00058015009022015409040903448070f002c0802f80350000d855910341c0b096a108184000c190500b0000070b40540b4140d4004c2031009242c03a0450324156844e000b80d41c24802044030300e101c210031100078034055141003209511414802d04140801034003180000b05000e0466200c003a00300045040c40c3c00c3c0400b440e00d840401a550705151a0359024007048014101e01c030b100004a0608030201c01703450900f140e014249400295501c140e9080d2a03203032800c8041c129100c10b100d0000340075840b800544d081031190048403141e0741d8074020344030030910355078011001d60030214003000941040c0c1e94000c0c29803c0c07070050305460f24009844c030644060250600081010104140d450503929a00807211264204222983c40fa5591420483c5088d141000c80e01540300b500281e008402502450b004d84034120712090501e02280b50881d0442e03509005142c4c40a015000000403946030b100 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 560230692 1250 560229442 560229503
    0x2030f0705101a091608070e1203040605030106020f0102190e040e011103070f081e0c070c0807140d11060f0d061203020d020a03080c0f12090106050a06020109020901050d 75
    0x102503d031225480204900140d00a0507504000c501194662000b58850310301a03125000707003480540e40c808600410582d0501801c0c0411a200000d00032407a56000405541291800d600300e410084c900000c60f0300307078080c07007440d5a1440c03030004c910075005001d148030100d03441025100058010218103403c1c03d54010f403010072140f200c0081440501981300e00f0900c2c0c0034613141440c00460521503c241c0e04804c030303d51500641e100c44000704006034005030444414940050b014446203849490543e04d1300f10521900380003248525503052941001c0350f00f900040d070049a98035940311038000380b0440b039000320307038031101043c04101c0e440c4a27020310300c40c0001070300001c2d240034284e00399844c0c0a032601c2c0c0c03024806c20035540300c200414002540050201c1e400b0160f05401c6071940350707031150150341d4050740566500221500d420020910340550102e000c0315000c8074a850691f0340c81c1810380c2220514036010b0b4006070801d0052140d03040c0070b100010020700c9101c2040070440700719004861410f8140 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 560231942 1250 560230692 560230721
    0xf02120406060f08061306110301092c0c010c060612060b180603030f0a09210b0106031107060b1c1407150e010c050c0307060c050106080a020102030f070510 69
    0x60a100600000e403245034050506095007000c4242001350b00c039541c54000b40202c42510035203a1042c00c00c101504003186050810302c00716202c0d6111a61040030b0918a245a0140c40700c2d032000c0d00c0b20100c100d01d1542043c600b5009000144421801141c6250f18020240d500d9521101c0024240c504035102c000028000c03e00010605001c0c420464040c0c0c0c1c400111850f4103440003800525507001c021180c1b11540b82c80701d250744180d0910203903035241d41a030101e0b2542011580301800043d01c2e5200710441c920a240750308850b0f80300d036400c0d8105d404440c0c5458520708240070401c00151158403c1c2d40882d8001c182c0241184144412501c0403002d81044034240000030710014411401c02001020704071182c0c03000b81104a040004141031000c0e004641004518080704003440000e1140100304070300a03065822603511a4005000d00242202c121550b40c60620000748a1401084815600303034168055403070100440c80d503121981103100240e43d07034001c610700707407800000b00e01c18100d040c01d10a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 560233192 1250 560231942 560231977
    0xa0b0702070501180b040e040f080d061e15050d0905010c05041d0601022802040e06100e0f0c251b09090c05100306031e02040c050705120d0f02 63
    0x1c000500922180104400b525603480042c012028031800b62426140240c40801f8150f40d07a003008880307034881348400782000e2000641c012410149802003025174414681140b0515420030f06640c1400f014030030040180040a012400310388540002c0024501d015408207840040e03032240340c00c5030108c1d4003075000f140001504200d800e0000c00308001c200d00110701c100903072a014001070345039140000c1441c06e4104001001202249082c003880840e50043c01c1040301c00c11141c4d841d50fa40c0c0080d521404401c81b4083c000810310150248a8401c5103800c104031002d8407098010340b02904507c013944642108070384a00015500c04d001c10780e00c14052590250000000c00c44e2b01450000ea80000e100507040140c0000420418444c000494000b0344a1f103c0c01490120110028111504001c0411100e00f031081d05015a84901c0002c1074003c0300c4c200403440303e034202540e080c49440c4000341700340c1140d0700012244005c4000707403010603c5801c0100c1c03003d101c00050340c1240d109a4000c001420f90 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 560234442 1250 560233192 560233199
    0x5150906030a0905072309220605041e020112090302030c06040506010302090a06290d061202150712030c090509070f021b0616110405040507080d021212090a0b070207 73
    0x3040000f00030000c22031003002c64170205001e0034042e45061106e6015050010110744100000c0a685a0106d06d80d0807031081810a841d0160182400352070039100f600104104d01d06030181c14100282c2254141c403400a0840340254142c081d005100c0f043c0d0942c0018000d0b001015014001e5908c114480c2c0040d00c0d080d8110310420100040107030a400310300c0c0c07a04c4801c5c89010042d0041d54008901c2104e2008481c01e0100b14000c02c0c481e080300c800541d81800030015601140f8205040050310031640c0e000002c00401583d5010700400c50050644480c01111070400ea00a0b40034090001aa01c1c1800c0b10546400101d2000101075491800140110400c100d005505011400c0c60300c5c042c4818035550712194001410702e00079417001d180c000030b01081100401c0700d20428900d952201400c14041894542002504c03403403948981081400360b4001d0313010582c40030907030602200c3d440c4406800d003030800c0c6101c03001d51402440e0a0b00340c42a030f00010041216011040e214002c01d80c0240419401c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 560235692 1250 560234442 560234453
    0x4030b01080d0201020a0c02010c0c08011b0909090f15020705031204030216030b0105150c120c060c070c140301090b0a0c020c01020c211c0201061a09090105150906030a09 75
    0x82c2d811142c003164810720510040302d40c020b8451034029024607040340c6020680c1020b1006081e140d108003007940c60110001c4400110f0700007030742003940e591036040e0301c1c654414560040e82c400300340042080b4900c4071604006584110700708881c6030a003100500f800342544d5910f2a540c40b0b0000d03130365803492600406c01056410400140d041c0304c10281c4090103459651a070b401c1c628180190b41c4250030b001581030080c1c5c0d0403819510552000c20071501e0025003000700c045203500140c040c2703080307004030f000040601003204100e4217480ea00c459442034151522540206003141c1d94480b650554840e0b0745c01d00840c031810724060017400180780c000344038041d50001906d000c0000481605542001440e0281e80d6946070f0a0100d401c00d4032240d0801c0b4111040e8141401c01400d55000131100550441c4020742d41580310742c0948000441402c3d58011a40515200340a06015039502c10580c0006101606014111040803503100382840c0c04e02c411500000c0c1140c00894441c90f00d25556000c601c180311 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 560236942 1250 560235692 560235703
    0x1e0403060501170a140a17070506010f08030d020d0b130501050906040e0a0231020d0c030605030c0f030c1c2a140d0609050f0d0e0a0612020c0304030b0108 68
    0x5956450f988940c1d601c4280d5529180f00c110050004050485404909031702070060000e00d81e48036041b0040b6009a0600f100e4980086109481c140304540010944140800000c420340f40c004e40214103004106c0c810348041e51010a0402019458849000440c3ca4410b82402c05000340d02d0040743d05e60516052144555006041c544030f0b60400b4602c0e0030700c0e4004a038059450b40c05540c035223582000a148031032a0344601c002480454141c6203100440d0074668040c042225079102d00b03120b6840c80c403404030b041c1c070708902400e5415081420324040382d182001006030200c2e07020741503074030a25001c0d00040c1500980d940ca940140029041c0e041042560324031a400412010754070200304c81d1031150000e03018050b0180e0031581d0400c045800b803e44e180c0452000555010205002c4a00c2074038196455208140d80c803d450300c0743c2071b00a003030729020f0710822404e0317132014210a5005291040840c0e00c44604401c00c00010b0342040380301d090510074030040c000f0f54054640400e030741d45400320311803601 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 560238192 1250 560236942 560236949
    0x60615030e120f1803030405461211040e0307030201180f080d0207170901021902091f03050706022104080601060807210b0f0108010b03010603111e0403060501 70
    0x2c1c00070070441c1011103225080c0c071a40c0e07204654010b002084036003c40c0c0b0314440c58000c1a41714500c413565150b0112000e10040d03428100c1600e85240070306205c5c21410301015a4900c10f0700e402d041000340315034a940c83c0d0103c4c845010340004c0038903403034540215044443c0e160841c00345030400032300d01e02419024080c003580d280344062145419425038580d14200000c403e4024441d40000035011481801501641d181d680c0140c4000d40805030303090a441c480d400591128058000c5298500c100611844034101181c0c010700300b45000c1d66a403400e41c00c1141c0744031152510400123080407000c00d070300b00103180141806030002c000842d00f805003414014640040c018458070300700801d0040751404502281180c8080c1000155071300d85000075115510003810070740e102d0f8844802010b0ba4031b0190401781e010301090301c0302c086e41503c1e080119010382090090700010301041004000e0701d8865270041070118074014006003400c0100f110203110011000702c00041d440d01240610038031805100d0980103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 560239442 1250 560238192 560238223
    0x4050a0b12160e0f0c070305040e0c070c05030f1b030f0a08120c0408072705131106070209240d03050d050a06080d030f0204091d100b0a0b07060615030e 67
    0x96103020342c2d41c4d8600000040070404984400724101301014000c00c2034070080c00411103501c1c400d144c0512107081c150000356064404d82c8001d50001841d04011800025200c4108054200058105182c9035045020f41c1f030380d50144250f00c0900c80c018414030041882c2d510400980d50b039000c1c4605284d038046005000351240d04810041007240407000162141224801c03101c4560404000345800324061404200c50811800d280030001c2d585050b4140c2c40015100307075403a40d100c03002c0e0000e00c036150083c018025080503c280100d2600452070801c088101d4852140f589103072001d0001c00d95028070450f0450100300c0114152400c441d00317002e5203a000c1c0080f00c2c10801503240440840d5215580c441140900d6514601400a4401901241e01038040c1d408103004181ca91082984010380c0d1100d10b050900a182207980c80d616540611102d06000411014400307081110301e400c1075004840c12214142d64010001d80c0075500075401000c1c0e00b103520b0003c0c00001983c04141800f5020004d903d6 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 560240692 1250 560239442 560239469
    0x30d0e0f030c030d081005040603030203130b18060f16050a20060706020903010e0102040609090b180c03090a06152103080705070201020c0307090510210204050a0b1216 74
    0x2514001420707503c0c4841391505440ca41ca50740350320064803551380c00940e00242080070100906800000500d4090002d58070303843e03c560307610070703142690142c840c490b08450b0159440d181c0500e086009400b101d40020081417610300c034002407040c1e031040401c00301d450b0b401041c02007007030116021841581a032440f03a095044c81060300001c0a910603140f0082443c2d0340414008a192025403160101c540c0350002190b5958480034040c0825600d41320721803280e400c1c80d14031585800c040c1100c04003801d40001103c0c042e165018002e03425000200300310a20320412942402084013402007510001c64800c80304245424090040400103000d034001c4401c80c0418043e00020b684881d8507a80080245096910340001e840100e0520805843c0c0300d903d84a044808621640e0a500c42c3d409050868603000c10b044e51490394540c0034600c04003c080510710b170840c2d080541420f4001c640d001310300d000000f407031261060000e0000581c0d010142c5165001440790f00094241040040242481e10072200 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 560241942 1250 560240692 560240713
    0x31315030c12020a0315090f0f1503020103230a020a0807080402010e011808010203100f0519050906120d0c110301140c0f0f0c01020304030f03050f0a0905030405030d0e0f03 76
    0x108120010340b80d03080c500e81e002455000c014070a0340301015104c51500c0c1080e201c0c1c0d0301c046010141251300160b041c0a49049004e55134144c90b4402c610720801c1c0c1c0c0d10000c2e80303d440c640040d0010b0a01c80084014000501000e24012400d00c24680c8074510b510300c0140c4400050301c00610f040303270080080e81072092907020322000d070b07170055400d250500e0f00346404030380300501441600c5540741070b900c031201c1d80d030002c0b06210042020f2011502928560b07031041c08003030740d604104200c0d0030003600c091108001e518410b2099040ca2030b00d07142c0c0b102c005007011036112910b03074086162441000101c000075251103240b10030881c0b450462850200304030001e00c0300703114581052455080c0600340d01c400b0400060060b0b03141510000382d40302c03110245c24294640140c0ca051074042d41c003c5500710006150b07888642004c80c081c0c480e09010385050301c4a0180c698071215404001d10f9101429100c0c1d100c01e020004070350313900308260900150030b82e42d040c82c940323078003000c0c403602403061180b4500c0398000c000b940 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 560243192 1250 560241942 560241947
    0x10509010c0b04080f0f03090c0a030224130e0a0c140d05060d08070c06122901022503060e0f03071509021509090a0608030a030e0f031315030c 63
    0x192101c541040044115031030340d2510350305512641780139102461001c580300f0703072000c0c1a10145104030101c07019a2143c030705036410046070324081c2c08000e5102c00301120309070700744070000040104c54600d40d0b900f0f032800e190b0111408072000030340c1c0050070b22940354040169401440c024010450b503641001a40d020840707040200d5400744500e41c200e41c9980780009120380c2e4a00000580c4140c2040900b5514074a504110307540f40c0e1030b80964808610712007100020300800b84110200c1c401007100545007003144000e40305800c0d0001400c14118842c00c602c8404070401c1e83c03010ba1032150340040785200b5030f1852510006440a24000b480070fa046200368a00d074003408012240300903800f07802c207056146100c1502d00107007010380d4042d4100c6002c0b030802d07070f401240300014003400b4800c840100c100d56605018405070b80d86800f8030f2170340d6082406080e40f50350182c1c0005075607a0304a001e03280c0f100d14103000300d40303150480c40401e00310b8007400d60304100104d403000b000c011940c89031500344511581c04001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 560244442 1250 560243192 560243207
    0x2010b0d0309060513031b05120c0d030e032a21030f090a0906030c061706030703120c0501050a06150f0206060105070f050d020f060a06050a1503110a050a080601050901 74
    0xb01003d04c000000c610806412459103503001d160302c600d054011a40003034030007000c103507540549805907000c4000c0342a42c26000601c40c0c40c6400003400d16003072021640c3e04407010510002459014030a8117a00b01c600c0700c140f520801c0841054410310304614100c0d003041007500214400c0d0580d0809179035480842c22001c030403103c2c030702540c4110903600c000c1c04011070f10311960396001005641c41d05002004218400842c80e04555081d610700c01d40c1d8601d0990003d41710380940f8950740c9035221180400000303604c401107943d4900380c0d0824681002141d101c403400d41d00110341101110f03594050510042d0726007070b40704203106100d2410f204c111114200203503503260060500c03810310801203100030400000310520903417542d00c041540c5208a140002079500ea02d4042490b115000701070004194481600c114401c80714000e0100c246185001032420041c114500c65500305a11103160180c0401d09200070710014541d681d81035600c022844000303100c00e41c060b100c01e04100741001036400503a0301180 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 560245692 1250 560244442 560244449
    0x51302360c0c0a0f05070506040e07030b0f060c0a0203070e0f0a0504110d030e0f09060a05060d02041509060815090402010f110601180b03060f2e09020a02010b0d0309 73
    0x51840d450307292420006200d02030400380407843c0c8070f0400e0030420441c40200c20444140710300100c408154440342042643e005078092043d014000b08001140144240c00c541d103460400340c00046489803138000f00b40c0c1c95010702d03180320980d48005508000c500b0200040f03030060488002d0600350341800511241c1d000c901401544c400e945510110f030a01100d01200e80708a5030081c04120b11007454a8060001c1c02d8808881c0d11510010300b0b038124600b02501124030442000340110889800c12040003440e800002c9200d84090b824800440c0c48100e066488030039000507202c0004440c40c0c02c100500d1844001c1c1105c4000d81e148034525642d80700d04103c40c1d08075509081c025950030a4803000c0340c0788805902c84280c070b480755600000e0070855004801c40c411120070024040e200c040818107176910016103202d6040607a0074001303008655641443d9032008641c4010380c5000380780c1c491000c90044181c1290301359903800100004110f40910070b50f41481d178151004a21060325840240001441e81f0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 560246942 1250 560245692 560245789
    0x313021e0a300f1410020d1e0629090402030c031f030c060c03021516091a07060209190b090907170109020a030605040204081006081b0f13051302 64
    0x90a000c894028804102c001d20f40030406c54890b101080c03071002030400320301c1d01450181080e042d00a80c2507180149415120342c00500142c000003a10a040910607500c00700804c064140001043c50382d8600040d401030700b201100684906041c000075490401100e60443e160b400e803282040050740e83c0d5030a00440d140b50500089028442c1400e900300302c03020000c40128403c0204001c1000c998039480c0540c982c00e581d034840c001e902d071002c840020714841c010000f0740009000c400c1c0044d10903001803401d0b40d4090442103030003604101d070050041050f000805003050126004409007020912294040981e181c80e001c4003244001031085072106001d5001d03100d4001500340c05240c001c0e0440002010080c00442d80c079542c803000d050b11f403015192182d54481c20014000b440e140009081500868600c100d0121164180104074084140c1402ca41d00030a508001c00c0480802c0d1050074800e4407011030300d07a1a0b01d880d20400c8030103041000c1214814146881c03586003080b4080030482000482d1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 560248192 1250 560246942 560246963
    0xb09150609060c0a03090612060f0b0a0c0c080106092304140102130807050a090204150f0c080a0513091e050402030a05070b040801060b0313021e0a300f 67
    0x600c0821582d20503a88039400f81d1244210503010164412803070b0045914581d0b0f10301301c1c1c1401c00710b0700050315018441c0c40c0f0715800c1128140544909030000b00034220460901d41d42040143d925020000380c59440038909035036400c02003004243c140285042c0c0601c4c260840c00c07071a03c19001c001c03441c1c0040c0020704440380412108800d40c500758121410003901c0a0820180c41d0795a0881d0350b500f200780a2a8020052400002180038060003580e09a030504039903080a41d4003260100d0715101c01203204810005100c011001003030003d801006046616912a83c0e01e012070402d10040c0c0110b42e02021600e85410200c602422440c2e5241c42d000003918030114031a119400041e18009030004090300c2405201000a0060b802000030412641e0002c02400210340c1d810000c0c1260004542600003c0c2811149400524103c06a140005a0141020f028006d0322001c201003030b5a076002100302110710100e01850241c2800c425100c0043c602c40124140d01641e101c0d00555500480107100b00b605 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 560249442 1250 560248192 560248207
    0x10111b120726032a030402030c10021006091b0809030f0f0f040e070f020f0303280609021b07030f060207080d0207030203040504060e07021203090a0203030403060f0b091506 76
    0x588071018058012402a0b0b240d00708040018110641c00b038182c13958a2021040c840030542d0702c81034a2107036030000c000d46008000101803200707002401010301c0071809203060f149003000c000d110360005413a4404002400c0c180b088130300000c4a0041040d034040c040b400d0100034100000008607500004030280c1c03d5140c036045282541c00d8010701000350043c04001c540813034031a5803601081e1260301580ea489108241000d4140e0321041080d0f5076036115041040020450001500f01c4410540e52000003550090780203001421284190400300a0301d030002848500c5000486a0303907480b81411014041e00c13032079943c0d0310a4000103c200107143e19001701d02031007132081884c00d95204420001083d0754692407464000d49030342c4079008442c401e40c60a000424240280e014403445608950001c100260400344029105e0708001c1440465114004108005803001d0024000541c0306600200d86030341c680c43c0361419900c00500c0b06010758034440400c0410341a403a02800c41d24000d85a9039130340c241 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 560250692 1250 560249442 560249483
    0xb0f040308030103060c08010e0c0403020f0a050d03020c011103090901051018090509070603092a0f0b0301030c06110d0c030323070801060503070e010e0310111b1207 73
    0x2654405011240040000000d101d119001a200074140d907443c0e0501d6171b240c000807000b001e02a81e0916000c08240400c0c030050900402c08980584020020034505540720b0000b0210f030b96032041140144c024030711490081d6000003401c0500e45001024500b01020705001c120211414480c00340b084030610319450840e4081c0c04d03000300f8a0001968100c82544072890301000d000180c03104030075442000700c0092490321a100781000180e1020011400c00410780030a0003502e003803110003414210b58140011918042c003010402410b42c1c41401e0303181d40c03450403c982c003020aa0f0100d820b004241c40c850004500115603064051700508112421203040d0804030002d00608200c00c40d1501440c10070b80b2000c0c010000300b80f01d0100c03a81c0d818a0750380ca5050460300b0740425211040850035082000c00c0710f40c05000c0c0040103100190450300c410005900070420b0b5030900c0c03540500002c0000d03c41c00c011402504100786c2462040050440002c1d074507803000a44500140074122490452036450100c0307 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 560251798 1106 560250692 560250697
    0x906040306020702030f070602101d1e1c03060e070903020f061c090c080d020304030305040314011b0e0f04051012151401050a050414010b0f 62
    0x40c60350340c81d4000394010020490b418011004175101c4000108094001040586e00400540008506043c100d0b21144109080280342c841584d0015030005420070409070b8011441202c0c01050440030f0030500307500c11a004200e6103058080d034050780f581168003600c80030070140c010b50b1185c00c810387d40038803903100094014440b004d088600c0d00c0e110000c1d08448041c524640c0c844890484103c085a011074821030b4407104d01d140c18400c0030783c1008001c1500c1000d00040d440c09055860140050050b444010078401243c591103201c1d4100390080450b070208201c00f00d201c03000c03801c4058a2258804500d5005c0c108400e4070404901d41401554095155030101302021424042a607a00c1d45c465442503c000c1c4120060760707142d401d94403c803203c0321081c1c03880644a5060604205082c60700d035102500c40c40c1400740c0e14000e45c000928441c1100c4040381031a03641c68140032241d9850 = true := by decide +kernel

theorem cover : BRFrame.Cov 560071942 560251798 := by
  have h0 := BRFrame.cov_init 560071942
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 560071942 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 560071942 ≤ n) (h2 : n < 560251798) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
