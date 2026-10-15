-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5126
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:50:06.130836+00:00
-- url     : https://prove2.me/submissions/be240ed7-9c75-4523-975f-60783874094e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 921762589 ≤ n < 921942446 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 921763839 1250 921762589 921762601
    0x150f020c091e0a0e0d090b0409052e0e1509060f04090204021b1213091a040915150b0f0a031404032102040806060906150406020105010906090501030803 67
    0x440070350405219800c0a0094050110405506804586030018240d544514406840e0140220a101c070158a0059160703420124810322a0055000788003500740d940001540c48100602840c1032038100c402c4642055003d0303420800005036601034160342040d48801b203101c0041080448111040062250b1201d54516040c0091100066081c950041c0c64410400160b143c51004180d10b04141031041d01c0d110042c04044d02d80000c0924920240000704405489120300c0c440340410750700403140118008103001440c1c260404400c01ea254004e1800c01001e00300a00308803000a10118648140203450034004400c4040101d44641c841684080140038060102c0c0d40051111050030b013400076850f14801d00c030300000482210218045240740c1009100403100500f29001c000200c8000d601d01030401108036103d00c0d0140c007850140440c03074041400ca660342e410042801601805680e20b8035500c0c0e0000340078003020b102c2c0d440c1452a0950201c0c1c058000d008060590740c00c06020b07440d644400c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 921765089 1250 921763839 921763849
    0x31e040501021506030a2d150b0102030a12090611030a0504032a111315030309050d0c03141011120c090d0209070509130504022806110f06010f150f020c 67
    0x440200d507040e02c2000d44031000071021001c620030990003230044050300e00c0c407525003030304898006000e507055500038010951155070208803030381c140b00c15420200b104102864144081c0c4140c008003a48002c3c003004110040102d9030103a40308034081c0d640c03020511403060480080c170320170480c52145080300078241000b0074805402c000c85080007034010002d51040200d80d400319075003c1c0c40700740d0400480c2020014035030b110503420054107045414003d41d1810340d8405803100c42c44d200c020b060405c0601e40604e01c450901143c4041c5050040510044800021515481d401a8a0384815442e440081600d9400d4202034408000340a00007821020b003603020030020820040500d401c200b41004074800d50745802088001c806007448011841d4102881040344004100740c40c040c01001c03d416021448410032007180171076200d810500c91151999000d982080d0008112114620030000002030030f544d01c08510084a00c0001c609281c049021411a007425080900d440143d001d402048094030f00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 921766339 1250 921765089 921765113
    0x1050f0907120c0506070c0302030708031c0e0f06180d0e0d1e050106030507060e010503040b04031d090f070905030f070e060a050306150910080a060509031e040501021506030a 77
    0xf5525070808180d54500262241d40720003022a00c00c01c046004000b1820200f05020181c14000302a41c2442801c050030f00d03000c0140c4102e04c01092b204c2500949403d000d10a1400b80c103070706816509285018440d9200702640503d421140d841140300700b000092246c403c5201e09800100720624252554940000e6030b83e08803401700e562442d03a5141030015900b44140d9000310304c58005440b0691914401514141a40c81035905100e070400401000900044d0081e50199040c1003030021112583c2c0c0030051036100440d841e0b0007014110501003603010034001c1620071860750340c43c184983c0e159402c0c1030301c4000e2503180180303c0e4010403040c4981224046060360015014200e035044550b107a00180c6032034002e40387c042d15611300c072490340e4150828950b550340c811000c0b03211a500d00e1400500e542e4800740841f02400180e501e501240c1c590b002441205e0040150070300350003048002c440c15000c1a40a481028054403c401083c4002c1d800700c50740d81c0c8611401005029a0b5181c2e03110b160300020 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 921767589 1250 921766339 921766343
    0x41217040b060118030b090d08013f060e060a0b1e010c210f020c0f06070c0e0c1c0b0a0b090406090f23060306040807060902060a050c01050f090712 65
    0x2038444c8141550404242940000318040c40c60702c101424840901350600740b80102170400c0040c03800c0140100c1d220115035003103456804081c904a0301000c02c92180b001080d11210740030619030b4a112062146a4005100032201030701581d5054503001e4248040740c80d00001300b9045210005040c84101440b000b84403c0b00040c10590564082c0c0c0d034034a440220302d1042a40c2030511580002d400c20303404600b00702c134130080c0d000500081d540940081c924801030000d47e4856403000a014081082d00200c030001801c800143c407101d400d080e80141d415400c402402d040100d0310201c801e1241840d4010f0303100011000e01304501c1d841c107100d6113550582c064188103070860740f9180001441032803031207241400c2c0040400011005542c07070040d0400e441440e440340045002000380011030343e02060240d0070680c0005440d0307485081d8684100500040c16001e540034001003000c01865070408001d0000e654590000c2142e82e031510340c6c041100d04181d8202e416a405103900344103241d40240d0341071030a4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 921768839 1250 921767589 921767597
    0x20607050109020916080f070203040915170601030b0c07121202090315100803031501050a14030103050c0103050f040b04121b0f0b1006120216020315041217040b0601 73
    0x6039030013050425400380c481107040d0041ca00e00841040d404804540c01041c040c1500300f15003003d42009507030b4001ea00920b81540c0d500c000d82a10500e401d0702400041804480d24002034010380000d6469101c00d2005860f42940000020900202c120403181815031000a0040f40b03005028100e40034481820300e0340704030390300304030036034082e80d080000b4802103031850510900341c9401d20343c4444100c01030b84109070580c4184140400340d0a01401a1646c0b802803804503250306151100f12604420044680d134040303000800402070040100f5001000c000a8034140001d8890720035040034080d00712009010070345a400410700180340110441051009480d00c1181440340000d440d00250350389a080300c403030342481d0b41c01040009601180b648550380440d0f009485140ca20088d10b07070b459080146444c01e6001035003140d00481c4c0c0040140154003e021030300f5150004100c00c09540c001d0320162407400c40c4040b040235962040c0d07a81c00002c0d0782c12070702c82100d896550b40d210010760007914641c140 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 921770089 1250 921768839 921768851
    0x300512060a03060513050c01021f0c050403021009081608060a2c030405040e0106050d03050c0a0803090303040201031b02100e071a03040605070305040803040210021c0203040504050916030206070501 87
    0x103d0b4140c080c00c3d0060619296100d186005c62414600e0030318a2140d8506640000703007003c0c3e500078a40c400d8041007030950300c04241207a54103030403550f034441e07a00020b40c019401c2851140782c0d5403105103407041e540785104480ca281c2d03160864484009191017014007941c00b04000074085869a0030181e031081d04102c521500a0a0a2041c03440803a001005111648042020403451500380101d9801340c100030000c100d914107280100e0041844c18001400b4014000340c0401d0000c42001985c0300c1c2608410707074903160f0400142c21901c0b03600c2039409a00182c14800d92111855500d00d00340d4801d8880e4000301620300c080b04050303000d044003860012080c01140f4001482d503a10120103c07645108401e0141d82e854680750640407100c4c040d18500405180004000000b000141103e40064046a00610342100008200d24042401100c403d50070041004410591340000290054440071617003405a603442040700e5035101d2500c035030003603034410808041000d402d00e9030091000070301a20000c520 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 921771339 1250 921770089 921770093
    0x4052803060c23040806061e0d031d0301110a03091a0f19060b040e0a3b0609060703020703090e040c09050106030e1f1404300512060a03 60
    0x449189421540106620b41c8040811900d03140d5044252003141100c3c5060501740000c241d9a010000d20590042003c0c005041404030000524140c0f13200c014680c2000c901300c1e16000f014003681003160440d0405e40303499003120b880d06004800c2d000300b0503d0349900340188180c046029107001d10013682c001c8100382c03001a15150092071184035031400b0701d03200c0c41810180001004210b0b001003803015180f5103002404000222000c94040b50308413050441c01e0b031101d0350088000c0c080d105050080b0319466081701010701c45108130040031006200e0791111817070b0002015883d0f4500300d803110b013141c0006000408081c007e9003e003075228060302d0f026040548030300c003858038aa02035505235140b407866041000040d0150040c1405440289820321051501c20f283d19998000e443d80010010600483d1070042001e9920282600700b12421243e043d00b820304100c81155400500c0303030306420b44118000244808032683c4042454240e07103862403e1440800840050f00240010740d100c0c55800d40080 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 921772589 1250 921771339 921771341
    0x4121b05030408071e0306020a0306150201201612030e030c0604020406060314061e0301060306090b010f0f06030203070e09040302010b1207140f0d02060a11120405280306 75
    0x1500d200d03500950741c1d1414100510716050003a4411520b110b86620003820b4007100d1180304048961240003da21120000c0c0140c020300304a41152034171032001010318602d15030541004505889034011100c1d01c40b082c689403c007500c034035441e02c0c0911249846005c0000d4440300e40c001c00c0920f521740040c520192401a6056034448140060940d10400c20300c804d51a161050b4002840c1c41c2c18104107100d4110007240307500c03100406442c0b06900c00100700010704074100c0d51100c5d8150060003004140c5c0c032032a102000f401074000944040820788000718515061141500c240c0d140c21030310352101c1d85891f504501a60000b08000c0400c4899264007804d600c0d00700b070b2240103d200380c0010402209800078828955000300030310201d607010300320801c942e10f130429280c406828160b81c091041503400002c01e240e564400c03c000d401400c0094282182c943c840443c1c0c58803481441503840d4a0321441c00d0b00c0c413034001ca0107010351101d440b603186030a020048007442081c94854188103c519940d0322504 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 921773839 1250 921772589 921772637
    0x80910020a090807240c020a03150f0b0a061710031e03022e020d090828030519020a022e060501020307050d11070b040b0a0e04020a080412 61
    0x10002c0b8001107001e00005030b0601140c0c001c2c000e09845182000003045c40030340318200d02c034420024048011143d0f4159203642e90660051600018040b441c289003a642038024240540040c040030301c0e00c00b0881c4a0b141008100c01243c005507a020404007507240f4002da2203102822140c4c1d0009030910000005200283c17042e810030b400e80c140e405100c050708000c1c1c1003074024568100d803100c150600c4110002c0901c441c26541074940f0740140c45100c0076034000000d111256025100e040007240480e21408800c00c8030b40c0c40c19040da8906c055210044069065039030607112000c503064103140c0b8004d4130003554003030202d0100510403115403040c00c01d00d13010818605645c0650340c0454a2101d50044601c2c064100202403c1c80203501e071846c51b880e4151140c850403031032001c1020021035584c40d0001004244050440c500000365919541c0c0c90f14071b15640440e140030b01080d240203802880d07140078400d5540c00209611242c48030f94550342c50707040740580580d00400340000e0303c2c00e5601e1151525884 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 921775089 1250 921773839 921773857
    0xb0118060c0201030b030114011a040b0c0105090d0207030c050d080904140601110a02030a02040906151401080a14040b0601050d020c03131212050a020a1e120503090d08091002 77
    0x2581407071805000040a880c0070421030b034081d030f040ca10304043c4407195088150441e14140c0c001d06d04540e014288208901c2594403803010001e002c80c02c003a5003001940440e009080140072900b50b26000d15042c1e0701c400c0740b440040c00152840800300482d041c0b880c282241305110743c80b901d103048203031400101112124450240e41106480030803046517001101a008000d0450090206441d240c2c000b9a0714045410000e02031904c80c00010100300441e0000f000322283e190040413801c0d180d03009030b280f101101040500150785d03c004240c0c820b41500c90303281d080080140c2d41010380d5554071080540c0c80090b120604015041065101c10000c030b00c060300d4926120b0024542e100d65503482800c0c8107030f00d034100800043e41000964000b03003094040d089080c02c01d05040e91518035003041030b8104400b0b45005001c80071624031040805004a0102401501c02c110450003000215403c80c0d440c0400c603180d03a03c07540800f0894030314900070702012b5401021802110760b0020600114003e9070001101c4c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 921776339 1250 921775089 921775097
    0xc040b0a050f19200304030f020a0e1e1506180d020301020f0c0c0f01020312070318060e060a050c0409021303020a09061805150f121606020c01090e04060b011806 71
    0x1d81c8020540c00760f902620303400e801180e400f011310600c00c503039103134441c40c1700c0200141403080b00742d02107464510201c4000d0001003c0300c8824070b402c54222a55019165036402240c00400c009030f0051110b03071215a5403000a050242842c001000d0b03485292509016035601015103984080180d40900003818480001e408080c2c403418044c070070910700007940c1031051140c64920144030340c41e44d0000c15144920244102c0f41d0480e1140c0405500500c00640c3d040390b5100741071410400d101440d0482190043d030b00d800c84003d680c83e080c500c41103501c1952900400c2004000c1000416141c3d0007603ca00b80f101004616520750ba5400552011581d46c400c984c5d4685407031080141c0b86288801e034034244002c4800713010504d40351418001b1469411406803250354007a00c0300303800340c07529188243d050807440c1c21601c1c045495400015440514419100140300e01c10180c0150b51040503510100c5004080081c0c0325155503503039501810714504590304001030984003800d030446050140004180d41d0b11 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 921777589 1250 921776339 921776377
    0xd0c05040504062903060a0308030702010b0a0905093007050a0c08031204020603180a0606090c0f170919030807020607080c07170d02180a0e0c040b0a050f 68
    0x9000964070301c1d500c002059111002c00c4018450341424080f0f504c511084616560358482002842a0720030b0b41001c0e10b5010080700f040340594055020750000c150844900c0c40e03442d03541c4c9100041e01d10480300c03c0e1450b040240c401c142202e41003c00507000740104141328140381a441d0010040e0400c3d80d00340c69030f60004118a0074403c083d0b10b140c019102d444091761500c04d00101c581342404010308001c0c00ba500002c0040c002407900c8c0c03c8040248844130965020b20103509203000900054000c1d00406450000d02e200401d0007040200010005a21a559481d000e408144044d25005100058074003940c06528900d0500400203240c01c1d100b9203c138801030401d920000d1500c0c00041900c014404403c0501c200703986503500b0b0326201540200906403c1142680074015070043c0440000c85030300200318940c0311100070841e400480400e41da0382c841c403a80c2d411910002d14023070351b4845d00103034200014004021064006e11042c1380d5401d110b458060541070078144c3d070344081c400c840d500180c50 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 921778839 1250 921777589 921777599
    0x5060a0b070b040c051020060919030224180d0c0b0a090c03030207080609010612020607320606091501081f15030b011706040b01030f05040501020403140f070b0306060d0c0504 77
    0x5039003ca00c7d05810002007130f0614001c0421a40d0700403040380200c8a0300761002e20802c1620070003c6600100525000f00d4010480b141c200f04255019036000d072107040142c0403005002400260100404580c1ea550a0068a2131b1a14144048003600d40f80348140c480a4150100301c4165100c1d008501c41d900810032286402c000790704141012700300c0d40459040110412a9841460344000ca0300e4040f80c2c415558411860070780300800c0740341d40b90810007041180c440983c50074201203004115410054508554900013004241e6004407038078400b160162601354401d5108800301a0300c05400c48040f100541c5000204111203140e40c003416904271407820060589034140a242c3d40c030603080c00e08010b13a0050300c028842d142d600800040c016681c841c0c0508851303100b604460544041002c0070480c5080c50700300903010354400d00081d0b602002c0700010764074510b0000707000480c030440f0030040c02d40c0505150600300c950344007905c1e04c3d92008060008110642d050b104510740078900b500d64a80e21480c003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 921780089 1250 921778839 921778877
    0x90d1e0b070206090a02120114010f0810060b1204081e03150d200102120c15010501050f040902070f050609010615170a0c140711010305060a0b070b040c0510 69
    0x8066900b150803503001c1c400c143e200043e0f904000b41d0704581d02611032007400d284a0050040c1540502441117800001401110078242e42d016038962000f034072410491042c00e58144c90782440307080d500900806c0348a070714002c0b55200c00d030418410441c0a14004009040c000c0084425940c0384007980000b05001b41c04c8141081c681055200b039552004203119901c44403d001207000c03562280d01442500d840c001e82c400e000142013070340c11910080d03d030b00111021656880e004103101c000209920300200e055070180c0c0503154503000c1d140310980341604003107003403019400102d03040303030a1f003401281400024001e208003446061280700000d682450905003001c14408403403100107100802c0c0c0001150070f9420001a884036440c41d01003483c0c440000200d0360940c220b04900505800840d041040014032000009040b40990702405240c441e4410042420194810445840c42c1009010001003804c1040382e4024000d020369008280c1d0384000c5003900329180b98a8000400c80c6d22031101010349 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 921781339 1250 921780089 921780091
    0x21f020c07060309030804020409060e0f030403120309081602061314040c1e0e0d060903050d1a0913020f041a120a030912080408030f0c012a0302090d1e0b 68
    0x551606001340d810380d440140101c03002400290259407141407040600100b500410340140c005030869240705000e4418070340340e40042c001140d20800b0780e40c03100300041c424080c0344111600156114505002020503080100d41400102c0e00101c1c14041c0d40c3c10018400252001071040e403051400b400e00c90310030001107590380702c5044184807458a4900400c00e0404001800003094141a880080a14005100c050580400a0005090003160020141c2c000050211825040414485154024003040e6943c41c401e24080e0013104040000d261034204195400c825400641103d191000c440301150a89034200402081c0d69501c00c0d105d01d60b420700c10b15840007880300c98040d05041c00030756030007044024984a00900514800c1e030150070301100c03904460081c03291004403a039588200c0c208541a80041a194106519040b6000e2008600d01c6007158480c0c0540c250403d800c0b10040d00341c00a4201142c0143c10049244016001a0780e0b509550b81405500d00070740034101d0680b03050b00d05580 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 921782589 1250 921781339 921781349
    0x111070b040b070605070f05090d170f091011060c0901030905010c03020418200c160f060e0d0b0a050c0c0a0c0e060a1409040624050102010e030406140a021f020c07 72
    0x22191f1807503024030340c0c40410b446140500300ca50381e0020140b42409140d981b06154181c440e103100244000a07044103030000d00310054103a4000000101e4001d0680f4104c461072840c12060f04107100080740304036120020141d02105060000c0c070300b005074444508440c032400300c11b000321303034006070512584201e8042e005454580340301c04d00003072070204201c00307807103181200303001c55120041280041c403e024000300780803c0b10480707400c014943d2010060b110742200d2041c0c0010075181807900b1003038140401122407251300701c0600d44854072403001000051000030710150380100c007441000c01150041c8490301d1580e000d03850151440d404c021604070040b2016007041c4c421000f0000c10017000b90a480100c800080c2140d01d10099541c600f4254050b260303a282c031041071407059888001e10420301c41c488051703602c2a07000b00301903200340c400c00740d40e441607000d0705011546000240340f960b140345000381000751182c4140c4c0c0142e03441da6140803508265140307000c207154011a150010442c20040d07400205 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 921783839 1250 921782589 921782597
    0x30e06090609090406020717071707021c1b170d02030a02101e0507030219260910020309100e0115030f0f0b070c05010f0b09060111070b040b07060507 66
    0x3000800107031052056010843c0280980b10000b82031244540c162607502c0d42020407020140400c00131103501e540b00c80000ca8210207200499401d0190b6201038a4a895000c0c02d03254002d40300350036001f10889040c60031250300503610030602c0182918080040109507000c80c2c600c04241481403a402d041c140c0706188110740c428020b10700c85990004681e40d5401901c4000282240b0494190405841c604c0102001e10700b07203400e000b5415803580c0100303040706040c00c401c1d81700c4c022248225510303070400e518061001300c1150b603800c042e8008a0a150820075180403501012400c0e80f00e042a40c008540a01d81a00a00d80754505aa264004c000c02500c0202c0200800780c50039040c41e02800450001601c5140326a51500420081d41082d805117504082a0f610529280500400b00b00c2443d00880d1503500307110b554000c0c2c01c8036009034101d4100c001c00712100c42e0380d003400449403800d034400700108d10300c40c0c000d0004102124100605c0070b041500350380c0c1c0d074a420307508000081c0c0c2c6019100741c0c200 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 921785089 1250 921783839 921783847
    0x307020103050912122e18050907140d060507030506090106180b03060d060f0f180503040b09360f090a080901050f030c1b060702030d0f06030519030e06 67
    0x203480031300204e41c202e41420390040c0303080d11482401d03941070014007490201140e110003400310102140c006003040314168810070340d00c4100b10505030b040d070700b00703488456865000603820300564050208042074004003400e0b045034081ca0392555001c0d107100741c44200202e513171601400394500b0700c0560640501414107210001548040101444c8000c41c0b00703d030b200c420080f01103280c0707654813540c080515400017402d00c80006444000707001041034003800c0c1c182e5803802251b02e5140006c00448018a40c0040107941010302d044000e4110f036201c2c840c000e5018501c0249607800d20809000840001412405041c81903040301100300158800ba065100b1052070404108801a0005842e96010340c40032903a5107402443c4010b07110381c0251005103440000c08810031901074085405890b00140d4001c828107040340111800e85c4070030050310194010b0f002000311040c9403099811031180d00c8141000000c40366602e4507940d0601020b80b25003240440398000c1e01090591103680e8203000b5400329620740c60 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 921786339 1250 921785089 921785113
    0xe012702040b18070e010c0b0f0f01051504090b04150f050f0603091e0f030c060a0b0a2904090204031101181d0921040312090617040204061703070201030509 69
    0x3c3c40004007003004210341c40f000003000343d200390540741121341e00c28240c01481c2425005003000120880c4d1441c54003141000024007494091610301100e29600c80d29031400e4100488840640702c1d451070341e500b198031240500c1c08998031b1208a030040050080840505082c00e08000c18400c440e048184281c10902c14011440404280d03d001c0c10350f0184950100d50095a480c0e0611044411100d000e000c0400c18400300c2801103040e521941c1e80010411034041c0c07030001c02c00021100d004500c800da4510030030b2401d444d21014184041c0a501e58401d0a081d500c0c018042660b01680041354400c01c401c040882c0395030484645030384040c5004502c0d0b8818123010000d00503008100808030314652410205100900030b1020015540e0091808103982d0014a50074605a00c144021110903001c4c035002d144c240d00c501e58403c140c5078a656007010a4401c13040c0255511130107041a80c0c41030f40d42c1070010b07088034215a54410611181e02951712845940009011140018407004c030f00e402c91108011 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 921787589 1250 921786339 921786379
    0x50403020a05010815100914120606010503090a150f0e010912140c06090d0f05040b0a4b02010b2b0c1211220e012702040b 54
    0x180c40007841c004400755156407003511517034900301000340c000b1010b25804d81403c1e80300b42400c09032012440f1400d030407030034a0f0a0210300e000b070406100c41ea80001d004214158070402c025600300d10741c0c104880c10741d851600d443c5d504860b0a503000600c190b80c1c21141e503034282c20340039540e0040a400c00030060407090751141490b1020800ca00c4040080004c440f01d00700c003250055581e0801d2102c101c40300ca291604050341e4841411070301c007000c20488004c16a0240c4200200d034203071402c0c06005400c020f40303420140d4049140d0408101500340200c503680310804c0400300000d01c008560307412200040992110380c1102c459002c000e045904205462407640c0f5486144462490178608422060001410b00582e844c0c0900b00240303031100c00f040c0014021240b81107620341c1e60042c8010000d10006c8405c102e86405042032410002000843c2e05080c0c1c4060b6104c42c0c050b1740701e1400404c049409a60f250405a6906102d682030424840982c05500b0180b10301030780c00e002070b101c10f04122440d0071540 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 921788839 1250 921787589 921787609
    0x6140910030510031e0302061303021b010512090115120b010b09030c0d0302011505010f02060f0709050a1d0a020a080f040501110c010e120f1c0207050a05030304110105040302 77
    0x9400c1c5a100c8000c103a0240300005068002c50300700142c0e4001c49031004003010480d1070f420043d4010300c01c500200360541c10900014107540d514ad00104140c1416800402c00300090746100c0b81442024408800196001c0340b110b44519454000001d100c147c0f288582c0300c80004e82c01940b04040503246820004c0c1104200c581900d47d040a0b00780c80d400c1140019103404001c11000e904068910007171400c0540540011a220b00d090703860381d00e2142c4690044440c3d5400c42000d5005a0003230b0b0204060703600048015400c000070f8588944415244c02c0401c0c00c103e010fa10292a808100100f00c8a45010700201a0002c010200642c40c001000c04018480c1a002d400346500c031401c4000f08082200961040000740d50300300c120b40c2c80d206c400900c94004e00c1003040c07041c1a8051000a103188805410803a14040c0060703120b10708100c180c410304e010b610110100c001d4602d5003000780300e0110340204510404036210708011507580c0703024070349414038000200400f8144901844140010390354140b42c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 921790089 1250 921788839 921788869
    0x2103040e060406050307060c17030411040209040e120a081f031203060906060509030f0d1d014505060a1101151502010c05070f17130f061409 62
    0x1818007621a000050010003c1d036200c654103206002d00040d08540008026403d5402502208502d001080200d1164841224000c11a00c002180c0050340c2ca480d9024000d100405400003801107141900d4501d80400e0300541c0764503140229000b007a040d4090400c59200d41204140c2c40c00c3c80c3d004410140e9215640001069801c1e80401c81c4c1c9030300e1096201c08003c2001c80b40510446540c0e0402824991088200c603000340a40c1e10b40c0d055035003000503840801c010507a140c03206a54501c04001600002084440c1004285c2e8004000c916410311080041d044c488c1008408440003000107540302650b10802c90200405841004030307503924002e032412001e0034244541c0d111146001107004241650350310300000c03507402c0c0126000000c9502c62076500c0f8940c008002c0e0381600c50081d00c0c940101c0500030f1000301031549401c0081e6500450f00d424281c4d1140076401c1c50403140c500d840035609078100030303000396480500b04000366120a0354440021072805081c500705004010034140780c0103540c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 921791339 1250 921790089 921790109
    0x318230705030703260a050a0f020f0d030e0c1503061207030506060607031704051b0f0a0306020c03120901050901060e01060f2d030204050a0b0c0a0f0f060207060902210304 76
    0x10001c1c16007171070075107208503542030f0349419a00c40548801401d580c00102c00140015002400c07082c083d0300005915145140000c010319411803900401c03005040c01502c4421a4010f000d885441620380c90845e0b001070007180b80003500ca2a1400501200b80010724203405030b9031095008002080010035055000441560500d9031a01c0600f01a10445120b0551514a03088203041006014000c9000000110600540320440113076508108074030418280865200400e8901000001d02a80c010504662040103880c1811030b6014900c0741003071300301c88104603a5160020021036100a205007005807655042d0000a075061660090000310940106400d002c005880700166070002d994100103956a0052202d8070031007031400a002e500544900c40c0030303145401c008120000080c058400980c0240020110801191a0f0b42014909104140c9a1040300030b90100400c0d2107000502000380036400102d07080016106000703441c105400321700344d00b07955500c401c0f40244000c0200c0341262102c1030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 921792589 1250 921791339 921791363
    0x70b0c0703230a1815121104180605010f0c0303021308030c01240302010c080f040b0f03090d0c020303180102100c1707030c08160318230705030703 65
    0x3805a4a0208008108010852151911545403081c4008156010303030399076484807444840500b01501141402404034044440070b002d00c03c9441031175098a406c00a00c00812803161603000340e1071701d52040d0020b0440e83c0680a00744101015406110010203080c0703042e42c0d0402055400922040d030806004041540004a10102414034206000074004c014244d030b640d40905144103008100440f06020a40e41080800c1da95190b258003010071a034060f11508821240343c0d0300d400d01d562002e82003d080c0002400007150800c00c1401400c05016985a415a01d0401800007480d24440d0244030041040c000000c4005032404400c0e01d0103c2c15601c07000c00c60398040b100607810044900076080005240250b40d00080b43d21040c072406000d01010300e000d00d40c9414200710265401000c038040851180c0c800314a101c04d1404000c0391300c592a00e80000d40e805680c101800340000544282c40894442c0c110107050041817803200c940d803002800822400386001c1c08a80c070b65180f84405403070070312006 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 921793839 1250 921792589 921792593
    0x90a0905010b040c05181c0609031704030e040b030d0e091518041b350a121d130209030a0f060c0e040903270b040303050d05090102070b0c07 62
    0x50414940b85000070014040026a980e0080590300241c208800d240c2d03070882c940c06a403e00b4411010340c0055054542d11113421034540300d014051003002181000345041d4400155403207180b245005601c280d0380e1240d801c04103010042a43e03d1440c00c18401e41091818041ca1600f0401100c0c00407020f82e004405959405400c080d48216210720741c0c0c0143d0901ca0311440b500c1c4000e010380c8150f11917514100340e40500e600781d40c80c086480c0545040d404080001d40740454040b450000c6c1617500c05c40c0c1c407002840914141d410100703850021a00400140180c80e00160004100c000445041841b0034080c094900010140481001c1d00440e05a0024600c0040e40301441400a05a004140c0c50030404040c5003420041180c0100400005c0c07a4240040b0705152500510b076100d60903a54880c0c03c103081c1c140003680800c4a401300004010312210024400d40100042c2000714000e0311015201c07402d00c1034032020355100a054410607403042101000160f00e0a060340e401c00000c1d10702944550b032074 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 921795089 1250 921793839 921793841
    0x307080424140610080f040f06090804060c050705060f0904020c0c0411030901051509071b0c08010b04050a09030504030f1401060e0109140108210f030f0610080105090a090501 77
    0x2601010a20b4103140c414586102900d44881c0110019100040321012100d411200340d00d003920000207800d11000428003103425080c0a8807058050100001c1045e15070ba60a115648a6486070740030841001130340b001e0110a00204000303103c250740d82841d048000100b0365481c881c0354442c52055602003a0a082508104030000100202620410111410107521911600304946c2c1203019820300c0001350102810080758500003502500283d080d48072000192948003880b0001041c142c91600c01401144208402200428260300002901c1d02c1c20700602064507401448400f00038202540c450002e0361100840701200c2d00031121080c4103413146040801240d000030344014540c00c140c0049241141c4050903412200b01510400c0840340d51882d000d80e6480c244201000341d0040d0360307420f000d4400b4401c01c5204d19403410500e45003220b042025106600b00340c4a0801074080e000401c691030030011385010051549051170741084d03140c803001840e029001800c00761201e8494400d00100042 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 921796339 1250 921795089 921795143
    0x30915020c1302090a060c030909052d06031203040503030a02130314030a120b031507030e01090615050114040b18062d070206042303060114090a0203070804 69
    0x41010724000c2e50012504040d420403011a0700c6203909000c0052094040d918440034513a00d51581c012851900ba60b81c00203200040590103694441d5030007101c0002d0711401403010714141340d0f0840490030200c1c20f26150042e420b9130300181000c200144404100000103480d4420394440000d607440000319400c41c0324200c1544020305151009030f500700c0824010001e042c881c845c0d6a03a002a00b04070000400076529601d180b560150002801c090000c011098099405050341c14041030704080c640140d404c440ca90b460541e2410780e1504900c40d403480c0208000c0c001c2c802480d20203d0260701908101007481207100d00c5440f440001010115250807880c1c1c903c000704000c1413241c480c8a0310a403003540786544983c080d2a0407461441540400c004402d4038002500a40124201401c1c5032051003030f8916001f424041840800c1801040e40c0e0400406001e8420710511058a962410a00c03414410260105014a006104100b440d81d841000b15074020340004250540c0142a80510b01c6107070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 921797589 1250 921796339 921796363
    0x70509181e0f07030c05030c070f06060b0f040509060f0303030a0902190314070b0a170a060503010213090b0604150e040e10020c0c030307030c0f1a1512010903091502 73
    0x141c054104440a4120581e01e031060b911a103080c802d01e0000a000c80d1341d80f10496400e00250024049c0d01e010529000c4051200c51080300001010b507100c8007003503610342002881003d20fa00019051109042011b4a143c101000f5180e050b2144400d00010f03480c0c0c0030081c450a40a80c1d1a04044150754410a8003d41c0944c018800c03140130f0b03200d0920041050500c1c12a0f0700074460100d0009282d001402140c040110740d907914240e20040780d41262820030041c0640361015152900840d80d80d40a200501c040c3d400c61658062091400300110140d03440100031030700c96a0b09010401c910181c40c603405007410f0040c54160154010349000900400310200c83c2c0c0510710a00610800f44001540100340004411003101c074459030302d904260b920721a000340100040c11100113200002e41c03200300c9208080c414a4215405003142d00052401c0f03100300da1071220b4520303401c3c01c641c06052104112200149800c020320610356940c40162881555106e01d19101084a051245880c420b114401c45d80c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 921798839 1250 921797589 921797641
    0x41a1f09151418190528081b0a0e041106031e040506191a0108272a030c100207050414042901060c0c0504020a0903050607050918 57
    0x80a0f80410300c2c0d004103014169402040320051140886221401c09800c40f20003e20341d01c801d81a103801100d05540310a0201c810b442c440c2004074403540c0501c030007044554400c1e8080d1082503000c0c100300c8400d000d64403404100e480b40c000d200210325401110701d01c065050359804c0d6203031074515401004000b0340d5009041d154242c4240010004081406409a0403168480210031010500310007111414141c03900300039100507000c220742d401205600d40c0200705208544c80712a0302c18041c4940c030400c109013245500241f491810a200c2640000340000114071612100115000425950907841843c14407858145141300e85051003088084050300300a481803003c1e0408003007050702c00700d0564049402404500d4005a140740035443c44034541250b6650009503403804400b0b803000d2814400613a0f069900180c04241c1e5202c0303000422503503803590744482107a813450410f5070421402400c11410031004100400c3d0695540e034010b119021940c1708441980c5844614684030140628840040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 921800089 1250 921798839 921798847
    0x4020d060f06030302010e030a200703150204060315030503120c19030506101b140304150206060a0f0501090915030605010312170103020901180b041a1f091514 70
    0x4a2482d08202c0480e88a0b030001d101c40f00301c14003c2601c2e401071080c4032000444c0508007251120008695026100c05541560034031078494840715000002c4800300310f01540c000a0070400035516104282c43c99080841c4440d8080c01d5588258a91044411020800d00301c0b0004c92030783e0620758121a160300c824a0f60b800320701c170f45540c0a0080e080c100c814521810b886060030044030b0299206034090084442c5061507002d19954072404400b520841c2001488203000228143d140e2000607546844150001c0c05185003140800407106400e8004180e0101c50749410851a60460740500030341d10040d134081400010b16180c0650701d074940d40041c1c98030b17042000010500222160380c22a18580b5a1a1446095945100315910340b00788402908001d003200100006000d201c41c00421241c2c1c90b00c0070a030200280c0000f02603800510502e00802e6106514609501d4203948000840300c2d040c464540011190402411400941c41840025403c04071900100c505c00e880e9801410f82c0c00f0700c01a16 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 921801339 1250 921800089 921800111
    0x10303232d0a030f051005061b100c1d0a0e0c0a051c1d07050922020901030b06010906030b0a0911070b04110a05030604050a060b01020c060301030602130b1e0304020d06 74
    0x50420a0840c800851605d40800e524803080b0304404140c800140c0614540807001c0c603009500c0c01c443c040c41210b0f01945801d181180c0c414041c0301d58840d4640d40d40407002d90010b4000c004800c0304103035640f240840100821204040c3c0011507801545955402d0326544d50a04c15a06841303840e80501000740022102641c0041310b038840000c54422000fa10250040e031800d1550f2692103001c2c20307a0100c1c04000240d1003504c0448403a60f9038017078107182d4610201d150f010641c01c0d0420b800403504180310a00b0030600d0f59000c06040024941c3d4601845050304040100c0c00c18103143c000c6040280d140d0a480d881d10714088120b494060784105049094545818002c05d4500010446882501e003030300300181c0c82c40d00090007030055401c00045d1090718400d507904002000c0780d95485040d0b0050b001110282d640d0300b0007550085005410140c0d5454100c0752911404c121a04000391000081c40b03141640c1004220320782c80445d00c40e94240d540d03100d500024031380c1d020020300200300606003000c001c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 921802589 1250 921801339 921801341
    0x5040b180109150f08060f13020d0c05011101090308040b0601020f100f0f0c020c2407030309020f03010c020607050f2b05090c011421040b010303232d0a03 68
    0x303030b9062103842007030640c03140b5180f007154030280705071700c3d0fa90301c48400b01c1c2006185580858100c080b080c0007480e42c60312030340411144200514140c0f601e1104140401643d42c01048030646410307110000c001007003295802078843c00004d04003411104c07204000441e1a4001c101d00c05010130300208480c0180100001c00c0c000c1c05c14100e00142c410f0a012910320303003031864000c004907460250050130700c0c5514102846070179840b00c0c004c10703c000e0328240d040c00c805d01941e0090582501940c3c01050150050052100c0102142c100500070b0785021001005c950703002c6402070b00802c440c5482c0e40d403a1520368106402c3d014595595031078452021107079507003420385105121240f006010902c69941d03802d44654480140380100780c00f1032041c08100310b20b102c0100c001c0c000380800a4210000d1007003202040e0008004a4044440703100b100010703c189900000020300c80e00c90410034020354001e07001e1042050013000c240901c1c44843e8650040384100036184100200039146405440e1500208020 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 921803839 1250 921802589 921802601
    0x91703040c030c0602070f0513140901090b0c0a0e2e0f170c0a05070510060308070203121801031a0d0c140d0c060809070f08030301050a0e1005040b180109 68
    0x55241d50f02c040300081860011442d0b604031001e24508241e40340c0b0748001c1c40000b55101030715000e100d55800031070141e58140100d083c000c4482100000b11000c0c540307002585180c01070b0401c0d100310411312404001d81c0d88a04078100040080d00d80314101200201c00e040414410020506409403003040a4440759114500c845d243d070756541c40340184150703601409880314040c0c034a902941e804204000015018600804240c0d01c518100e402009002d812102100c40980088800c5030f4001040d41c103601d42003040c0e0707039108009650a4600101041c04140c040d030013490440c14503480e00503090000d40d0b040d08980a4440207003281040050a2800800848050040c10351441002800c507105050544540126a60024001c0900d5041c41f600fa02c1c2c0100044c4060143e00c260007020804a500c094100c00400b40b00000f580c403541801c1c108008100345411a0000c201e50744104801c1c04002c9810030100c03030054500040000800011031580b800b4003600003000103500f0300020b90707134035941d00103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 921805089 1250 921803839 921803843
    0x4030c03051c082403070306060806100503030324150307080f0a0612231207110f0121020405190305150408031918110102010f0204050a09091703040c03 67
    0xc0d100da100340c11030a0351003140030740c4c214500300100f0b507040700403281c2080da4480c010300040454680780c0c0d490355130109a40c030940140c030540d04040240f081c00e006125903207000c0c0500310091410351400351014400e503016034410704c1c4e0384c0d00f11068040c200e0700c0f40c5408a0400b400b00744265506d02d040070000c0c102c40000e4440400ea01c00d02800240511120700c5284140c0da45031a40302d280c1c1c042c540b02d900c28120480500c0040d840c00c0d0300604550102040481046003204031641d0300c8044600300b52580100c0b0680c100c2c050203584201c0d0b40f0f5070703900c40746181c0d1060f500c12607110700c16000d04241c00203004607000b482d007004040e4644035584180d24104800c81c1d1082045980300c1d009000d031650782d1003003520028091641400070801c0114440d105900340e6950880c0090a40e2801c1c1c41e0001f03d8002c40001d88400580c988041900e590a01581d2465a000c00084d80b07028a05408102010f695124050340d207641c2d260b0300002c10603901810302d02000071125940d103a003064108941d28020034401 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 921806339 1250 921805089 921805123
    0x190603020703081f05060304050721060606080c0403021017010f05040e030906070f0303111207020f1204050d111e0112140a050411041d0c04021905090604030c0305 72
    0x1601c00d240c401041070503020604c54042103186410144010398002803c01c550300e00580001180e0007040348800c298a107090505000020002d06040c01125420f800c032008204c1003000300081e107881c880c110b42c122036040d2a03000c3c11310100d260032039101402c000d1002d00c1a03954000010482d50803030216040e1071040740d007080550002003040745d4903c00c8041883e0813030400e225107004501e030303149080e400358000c0c00c002c0f42141100c89103104541c040e48000417415001020300000c1b81d41005401000040d40c1c0050108811010720a0824000e512840d031084883c0c40e00306042140303003242481d1400b0060142500581d00c03152980a11100301b207041e00050181c9200e056004183c06141480012400c00c0e1000c4d07110040b803400030f031900400c269900743c01c00302110111380340c0c0cbc42a040c648860030086403c8005100c1041d08010801a50911407401030000c1c0c0c6401e036400d8115001d8400908116998001210219000f03003e20f500c058200c21100600100748070010603140d10743d00701500 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 921807589 1250 921806339 921806341
    0x120901020f011e0506031203010602150f04030905120330090304030b01030213020c0a03020a0c0605041a2a0616030e03070b0402130f09111f03020919060302070308 72
    0x58070034201c94820382108180f0603504a04001c0885a0340403e0304450054181c2e046420000440e41c000e40c002c0e0300000041c1e01003150000d081c808442055001600c27416030b00d0050406480040c0400c0942c0030b82072040b5144000400402410411560560b05800b40d117108418070080c2e40c0701c0150701c000302402d0101503600151a00300c3c08022501503941c00707541e6903600d0b400c503024404c01090240d440d48011fa42007144822800342049160342c030520a500800d5610307410300d820003081049034080d8050020500081c0300225010030f1206454040208480e00c81c50703e8000940402c0c5a000042c090400c1c8a50309ea002480120300d10f44140c0d001549a0740072480c101c4d0480480f07107129045411900280801800140c0c504036154006000400580800500300e0440040381c028105000c0d0703032a0b0702c1d40c080080042d030703038010320031072000312043e60302500480c0740c200d03000191595140400d58009840841d27a61a012a0140403081d407010303001007600c4440143c029440b800c3c090f00491107440c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 921808839 1250 921807589 921807613
    0x1e090e01020a0c1202070506181503010605071e021906030b030a020a061d1507030305221b090203070302120a0615050f0c060412110a0c170f12090102 66
    0x1000300c44403031240d40c0d5002036140d40381d1542000c900610340400c0c114041c103034001071f00d9611800540044415101e0001d0900300041c104640201109410644244180010001c090708001a5600307250400c0d0113002100080c184400304454201c4025030203100042c0e030b008900600d0300503605807042c1da1800c0102c00550020141c2d9002046d00003540700c800e54070240030340c40c46200c015140c0041b514802603c1181c44000505440c40e0b2201403450540200b0f050060603030501800c0d4002120400300c142c601d000d800801d10806241c4000742610280c0302c50740743e0707121044580d0f400600107031004540300c3c101224020042c0d4414504001c0b080440c8020a412401074840d0008035420605180100c508501c0240e545401a04444504031024802c801250009000d100d10070340c4a021850300c030748102d0f81c02a00841d13060080c41c0c001c1d40130b010848001102c0017100d0054806032501500c40399600c4061714604154005a49036178010f0802581c0300e2443c080c040c0443c940309800340c41c440c2c804c40d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 921810089 1250 921808839 921808841
    0xc020124080706200f01330e040c09020705030d05010b0a020a0b070528090b031003020d02040e0d0c020906060a1209032007030c05060315040f061e090e01 68
    0xd000d803084079004007008104003400303110100c11101c201340c6410f06081914400f5030400300b0240705c840f9103075101d0900c0c0c4800c1e0140c1009141c02c071200361403220542c0700b000c41e1008003a0039001e82c0010300b045401040502072166130050080c108043e0030f540c1c0704210300d49552203070445800d002000e403c00002040f04041e1314140d6103a194141d004000403545074a4500641d40090000c42c207000040010f929030b00403220010f070484038022030040150320401030007041591140d0040d42c030750400740b0501c5089036000c055441102d804072200f8081000c1400024000c2ca4562070b0700c40745210380030310101d0454000c1c91596580d80200c40c10111682c1c6c031401c0c0040f51040303c00e6540040e5045031031922001e03050340400300d0b040c001d140020301d040341d0844403e44030f0017180d041e841c642e0110384100204a01d200010015103000e41b0041e0841c1004402021500a0741188a201e04e844c1c07000d454461000c0e0388264020444180b8a0560048002c0d540d52004414000d604c0b0709030030500124812501 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 921811339 1250 921810089 921810161
    0x3030a2a03050a08180d0309150c12090218040f06060b0a0e040e0c0a0602150a06050a0e06120102040f0e0a0501240903060c0305060f040c230d0c0201 66
    0x1d525194580395000c6401c40b400140240b90684022032110000c02040c0c041090400310505501e00055007080340c2446584260038440581ca11810000d0302c0c00b1569100c103505607030410324940811400210b100003290701c40008622900780b03032078104000074000320221800207140a041e040208948440e02d101251050706143c030040f825021250515007013580c01610400410701c1620a01c100030800102041825401000140c4c8074503200f610504007241d00f5038115034119001c000b03091401000c60340c859028401e40007200300d89030010b40103441c0d0404800405c8090002155500d032204855690003a1304c2c0201541c885219001600034a020b2003403a05031056044605900744039920200110304003500c00204200514034000009011805100003114660b10089091b2070464144401070348044940762285003003040e0790248540081c1e05021046c0110440d80640c4803d0058400301c0c895146150600d5246c1160740c401c066065001c1403140079101c036102840b5105217001070144103 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 921812589 1250 921811339 921811343
    0xb100531171c050304170403170903010e070306020315010e030c04020702120d090e0f10140a0b070507170a0c060507032a0606060221070204060503030a2a 68
    0x442000d0520203a480700c03140001140c80001151288015028428555084012100049030010080c0020408511020f44a0a0400c000300d03040c1031960300c842d43e070110034910306131091000190701c180544082d000401d05076501d00459140701c3da00d1400c140294000c4403e00960303140c0c11340d181c0c85076104495454400d48000d0040114281c801c1c01c00c0029446081c00f2648248110b60320001d200782070100d100508600d0f04c0e4940600d25105814801c03110050004402c69403000400c002e44549801100517642418091142c281e0300c0404101003009507000000c1140c4082143c0003081400580322041d00d034500f00c1c000c082803400307132400d0f80d0b0540180300402e0600749400610245101d5005428007900918101007404c41031101c078529248540034405500340c03000309240600c000f40c000d0800401d254401060f920002007045810480c1520107090750002c00100c141c20343d0f07929000f5002900c401001d5a9681d0050b0f240604a904010000c09002c001e60301207910008403e2100c0b482d980d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 921813839 1250 921812589 921812677
    0x1a0a0b06090a05040509071205060702190210110f0a0c0f06030c080f060a0506030a0902042f0d02040807060207061101020a14030907030501020c1005060a03170a030b1005 75
    0x142c03e02040002800008041120318451401c000a0810303560b104a0150b030700a8002c3c00541c106458000d041140070039240300c02d600803910000c01600c880c468040040020710303001d00c0100d07c501481d030410080100c0200d0900c6039440d044203102034070785c074501200e0710b103920302c00066914141681550144552a0f02003280340002074014491103424650100004010380550742c0c980c0d000650036007081d502e0781449666011410118100b42c451039070314482e424440881c00712000f4014001c0f03030100001d070714540c05c003168400c2c1441c4284c0517903018002031425149a161a44002540c94840f407050304002185a00c0c400e6a001042c400c5801040040c1d0300c001182c03641d2000c80344a0f5001900141c00c501c12140c000010032800cac03018252020384400a000b2111303210f40080265200540032501c00e44d480341c004c000042d403940041081c040c9040300192200131400b8298010602c520300642c0001aa06c0b80306945640500184a0301182c660b0140c100c0002407510b907201d40800788404089 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 921815089 1250 921813839 921813859
    0x50a0f0b041a2203060c080f19090c060c02031009080409020f0d050903180a080a06050402010c0f0f06050a051308092205010503012708090d1a0a0b0609 67
    0x20581c600800046910381c158207803400c00010f03400da02d80041d0222144103003032003420510422005004e2055881942e1904003140d05065070140e0445001070603170070280341e488080300b180c0c45254101800c6260001c1a805080740e42c3c10000d09014140f00c4220b01c6806000303403556071001c0d0351003a01049500241c00700d060034103025104000f584503c2c0d540040310b10601501640d050310340211403180b000360010b15218610078411400305102183c84034400e0000f170701c09100350180003801b44e0740d45402210215986c0c031540016140c040000801a0180c0c2d05605402c0c28400881c005900c207512400040145940381c02040781100c00980b03110101c441401d000348049154003014144000c030040150244200d9a00ca1100c01010700000080d81920f5200406c140e103020b100d100c0e00c0759a140700e041d40c100090f0610705072241600c4401082d840d4045540c1a041c1ca030341c0120100b00e0303807124444c505101190800c3e45e00450466095030600c3c2000c40b00b50b843c0c00d080041d101c0c00d01024080f8060 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 921816339 1250 921815089 921815099
    0xe090a15020d14131b0801020315030706030e03091908030a0f080c03041e14030d0914010908041a0d0e01052401050405040915020a050403050705030703150b0f060c010204050a0f0b04 80
    0x38440850a20044617051a1800308030305030284004d5008100e2000c000400c8070359035060600b00742c12036020506140ca0b01040700d810803004400c444560104035800c0900780d501201c01060000580c010710319900c80450704506c602d8004a80c0110790505803505509a42d82c17801c804418401110014403540070f240f00304425240c620300c007042840c41945405c00502c0402002481c2d5040011404c201c0ba80312070442d014000b2500440402001e4100240b1401c100764541052610403031140b0710301d1841d840e81c0030781003050540a0b6602c0d40140c800920070b865640c1c4410380070b02801c0d100300144a46a1f00b00c500311000340e20210b40a4041070f140d59007418607003000c12006045a01050b01c48400c0c026000100201500c010300b2054100e80381c0a4845042d4208181303010201e030015070080c1c0c400282403002c0f0f80c0f40005006a11020440421641160000316007440345240e40950841c60105807035a1740302041d00035000703031a01518a0080c99941e4001c2540d034000038418a40caa580030001070007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 921817589 1250 921816339 921816353
    0x2100c212109381e271f020a0e06030901090f030305060f0f011d0a0305060c030f0a0605090109090201030e01140105131a04090302120304030504060f030203100e090a15020d1413 78
    0x980024074110015451742c41d0310500700550001406002140c00942e600c00c5078410b907001016444620304011802d0202c1d10202818600d090090036108510100000700440ca00750441c1e014990302440002d000c003007d02c0d002d0058031040e21810704c20300404030003140604001c465003440480503510b00e54416410007011130012480714555400c9a130034400400419000c0154030f001d00d4410603001d0352407820090750406203001405142c10f441c01d15804024980c2c42c0b41a50b419541e00d40e400007400d95051005134010711004010122550814248500807002003926504903030090300d5000d02d048241c000e000403190408199203c01c404a00790703c09c103041a43c400c40600344640101c3c0c44081e2140d090381c5554100322011400605e0019040c000c99a003ca50640345094900b0194214288460428203103c0c01d8001c10418072449000030341b815200300000100030360055400048a01c4904101c0041c1d0f10a590401d680c1c0e080800840410100406072440340380c8281c140000149541d50b050 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 921818839 1250 921817589 921817591
    0x3070507031203180807060e030c28051009120c08030f0901140103060b01030b010306060c021915110609060112150902100c212109381e 60
    0x4010180d841e4140c1380444450031070004241c0c001d0203019210f08403883c1c200d05845014400000341d40051040e061101800201d00c0c800100e031101803580e500414903268810080312201070058440c0382c03103804030000c0340c0c0c1c0080c0c641406602000743c440d81281d026036003944042c400034902801000059800c0444c2c07442c45401079840800800c005400050b0a954044203030000e0f5811581d07100c66110641e0940309059400000782001d11200d4075055000d03004001007580a0b00034051031500d03210100201c1c0e42c0c04040e000035003404ca981c926030800100104a0350301c10074146d115190204071004000508641240c0d004418032502150319554294a6040380381c245c0c84035500d031050300780142c1e2802c5070b130041140a50b0b1075442a5095007010003240c0130425071000ca52051040d11001540d004810b4000c161403e40e5440306140080d4000000b845002030181111010315248070120b0205040710003003140c55142c040088201500c03150800001b07640246c0005003101c60071a9030140410380d1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 921820089 1250 921818839 921818873
    0xc02030414040902030708060703050108010605130506040b1c03030e030c07050d05031201030f060506010f0e0f03070b0d140714070f0807020910090c0e03060a0902031c030507030b01020307050703 86
    0x1c1810781c3e40d5800700b450556140c0001d9541c0e041001048500e603410700ca40d5006280701d400078006a840c00d80411049449980400c602c151a040010621b0b2201c2d0000310b00000060450011200c400d0100d02e4880710403a41200042c5c100780044040030400400d4454058801014000c80340c4ac001c20003254884122084500340014048046045142c076490750082d03000f0f42c80d55104d01d14034540303802100e40060070141480713207001701c082c03809a101e80440b46100084e1404400601113500103490310380564444001031000107074442c900412078020903005d038009403000e0511f84650005582c090b06003004121262014400309000c03038081e1382e074050294040e03c4aa482c04419801040068408032454401203100701000c0156a010340705281e184055407500702c040c1c0008134002601c4501c044d011000031a203d030400340543d5400e000c0d081038401c3d19040110302e5a000600034001d440100c1e00700001c00d10300001c980c040e50020048400441e0722001600c1c0d06070035942d03000c003a07d103031002c6 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 921821339 1250 921820089 921820091
    0x28090c02121e0c24060a060f09030b0c0705010618150b031f15030c120b01080402040203180a03090e060108160f02100606030b0316031e1e061401090c0203041404 71
    0x3840815a0a420611348902400300a41c10320b8040140407000074554030030b0041020500e051022182d01040a4042d01e40c480312400d0300351103d8550074241e000e803c40107007041d460010001000c070111803815070010700340304060107107034146040b10300c1d0a641c620a4150007802040058091112004c0c4c05020310241c00e0080700c0e25407296281d08814140d010f1200100340d603044402d002d0758204020060826400006200c00d01203003000900d4400c0c080d00082c0165000f001099010f140f04004202e9040c0740011200d4210450030000c280c043c2c188035480a640c002c00c042043e5501c0b94020500c40c8054040c20f010150111004031600703105d80c0150350440c00386850340c108030b043c10b004400c000c200035070740814082c000321300b014100445103502030340f104820b240420000d5541c00e5040888020f00c50012610301d09400e012502001c41c840420010003080715160412200d540800b00e00c03d1003c4c0b441c1c0903603880e91001c000b1282c1a007040c0000d41d10901040000140e000c144106d05c6102600c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 921822589 1250 921821339 921821353
    0x60405030d0819110c0106091a01050708041a1908250215010807080c030102070c06080a14010e011d0702030d090302070801050915220228090c02121e0c 67
    0x11641284c0c00307503050010072a00018908580282402444098880c26004000704480310b600302d0811800091090305104020038450705009041040d01d00070204190701e1145d0020500d0444240d902c00b03202203010034680d501101503244565101031040780000c0c48245007403245c00429414a200c0132000c1d04521414820520850403401d08034003c00400e00240304507401c03c035402d401c0c05d0b0074002003406030b88140007820108a01c4c8540b04101c43c0241058880c6842e0505034030017822042c1074252101d05034000018002d801d29001d54100c5d80307890610107140ca1034100800c1146800c0da080401680140b08000c800b40c0150700c0303e241c4da442401100c5510303581e4a08070382500c00450b000d418503002580701c1c88a0306004203410b0740c40011070181d110340404541d41402c0403954103601a01540030644411400324000301040864400071103c2200075580e10b0440b40508035085042d030060140c1c0c02e80d000a001400c09661003030041c02072400b008402514900900c0c1c006035402d84883c82802 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 921823839 1250 921822589 921822631
    0x1c0f030b040b0d060b101701061110110a031107020906060d0f0e0303060307083004050d050703030f110a0f11060c0601031703010602030316090b27060405030d08 71
    0x509070f1020944242c00105403010b2860030802124099400f440034454158034a04500280980d01411358030b15092141c41c600007220310780c1c0742c400f90201340d8181602c0e20701001d404201c0c0101400880c070700350f40c0601c141103d04020360384600500100075000f01820000c5103441c0391002c0078001c02c0102003000900018080c41410603180810311541c0150400000c0c000282000d00c084005001510000d0510030741c882d41030002d25035840740c2c2c3c42d1119902400550703130882c0e610494004140c01030155039440042d061564580a4030f200807408241206070700d9070f2072402514156440e030004006400300c0410b03600c071020b03440c6842d2000c585950000700e1002d240e50705d60010340f024000c1b41008000039070461820030002241c464a01d04c1d4510140010005039034000222544000d0703020140790603242c110015910140030b500040d920341004101040a02030b09000c0200b0801c0710b45001c00050020810300040344a82c0c010300360075420000302d5420343d900407284950040c0e0880c140302060a091 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 921825089 1250 921823839 921823849
    0x5030d02040612050a020a051204050c0d1416150e131e05090118260a0e0a090612170c01050708061201050907061b15050402031c0f030b040b 62
    0x10390440c001044030400c04482e6094113120b4250f101d01d8082c02140303071031a00c60019259000d810b26464452004000107010804148070246255070042c02200c00303080580b1304205189200110f0701101d1041039906862122480c644c941102c1c401d0104090466101500b119062a016000340d00300c05400c04e1006690317014819103a10082c0f28520b2075105c1c94069070034055030400b500c0031099038100030741c95594440029075010001c1e8000c0b9030700c402041540741c0d25280441c070103040d00c1020380402e40c411082c0c0c0007400034035540b0040f1380016141d5107400c800000c80300386009031410143c204800342c00060355046011005100ca0001c2070811092810243c2540d1040315080700240c0d000b424040300d402e048500700c4c084003440c4d009110500d0301034002d69842115203d44001c01c034a45201000d000c01031000800c880b03810040c40b400b904c600c0c1c8180c0025200c20354003240644500039142e409400d051001035070010301e642e5040f4219884210440250070b0128010354003681d074244034403050340d034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 921826339 1250 921825089 921825097
    0x2010b0f01121103101e1d07021c0201050105100903170313050307030f12140a0506060909010f03140604050d05030703020d0903030605010e03010b0f04020706142e08100905030d02 79
    0x31080170700e0348141001c14490215000010540d550750420000b40418211800c0107001008004181d44141d91070203400c034900402d0140c0d040401c040d02c0342030200309074190406816100155a401041c500c1070004a03001a218800503010341001c0c0302d43c10400c4010317402140c00580720300301c11040110036101d0f6401c40c1d000308011004190006964941c00e500801c120000054840041000412402e4540c00c000300080042011680da200050055a80c03801560043c4001070310f003030415a150b0028201d1400c640c04152454410741960804000c00004d9152050760b12030041c200c021281e420680e83d40e0806803048041c9074007401403040c2d0224901c00c030501c2c18000d540100b0010b103840d00150514400c026054066414600c0c242a01d07200c040c04520010703c2034500507030350345072030030004010515107d21080c86501001848413800201900c41441d102d412100702500c1d01c50f40c0440c80c2d804441c4204100d0b83c00142ca12149254a42c3c0f041105e64010016039140c03080c03c072203010883c0c0c4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 921827589 1250 921826339 921826351
    0x305370f02100503190614040b0112021812190f051e011b03020429071b150306050f011214090d0210091113150b03040303050702010b0f01121103 64
    0x4010040105100400c5401d007040da41805e010003003282840711075100e8001803042030380200c2d11115500e00a91080f0312402d22044020004c40d21281c007400000740034023500c011507110f19031012146180000200310350a41c4003140c02000e072589181e540b00d0601c02c140c84c0b030a440b82c5c01021134064030300c22111900b0311409601000011104492950350424101c0311551704101481480305000e00116400c0c2210f05c0c041403410100c1e140c0840c004081d080c466400c000b05079000070041d043c201010040c049054541c2241d105103003054000d811002ca60f443e02c1195480800074401c10820b50083d0300d82040c0006016020401c104542c80d400c0c00100180e8100442d540105204170406138148078145400d421400300f4410740320395455107504034950340300861040c40481c6840d0070010659104030040414048259107036035a4040c401d0380c5030003c071815000301c2c2c00c00380056011071061080b030041180c01420400e0207a1110011074100e814003c40c0c1c144503941c0c3c05c00400071105000a180302c0c00c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 921828839 1250 921827589 921827597
    0xe0d0302210c15010302031f020f0d0203040c1d0705071433010b0a0e120d020102030f0a0b1e06220623033d0305370f0210 54
    0xc042081d600e840c1c290b42040000440f0b51190050005a40105a2003c0e030a0070207503042c10301d10f90240351b80091180f030b500c0070050500002c0080c007404207500030710310443c0119541c5404990b140050b04030a109001802441c20f90f00d400213500d1800307540503010040c0203112804490785012051440c1c00300280e9842e0074070050031024180d42d00d00403001e080c50b07864015181d4041d4981003505140d809521815000d21003111500c8107141c41c0c2980020310703140b110702259031540000501030b000354404c2e101110300c0c005500c0001c50825080c0a8007048003005418010601c03940803040d14003200b40030070315500110400c00822003034801c0e1a00c0d00d64901030020719441a2801d10094400c0c07030140f41001c2644c005100c0000e292008030300303482e8007081d074402c1074035408904130201ea03034108940512160805000f008541122018014909480c8a101125081659844aa260a28070300c2201c44c04485000b117800408034807003842c00d1000c0c401e5a140c000c401035a4001b54018040c840d80000003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 921830089 1250 921828839 921828847
    0x3070e1306090911040f0902060403141203280b010813140d1e0c20030a1218050402030c0406050d0605030d080f01060f09031202070b041d010e070e0d030221 69
    0x107440d0a100c1c41300c5400c02a0420000807c00390302080030307030003070340b001500140c60485100c004c0a004d1102504c80060542c0c502d90364940365494a1160b2002c04103140f850040e4606002800d10f24412081d030000140c68416052303640c5035032040110480354084600c6d203a02032501d03c0030039007006801078000058942c032000141130b4000d400c0c10301450704c024007080410303128407000c200c0c08066035000b03005c911085170b0408080004286417a811402c0201600140288501039590010100c01168043d07008a202c2582e44c031700708020781c00182d07400c20703107250104800c20006010ba0002e0241200011020920503a9100041e0502d04400f00c0d0401040c0404200310611a1003450940544024108110304105d00003000740481b005000040415101203501c0340011700800800008000307252000341c1d950f80700d14003200b031203040b4500751020820400012808000740c6141a100300100e540ba9100c000b94082000003140d50070700d040d03095000701400d01c072029042d90021031006880c444030b84d5031 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 921831339 1250 921830089 921830123
    0x803040803090f040605090c0304050c0a1d10080709180501051512010905060708070c0507060f0906020601080c041e02030c0918090c06032d0906090303070e13060909 73
    0x40c603040f080c0c105100f01e141c0402844690b4402c006240c020100340c40300c0d9102c1c0d0303407480d0451610201304040d07a1700080824000460b40704400f16409403a0b8880741ca404030382c44100b17811084c6a000d001315041600604414400166907038840c04125800345112041d101302901c40c5800c6404c141d8180290520a0030f044965003403800c070080701182004000c200c910349645400d510b903440a0903c80422060ac00420300c0e5510402c01d6014040c5c000d07050f0340d22079607180805403040041c900c9080100307101600000f00c050011031028104e13050300015080ac82c4c48941044024120032040e80107550084426298101240c4081c0d031041d6031010302c19680e010300d0710030440104180200d10a03603882242c01c11103451408910780d0032b039540a91325107840e92604a80001190a4112201c024540d100051b803812040c1030f401a00459800007503461039121420303290b41b6844100c6902d8080740300da400c0082d0506102c20081c00080b400200041c40030344581e000d90959100c90025103040c0c1a0001040c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 921832589 1250 921831339 921831349
    0xf060b0403120c29270a0f05030c060f06011d06090415170102130e011a0f1b2a0a0e10150f030506030a0c09020c07080304080309 57
    0x405058001229820030346582e846402e0801080d4040341086283c83c0b1100410200f152682c0f81c540d0350f007150400304480d05100105001d002c49900d0102c460600c50380b103042c85400c62000d40d03116118041d208164440e200c000906002c400d04030303001d2000b084440700c035042c01c0c403c190013040c600c0300070103503420700000050010030340303040c0090102542034809400b5543d96003200c41c0064161000324008001c00d4180074500e046500072003500c102402516040b80065005103074507aa031882c031908c01d44d241c0c0300c2210000300900544550210b6040c0b540c40c10440d04000c0d10700351403480c40e2a4501254850a90f00c00e414881c0401d030307990700202c1c40d05284941000070341c444840280e510100300d658030000854400d5580b24810780050a040407481d00801080401c0242841c021110040c5d07042d82e00c0103002685070300c0130600103407503e008034000d0316001c600c95103050b4021800056139824090290025480800c0b200800d03c96007500041c40d40007403006c0c200401c60070028585420003001030003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 921833839 1250 921832589 921832601
    0x6010f080607022406030c1504032001200106051005040602150f071809180c1a090909010e06010611010b040b031e0a081306030b030c0a0e0c04050a090f 67
    0x1076400500300e520314501c00601300c40c103601c50450201078940300d50010a042c01c40c13280b000c94001c240a5010280545000b0041080740e00c584450708000881c811f1010f00000480000d90014404401e164110300298a5a40094078003070000118240d413200007030510302000310010045000070a042044a07010f02000c0094480d40c500d020381c0b4585417002c040340c0c0c1c03070080c041028084001082070b412040b029901005c1c00d402c400400800c91004401d030b440104000080314425400c0d9408203502e840c90b8400c4145103461100315050070307125400c201881c0d20081c0034841d0f540d82d13101148031680c1d040003080c1c02850b280e00c42c03440000582c0805c50950700c000c03a8007400b0310309200c0b0780c20300394400140a000040807043d240924000b40d242e5181000c40c080d030054164400482d105a1000d041c205920440303650380c50400000480c24240f54a4140040c00709074050701c8201c0402c83c5800784012039600c00c1003c5400c23840d1944410006403c0b408a81112038090b640e81d130400261000c91040c4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 921835089 1250 921833839 921833851
    0x50a12030b0d12030e03040b04140d12140712080a0623060706021c0f050a14190f09111219170405060d0902311d06010f0806 55
    0x1031101d06292000b0030070221042600800340108404140c0b21244654001e00c4648006026260f80301d80d122625a0140c00900a840a1003003d0300d6409040c94900019101d00b54040180000341c0e82c180c105548840c19282e11080e849010407400c0000b410303034020400c241d451a1075482850504900203804c4400607004650106090684201400e45c003410160200004481995844495181103000b85c0100c1c088021f00c4058400050000304282c4c008494801e4088410006540c403d5a403000b07488042078408000194a00401d000c4449003c4401f58001c1d8a034011a001e5100e8844804881d04881309480184140594030803600d804030003881d040d200d0200070180440d40406a00010900c40c400038910100325004035140a0b0b540309031401081c2c014507098468403141e8603c000f030034114100b05c1c03203906c02c142d0988011a2502d030999801070010600e2044407411115903005008604144125569000e000702d191282085042d01820403503d81c170090601d09800b06140207006416 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 921836339 1250 921835089 921835091
    0x80711030309100b1c03050a021005190b2202120f040b0c180d1a060d0c090f020d0603050c0102101803031107020904032001060317130f03050a1203 65
    0x40c0400444002085204440d81c50310002d0f1131082000090003844104114050f100b0020041800381608a005442c444c5080d03001e0b146181d0000c0181c2c011900215100c560460146240007070074503c0e03500107100600c010740310880030300701200680380300082c40f40b4103a825500000d01c0e010600c100240150440a0800809442e0800340d489045070304009003400034451020030498004059440318601004018003246105940c82c107183c00450800c106611900b030118003c2400c45c10011440225079400a030401042d0b4100058540036110a44007001c0094003070280104000141c440c10008602c07030380081400c0616400064107244511030040e2880d450581401901400c0081441850341c1c149800201c0786042d0300008541d0040d098040d4114020008100815821003c440d034240c041045c443c40f5150350107212030a80700c0500000384400c0284c0200180d0aa1000c007521401300070622007003d44bd25404600f540c04116031044d00c056210a400c0010301000c1c03181032442890380e282c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 921837589 1250 921836339 921836341
    0xf051006080c090603100b0a05070c06080f06120c03010e011b050f0403121e200a0201050d0510030206121902090d14011e1a0103050907150e0603070807110303 70
    0xb0340c07038100e40a42002c841c040d0b0400800904210101070304030000e0200485440c2e25036002820047c02600403020840324442c94030004503200380a1501c440c0702e4500c22420050035030301d0b20240f184906554400d841c4600c90800542c610740c1e001e018024007902a1000041c44a8061203000510b508080c0c03407100340030080100107482043c1c1e4045a0560750003000b0301c801e008110008448854440c15120005683d50744008840340d4402d04001c02c2e120400004410017a040c541c284c0c0300c0c610540001c1c0400c40030451403003248029001940d004c0303801c44403071200c0c90b0341c0d4003c94055070081403440488040300041000c41811160005054214502c085082207522400b1407010b00e07641a01801c4400b4a030034800c0c2c8900c0c00d4100903028024052104500680c20000d40d000d400701c0341103189400e9030400300b0010340d4480e2040b41d20401030040105060380c82c104424050b50118441172013040f104000c480d00b82d4030b800000754010b03450342d96540218603080038001d11140d0004210705051304200 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 921838839 1250 921837589 921837601
    0xc08161511090a09020c07050d06020c0105071115130c0b040e01081f0e07091a0310141f09140a0f0e0d0f1704050d120b0a21060f05100608 61
    0x1540040d154152001640e1b1038400c29028901101584a151701c605807101da0000c104840c1c01806802c1c440c40d0081c0100c0d22902c0f01902c02c584d2460b550b0f8160750141d0501e400c040c01c0262030b81d800000040440e80004000d0f211035554140a410640062400080410254845285072030040040802926013408102407101009540706141c24120361540c0400580c00020f104400c018880550200030041c1e202841d01c0201002c40000c51203801000005100c5403824042c8260090703081604500031743c2c0d11803080c0b017034035840148010400c41492002c5482000780c840c802001d03003031039000c18007803405402e403105540c00e10002102c03080c02c2801551004000059402d6030b551142007940301c400740754000700c840250304a04e444102c803044040c04103001d0302140360060150385584408042945940071000d0b521300c004101d41100702020104191112004040a4800124414000001075031618020b440c8069001040c1c40c1d6208140070a1089804480e00200218148905145041 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 921840089 1250 921838839 921838849
    0x503040602032203030c020d0e06120403091802030a1d150601030b0315060132031e0a0b120a03050d02070f05101505060711010c0816151109 62
    0x508010312040c0c000c004207800c6145400c030440c1044108450300b501d60440c1c10005e0150190204a4001d80601174a08031602c0c41400e61502c034030b40c0500442c0c6841c4c407900038072400720001002030f13040180141000c0303001011402840c0807001c0082003d07880e414030703110400440307040c0000007102d101071084a0420300b8001c02c4000800310380001401e0140d450034010b80140c07011a421a515001c2c100805880482511516004d41400ea0320305001c000f40020981039075a5450340c800b0340c21041c0c0310001014660000540e072102160004030750545500d0914501c00c00107481e40710005446160052290805880c1d441e4504620402460070302800d1b20040d140e44141c0302540e004c5900000c8440c00e001820b00fa8640c0075501a0440d8a000511484800203002003a00000b84000091001442d840d040c03090311032041d00310840018030b0820ba0b00642c1e1640e450311007210741074424000c0e288441d51604040c002d0341e000d68800019685646418001c0340c00402c6420110708051142514546075 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 921841339 1250 921840089 921840091
    0x170103211d0409020103270512090a0b0c240f0901051e0c0705120a1b11040c0306150c0308180a03080c074e2003040914070e010503 58
    0x1c15a000140100c05000480c041c1036001d903a443c0b440c000b81840e0005c0350b509001454224020429035640031040414000944612a2600e910103031303840d0240101c1041300f0042030302100900440e41e15400e482a0310003c003500c203a0044805011108120701c12000703100706a4800d800100800c56480c0075030b5a50495081900c070796160705039400c0082d11008052007110390441c2c004084401001c0c0c111000c0000c1d910000340e07240015003001000340c0f00c9400304003040800703910034404c034010f803a880f091000074182d02c41100704240c0c56220002e40c1c0c10180c520b514030f100303035651000b011002604010b0403041b009010380048081000c01028824004208800c1250b03040c905401c40782c0307488480c85030900134810060080300480840500d041340d840b0f40c070500050f03030100c0d0100440300d01d00000a514000c00c000c00d0605034014a0300c119621580f0b40311645012030f1446401c0c0040c07108a58950b030459007080300c00c075586035a8540d26003906d00c3d519a0124682c0f40c045080c401707034800201030b408 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 921842589 1250 921841339 921841397
    0xd050c01050a111602030f060901020405030d0e0105070308090109120807091d04121110090c0611100e0a0503120103020910060909090c0e0f160e06090d0317010321 72
    0x4130707510101c1150380034010b0801c03109502c012902c040c100741079214000c2d40103200d454460310924418004550140051400c0b445058449604100b0192000d84031030000404048080d5aaa0551000215480440b602c698044c2c0d032800ca4614101d00c010b418071801b030b0444502505a041e009403803002800203a0351207a440f07607804144000c400c40076941010941e0095805018190750a1000c0d82c055000f014040d00445000c41c0c107070360342c460944a0701080900d06d10184c116801d0f0078441e02c19500070403191020b09048400031012603e985040da0404414a05d0b0070507030000400961400c07c1c04a03800244d59141a500d2610b03203500600304244c28402c0848860b10b42c5a61001d01c00104170b004024203119559103014640f2500300c0d01d460030100e604204400d94112070b42c3c8114851041c2e510088070103000c41d41f5000c104420840d030808544000c03010054128060f041520034011024000d41c032410094010501c50f02c26803034020100c109a408101d014600d03100004c003d4198003178201 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 921843839 1250 921842589 921842617
    0x1a030c0d030e1c060b040e0d18080718060b12041b0504050103061e0204050d020603250c050c0607030801090b13050c0d05010906030b16050c0d050c01050a11 69
    0x1114039054503494a46042c0750b03807042030030141d04010307088144010200b03846a00c0811003501c58004200880d2005210240300b5801307c0561540d05008402400381e030881d0400c0c0898149d0340d003102c0d6182800c550845024456401100d100309601c41c002d12020f04a885005810507140030031065030140020030140992203000c2a00388051042411000941070260003030060750703100d0900c1800f5100d000740740741c031746030b5006200f070b04c2c0402c64804d450a982005044010400003902001003680015003441c040c0701c180a001201c0d1242c5900300841c18469072101444801e1780d0914031b0902c0707580c14025010740c0c0d04202d11400250f0000c0b0340c905540e07001d02c0c00115000d500c03021500080ca18010001032520340020701103981c4501c0c01030039192041a005002d10b82c0c07101c0e02d0805440c514440240500300440c041444005d08101c858807030f00e00c6240c902d0030542010b4800c0d2900224030040d1021a4000454650002c0c007805090750064592400f0310441c942c04da039610080c481d20500700e10710 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 921845089 1250 921843839 921843859
    0x1a100602011b2f070b2a030301270606020d0f02071a0d0b0a061d0d02150705100653030f0d020d1808030703090f150504061a030c 57
    0x3040c041c504451102c0f800c2c0112040d8580b03c4282a0841d400400c2c0302d00d02e10700d5030002801c0303e04d00c04446000c3c1591100a14116441d0035240e20003440c00b072581c120f00712075540301a51040d044d44607480c01030000f41e00618416074044405811400c0d4460003008640260780306112241c0000301c4454a10014144c4aa23110780034800c03080104100d46580d42d1200020800042807030340004d40f01001d80040485081c02104130f01002280791150380000c5d0804d10800c030070005184008058201d00c1c0c065001d541d000c120085407041229226006840e2010855251740c1100c112480d144041003200720304820130140e10340143d12407900784907115a899864004580748420705006481014081051007600e42c01c510000300d000e90414114440d10324504020107003d03650300c1c0842540942c0244403585580c942100c128040c6c03104140596040c1c0c5440b8402000440c7c130707242e2110002481200140c3d5051030301d0040c094079103922010040b40c00c10a40381007183e030003007107052610400722010082c1d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 921846339 1250 921845089 921845147
    0xa080403090306090b091c1736010c0c020d020f06040f0f0302101e08060409120c05071406090405150402070f05070509010b030a0203041a100602011b 66
    0x21440580005000c035050800d0341007045031900466002d22520010744a6200e10b80c07611f41c00714415601c841002400d201000849140c2c1006466000b954224203004003e00d42036680285060003800808801c084080c42103440e1001e04c80c42003031400a2078400b1a840443d0002031030481d00c0c0801038070404100580d015942e580c0f41c2294010709a14034903000d400c3e65800e81455010851000f6030088010414050050f442a0180781c01aa070813449030700e00f540385110495542000400c0d0302d8009581c1c1e0410f00116150121030990310b5455640c02d509480703e4a015402d00074260b1040d464074030a0710310b66400e5034585041d109903135819280040c0d2070760341c10002d03002c55883c20f01c0c0c85e030064800030700b2074103014900b001d40004074002d20803940b80c9a41ca005100c1030780401d100d00c0c80c09000601c00304101280c1e40d0002d58009005201e001010703224442444000401602c10f140c0840030b1080403c0030307503028022100c031418091b1080c410501400009840c00a81102c10b1020524070038030014 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 921847589 1250 921846339 921846347
    0xa0e0d0203120a030c030b0f0f0f0405090d090905041703070504080a08091827070e07020703030801080c0307060324062001050c090123040305060106030e06090a0b0702030706050a060611060c0a080403 88
    0x100c8ac00014410b01031814555a0740d0344403208a20b4210005002800c00b0882d600a4094240240c2d4014120410f425060003070001039000076000d8010040100000607214001b00461550316020301101c070394500010007001030704603e40c00c90400c50041e0504120703611500410f00d81c414242000d000c10701d200040c80d00c0e820700b1001d410148181a401701402442a40080d00b0404d5a21170b440c0d5030240e07600c81074100d80d22195540401d625a0100e14103102c0b10740f081d00840c40130150f0250000310416500d29020b0b00b01c895802080000700b200e0301011003946c8480205001110301c4008101900b0203118003001445542c00071414007244a00782e02101c003c01800400c2d05d2804441203131507030f8991610300c2e21a4800e2162200081c00c08034002030402c0702280ca14003500301c0b60024912030090f030391029482d072801070401c0705500050100c800822014042d0502c2400403040c001076182c02c004000d4103c04034030740130b10304c240e1010040100c0403507d070301140d0030124581840c00d0542d03680c0c03074121 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 921848839 1250 921847589 921847609
    0x606060f07060204030501050f0f010e04030e0103060e070e01020d18030602090609211c08072f07030c06170406050406020d1b031b02030a0e0d0203120a030c030b0f0f 73
    0x340300603c001000010b102c410340c00240075119045002000340c039158000c12601d0000e01440b0501400880440c002902681d00c1c807668817810b0401280c0340d43c2e20321120b509540700315002004251245500049513905002c3c003520503409042a81c0a00c0719480c911407014494000201115400510303150b080c1d8441007034442800000b84010100c144000220301c0c0d0130400310b0840319074840e101c0c1544210484104442c21500c0d10f5450ba0845d595041045906407400f40c842c00440303a542e072001b40d880300c1c83c3c101d058080c009503000f00180c1d4031754507102000c0441d55000c041004014400126440350520314150065005100031903136031907506007840240310701d0b28404295031400140c001c0a40c0d031030407040e010301d143e920200404c1404403c40300f4104240012800141c00c2000700c1c03408540156016600c0c00409030080f0f05002c49540460325002600041c02440d0300081446941d582d81400ba070303c0c20820a1805020310400180400c08010880500318491075001540100d035403610f071824 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 921850089 1250 921848839 921848843
    0x8090c03010509150603010203011413240e09030c192d0b13030203030705161403031807120803280614090f0a1104030b01060e09180606060f07 63
    0x80140342440003d180d642c50a41150310000b8400c400003075654507040c4241c1e412a54035240c1040b404030110700b00503400500400c1d41109981c1c0d901081c0f00c00c8160203264070807039810000d1860b800e040446a810401c0010001c08142d40100000e030030b0728a021036070212b030441c0d905424004401c2482c0447c032681c100c0341c5260307510414900110120b080103151700e2515002e100803000c42e85518040801d080c0c42144083c1c0540d00401c0800c010750301c40d800600701d11400401da151685c40541e282c003110410103840d00a00e81c00801441307103050301c12180700d890024071070003002070b0703403900e106051801984c800141c01c801020000a45114480c03550040c2c200d403a614030f66182003c12410300087c0014025001c007520792216007055800c0441249000d10328046030200241c0c1c50002400280c200b0002003844c08505100000010344e206100783d0103420b40c0d445e0400200c8010090101e000001082240101c80400d01ca895610020943d01d40003641525407542e680c8054401042a108070080 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 921851339 1250 921850089 921850091
    0x190b0901021c050715050603061b0f0c030c1e100515031903110102040b0d0c091212021b18060103061d06040b0f100c031b1b05011d0108090c0301 64
    0x405402c1e90380c86402003401c188150b00146084080501c1d0808850084503100d4040e4000d0010a00480d60707d5590741d4644000301d00b0600e40760059203080d0281d0807143c3c1042441d40017081c50700128409101c5c03002e0345501140e4114660124201e80b90751007010b035691404980d51400030a11400342c00409086455026088070101103412020024070002c9441c1900000d03011f1100948201060003150116401d20302403909040d14148200024202d0440c040280408440c0000c2e0240081c0181403641d4000c1e1495280c00400040290500540c5c83d80e50a201c00720369000030b8565030b4103130b41c3d03a0152841c9048402c555a40401a801000960044003075001c0000900607810801107106203e020191814860442131000380b00a116a0300c2c50107902105085a60003504c0c404e5144191300c49c0a0314007000501e50032045000800484913060f20309803600d005511080010034817010007049c003840c01c03507000f603c591085600d01d0180141c031410000501f010814842007040320307110f200700081c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 921852589 1250 921851339 921851383
    0x60204030b010b030417090d1b0e041b090902060a0e030f06160212030903250f0605010602010c020a1110090815010807170309060912101a190b090102 66
    0x1081c10f020b904100c408aa01c0c000c04600c88040e1180801070798020381000c3c109a0162900766540102e00d100300a600c0380c0d126605000203841d41003040b02c940650300444048984008013408403410403426044010b041c1d040411240058070b401d0101d662232041da00d4200708110f182000a41040c121041c0b90005204500900180703400301102c0e401c07071603216000c82c0d001c40c041c000e26101034001140d03045200e81050211070110145409542c0080c071414010a0514042d84d030740691140402005032819507403500144103040e0240b241001c1c3c04440c1c00241240a91681c40c486007420900040e4013503144c0c2c00e03c051080340103280c81006010100c050b07804254031a00f001c40025002d1203402400d00c144500090106010742d009141c101d000406149031558075420b0226039402081c0c295080940b540510340400d105110700591125901c001050241c0008407069030005990030241c0b086003c000812581544c503415401155044400e150700c40d085e940050342044510006c420062800714 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 921853839 1250 921852589 921852599
    0xe0309030f011b020a0c050d140d120501050303030f01090b040209041b03060506030108060c1308010f140c040b120618010609060f09060503061513140a140d030309060204030b01 78
    0x2400c206916030000c0b41c6103e0304425094201e999010044014040303010082c014005810002c0c40004201c2c011494400550b44035002c85262200308807031280010038648641150102d01d008403070050038101c1c015400c50a0442a100c2401018170410746210b999014105041d1960b030180d4004a000a02c00c00456043e6840341032000825503900d0002885c0c102c0c01700c1c030b600c0e210044d0b80c140d0342481c00030300031942d40c01603194081d070082541070010794905030002920b02c024040c05403003101c624008070300000d42d2195030000c0e0501401c2440d200d80e09010501c2500307040c0098070720089007140d6105498442c0d0001c2145103100440c11100d2000820002c242503400513025800c5540035941c40f014141200c200325400c10044c0a144001102000070038458a402040011142a031b456854500300e000512244a03251070380c800c548000c8a4030601c0e405d0715180c444103005090003000d1400901c20000084c840005a450080605070b45101100501489a050b10086c541c4441594101d50b1030b4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 921855089 1250 921853839 921853841
    0x309030201020d0e03033a0902040b1804060f1509020d0f061818080f12060105070804090504141b010810080a0f0807020a060309140a0c0b090619050304020a0b03190e0309030f01 78
    0x40e100c00d8ac012030070600110224200401c16041c160b40780d05d02007009846640d81c00004d00a103603100b000d860380301c40031815600d0782040180005c0030801c10041e40d500d003140c061029a507109020407240b600d480c400300607000c0e21032005c050b01e0b074007004009000601d00f640282d21020000015000c601c011900750b00c2d41604400030a0400780d001001036a61784d40c00011070f52489950300050145005200421510740141c005507045442844c1c051700f034800000d5100d2800681100c0c8821021000c05038204558018000641003007480785250040c40c188002c3c0f40d980ca00c000b200424400c1310000b02070902c139900d4265041c6581c000c214010080c2d84000090243c4801c1c00d083e142c40115601c006580d43c07001a000d1085a800b00410040e14035229030403072144c104a03021900300380c04200180007001e5180500188000c1529480d0320303800c00e801801176405094102d0402c0082c10414440000c034041242707200544815808555000310031070050460061445041e0103110703a041580c100c03041 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 921856339 1250 921855089 921855101
    0xa0918021308070b1b1f06050a05190b09012d0824010f0e0402030906040c0b07030206130f020d0302060a1b080f040c0806040309030201020d0e03033a 66
    0x24a08003140400c1d02c401229446041c00e10403c1c3d01a01c0c20040703030118900c2290b180740e0002c0c1c00c105640d1150703400c140c1301c0c420620301030074031003000e076110b40900c0140741000322500684401c1d266804c0c40764a4400d142124041402007010080c5d02203410011a032040e2010600c1000340c3c80407070003000149416815030f182c851240702c003140b1040c0020744903480400c0112100502c2c4007802c503174030f461030f0019120512901c040b0003c0000654400005071100d000550040c0030348401013040b4901400c2441c0c610300f20703801c4680b054404005080109030f0001c6c3c0646c012401c6580303200c0903c154039000744402c04006000307401c400003c05074018190041500c5118480c0340d0703030034801040f40c0d55034a010000042c6050300030404030004205034000410800ea0b002e031003018049520b50b2203040c072514018086a003100001c0540000b401107580c14005240c4494242c1040a0040c0748000026200e01401d211500d08055200400d240311900c8130311806400d103d004030302401010614000c0143c04 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 921857589 1250 921856339 921856357
    0x21023090312130807050d0f140102250c0602030a0f0305064c09030602070f0501060f170d17040f0c080136030c051002040e0708100312050a091802 65
    0x59400300145034105185041f440ca80e21541c10940405c817550303403010342c81c200c0004c1005590709205d0b540ea5902e060070644814107001d0102c45041c400340c98210102c0713006801c0703903085410921600148541013103c0380c1d201d048500f0085400d5035460b02043c0d503140c0a00792003100320504a00d000300340301144541c000c031401072031416652000d07414020758a00c201c60442d6001404803a01000411019809407070018460600d5250303212090720380500390303002c54220740ea2001940c4010420a8000000405540301c030030080c2c50040a1403401408170f0142065084501500034002000c01400c0230f5405001a8403c0081007000d07100c018090007040109541403881d0f0200c01c135058840506800d401c110820142d952090134102e540c111038000700807100300e03510b1081780d40c0050260307520300151024000c1650084402d140c15040201000e0028000c880703e44801841440450b03011801540c580e002c90030003e948080864007203802241d1944a8108580c24540c800381001c000e40007012030034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 921858839 1250 921857589 921857593
    0xa050a080702070602030322080f090a0f030b010501051c0e0105010810060e130201050f030703091119030b06031e1507020303010605220e130210230903121308 70
    0x641e0742002030faa603062a02034480542e05c24000074081107130b000c007100c032096010066481285090b42ea00d2026070009203d032183c490000c0f51038000d038140403003050000c0900c103c00c0301ca05413940d1160355036100180181c2d030410030700040d00d510041c00350050000c8884000e0003040b04c400300d044030f24001c0c0300c2030042d41c246002d4805024a8a4458010001a520f802c0400609a143c5140308079403035a01d4030080381480428480e524081d40c540313018501c81e502c82e0720b000c00c005e059403500c8a5044a0310001e030703214140f02001642d081c407a885601096035400000d0301002d4691100180c603210300030f6525580141120b4100e400180702013070302d0000c0301e00c04030410019160b0305816604d0f40024040c81000610a1100f003414104800301c08244505d82081c0c98011503d81240c1d14154104660b41d55600580803082021802e01004528110002d45042e40990500c1026441041c214141c000d100c41e102042912490340c0911072822401500d04100e0358551741d0309044180c0703100f24421030b6914 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 921860089 1250 921858839 921858841
    0x3020a05010e03030415140307020c03071d0402010e01050c100219050a3005010e100e10061206050418050610030803041b08030412110a03210e04020a050a08 69
    0x1079400741071441c002d0701006002d50b0610741800301018a01c4040303100f070010002a51b200702007800a007001180600f005902800300302008409051410300164045034003040d400140200181041004c0307070300281c2c240f03400d0720010350040040f03c46010301580c2c240d8038000c80000200e2008503a004081034000c80c21003118260f2001c0c000d0707603507001e807110300000702e88110902c040625603c2103503410442082003041000092440d510308a4030260820305c0c04540346001c4c8903003540c85c5203003400142042c40d0490b05919100035100c1c80c04800b8868401400740b000c02c144503400850300041d0280902610070482c2c3c074501c10781c0d20f081c03c0c402801a252402140301060b1406d028550310b0341038a8025803e140b80d83c179503658244c24201c04000355a68111a5035001c55044028001040200787c050080c62030042d0904050307041c04c542d100c0c824401ca412441c00c01c005019446807440c400d00d003010f2035039a45020a02502e0b0205104161540588002449110680c121000c1c0016602d40e943c1c041706 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 921861339 1250 921860089 921860099
    0x2090a03200a1a042c150913170d0e010c02070f0b030f0103120c05010c0905120106050a090209011b030c0c060c0506041101020c030a08030a0e03030705040519051903020a 75
    0x8010f194910200300358001c1000b801401811181c201000c100501002c8405500403540303100c150041e070300c150318160804e8210280c0d1400801294012200c00074070b16017904e840c1e4401101d010440d016030420b920218002d9000b40c0d0a0340301d84041c0044000903c407189500400945895060040803881114080d000c07c400c050f10082c2c030703c0740e4010081011983d00315220081510031000000703003000028100140003174030031300a4001ea000c980e107521038013074207000c10841080103407445000710360f240140c204030982e24800100f04031640001c0041e030b5007404800403070700044020800d1030b1207040542e0040800d03a00200d400c100c035000390714040c0c2583d01e42000312281881c041000d0a2079001801103004982007070390460b5230b03040c14012104103180d0b0070f01003810604040000c1d02c0b840340120420075801070500806250454a90245140d480e14850180c0140079030b000d11805181c410300800102c80c0008181d03c09071100820780000c0b0301400c04030184130500f901040380101520702c00010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 921862589 1250 921861339 921861359
    0x101a0316050a06140f0f1b0c10031a0906010215010f030201090504180215190c05070501090302031e010f050414010b060f04050d050a080a020d0906050a080a02090a03200a 75
    0x422101004e032032880d0103150302da403410380c0d040001001900401044601000c6410b000b41e00f0400089401906000c41120700f00300e00300d403002903414240360604030503500b82000c3c84019603203846c044868841c2d0351141c4004030300e80051115000322100004002040d040ca004005108880c400d80e00c103030300c140e10740040c4029101004040d4a1400011501a0061421410107452000e44103845800c013043c24410524483c40d00600364003090700c104000302803081c2030041801a103001c1c02c0480302c49240d41e011a0fa2190b201e508070404c0840c030074032004031041c02c1d0051027200a0004040c003960074141809003158201c03d403901c9803507180c0800c140c1d882c00c2240594a442c00712900450505142506021051175078046c11070340c90042d41c0d40c05000500001c068420b040c0190700510142040c3d00c4090482500ca8012a060150a0051a0701d1580c08020b41d94400c80050b8090380301e44030311022514a50b1250001041240d400c040019640c01842c4001e40000c0304482510020f81e940003481 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 921863839 1250 921862589 921862607
    0x42306090f030f09120a0204020d0b0a12080307081009051611010b010e040902030309030304240305060d02060c0c0d1506090218090417030a050f0117101a0316050a06 73
    0x1460f10803003400020b1051502c1010f00d500c0c00144010b865801d00035a00140407030348500082d004d0140d4552400029081200000d4040c02c2c0107441c0140740501d913152641039000041103d020800044001120260362060380b40040804200c00c0c403035030078011103e40390258450450000581460104100d0040500480c04107030fa0684074030042c181480144070140110080603a007620042011452544080008000405030001d62a080401c99009030b400300c44500300e407030300f014105818004160384841003440d100e50b0440c0c582e542c07488160001420301c50560155680840307092403e03c20710014108ac0c0f8a8044285070401c440346c0c413580030030100d014101600c0c00b00d07807100204c601e013420503211007500a0b005070440340e41d42c0001c04801c002c0d80c0c0220340110781552076030280804c40c0c400d00d01044c050001d802403003100a1425024650714001d29500001d85912091003c02145012403003400940000d025608001901d546580a070996842868010400e40c00c0006182d8400c040304 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 921865089 1250 921863839 921863857
    0x31401061d06150d09080301080f0118080d0513060f0506010e030a030c06020309010b090a02040501170402090f0402011112030609010515040303050d0209101205061504060305042306090f03 83
    0x2030107059010f802241d803244c20564400b50010742d58100c09000c42d0328007001d14028850200200340a0411111050a41d40c1d841400302840d00c1c0b000781134000401e503000b80c41100040d00350010b02c564884500c820141800e402c0a417600349021050300d05010281c000300d20411003a06c0f1140a00c09003004e042e6240e000c042d02030000380407038a283c00024080d07001180c2140f000c000201c0c0d100b00c0e2000147e2904015960403115a50000c0d00f00700710758004480301d100c10f1340ca400c269443c1c60030341c0106410401c001c04959400854100280c1160f00400b180c03031100c6540011074120803480c62030800a90b109640e030f1403280114000025161a0518002c07144882c50249141403524550302500c850700300d18102d62043d902405981d9040d210181100640e9601d60f445070032110400d0880411144040d0078079001c0c010f000030604c09100010115801c5a071689000500d99449040214201110403010901c004405980b41c28005000902c00e018882803010303104050350a06900d6070300e01c980c00792 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 921866339 1250 921865089 921865099
    0x20f0306091b041d25060f1206080105010f05030c0907052a0a0b010314010c141608030907030b01060c0f03200f0615040213030615031401061d06 64
    0x40054440044182d2008140b0050701c04190001e940c0703072404c100460380340040c507640e1003400e01c05421002003001c40c000c0c0c203412035244400c0c1e04100000304240e041113060402e1101d180c0c0b902e51050f215500070302c02020308500821195844082c0ca07030060b843d40c401c0510071700c030b0b010500c0c290340380984515016078903544900f0b24081121000100b00a500704480642c10000340070480c0a580501030020304070300c02d9525005541c11860802d00103100c001d8907011580c501441d105400b5040181003222042c0c480b1116210362140715000c0032442800d6000f46a10004420311a100c6c2d40080d0310310980b440fa4110002c00d070b80300c0702c0071950503030f400001501005600a0800100380122081101100116003109000c001c0300401d80c9003080a424032140c5512282c2080407940b603030303482240e040204440c1540751059290741d22004040306d00001c0c1001c0d07502c0441a0b681f12010961400941e801206840c540c0c1c2c0580840e4021b12591013060130040c9a82c0c061718844840118441c454800149 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 921867589 1250 921866339 921866353
    0x50102151512120a0305070e1008091207080714031815070605150906030706020616031b0201050613020c030d05090309061305190312080901060509070309020f030609 73
    0x1101c2098440700700c503035942024101421111505003030040300341d00300310a02e1540c0c2c0c807100500c00400701c9200800d290100441220550003942c0e8590b1300e03440b03c034445e15060b40a030703c6013942241010041160b26100740c0d400110801005941805020400d00030f543c0a1400340c05105100e07200d1060030000302c45400b002c800c1c1c0c410b502c1d1101c03025034003240e200c0d4510305010b080d036546800c1316001c1e1010380d500c601032100e40301645482c42c00268400c00c02e0f005020746a00d4410040e58480e0054205650070303003080d165550162080c2d0120440c1e00f444e1610320000d40320140040c0c003c08040e07546074000c0418800c0403030b4411050085503001c2d622000150f2801010164510082201803c00f40303043c001004102040d07580d2001030000744210324038001c0c24601d02410070001c48080960300140340041710003000410b040120070602a00d503803d02d4070f2580d0310390b8400f50040c48290000e661001e140014043c480d41d0590104940d117100340d03411080160f00c002015610322040b240b201095118034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 921868839 1250 921867589 921867601
    0xc0c0b040f1502030d0614040e1f0207050f15070f0804080a0c050a0221060112030e0d0809060d0204081b0913080c0a080717190c2f040605010215 64
    0x401c0c4502c4290b5441924145180c0211401c186c1300f0307641c00911111200ca13040622460b091050b61040f45501004000c4040e1180d4849004000341e014014419070125060061160a00c80501d8904100c0c0c281c072003100c03100c1030744c02e0f0703040059400c5d0b8000303030341c08ad64010103501070354445000383d801480320b41c03c20704c00707031000c0f5000d11070590101ca4a010703441d8078400586861400100b4424910001e0300301100146c0482d15003041680000510605104501c011a0f08071709124030000c41540c2408c501c3c956410240010311a405005810500020b59412a16015400350054071000760036600540c1d04000740028035680700b0412540040880c001c070b0040c03503e20744000c0140d0b1003000401c0c00c000004080c2c1c0e007008904407064800c80d50004038007080140360030841c038101c43d60b07420841c100351045464007030034082501c0010030710501d00c24440030701c000594039440740302d190010252505d100e01f48403840c501d440e601c828001c03820b00101140d107600208100c04266182d440d0716140d6034400b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 921870089 1250 921868839 921868859
    0x6080103022101060303030b040b060f09060f0708030702011b17070f021e070602060c04080606040902010507021903030e0301020408030f070201110d05031b09010f120204080d0c0c0b040f 82
    0x50000080e20200240d8103030300702e80e0a0141e9001140a47c5000411105481c2400152003080441c24420b207c10000d200d0195280740c107440703a240d41900e4040e200c282c03a4010b03110700c4c404d00708041c06000021003001316045e0705400070036055018111061070b001100c1c40580c0c089107007040c041090300100b000540b5103885030002c2c0384249850320444480d441c004144070410007194903080708a070041541844001d4042242c660846050421740d450189048000c03910740401174407881c0b2030303034481c0000c9055a03c544250752902c1c2c1c0091805000404000300d5512842c40b070301c0b04034080ac01e070703444c201400e14041c400d5038101d4105001451a118844010f02d90035030006030200e0610545085400102c1c01c2008080c0e039052a644581e136503824800f0191000c01e8107841c031000103640c100078059a03645c0c4054051040c10441c1003551201882c61007440181c052030300308810760300c503249000300305a0f8411699038020f07000c1c006000c0d170162a80000d90340d41c440ca0145010744164048204044610 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 921871339 1250 921870089 921870109
    0x2030103020f0909070515070b0708040f060504080706050a021801020d0c02040b03030f0723070f030209070c052d01181b0e0a0204050301150501080c220e091005010608010302 77
    0x2c0c8010785103207681b6040026040d440c0000811140400840c13000100083c1c1c510b10303500918641001c210b00d10305079880381c10b014149400140700545034804101005000001e0702d8a2300d6001c6014050741c80c00320400c0009400030045032111080d404909065540085840c001c44201c583d40c0004200b5160280800b41c080c801d140c030340610041048440d0303004100c0140c61203034411402d911014981294075400400124017034801908040d20800c04a64040010f2080343d90559030b056440c0d03250070096502040045001d0014003500583d5828005c68421030300c0c88024a204210040c0008000b1900b21411030740c0000c6a10b01c04041000469515002120714205016070f0f805c074142c460b9010512900103507000191030740c012405108910b400e000b10390300b4690070704540c03c40d146000002494110041c2071108100f00005030390105081c44850214900c11904441100c240d451140a1a4a04c1240c2a40d10741c022604584500e454a0060a048815a940d0300303020364250b408112515003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 921872589 1250 921871339 921871351
    0x80304411507051606180b03040b1f0b0a031112070c02030f03070b010f121115070c0326040f03202112120a0209190b0d0f02030103020f09 61
    0x400340092000124100310340d00071000e640c0c580c1d046042c50305c40007a0180050480c04aa003510400051200161240549900c140c000300490020b45400c0b004007480c0c44401403081203188410004141004400001e0520307030303090340e81049401600701c035130b0007c0e002d01e00700c0341c5400961801013001c95100e81041ea250900080036542c02a05001245280d6070144004994050804004110261806544a008240c0701c000303038900814070f40c1d41d10110004102628806c0301c9282c80e1208210200c8159100e01d980002c0f064101c07034407800c008025008081e0200039108441e010701c16501c2c0b901065400301e4045900044409042d075880f201181a0207505030036819294849648a580b90b01d0b004900750419041c07600a0324401080703c3c182001d42d1840e510200d01003001c60420010300c541940c1c080d408400040c0c44070481000600501d107d0003401c080000c81d0030000c0f40001d0000c0041c10a005408020070410580041003001c1e400b0901c40607500c180c50380c040c2c041a06022a000340e00107 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 921873839 1250 921872589 921872629
    0x50315090c0604090506090a0c0f08070e0a08011a0a050102030d0209060712050c100c09170a240606140f03040c0b03130201080a06210c08030441 64
    0x907442001191498015600c0a415075440380f06000003424100142500f080c8883c000b41303c440b02e07400b0f0107003d1450896907441005422400144240c0c0300b8907407005440c030001d00c19000d144d0307508a000d000e40901d100c1c0c0d2900a40b1040d901526240c100e0402c01210410b8000d14203040005414100035040803904d65084081000688001035405010f10141d140d903450f030b00c1d202c6110b082c80d9860098404000140c50b03240c110801c0156400900f080200c0380202d0000a5040007980e6983c01d0118015006140c0490219014441c1d450b4007418003d004c200c08080122a6640808842c20200300d00120134a01d010032130105e40c2c641c108002d5500c0390141c8981c841032641c901c50500700360b108850b0005e9007030301c0038001021980d018981350303001500000c040c0b007280c5c00c082500070050701400381010303901c0e140b40201c03041140d00c4001d44010321144050300d80b01da0ba0317a0440c0c41082e040b07107030144011002880150f1011010078904884500c9050f0040f0000d01000074080c59a130b404281111203 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 921875089 1250 921873839 921873853
    0xc030818062106092503180c0501081b161103060709091d07090905100606020705120d020a1b09020714070501111f0b18041104020405031509 62
    0x69101e400c014404101d2080c240e0a403078a089810b800c1108016107514410312100b000d018294440442543e00d80011203501213090928440c241c0040024036222003817a4844001041030010340b0424030100d44007038803000b00c1d581d43e040081c105e04040c240748400940f4140180384000a1413100c1600e241d12a10f905480c015400001925200d01250f000300040c401040c284020003050042c04005ca0f01034141074101403041103902e895809d00d009003548150703549070b09814080704208000800c03c0010040bc00a903d415000b91a150309010342c40c0120007503068144c68500016840c3d41401e810740c05411170150664075844035145a1882c0d0414030610b10010810000e18801800c0c1c2c50302c9081c0348200042c2d06500c507400c00043c0d90100e8144005503482040070b072404504e9081d002100814950721105483c018030051820061003038012100d1600250071410044085000740d000d8480355580002c3c1800700005d0788075500880d40c044d0407442125000e00a1810940d400240319416a07801c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 921876339 1250 921875089 921875137
    0x3030b06070812010611010c0c02042703090e0f090a0b0601051c0e070e09030a0e0a030c12030e040e120708090907180501050301120f0606090e1e0a0c0308 68
    0xc6900301d503940d030403d40880401080341c2500140c80b2070210642c84000c3c40350ba01000310240c503c1280c520080d0003aa04d0701c02100d001c110004040d00d1a480201030b81030303150082c0c14001e180310b80c94002c0824019102011400f110319014403540302d00122402840903490f80e59403060341c04030192038541032090901c229948482c90f4141288442003a072400500080078810320b40ca40a4550b106051001911043c03007103c483c007008480030310103141091507015008070042400d058459002a00c2c1c201d9a40e000300d0403804610301080c0701030003996140109043c020030401124514040100c542d8441c100a07910920170307078007401010f801200e01c0380c102444a00442c072201030403150400006d207000400140381490305581c02c05403a0a19003182035606180d0b0320204076281c036a020f48100c8070918448204800e68220b0301c091700c102001031042110603540190b4580d224001e2900841301200e07140d42082c00090307140300f240e40000590b5122851500c400b03130b080e0f100254040e501000300c020404 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 921877589 1250 921876339 921876353
    0x8211b040302010e0d02032512170c0304030506070e01170c1902010605041b09062a08130e010f06031e020318150a14040213020d020d090b0604140705030403030b0607 73
    0x360b07e0f0015100d013405400042201d0741410800d41107082ca27041c40c0c071444004528105408500c00e808900815540d45041684030b2450080e0380c0002e02d03510801d81040b105e1035100442134a449002c0e22201c0f4844d42420803070600120032540040c9100c0d09012003200034500f00c1d00c4171403010340e40c000000c405455030045819139800c0c0d005070342c243c2c3c0341c5002450301d56402084803004055500d4841d545984007491213003400c00091500c50380210b19036440f8207001c44841210f0740c1100703104840c0300c4150b8a905005058809116070ba410b4170140c100040d82902a004220701180520051090740381c0751250b086c02900054200408200400e4000510400400c02042820b02508620384141341210080081c0c9043c8400c0302c201080141c14800141c6031052072000d01700900c0801340e00c50f00740080c40070003400b036a490043c2a9092010050034007130755501b200e015480c180c40500c8410111060b0200080c0191074080006108000080110348a1350103640200d40c010701d07091500d0329036100c1030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 921878839 1250 921877589 921877603
    0xc03031a09160e18270610032a0306090606030c0603020316110d08070e0a0f0305010c051e0705070302040507182c06040908211b040302010e0d0203 65
    0x45140c102c8818040d403015081840d01420103400c41d04044120344460a80324281000343c07803010b0040703140e0010b50502d6000742800c4821041081203d0344e9107020000341c030300090144029284004091200c920303052641000ba8486e90361f4080f03811500b843c0d540e50030001d1007600400e4404e65584c00000c4000b90482c3c12a80c0100b03256507001d40c0740c0c01c101300750b00300041c8403030710002c00d00c44500d424000c0000d02107030303080c002d640604294000765903046058902030b059040a55020000c1c01001c0340d44601c0c4c601503020780c2c0c0100c000b00040f249000060341d4920400e204104200b0404a00d8050407070403034020030007607200710141d5014594990218094440550308500410241d2078080d00d40c61032101c10f8001004000102e00080e850301d2040e600c203000c82c58100208a0b01d00c0005144c0345c031140c00004040c0e0b40001c5076981d0340c4c941d04030b4400c03419503450768900b00c50401c4042100141141426103070003044003a5a072a0514641c0192402c10740b4110580e04250701c8a880c4015070303000d210b50 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 921880089 1250 921878839 921878851
    0xa080316081b24131e12020a0302160605070f030306080a11130920010e091305060a060513090201021608010608120319051803040f050108090309010c03031a09 70
    0x1481c4041d04400e07501000f51441c50180d09116110080000a2403000352011505412903030120031003030100d0941200103100240540000d40900640f151540e0003d00444418025800d40e40c844240e611003a110019902c501c82c0017130303401e0080c803022503c400e109622140c440d040000d819035440c885a414840090400d0300d400411302d13983c10160800510642c101d510140b82005150b10550380c900b03c42280b100d003010300440131401395200c1d07405001c1111078103c000703000550720300d00041c07400c07941d0700c3c0e009045565000c0c80b0f000c200d4134201c501450f010340314004c141440141e22029404004e10540e04140e0451007521151b000d00084c40c146c078000741910f040040f44840c1018101032400604c00380815207040c1c00c00130400e081000c1c09402c0015001210003003825101c00440495038200c140b41202d840c000003c5c00030f1121814550081100d5082e00c40c4031303950ba605d411003070b268010100301ca804078810040c41c4002034840c0e40040b080c3e58a841c3d022920381801c4010072640780b022226 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 921881339 1250 921880089 921880093
    0x5090a0e100f0608070206191d01020924031605040e18010e0c0105030f18100209030c060c061f15080604060504050c1225021b0a080316081b 62
    0x802d0240064200100000c0d0a0b5130400c0c3d02c0d01c3c140210000d50310640100010f00c4054980381c805460300c20342e04200341c050f05100041400e81004100c040c001e41c8484c00e10b5100c0d410300108003884d110203c0401c41000c0a0b00400707415543c075400075201400d11072964508000d0100404118600c14000340c600a56010400780d000101c07003160f50303003120410320070052903070700151000c90180c0c0d21000301c0e6480310100030001e0303040c1c4408141c6224600c03003202d240f0b100e001c7d818500b060381d0070942c0580010720003181158031582c402400e0140c40c1c4182d00104600e6008003002501d070401c000d0811822b042004000344c1442c6d0b40d509019180041404188005540324050040c3c0b413030305004401c05001e040f07038104040d06000901c00c055208035a00080c3c0c6142100016084001c02540b03103502060349002c4429400702c0c2c800003521030788004888220024528a55411401c00e80d48240507204d504000f14540660607000c603840c0c1e0288801144c1d031080802410700170307547c2c800c0c11f59018020540 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 921882589 1250 921881339 921881371
    0xa24120204050a1d100b04121104060b031f06081302150301080a0b0c0a050a1b15050108060a0e0c0111071806211203091104110c0d0e1005090a0e 64
    0x203001c590704003d80ba8511500c0004e100b8820b02969504803021a1040c062800d4108d0080c90701804c004035000c1d00c541d0092904500042421800000714030441a440181100154400181d103c1c01000c1c005c0d0b40015041a00268003081d0840301080a00d000501103038001440c2008424a039009030403210450f000348210904104d1513000640d0800c03010326180381018034107c80104a40030ba452004c00304020881040381e24070688881c841125005a01c86d1540c01c040c1c0d00c4000505400e2040c0c0c030b060311602002801d9040d41d80301c0c9458280c043ca01130070344810701c400111912040c904048080d400f0302200000c0402416082580d54480150003051003031818242180d104403a86841c0d508074640d03d00c3c4c0000969090b00011106001e00300002c0e03c0e18203007480200c2039581014141c0040c81c09100c004100b2044016002c41d8011504a9584a101c42803c69803180c42d01c4010340c01c001a0822811003a0180002d04030726500540420349541c2e0700c502c8014440f4060701e0064211840726 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 921883839 1250 921882589 921882629
    0x21050403022401080c101101060f061b0c090e010b04050a0f0501050102030f071707141b0411030402040504110d03030614090106050d09031b0b060a24120204050a 71
    0x10030315070401d542c07610303001e0150b150503045611844900da58a10031030202851000304e500400b1104504002c0b1002004030365201d040a00b007500f070f01c0c0030f894082a0011399890000d05030040c0000d8065000b0b000e900041d1400302c00d80c01500302074002070159501c070013900c003480e200c9100e1240724210480001c0f40c0c103500c03412044115841a0016030441d041045258001c0204900b10707916154044c506144100745403000803800e0080c881c00501072032850022000c2e913400098900d4410240c020b0204e450000d1204101c1280c20703401240e07007144024000a07025140551040307a010b40242040203410307480d0400120f80c9101d00104401081d0303a0704003403084c900d507100c10051000040d101001a54181800613189000d907902c1628001c2e00d6404070400c040c441c4809842e581e00a03040030494040b9440c0c5090315450803580d441c002d481001c00012408802c0f11481c465141a5000f500d010041e0501113075902c01b500c00c1090700980822001a041c2c841417200c00061094400d00d0002800c00c0b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 921885089 1250 921883839 921883873
    0x61c0606150e09071115060102070e0f07020d030e100203060a1a030114010305041518021f0311040b03220c090f0b03210a09080708010603052401062105040302 70
    0x3409682c00c00c0b45c0c803218165402400900030b1101192072002d07410960b41e14004030b1424203113401610018541009101c01d400d0002c8106000307100d240c0a5520554035050110700b01d039000a40d0449503404100300c0c214118041c2d000b10f130442d40140c00080d0031307501c0c1c442e0503003045441032801c40d95100002c010000545140a440303620f0f04240b0b020300850402c0c1d00da01c8600c00d41507024121803603036524020041240c01e60840f2029501a2040050348280d030b6524402091040302507000c281010216000d1810600880c7e00b0f40d54030700034285c110b40f1740042c820382ba50400d120b15105600544480c078080394081000000600c00b40c41c012030142d0f03215080c642920180181d0034040e80c400d0201611581402000c1c40c075403d103002500351220700a840072251408291700440140c0101c0301e010403000019007000007aa0300405c11500340107200440e0310001051203042c1c49070308203c0f03c0107210071032054516540855010307180310498a007003000b90b001c4680a9504501590007401854011806 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 921886339 1250 921885089 921885091
    0xe0616030212070e181302090a0f2901080c0a05031906030b040c060c021503070c0218060f09010b030703020703110102120a0509031305060304050f0703050604051005061c0606150e09 80
    0x408117510031401d00c140310401c0c0e41c00c08600244929075910010b913056010790701c00c9603441d0070075800b84548507194000324a0408501d96007250f009961050f100d0039405110b8050240036424040c40c83c2c4040c40c1070480305500003a25903200d80c1510005c918044a00c1c3c014240690f0140c0300d90030090400d07184c8246013900c05d620031018407101e2500c40000d40c0d20740344650b80191358155505d50300e9554031021202e0702a4002c0080d88050240400207006880700c2d0210b200750419a41c44a800421108001c5403101c24411507042c500b040000442544c440e40240800b0f911034200401c40b61010050305003a40c00c001c52101410f41050f0400695000c40c1c0102900804a24055441d01c09001103040c03401c0d1a0340a0180070302e6000000c201002020449480003000c05004e58103419100c3c5055904c1e60800d03034059525101710b00703501281001500c075243c025980240b03070700f40304070085c1c0118204484104040d10b52036075810380061203003501e00200105540a0750b4520915003440108410b2100c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 921887589 1250 921886339 921886369
    0x80306011b08251e03090909050303040b1b03040f0c030803090c1509010507030e180702101a100e040917091e030c130902060403060c030c02010e0616030212070e 71
    0x400c4602c100100d51318003280c05240344440d10340f59255585003001d42d40882c450b07008020030b529025500061090200241d40034903c6000200e49549480c2c0900d81c0e110100020009400002c04c00b2034005060125500021031084821140b00344d900d494006481c1c1080303529102941184500070014500712251204800ba080d120b43d0800300c030720307000070202c2c0604c610003802e0000e100c100c1c652a81d00d5031462054820003d40448080c90845030080d00c03500b11114007401e02d400c102050851098a95419290120184c03004114203074041085440202907181d85030820b07650921013001c0346010703841c030484400b4841300c20368800030321007408400c5980c00c00010084034010701d009155a804100b02c07425840854412001c40c4000074a01e00802d607299002350321075000100002002003903002034800000c80d0b01d04101c400300441c0182c0c2038407050898100d01ea0008400200c10722440500c0026840c1c60b85801030602c2d41c4000140720001e0155241c2e40420303080d100000d191702e00860060302000d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 921888839 1250 921887589 921887647
    0x70209070c05030f0903011808040e011202090601030c030923150c18121605040b060a020c13150305033001053c040510030f080306011b08 61
    0x31500c0c0c030703100d44a00130039005044c04000060610441c0e0340c01d4100d09184503407900c0300081081c0038941803001d40d0107403040e4030b04401e8070000022400c00c44043c2900164002c0c16444855461800440c000c01d80040309206050303440140002207415808c80e1002e07107009110306259082c00d014807034548940120600d0b510541c645c20004d03130a607500155100301064081c826454100c040018400700d03c035420500c1c1c80c0c4180001070502607041d4102a085031410b45080101e0301c000070500c0100c0c03040c08541c4015a0044030312080c1400c1c0340b81441c560950092002540c140c5607544144a00c081c2d0b801601c0a40c00070610240440e10b91003018040c0e41c00c0c009525004d40c210920b131051040500c9400e11407440034009850501da58a1010107203820b030003170b0315011100d441580e03155440a86016000d181307083e0020742e8400d0b00701c2202c0d0a803030308594003e1580c1441c4d601e105455000030122030411811142e03204513035502d0396941c81003522030700d4801c0c2c541440c1c1c03414010700c142d84004020a5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 921890089 1250 921888839 921888857
    0x20010b150c150405070509040506102c0c041805010e1303020a0b060102031c050a060b0a0219061103041211010b2d1302090a0b13050910120807020907 66
    0x480010360384100c05100010308106990304e003070030350400c2010b80c0701d190010030300010001041030106441d841098005003903c601501d504001da4002d1044252a030785a29020100c40c0d11824002142e5206c104041040c1c41c0507120841e40c11118299240d923900e1903119001400003090713085000d94441c4840c400c0e040d42c00c0180e10000c3d501c1c00e400701e0103094032400001040c000d134800c3c821150200001c4c5468100a900c0000100041108480038000c1c586010717004035060909108230b070721041203030f4010301c1150904d131070022112584801c100c80301e5071b42d61018a008480c102c05184614018444104201a8410090020b0f0b014502d40b407601e0345020001046030303546c000c81c210107006602000b0300ba40d11440340e0a0181c0c0e92301c1079048e0300c403441c80a951300744902034000300341c00282500c101703900c10b0b030b580c8542e600c5001c0c0c5c030605192810407150600c5503060283c20207922040e440c815000c40390741e0700c2404e10840b420303000a50300d0036030024109082d410314219458004000e0710f410312039 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 921891339 1250 921890089 921890107
    0x30703091d0c0304080c0d0e01110d050417010213120b09150f0612061006180509060402280804060501050909061501020a020603312120010b15 63
    0x103035040142810b0001c2c0d008004207003444a000c0513652101071080c00c64076280c2c80c190020705409a09000d41740000e800584110b10340c2404550b030798000001b41c44507410311381054400040a4202c0d00748540e41d40d404e111541a25995181500c010304505003500300c0308210303040227483c03198010078084c4c00d98440e00d0308590407030310305507910351000301040c0120070383d01d50702c0000c0d0155000c20020301d480d200e54010701c101804103050305c0003210819110341d40703070001c0307a40d600713030601c22501c03400d9441440701c000504541042d800030b00718140d00e22140e01b1405800d44800f405001a40403170000605450200410002248225400b500341201c8017603281ca4801e201035600e18004110b8520000144580312160740208915004541d00601c1c194503031a140e00c095036100940c02d00801d0189032402403415569519080810041e0401a99490314150b034200d80d02c400b44803c2c075001042040d4160404202e252071039144001c813010300114968140c18100071b00e00c0d240750703183c0390510000c00203051 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 921892589 1250 921891339 921891389
    0xe030714041d0a0803040c1509051017011a040f080c04200a030b0411041e051504030b100e04050c03010606030204060c0605061c120306080d14090d0c0803070309 71
    0x482130340b0001840d40c9540d01c0c44c01441125450380280450906003424a204940002e8150107035681510040358002d0f000070304494403064001660480307407400300140300c9680c410421601c403048076401d880c601130391960001e08803003d80d03200d401c01b5044002c00341703401d103803901417250890108c074012018040013910000003442003c0800e41032641e501d880403860f48480e000440b4a2681c544a10b0312143d41d854800304010284601d054281007202c800b1031039103024000340c260144101011800c00b8215680e0604000001d41990020028014005806044c3e100040d205610900252113120785200c01c0c10309645480d04003109040c0140801d00001f036010200110b4181c01c4000858143c403000082103900c58030100001c0d10104d2080c2c1001031180c81d50720341d116611036507400c000740c9941c3d405a688034003076142100001746c00e0190740b102a40b03080d0050308034260020924550020980d54101408600741c0c4001d1380d503000803820320140340d0414221001031007010040742c01071140701c1c540302d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 921893839 1250 921892589 921892603
    0x2a060c040902090d0c080709050603010c0f1b050a03090303020d020606010806040b0f030303010605031801060614030601020f150106090e04020d0303020a02030720121501030209070e030714041d 85
    0x10307003590b6010407962503c0d60b401d124210015000300500c0c0b9401c0d02c4066440e1298818025a042c0500380404a212800e0510501110000c1586d5200017034540d6042165001a100c150f000d90610320300250010510a05c03c0810291080d168a40628598903029090002054075041550401000c10115980156100c6e0b8000703c220380026803602c880c4000307200d401810506d680c0502c00480003041c881e4128008601490490300c2101880c071042d8426403c0e2680341c0100800111844582e54592001c10041c5400c904140103445200703142030881441c2500c118030004d182055138004014558107d00d002c0003030000e00d00c02c25154903041e000f24040141c01000101056030004010101920038003d0300c0115501ca400c42c96101d1408101782c0c82420f4110310340b840b40890116582c0079020015140704004080611a02145e00e540c0801c030300c01000502e500300f44250000100c0e22607800b40302d11005030501044500c14030004406100840e2440b51100380310b120700c1405940c2c0d0f150009210 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 921895089 1250 921893839 921893849
    0x3042102150904060306051504110c0c090c0f070b0a061703030f0907052206231009090e0a200d120309020a170d050f07030c02030307082a060c04 64
    0x140703a40b0412040401c005004650002d81541e2504080c031402d201d400101c6544841c003158140158071040c5495000c03403180070500000343d888680ba0440030306109954641c000055445e840c00c0059081c84003400340e01c11030301200c07855014001c002e02203407941b203020050095411418504140c001003a6179901c00030701241c01100c400c20008a80c4002006003002401000d080c008c0845084240c95000c0113810b1442e08050f410f040c00810070124540341c4c5c46904401c80da200304a0743e01401840310700702c0141c40d50010040c21075030216488985000300903030004030b80c00801c0107840341e007402c8034074841c080010301d03401c01280300240c0150f03101642e40b00120b03086004000e110200940c1036004251205000790401b03a8007000003001044200c00c1401509640c054982034109850210740c14420fa003012207100700107019160100f07100d14200030400307202800302c81c03a142c2a41c650100507040085080d035900d40c4041c81c229091040c030441d01414030400001c003c00e08144064016a00582c010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 921896339 1250 921895089 921895129
    0xc0b09040f020306131503060912030e060f1503070f23040209010c15091506150e03071a0f0f09011e022e06090e12070b0604151703042102 61
    0x6800542c54200814000940e23018604002105552402c421400f80004210300824500745100c800038002241c482e11402480004804a50f51005003100c8590000d0742503030544261800440c0c0340100c92600b80103814500b070514095410300c0136030b0100036110759003103014500602010041d66001540c6480d001c0d806000400b01e10300e05011a001014486170203404110510880c04512800f54440301c00c4d42c103599407242c440b608450094a550405904141d0541d204040c01c1288252400b141ca2010380c0b0408450310308400c2c11000401d85e04012a010540b480015001d5030743d6030050340243c0d46000141d849a410780321000046d403a15150755003a00c6007d00c80460b1841d412640d600a4034004030007804004132500c0e09030000081208070340001861040c00700c1500d0b24090001a1040c0d242e1000b28240541e440b60180405000341002c000001e01092401148a1001c45043c14031289050700568071a89490180400064a41034540e040160001071001603100c00441184418020f00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 921897589 1250 921896339 921896351
    0x1030221040816060c08091c030f0605641206050609070c150c020a050312160908032b0213140102060108190503070c0b09040f02030613 60
    0x4002c455441032400c410740140c480e81c540d07001c210190303104003130380b03209695402c102c0c0d0348552980b541d40030000155648601c0580103400174611070341100511546030000814915a10320100301100180f4208410015280e00720004000385040d0751480200d4940502c884114070450800310020300e2500241c56401000419001300c3d60340403070000a0207060040302030f041c0e5505001c001450191410b91081d9501000b10311490b114010022034127821083d414206814850050020b0142c41545425801050a10000b0950900c00b03080900c20400c0128000e2401005100881c12800c14103018014141d07002e01402c40c0010136103130100302c410b80800d046801c04503101001c0d0203054040d54401e0000811603441030405a000307040b1800b440401d2880014000103903102c4809018208440d84110781450709e41410300040c420590042d002d0741d1420b02c01c1d40314009444100d411036040302900040c941402d050903c04d440f0007601c481000c500314104103000030300301b0355445001c0800c80c2c5c92f40 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 921898839 1250 921897589 921897593
    0x3c0e04110703031407020f031b0109080304080a0e04060b070204090303090213060f090c0807081f06050a020606011e0c0c08060906010302100309020a2105070609140103022104 77
    0x250004580c001803024503622058103140040161240c079440f500b502c40c4200104070130500001d01c440355040b409000e181400e400035480c0d0111055607441c5081c0c2d641380c056500101e0f4421004601490142c91807542c0d072222024043c0004400da6002d038056480d14104000c0020002c0c10b80e0700b1142d0441d004038a401960500b140503000d00304019510104641ca541d4480d0b03901e62100d011901c0b0345400d00c0f41142c1d95241041140c0c13020071070b0808200128005554148039102c0c080d8044011221104030038540d001002c0046026000100441c200041145000341c04100c45540032200b441d1910a07243e8020943d221086000280c2091101c40304240c1c1c20840d0500301c60024200b41800c0741d88918049090b03c0d0340c2c2c08c0a00c8280c1c000e50f022042007030b88a219004482e8080c0d000307041141c20a103809420410406500e49110042c140c013002600058014032881c00280b03201d5a03452040c84c140903c540c1c070b5200494007e41030510421145050a84013003550814072030507043c000c2d00755128 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 921900089 1250 921898839 921898841
    0x31e190312050c1e0906040302040b061905090909300d0e0705010f090f060e04021b010905060901020a1709030c1002041e030f0204050a0f0c3c0e04 65
    0x1c6a40300303400350421042250400c401c00103840425041551030b900c07044481810855803040c8440213411100070082800541000c0c2c0018000c060044c00b40c515003540d132581c40e1080070010080000150300000e14130107600d0712140d6503400041503c003401500c5100146481c042d02c0004110741503040482225084c4800d0100799400b07902100d40a009101c0000007240e120900d0b805100c2c04104401071400030584950a0700003a981d210203210101e0341401400c1c2e40b4000d81e15819030b4016000c01c00d42c40320072005a500c40da071642c1c43c40049401070461502c40d0800c54010660b640c180c2c07040c0854082c1c5a88520309003411030228010b02800d0f102c8001a500f5882145045240c3d071085840d1310440140d80e40c0100304442080004480c400f94031a040ea0900400e40300217001200300b610075401514081e400907400240c40800003603507900c54900320702912190801000446d894905040581007122142d00320090400c941110010724290b810303801d03038038001c900000c0000380e400d058495212 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 921901339 1250 921900089 921900107
    0x80a060b0f0a09020c0708010606090e151f0801140d0b0c0c070602030c0d020d05030a0209012c041a010804032106091a010c021c05031215031e1903 65
    0xc0079103400702540c0c41c0d080180c040d50243e05c24180c80e2040074000542d240044c0b2822090781c41a566240c40700c0c0c500721044542010140002c11007128104080500d0382c0c0e43d02c0d1207100c1c0f014541e0001a120007105010300b0686c0142c0c0801c1b100c10807000340395190f0341c03006055000981d0003060010039072140c0003807158501900380031034481c0c464810040b641c1c07034001000c0c0484082c081c04440004483c5401280c68402001800004c101c090010580702da43d01d8000d890b0300038061400c01c1500d0721120f0507440c9d840055206107400c11284c800c8841701d0415001e4a8004551b902d02020140c00c005d000070309080e80200050100140c04210b80c101d00b802243c5e000b10841072030030a20109031140d0b034110040440c03072103010a91440e00a003110b194054802d480c03c20360024000d04644000202100740048059021199401b042254407040e9607030028041c064080101001d80d601d904000b4546800200341c2c41d2a84d04800c4a240749500302c0001e400c0d040f04c0455288001103a405250655058031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 921902589 1250 921901339 921901369
    0x40e010b0d0602030105031908030c090105130608062b020f0102100e0d1b032703320601030c052101090b06041b1d01050c03130e0105010504080a060b 66
    0x80641c03107041802030341e030007641c1680e1044040d11240b1489050400075000440401041800140001004003545402414502c00181003040c07408003591501d440014583e005a40480c2e4a10b00744182424099002d003103582c0079041d100c5950500c2d4048400350004200028032440e020050710585034420701c01031007121103512041c4080c9480301e0807075481d480004400e030300052074525018103582c00d88414030005070309602c50b500111507050014141d16082c411100420207410380c000f0029103490807417203065820914100e80e00e800310a038001101040d1003114030f5503108000600119950344000421588200d5000200740030076a511000b8171000808482d165107440f0440040c0000181c11502c01c0400701c60400400b0400c01003800d540202e5003203c00050b20070001803542c17a240301a1a26460014100141400d501c65122441c6502c111001d840c0d01280000c1000a8a124030b06070f80504000d003031840c01e00c0e003407150072070b9242030f080c0713001e001c40f0344034081035041707494011001c6207840c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 921903839 1250 921902589 921902599
    0x60603240306021809180136080c0f0c0a153608010e010e011a09061201181103010c050a1b0213020703080108010c08010521010c030c110c010e040e010b 67
    0x1203020300712000b00c0c8041d4031071441c4650a0002c1c10303503112400656000d03003400300811040c0c0388642c0300d0700d24802c4802c07507009c4880c24000c0190b4802c0d1002089201182480440100344c0070000c0c50a1083c0101a03030f00c0200c420031420070380042c2d13a0b00300d0b03120f043c02c000d001c00717656008a540e0480a1000e24904100c12554020900424400c0c0c0642201c1075010181000348100e2854100c518205d40301c5c107500340007451030a495001c86207003100010f030b04628010010b000141c1035482a60840e0001e00d442c98222081015180800c5602c551035072400004030020031642d03045500c040e00d42d01c11004180c0402035106070f03560b0040103602200074102c0e00904001840820241200000d40c400402035011444080000071203201c1402101000c001b0341e510703151580d28002c2480010b55840d06d030301020800c2c18030b44054100c0c0910422a280f0304a95020074500810500600980240001810f03036403c241036940c1540d81084007511503c6040d1000504181052615401080f049100541c08 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 921905089 1250 921903839 921903841
    0x20a030f02190c06031401050a090e010e060f04031403040503091c0f1211010203010302101b0f0309030308010b09090c09060906030a050a0e1c05071106070303060603240306021809 79
    0x44000c0c0420f80b015141917880c1000302210400c14241010400d01c6440d0380488807140a114001081d00a5440c184402e0300100e40c1d2800028050b00740142140e0b00140082070380e08100c01d0680c0400b030b03055414540a00d07a441c5007890344440b03481e446580809801800301100708100d0541c13582001c6090b9800c0203115203941122315008103032245450202c40080c61211202042120603c03c0b24100ca5004103055001410082c055a41a0507150100c4040c141ca030031400116249030030552201c0d100c1d6842812190451070701418201047e04000750980050100074444d86038082641d41044000800503180c0191400080062284000c030641001011090000040580e0001e81c001c00300d0b0803061050403550011260b0340d14100324001c450a00c8001c00c41c1d0140d0040d00100081c6005080302000c2146900c00320b8003e40c0010021000265203202c10058141e16100303407094440704c05509145145043d030762065070700c44c1c0d0002501c091760000b5550b00e10050b2107a100c61080000c3d01c00151 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 921906339 1250 921905089 921905093
    0x60604031a15010f020c0f0409080c030301030210050a02150624091c020d1118070206061905060904020d06080106060903060b060901080127020f04081507020a030f0219 74
    0x40144252a07a101440b81210020425801001d40b04800104e9500601c075407020642000000c446c0068625086580d405401c4042000f01c402842000751070401503680c0e500d1481400b61b040036002c01042041350900c0001d002e950b0102d038820b0399004140503d0000c0d114900000c0340440164038034010010a00c114500c10440c00018000401d4100c82442c0c040d9203c126081c4200541c8900a60012140181c80300003000f00d6034180702e441e0046c0100d09211011100315150440540301e18026030b2005040000a140c10304502118848486134000160b2403e8003280c0c007030040c0b4107910b2140f070300840c0e03045400495134807100080030088020700c0065510030015107988050300040c1c813005c1c140030280c001030521508841051006941c9d905103a807815032510281c080d481c01580000d400f03916555144000c90000d4014a0405400140c0c1c0340c1c035000910f0b190945072803805229694030000c0111103600429034a0ba01d07509420805070010381004100d040240e40528800302c100c4100314041 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 921907589 1250 921906339 921906383
    0x5210109060e0604022a011401122a05100302090904080703140f070f050c0a060e10020601030807060b030a0c0306061a090a031b030807051005130b0f06060403 70
    0x8955100509400320b4a4030303c01c0c003081e840380c048242d440f62950010420300080c8500c4c00b101c404044000000d180d0080302c10740441a20a9128105c080c850f0754840d0240091ba05c034a401c4c965503000614000101b03825a80c03001d503c1c03482161722a03004850710088290080e0101c0c0c000e140000c1c016401440c20307140403211604001400d0b000280203a4040c40407180e001c08036461074036481d1080b0704080d22a510502c800701b251504070741e1402004885106900c44030008005445541c1b2a1401500440207200d08d0720041c9170317070b0421503021000410205081d10101d800e0b040e007100c00420300c02030b100042031403c0e0050b94002c2a002100c0800814070041d80c0c0510700392407107120301030025041140415454022241e04a60000e111203041002950200040e00c51a0864184010103650307602d4580c840d41085001f901c003038108184011807090a441044e0340110b023019007403103054951b1501c1c1c5040c940280303c0c061040c200404282280d40e14410f85004503408510750181c40c18000c4120 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 921908839 1250 921907589 921907601
    0x8030405151b03060109180b0f0d0b01090905030405150a09060305042111030a0908010b0d080d0207080405060714010608120a120e19030f03020f03040305210109 71
    0x80c41900514848501100e104152180100026103803400c02880060b8001001d0b4409484181440200b4500080b2810800b29499044406481c0081c0074842c10041c0060f134410f00c0421403250007681d01040000f0510462281522081d0000051550b12403410520358411900815404034401344040e004905070700007043c000001e540c0e2754214944d02c140c29400d440301510003c00c504039880c0e140c48001409404420501c007603141100c4c0d40c503503000500d0b04552012400f100011000c0700d0520110100340145800721405440c03400300480305440e000100c0c01814008920a9000a02e640a000b41030094802502004040e0741e5211014501264820a41a608a40c83d424072000052610011441030f01d8048019102032600c07251482c111503850700d54007400e4040703035079640640885c241000001100300b80aa00d280322510282009003006030402c00d40d10825004100001c10704c0c0d004010340e03801c40da15082070707a00d6821f400091405030421417084103007000d04000002c1e00c0b100941002e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 921910089 1250 921908839 921908843
    0x612120f360303190503070c06061419050619120c0e030105150108181606030e0f06070914030a0b0901051017030919080d08070f0c021005030c0c060103080304 70
    0x80380d0407505010516490340116151030550442c03420803610214041c5004552001c0b05185c050314000341c82e902d000441c1c407541c000004415000c0b01c1907650381802d034074507005820040a241b00781d920300700001d400e61081c0303840d10410091909241c9030150181d00e1a5045007040b88052001c4400b0701c1c0e00402948510390524840d42c00c1001090a80704807221020541c081a1745031419941c030030a0300d601030100685280304600c950303511601e5000000014602400482d0b07004124101c14244892030310f0181008200190000000d01034690b80004c8200100c0740e90840c100c00341c0c0b401000090408681c54800b0b4034009004042140d500d07010360142d4801c5003200380398102d940d21808500f04116001e0100402ca82c02006400c40600d081c1150407001011032004240868550a02600b84042690284041105201802234881d00035000881c0d0000901d007401401d1090340005403840c40241c1c000050140020205681d141c10408442c4000002d804480b90f0707503036a03d80396040d54011102 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 921911339 1250 921910089 921910177
    0xb09010b0a0501051306031523032e05100b160c0b040302240f070503040608011d16020c102111030103142805060612120f 54
    0x702080a601940554a4041c3d10f0040341d4034850504000754003c0420040900a0b0b0207445070000700410a6100340045691008416403001d01c04070030301d8a080d0242c05440c0c0d40c420031101008483d418011105042000c1c02400710305a1034040c1c801209900e40e410800c00d8035000107642c409440210911030000d403242d040100324907034a204c1000e00d8040c80c04002e500403508015001e1802e1146910100702c8950507a040c6404a144260410303940324a808454540002c04c04021241d0040c2c0d00c140140312200031f080c1400e12004039030806484c000c3c40c0074241d60042c480040d03107910030030a1045010340604200201640680042c003100ca103104100f0415802001001e2940104d00075101e00e00c01718400c003400c42c2d01350b81d140e0304000c40d01420fa80f0184906264000c091903000800301111079044c1d01e514400c4d00e1410218209007005011901408501040c19480d040008559121049808504d51501401d0164070031520500300010300d030045034801e05130314404040d0340100006940380 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 921912589 1250 921911339 921911359
    0x1403210a06030f0b07122a08060f012604030c120302070b0c0703020f030c011505030c0616030201112802010911010f0c061103010501080a0b0a06030906090b0406020405041a100c030504030b09010b 86
    0xc0102e07101d208c200d502c01d0300314007044803007149035009000700725024040d40511420641038507002d80d042c0c102128103500243e00c2e0007440043c00108940c480e0800f201c0d00e420b40c03521440b82c40d003121008003e000988180d60001d05074060502c00e0000801020350841581da8a6100d443c0c01c80c040c0234144180c42040003200c000154900c0c000492605e08480030301540d06101040c0d800303501085201200340c4c195526206403080d62060724005082c00c40035500e2050711003214a43c0c10244e2402c03030640c0015613150491400201e83d001c00700304105c0901340307003030503040d0242d40d0f04aa1290400b01c006010350700744104114655055405141a074030f083c1e071075402d561b0b22114044182c40c030000c0026044902c989041c48402c0c80307500002c40c0d0500031500820003141c1680c43c2071031440f0440742601c1483d804202800545454010b04901d07082d0503210055421000c030000c1c08407507901090390248031100d1507403020035014400743c4000315000001600303a440c083c080d2a005e820307a41289485201688 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 921913839 1250 921912589 921912671
    0x705060114030d020616031e0203090d030b010203070b040209131e0b0f07050708030c0f07060608012d09170a1107060306080303131403210a06030f0b0712 68
    0x151248075020800f4081d5a01b40410829001000c1c01e00094200d003200040c000e50581143c0000c6000d40c00700303001062110359000f0014201ca51007006203045403c204408400308000c00d0480b41c00c01d070103d5005010361566180407407460b031000c1c0010214100011403000d030040500c000280c1c039006079070300041030750b8a4400c0d904905003100c0c8000030440503c41003011441020281d0741c4210041c0940d85080d0491a901025402c00c5500b12100390700c4200601c00040c01303000f044901c2203540c041270b410465010824460030200c21174040480e98410502003030043c8808110000f000c400b440030f07a290080c00e402402101144000c2c113191043d00b0000803001d110788910030480f1600000740d0305688440c0b2000c14044c001003c01e0340d00c2001d001c40d52504400510042c0a406180c0380c00480f01c080c8442d0b609c04d685d02c02051451003520308201040840c01c4186104c000960041802a2550300c04c00c0642d18050b2903440d803603031103142c071042502200d00500b070080001141d148145001d00742c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 921915089 1250 921913839 921913843
    0x21309050105010f0c1e050d0f030c090501080402030c090f16020606010f030c0905090c0903010e030c06040b04060212070504092a0c02030709022d040b0406140705060114030d02 78
    0xb88185030019aa5559460b2401c0c46680c0a0080c40c1c031401c0c48841c03015102c6422124400054020345658012050040c85290031950403040382c4058201800340b04032603034000d03120740421301c5080d0620019600080840d034003842a00722460700100614400e00306400b04040c0c81b64204c42079006d50802c01c00c0d0921007800000d10f5407041005039103104140c420700c0800c9018024140402d410300c5078a10001c43d19070303038a8000c144900130000c3c400d600d81041e0010075080d2a408200c8a01e41c0e001084094280c01e00072408584c4150031055215680e00da0b450610024428401d4803c4100c203094280040305600000810484200e10414444451041c60315a102c01c012100440c045441030300c4180380d1130048031400f001d64001001c3d1040240d0350260403043cac0e8840c5801110140110b5006400d0541c20b00000101040c0440c3c080d06190404100d80340710721a41c000d81c0b00780318096800b015a481138100b1109000d1340101540d0340303540e54401d080d0b9401d00c51040c0d60b210b4050001001805480 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 921916339 1250 921915089 921915091
    0x1407031803240612060b010c0b0903090a05150d2004060c02010f030203130b180106080a030801170d030f060302130914030a0e0f0609030f060603061b0304110a1802130905 75
    0xb4501134507070a0415a80c1c0c4500900051380d03001d042c450044240d6021580e40120184601d80e000090f6a42d1000703402003000350f00f01da070401845095149201025001144190b5032400900380b0002007011240d501806640c4180382640c1034000000350100324190701c068000c81a074402e032075010b031500340d001e426802d0780811610781452040380c00d45d4801040041100c250810340601103210384002d104155400e503101d681101c4d819a00002480c001c050340055101e0040c5110391406160f101d20800e0b2a880e0b140c943c451300101034032402d2040140d9000d038492801594000c0c05802c100741c80801c16005130030107100035104c5486139281030b2848000403048480020041d500c0d54541e071004400c2103a040d12078006950003440511500c2400c5c0c0302000a2401d08000380e0003000c061030103100f0140f4014006210191000c12101056003504000040d00c0d0000d80c40002015051444404224940429401880300c1500d071840c1a18240c02a4000c02402480302c4d0010459038403440c00c6800d0303c078 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 921917589 1250 921916339 921916349
    0x723070611011d0a06050411040f0204080f0c0307060804050c060c010b01020c0102010c0e01030216080a08090c01090509041202160b040f210b0c09040c051207020a020114070318032406 81
    0x7013000440300242065209035401307031040c50426001144100441d04440c011844204101c1c0e00080602540030100194402014504010040129180e01103030716247d051048500784a40c00b00400e04001e0140032100c5d1441d0083c0520b0344540a0303288060203440841d5569000d4018281e5404481d48103004c0d10540703010723980340c01c5900000100114001c0d80f00b03e013400c1c14055604895400959aa0014111484107030703a45801400c1000c000c5081c200c1503600c8134140903200381c0c10001e40e254090b001d40d0043c0c010000d0804101c20250580c24001d4120b84511400b45500c1c000c1f0b110f012180103441031721030b407a0030034500a440d11100c42d0b12000e503120700c00166a1241841d0005034002003019402402e81000354149501080490280c2e8444c2c1003010104100ac503a00100700c0b1822190b40e8000003e10050031042c4040d000646081007000c200c0b400741200095000c10b25000741e8013019a07890b4001c00307041c06944c90825101010518240075003001d14500c000c0320f9064540a070760141d40c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 921918839 1250 921917589 921917593
    0x70e0303031503010e01021908100e070f3b030a080301090b0d0516030b0603210c01020909010b090a080f1207062d0506150723070611011d 61
    0xa20741040e0407450410b260b4034180d01d9074860b840ba035403079002030001e0001002c04407260807030300c91280e0000d41201c42c002c06584924041c80410071004420301220b940125440c00c003d10164400401250f07408580a9006682d03000c125200d4030480185104500300103c074602c0180d01c010802c1019280c4507e40390207000400c0920040c40070300c11507445109040030080540c40c0912040e502d9900340b050625108884103036084040013400003040965074044002c0340684010313020100c0c0c419511188000500c101e0fa00030a00c0c5c1c00c1c100c001d5040b40e10006000301420380669459034840c0083d0b1240340000e0041c0303d100000204c9040005a4480741880e00d40507029558a8507203e8a0541040c001903d0960301c52013075451012181d903d40300c10102004441500121103a00300301076620107130405000e80c200524a0f12a00c041a055418443e404500c9020300045412140724180700000049041e02401800050050700400259000c007083d10003482444140528035040341d2070a2070b1203a480d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 921920089 1250 921918839 921918841
    0xf14030601052707080604050a331a0d15060f0c08040f0b131530111b0a02060a050a0327030806030309010c021507020d08070b070e030303 61
    0x907240003c8000806505250410000344041c00411580607080d200f4101050031441440400d0070607000d0076a00c01100d00302800046200e0b107410203000318004580010881c0c030a00080c0b980310018454000b80200449803000303103a0b08a1100c071581c0038081c00c1d800146032010007060b10b00750003200d5049401c43c1e15000705508101d40192580098148101d031864020040407800f00c02000d03016001d016550440781d1102940401c81c10001460781200507002880700c0318003180c0ba800b60102000340780e070328100c4002e01091000d010320b200da070084484c601414600000c03125505000075202c100034284030410f400c08a110011b48540c0b00c244041c3d00708004104240c45140920010291101c641c640000e40c508210910114400d02818181ca00341ca440000707014903034080800340d082a0101e02031894003628000280803074a0050f0003d0003141480c4541004103a111b080e9844541c014043c5c07407030310655140c086075650045c1000c550b040c4111001c10b41e401d208002090401314050000c4d0f1031 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 921921339 1250 921920089 921920099
    0x2340308030901090c030606060e0a180e0a12050a12020f030105040b130c0203030709082d120d020301180c020606240f0403060b09041a100314070f14030601 69
    0x441c0e000415640301592188801d400050345004804015800f0b9880060102e04000300180542c070350f88031161144060010034040f401c0c0d000d40515603124840d90004607017140054803414800c4031900600405000344502d44000e400400400301c0f401141c2c1c0e00000c0107031b00500d12049010300c1c91140810002840188058241a840000040c1008201300c2d0000605c690210690f00404909030050700003106011016070041c00c900060310380d0001820b48026007203a14441c5c146001b2049034044000010150030140a01c1480c8460402e140d11307a91300d600d800109800b07540700b0310a05402015424001301c541285200349150110320b0390240800c0e40741d0004100303540c009009201c540e600d2003c4000000c400080c010150511410101ca844600d142080c40840b24242001d9000e01c80700403c10000a904e8141428003003500510030444e6143c5084401c0e003012180c0006000200d035019080c8400070020303a920440f4064020f0002c407a40700c407811500580c1c41941c030b035007642c0401c0040c04 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 921922589 1250 921921339 921921353
    0xe150a0602101503021e010206061c021005040f060504081519050c0f070f020a050301090b130318090212090309010c020f030c0301230c27010c12023403 67
    0x4012003022484015125000583c6c0c0d24890001140000ca12091070102c55070140010f030b03172144007291000f200d00101c00e007200b98035070f000000034880d0346192081da44a0340600151b0380038180804008600b55142d40b805400f07507101e8014200203214001503001915440443c851164103004003844c1c46c1f6207a8081c010181c035015262018601042c05400104ca010f80007801c0750030300035141d071400081c0d180188801300740907410150099040c6070075000429114a41550011881c15560350241c80604040307402c400c03140d0b0140800814540002070040317080e005011141c8078001d942c0500d848038138009641e03205500f145c07404903078603860b0b86001d4501034104101421000d0142c4074803540c450006400c5914506568070407150003c1d150117820500890740d5170242d43e0b44462442c1080c400500c107501120322480d001405c6010145202c075074420b91003101d0341c6911030f030750500992203404042d40713924107003224000d1481070111442101c44101ca00b000c202403501003102c1c2079815511404 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 921923839 1250 921922589 921922601
    0xa151a0f040905030d140907030b01120c03061e0e0c0a090906020903010504080310061d06071b062303041e1b03060f0501050102060f180f0105010e150a060210 70
    0x1607403150380c8503564408107900f40f00415000c180e01100045007401c41c00420328405003e001e21002d83d000d03a20503c0000c60050031941034602c020416404c00700f145ca003400c42c8038269000100180c0c2820540c01050018070310102d03c0c3d4090020501c5451149955159103982002c1c0310780e0b2102860700c1c10860a01950301540c60780e03006090161032b0902450200f400c4d1031050b03d080f20109000405c020070500188239150280010b41f420b0000d0512642c80341c12207001a40b0614410b070800611402008441c0b0500c4c9888a030782c0200001d1280d9a00003d803020002540c41e5205148941031440c260202d00c045078421984407a4808107a5199022030407281c10080c4104c038602c2c1c03119500c86035828800340359401035204600200700c801d11219108240e48042c0d005078103540c00182031040d40d00769464034550141d906017020740c0040c0d11140c058904490720349071088552802002241040400d507045104001030345014018198202c14480c095000e407050f46c0c010f800c1040c4528078604640c0001c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 921925089 1250 921923839 921923869
    0x3160f02060f0612010e06040201170f0f06120a03020d0315030804030803091617010c030203010e06040e10110d06050a0b12060627010206010e360a050a151a 69
    0x45160f04c02505805086503004402040345a0060040004645e4003094042500c1d002c0241c060003420600c0c00e0054980026051201001c1d888002490540340c4072800390381030301030508440000c0c80074100030751621202075a10f40000e04003a466401d41714043d1f07410088a81c00820746103000e18544409006810160525459000c0c079811151078802407880304000e840c0783c2c103415600e081d24032003507801c480182400340d00f070500600040142126902d59103070f002200350380c049503030b80f00501c06031305000f00b030312840015610380407104140d0410100a070034062207000e0100b245548031010400081c489120754000200700700030707103901c00d40000040b81d0084c0c4043d081c1030810350140c680300c2c402075403c1c521480d900e550300c50185041da81084001c0c01811001300340380c05030070700c100d4200c4015a00180d0911402c120048401956403a02c004159290a42c0030349030080c1e0145407044d10f410340b90740140c07100e601002140d040030049104441401c10034000f22500c048180c01440b20603001d070504 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 921926339 1250 921925089 921925099
    0x5060a1202030a12120c17040201120f02031503070503011b0c0f08043203340f0e0906061e060c010f02030117030702060403060b060d0e010203160f02060f06 69
    0x110f003000684118010140613901c0d01e80c0d11809084c10868000c581c0c0000704074003080407440b510800b02407858a8039402640a1030200020800c2402400180003150040065248000308010340140d20b00380d52000c01c5401c6040d14041507071581014213841c40c0492468032104904000c220180c0100851078a03240700c3c94420380d80c840140c542c0343c265000b503440b01500202c000d0000a050300050350071004201500806206015400f005c2035035048a0700421140c2c0c0302460040c0074104050010303010081d2103030b181d0340070a40c913801200d0140840d80325900503074512401080d40c0c14000f084440c8100005020b404d40103a440c0c02000007070001448564200d0303010000c0b01c016004c28007076000781c07a136800b40150780c82d490024604c03180000c0f0b200b80c081c030740c00501203a00140e0380c0104440172a03400c0b680114032958a000082e0b00b0f8030a05820034034103441d00341c3c00300c2e000d4010b40280d03102c3e400c0b5018418403000030400680d000c00b20042800300603042000051a08400c455089812040184c8 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 921927589 1250 921926339 921926353
    0x2060904200f0306040605010c0c09020a111b01111203060d06090b1f0b07020622120f0c050904080307030c02010f060f05130c0f050f07240b0405060a120203 69
    0xc0070024592040910400030600001080b0942c01c00307000700b1000f048203290051103039070303d525000c04004050148101182e00020b83c4041c0d18804c4a0707000c805100801550484035003001000804070640c480e25011419011080c41101c4002c1000980f5003202280645141e03103400030001da5500c0500222801076807860040c0100b030300c0c000400c5c41201c01d03110702040820302c01238000c45108150b101e081c000008001d01d40060701e409080c1c800c5e40c3c2100003124001032000c40405410755283e003040c0c99052122410800713101c035906005400a00602d51130b0328107034442090010181e004c48001e0a28103041000c218581e1195203d00c0c0605407a20000945402c048004801d03298140d014080800e030000050140b1f15040701c54103090510b00c581000aa0b1001c100030300740a1080d101181405808222032a10304040800c450001d03a000d05d00800c10485054441d20300b041101da6100504d00d001c45061044c00c0c140300d030318011070005010002c0c031454850310041e40e040d006412a01802061 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 921928839 1250 921927589 921927641
    0x30213060b0f210f090610060c060e0c12100b0d120c020109090f0b04060905221b1701050a0903050313061b080f0702010c08040201051b060a06170a02060904 69
    0x11040f078000c2c4600d940400e0182020781429142400150007015500801075040203915003010b0408503403a40f080020aa00713092221490601002000841d00800304140c40911180c0100d2000d02e11006408100644180d40c81070146d601d24810300241280500000220484e01500400305558414502100f4061b114507500089e50310281100424513203a0841d003080c0d107858010b1601803c0140c008200c03a140c454807555000743c41010180c0320301c0c00303881883c007480041c451240786c0c0c00560003c00400369855020301034454401c42d595206500e80804a0582501c5010300581c1e10380568030307603041d1345413243c04000a20b00d82c507088a110303981d00b080905950007400170100c10f4026444183d404d00d401a0504403601d4001c0c491000c40e49080c901200c1990441441600650286400c0d81ca03054040683d505412043c6a00e07803040c480d80703007004801041c9130009402d0740c014816525109a4800c0c2c1c05944080c1e910700258406010300c441180703401c00794801d0b07400e14010480012104220 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 921930089 1250 921928839 921928897
    0x81509010b220f090f08130905070512090c03100b0301020d0e0d030b0a0b04090207020418350f0d02190309021509031f061e030213060b0f 61
    0xa02c003039450801071051070140c02070540c072074000c0c28040d0030401d100e810010303580c44004001d20034006140040106045018401e0200c1e144041c204805080000e03007407040000d405030300500900c003880094600020034550f404038405280020140c0100222a0b2455844000d0030043e000980c141d036003131000749440300c04e42c0110b00c00c02001e24050414502c41d4840201996500c0060714041c40c900b060070062109480211402c0b0b99001e0b40041c2c548103184001000740c092540303004501c2e4948103641d8240000c0c0c0f21341110215890050842152501c00080010300d805c44c403e19100400303200e0031442c000787d00020940d04000010052802d45c08100c83c0c112200122842800603a948443d5011414504004c42c40001402e03605400d101114002070b40d5400a03035440111902100c00400c0744510741c0c7c1100000c2c0c01411408a8030036109107095500d80514401688112900d03030b0949036504080c89060300765900041150300d055011446c0070b141d94800004800708074a4051800c2808040e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 921931339 1250 921930089 921930109
    0xc050f090907110d050c19021305040609140102090f10020705010320030405030415021204140d052e09030e100908070e0103050f010b060a121103160810081509010b 72
    0xd85c0320940c0368070000c280a0b2611481981c50701035154103030a00c81c050382c0c0b00720300c81c910500b2480c0b020a09907100e241040c003400701080020050036070b60b00030104140c810340103420805400e90b481c0740701142d40c004002c03c024401c940d1501603002110705100c554480c0d048a0501082c4400e0101010b400988088840e802190b09680307070341020409001c2c1109030180c00c51080250f1000b04049035890308116250302c2140303d2131050300003d940011140d02c0d4a02480c80160f08142503480611190322010f0100b03030780c41c1d40714800003402105209003405d1480303000c1089415a95040c070840400080c0b020000e001e80c4c1007000c0c4680301ea0006100442002200f015241d008c042d280383d9403542c0b0703100d89070007521034004506034108120258183c85850694a90b41e1103450b0045040510790050001031807407642c036617607010000003008040c40d01ca40801c680791041b0b98030500c0f16a540310240644d2034050054042c0c81d040700c40c521a544000f6240240c0041c040c500004180c1c088800086004107 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 921932589 1250 921931339 921931363
    0xb061905030601020625030c110d180608101401050c010615080108030a1d041e0501030b130305031b1b06070f030b0f1207031a0603010c050f09090711 66
    0x4000000c00c082c03941d0500c040c41d040002000307503c1c00040449a12080001c4900302c040c2003564031490300f03444500c1600d518641c924a04151401c2280c3c1100040c81e1800c5003078640e200c001080320002d06103109141070361140c13100b40c0001560300c0c2001000500e80c0c12094900e17041000501000c00b0708407082c4074040c0103101c44070800d400d1200c0e40001501d0020b0581c01003101e60400c0c000000c003250000c1140040600210036544202000b400182c000c14491208031228800658142031000145d0b0000b41600c1c0030341580c00c5160303500620707100b00300040b00b00113001400520204821005024044415907000c0f00030703e0400c0e051040b050310701d245584100301c00d64821424068002c4e04102036014070440d524040c00b01d50350417004601402461038066000303040c02d0081030203045007807000802035076000250919075154041040304928094440620075440c101a40e000c2034050404c58040f84102242d03d41840351450820019070801880103060041d0042c0b00b504041d400e20204410b42 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 921933839 1250 921932589 921932597
    0x30521010302310b0303040f0f091802030d051e03070302071a131b08060c0703020c0105090f040e01110a02030c100c140c01140103030c050c041a040b0619 68
    0x5803460040203650306103d001c0350b06034070b0280764525140594550780c25a00b1010100800c481c520b40000ca4618810366224184c400712404012900d46010811502118617900007401004d80b001404001b201d154a0000d5142d40404011002c80d405203002e06081c418603200c1c0c0449411110340e5254030f9000311440400241c2c002648800c00040c411402c24a83d0302550141082c5010356010003003281c0c5650140044c16400c9103500e16001c0c10040502800c55002680e20360b00f08460485401d801203001180940522011250203521071002da50794600000c00302d0070030b145a0400d200090840c5c49100b2019521803400d002c003501c581008012040d41c60b4011036035407031501842410a00c00d411150b14640c208a10031651641c03040d121000c4038030340d5000070342c6c884903907d1150052400c071901c1046d03198140700010030b050f08809a294050700840589140c0241c0c2410030040f52403d030b100300d0403080c951800341c50600309980012040c00340503080030320706203080e0491010b00400481c82c00c005 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 921935089 1250 921933839 921933841
    0x3030203060310060e071b0f1208011502060a09020f03010c2304050307051017090c12060f01170a051509071d130c0b0309061f140d030521 61
    0x140c101044810001c400b80f5008000c0d90f401e1003505d400c09072028101d6410440c1034003010700c0c24001c0c6220f041500c1c0d404801ca061500302c0385003d02603444912800c0d40410a140f000103030100c011100d1440c1c2004550140c165980d848005070002c20304060141d8001c0300c821900115a1000d118080325283d55856a8035a44000715220207082846d400d2034025980070303c03040025490000d0541c069400c2150a81c0c1e101a004804550000b015501d0120502e212001c3c040b400d44007040d8a1140c480c1550350f40d480510504c03601da42c400d000d464031310290032010300400105002c80e51056440b024030055405844403910703107600c1e11140341581e2150324600000c4c0804404100001030042c0100f00e80003500e02d0070784c130803282c44400040140b0501c0000b12141c00400610445640c0941080250030351641003026400e6030780c010403600203e541c409010802d111000c104d90750f200722040340c0703051581c1400c030707800b0b001d1780ca0040d101c12001c0c002c0600002001c1021041c031403140000c2240402c042d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 921936339 1250 921935089 921935101
    0x815061b060115050304060207080c0d1706101b0213020406031d0a0c06030209190b03090f01050105240d092d11041d2d07062c0a0303030203 62
    0x10710300706a01a10903200c3e6a00501c098540200a0341d0303001e500800c0040c0c48454a0030420118070a200c022140d90040c8101d60110070f40016a041100c4200701360001b407540c50f4818001405601e1001c800400c01c400320086280905910103541184094a4001c000140021901c00d0360020380000001c00d4950b82045040303105090456400101075004140e0302c06280c403000b50100d01c9001d080101a0009003401c0f40786c07500d00c26100181b1014000c40c00e21503844100004503001940d00318194010403100704078480d01401043d050302c10041c02c1040ca907090301c6c9a0741440302002c45800d0004010b0200615400182c0305154212703008081c0c2200100ca40e080038141da0ba94080010100c00300703980d84e24040f405941100000c05020364002800c003410030200719a81844011072400c0748031303605d000c00d03140340b60960001a400150262010140c0c2880b609a160000340c00f4100c001035100d45205406c2c0300c0c5020a11074122000c101050404003100804c4000d00706400075400300340c00000384a2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 921937589 1250 921936339 921936343
    0xa05070510050411042d390c050f2415030c060c1608070609080303010f09020d0b03100e0c1c0227090601141905060901120f0f0501050612070815061b 66
    0x50b01202e41c07d4194040c0340504452040306c12034404c07100400543e0044c10081110400c12060042101411144249490015910391a140402d503c5001c200080840c4146500e0354110300070b0303480107001c4c00e185400302c014024142c111300800d00f26841410700d60848500000b08440103002c1d040e000e003190500b054006401d00c1c44550010000368010030040085101c080480010381d0684900541d6980c0c40503080c0c5c01500100689a90500170900441842c000d180c0c00007000c05594801c2c0e0340a42550410802208100d00c400b034840f80480e00a04014940111910312098000460308020301c1c10003410fa0b081d90040f200041e20781d02410052040c50481d00c404034642008403443c9007c00c1c80703c59603004d003494a200d0300b401044081851400c1fa0b005060609003021901c0041050f454420140400740020248a5450b641b13420004201414407000310364140451000e20100c54a5480c412502848018966000302c04500c0300101695209801440400140c080c110200c01c5103282240c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 921938839 1250 921937589 921937631
    0xc061f0e01080d17010f03030c06090b15100509090103151e050906131104110417030d050f0408071403090402210106020313060e0f060a05070510050411042d 69
    0x110300c4074550304c0100000005030002c902680c2e411300d404108180180303800c0b0090807501200400c030441800401c10014880200100441c100300e800d151401283d200c2074a40e8401c00445640010b5080f0042c07010604400c10a41060142d200c0000c035612003c2144040900e088940c01c0100d40b00c0c0c060145c0f4680801101d6000942d115501c0003011042d5102100d0703881d814001ca00550304c0d40703401280c1d021400143c03401003c0300c0b0201710f41c0c0074034060350507220340c0900b00f0764600c240b8240100390350040a14003144110740c40043c4a02e0000c0d59112541640c001d40200e20441c8020040c0c03000c00c0d280c0c0e00242c2034000c40c9051000140202058203000301205805c090119070090000c800304070182c944407011101641082600c050004001c241d204504028030b5400c030380000360a0f05143d074000c2c0200403050043e400e031503074560301918240c10355078140c03000b90003141001c458500618283e4000030030000100800706800706003440e0040409204048421050ba80710340b45a01440b620302c0780 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 921940089 1250 921938839 921938867
    0x40f06030f0b01050304120e030d0f031b0207030f0609022e030c050f07050f030c060412020304050a1403031314030106050312120c041d18030c061f0e01080d 69
    0x40c4100e440600000345180002040a050501010141c0ca6088d0180c0e542d61a281c401805a982e210020500540000d02518000700005c0c40c0100c03002d2048944910522160700980c0944106407440c1c41d1102c040a4402c0c1c180c8025554000040050703503659070403c0c1d6803110105045035126030540c2c0c5401061148000418181400c1c1a01d11099002c0e00715901ca4070826640d54490110307042071b40c41c10710041400c20b400c1c440010700348511800021054400c52244101d0120301c00c18180413a128040e501c3303007070b81200800038144040000c4003007032880c00801404403400c0032088100d9000080182e40200180302c0d100004800380d04003070250402904c002e5000300f40c2c1082e0b0b10000c40d00b03881091800d4403000c005002061000203c042180d0040100a1030703600707580f00048075820b0003c02030b03c800a0341d9085041807481c04d0408015a0207216500c170291410741e071620b03810b4203402c9811100d42803240d1001c20228a02d00703640c0700140030301003110052006411105018008071400040c0f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 921941339 1250 921940089 921940091
    0x31b0215040813030804140f1f030906180f02011b1e060608031206010f210e0319050408152418131b1809051002040f06030f 55
    0x12040020048441900990b002c2c041c0d035902d10030b94160329081c80203500000c0c081c1d07a0000700045c0500440032060420700003140e40300154480c0c00d04001018421154940d01c0d41d0070250544540f80c0079511800025000c0d150100e8407900890081d80d944d1341d900c0301243e448400f00384920070342d68018011903184140c050034407010185a2a007008441800074809443c05000e0344190030008150000c000a12101c01200c0e01d50060000034200c0c4c40e02110004e0000d00c0941ca4449128801d5280c11080000000401000c585503040100542400031072400c05100400c00452002101000c1e440680c11541d54141c407282005c405600700350840e90325018800e2100c081c05042859079101c411340494080500b581c900d01d5a01145100e96a82c08110200f2601c504006c2074121070030540c03001074800c84c1d40c100d5245a5104880400b2100d01800007400d40204c2080d516405a92102c2d840ca1700500440d030840c994000d40300d0580c0c0c0190024030050403d40e0003001819014064114a02c0c40b401d4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 921942446 1107 921941339 921941353
    0x60509150c12190504050907270b070b060301062412090f030219031b020a030804090b030d110a03030c0c05012f0301080c09060a0801050106031b02 65
    0x1102c0080300045460010038051281c41111700f583c800425900c1c481d02c030302c02d089a5206034514035851501c403d00b4180c0c000c80c5041c80f00d80013003140d0100039a58840c51328050401c000003820f03c600076814040141304910cc0d01180311800e001c1c0340061544210031b043c0c00c840840740d800d0b00015552030410170301e090240c8100c41d885000d019030202c80305000c40e0090808007004a43c000b81c0060604580c0c00010301c8503603076129402d030004014420213900c0e82c95039100d41c2d01030f40c4490039055031030b841b01d80a814140440f01a041c030318104226000a00001651241110b050003410160345031800c81640d8003c3c40d00f04040d5800500030803110030141c0030b04180d004a0f280003480c2d0004591080c181c0206441103a058900c0840030780300982010040c0000b0501c060320322984803a540310040703441c541c2480341c60f0080c074a6540118401344890301d04c107800c084000d001d504540141d8 = true := by decide +kernel

theorem cover : BRFrame.Cov 921762589 921942446 := by
  have h0 := BRFrame.cov_init 921762589
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 921762589 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 921762589 ≤ n) (h2 : n < 921942446) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
